// Copyright 2011 Google Inc. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "build.h"

#include <assert.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include <climits>
#include <functional>
#include <unordered_set>

#include <set>
#include <sstream>
#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <regex>

#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#endif

#if defined(__SVR4) && defined(__sun)
#include <sys/termios.h>
#endif

#include "build_log.h"
#include "clparser.h"
#include "debug_flags.h"
#include "depfile_parser.h"
#include "deps_log.h"
#include "disk_interface.h"
#include "graph.h"
#include "metrics.h"
#include "state.h"
#include "status.h"
#include "subprocess.h"
#include "util.h"

#ifdef CLOUD_BUILD_SUPPORT
#include "remote_process.h"
#endif

using namespace std;
#include "share_build/share_thread.h"

#include <grpcpp/grpcpp.h>

namespace {

/// A CommandRunner that doesn't actually run the commands.
struct DryRunCommandRunner : public CommandRunner {
  virtual ~DryRunCommandRunner() {}

  // Overridden from CommandRunner:
  virtual size_t CanRunMore() const override;
  virtual bool StartCommand(Edge* edge) override;
  virtual bool WaitForCommand(Result* result) override;

 private:
  queue<Edge*> finished_;
};

size_t DryRunCommandRunner::CanRunMore() const {
  return SIZE_MAX;
}

bool DryRunCommandRunner::StartCommand(Edge* edge) {
  finished_.push(edge);
  return true;
}

bool DryRunCommandRunner::WaitForCommand(Result* result) {
   if (finished_.empty())
     return false;

   result->status = ExitSuccess;
   result->edge = finished_.front();
   finished_.pop();
   return true;
}

}  // namespace

Plan::Plan(Builder* builder)
  : builder_(builder)
  , command_edges_(0)
  , wanted_edges_(0)
{}

void Plan::Reset() {
  command_edges_ = 0;
  wanted_edges_ = 0;
  ready_.clear();
  want_.clear();
}

bool Plan::AddTarget(const Node* target, string* err) {
  targets_.push_back(target);
  return AddSubTarget(target, NULL, err, NULL);
}

bool Plan::AddSubTarget(const Node* node, const Node* dependent, string* err,
                        set<Edge*>* dyndep_walk) {
  Edge* edge = node->in_edge();
  if (!edge) {
     // Leaf node, this can be either a regular input from the manifest
     // (e.g. a source file), or an implicit input from a depfile or dyndep
     // file. In the first case, a dirty flag means the file is missing,
     // and the build should stop. In the second, do not do anything here
     // since there is no producing edge to add to the plan.
     if (node->dirty() && !node->generated_by_dep_loader()) {
       string referenced;
       if (dependent)
         referenced = ", needed by '" + dependent->path() + "',";
       *err = "'" + node->path() + "'" + referenced +
              " missing and no known rule to make it";
     }
     return false;
  }

  if (edge->outputs_ready())
    return false;  // Don't need to do anything.

  // If an entry in want_ does not already exist for edge, create an entry which
  // maps to kWantNothing, indicating that we do not want to build this entry itself.
  pair<map<Edge*, Want>::iterator, bool> want_ins =
    want_.insert(make_pair(edge, kWantNothing));
  Want& want = want_ins.first->second;

  if (dyndep_walk && want == kWantToFinish)
    return false;  // Don't need to do anything with already-scheduled edge.

  // If we do need to build edge and we haven't already marked it as wanted,
  // mark it now.
  if (node->dirty() && want == kWantNothing) {
    want = kWantToStart;
    EdgeWanted(edge);
  }

  if (dyndep_walk)
    dyndep_walk->insert(edge);

  if (!want_ins.second)
    return true;  // We've already processed the inputs.

  for (vector<Node*>::iterator i = edge->inputs_.begin();
       i != edge->inputs_.end(); ++i) {
    if (!AddSubTarget(*i, node, err, dyndep_walk) && !err->empty())
      return false;
  }

  return true;
}

void Plan::EdgeWanted(const Edge* edge) {
  ++wanted_edges_;
  if (!edge->is_phony()) {
    ++command_edges_;
    if (builder_)
      builder_->status_->EdgeAddedToPlan(edge);
  }
}

Edge* Plan::FindWork() {
  if (ready_.empty()) {
    return NULL;
  }

  Edge* edge = ready_.top();
  ready_.pop();
  return edge;
}


void Plan::ScheduleWork(map<Edge*, Want>::iterator want_e) {
  if (want_e->second == kWantToFinish) {
    // This edge has already been scheduled.  We can get here again if an edge
    // and one of its dependencies share an order-only input, or if a node
    // duplicates an out edge (see https://github.com/ninja-build/ninja/pull/519).
    // Avoid scheduling the work again.
    return;
  }
  assert(want_e->second == kWantToStart);
  want_e->second = kWantToFinish;

  Edge* edge = want_e->first;
  Pool* pool = edge->pool();
  if (pool->ShouldDelayEdge()) {
    pool->DelayEdge(edge);
    pool->RetrieveReadyEdges(&ready_);
  } else {
    pool->EdgeScheduled(*edge);
    ready_.push(edge);
  }
}

bool Plan::EdgeFinished(Edge* edge, EdgeResult result, string* err) {
  map<Edge*, Want>::iterator e = want_.find(edge);
  assert(e != want_.end());
  bool directly_wanted = e->second != kWantNothing;

  // See if this job frees up any delayed jobs.
  if (directly_wanted)
    edge->pool()->EdgeFinished(*edge);
  edge->pool()->RetrieveReadyEdges(&ready_);

  // The rest of this function only applies to successful commands.
  if (result != kEdgeSucceeded)
    return true;

  if (directly_wanted)
    --wanted_edges_;
  want_.erase(e);
  edge->outputs_ready_ = true;

  // Check off any nodes we were waiting for with this edge.
  for (vector<Node*>::iterator o = edge->outputs_.begin();
       o != edge->outputs_.end(); ++o) {
    if (!NodeFinished(*o, err))
      return false;
  }
  return true;
}

bool Plan::NodeFinished(Node* node, string* err) {
  // If this node provides dyndep info, load it now.
  if (node->dyndep_pending()) {
    assert(builder_ && "dyndep requires Plan to have a Builder");
    // Load the now-clean dyndep file.  This will also update the
    // build plan and schedule any new work that is ready.
    return builder_->LoadDyndeps(node, err);
  }

  // See if we we want any edges from this node.
  for (vector<Edge*>::const_iterator oe = node->out_edges().begin();
       oe != node->out_edges().end(); ++oe) {
    map<Edge*, Want>::iterator want_e = want_.find(*oe);
    if (want_e == want_.end())
      continue;

    // See if the edge is now ready.
    if (!EdgeMaybeReady(want_e, err))
      return false;
  }
  return true;
}

bool Plan::EdgeMaybeReady(map<Edge*, Want>::iterator want_e, string* err) {
  Edge* edge = want_e->first;
  if (edge->AllInputsReady()) {
    if (want_e->second != kWantNothing) {
      ScheduleWork(want_e);
    } else {
      // We do not need to build this edge, but we might need to build one of
      // its dependents.
      if (!EdgeFinished(edge, kEdgeSucceeded, err))
        return false;
    }
  }
  return true;
}

bool Plan::CleanNode(DependencyScan* scan, Node* node, string* err) {
  node->set_dirty(false);

  for (vector<Edge*>::const_iterator oe = node->out_edges().begin();
       oe != node->out_edges().end(); ++oe) {
    // Don't process edges that we don't actually want.
    map<Edge*, Want>::iterator want_e = want_.find(*oe);
    if (want_e == want_.end() || want_e->second == kWantNothing)
      continue;

    // Don't attempt to clean an edge if it failed to load deps.
    if ((*oe)->deps_missing_)
      continue;

    // If all non-order-only inputs for this edge are now clean,
    // we might have changed the dirty state of the outputs.
    vector<Node*>::iterator
        begin = (*oe)->inputs_.begin(),
        end = (*oe)->inputs_.end() - (*oe)->order_only_deps_;
#if __cplusplus < 201703L
#define MEM_FN mem_fun
#else
#define MEM_FN mem_fn  // mem_fun was removed in C++17.
#endif
    if (find_if(begin, end, MEM_FN(&Node::dirty)) == end) {
      // Recompute most_recent_input.
      Node* most_recent_input = NULL;
      for (vector<Node*>::iterator i = begin; i != end; ++i) {
        if (!most_recent_input || (*i)->mtime() > most_recent_input->mtime())
          most_recent_input = *i;
      }

      // Now, this edge is dirty if any of the outputs are dirty.
      // If the edge isn't dirty, clean the outputs and mark the edge as not
      // wanted.
      bool outputs_dirty = false;
      if (!scan->RecomputeOutputsDirty(*oe, most_recent_input,
                                       &outputs_dirty, err)) {
        return false;
      }
      if (!outputs_dirty) {
        for (vector<Node*>::iterator o = (*oe)->outputs_.begin();
             o != (*oe)->outputs_.end(); ++o) {
          if (!CleanNode(scan, *o, err))
            return false;
        }

        want_e->second = kWantNothing;
        --wanted_edges_;
        if (!(*oe)->is_phony()) {
          --command_edges_;
          if (builder_)
            builder_->status_->EdgeRemovedFromPlan(*oe);
        }
      }
    }
  }
  return true;
}

bool Plan::DyndepsLoaded(DependencyScan* scan, const Node* node,
                         const DyndepFile& ddf, string* err) {
  // Recompute the dirty state of all our direct and indirect dependents now
  // that our dyndep information has been loaded.
  if (!RefreshDyndepDependents(scan, node, err))
    return false;

  // We loaded dyndep information for those out_edges of the dyndep node that
  // specify the node in a dyndep binding, but they may not be in the plan.
  // Starting with those already in the plan, walk newly-reachable portion
  // of the graph through the dyndep-discovered dependencies.

  // Find edges in the the build plan for which we have new dyndep info.
  std::vector<DyndepFile::const_iterator> dyndep_roots;
  for (DyndepFile::const_iterator oe = ddf.begin(); oe != ddf.end(); ++oe) {
    Edge* edge = oe->first;

    // If the edge outputs are ready we do not need to consider it here.
    if (edge->outputs_ready())
      continue;

    map<Edge*, Want>::iterator want_e = want_.find(edge);

    // If the edge has not been encountered before then nothing already in the
    // plan depends on it so we do not need to consider the edge yet either.
    if (want_e == want_.end())
      continue;

    // This edge is already in the plan so queue it for the walk.
    dyndep_roots.push_back(oe);
  }

  // Walk dyndep-discovered portion of the graph to add it to the build plan.
  std::set<Edge*> dyndep_walk;
  for (std::vector<DyndepFile::const_iterator>::iterator
       oei = dyndep_roots.begin(); oei != dyndep_roots.end(); ++oei) {
    DyndepFile::const_iterator oe = *oei;
    for (vector<Node*>::const_iterator i = oe->second.implicit_inputs_.begin();
         i != oe->second.implicit_inputs_.end(); ++i) {
      if (!AddSubTarget(*i, oe->first->outputs_[0], err, &dyndep_walk) &&
          !err->empty())
        return false;
    }
  }

  // Add out edges from this node that are in the plan (just as
  // Plan::NodeFinished would have without taking the dyndep code path).
  for (vector<Edge*>::const_iterator oe = node->out_edges().begin();
       oe != node->out_edges().end(); ++oe) {
    map<Edge*, Want>::iterator want_e = want_.find(*oe);
    if (want_e == want_.end())
      continue;
    dyndep_walk.insert(want_e->first);
  }

  // See if any encountered edges are now ready.
  for (set<Edge*>::iterator wi = dyndep_walk.begin();
       wi != dyndep_walk.end(); ++wi) {
    map<Edge*, Want>::iterator want_e = want_.find(*wi);
    if (want_e == want_.end())
      continue;
    if (!EdgeMaybeReady(want_e, err))
      return false;
  }

  return true;
}

bool Plan::RefreshDyndepDependents(DependencyScan* scan, const Node* node,
                                   string* err) {
  // Collect the transitive closure of dependents and mark their edges
  // as not yet visited by RecomputeDirty.
  set<Node*> dependents;
  UnmarkDependents(node, &dependents);

  // Update the dirty state of all dependents and check if their edges
  // have become wanted.
  for (set<Node*>::iterator i = dependents.begin();
       i != dependents.end(); ++i) {
    Node* n = *i;

    // Check if this dependent node is now dirty.  Also checks for new cycles.
    std::vector<Node*> validation_nodes;
    if (!scan->RecomputeDirty(n, &validation_nodes, err))
      return false;

    // Add any validation nodes found during RecomputeDirty as new top level
    // targets.
    for (std::vector<Node*>::iterator v = validation_nodes.begin();
         v != validation_nodes.end(); ++v) {
      if (Edge* in_edge = (*v)->in_edge()) {
        if (!in_edge->outputs_ready() &&
            !AddTarget(*v, err)) {
          return false;
        }
      }
    }
    if (!n->dirty())
      continue;

    // This edge was encountered before.  However, we may not have wanted to
    // build it if the outputs were not known to be dirty.  With dyndep
    // information an output is now known to be dirty, so we want the edge.
    Edge* edge = n->in_edge();
    assert(edge && !edge->outputs_ready());
    map<Edge*, Want>::iterator want_e = want_.find(edge);
    assert(want_e != want_.end());
    if (want_e->second == kWantNothing) {
      want_e->second = kWantToStart;
      EdgeWanted(edge);
    }
  }
  return true;
}

void Plan::UnmarkDependents(const Node* node, set<Node*>* dependents) {
  for (vector<Edge*>::const_iterator oe = node->out_edges().begin();
       oe != node->out_edges().end(); ++oe) {
    Edge* edge = *oe;

    map<Edge*, Want>::iterator want_e = want_.find(edge);
    if (want_e == want_.end())
      continue;

    if (edge->mark_ != Edge::VisitNone) {
      edge->mark_ = Edge::VisitNone;
      for (vector<Node*>::iterator o = edge->outputs_.begin();
           o != edge->outputs_.end(); ++o) {
        if (dependents->insert(*o).second)
          UnmarkDependents(*o, dependents);
      }
    }
  }
}

namespace {

// Heuristic for edge priority weighting.
// Phony edges are free (0 cost), all other edges are weighted equally.
int64_t EdgeWeightHeuristic(Edge *edge) {
  return edge->is_phony() ? 0 : 1;
}

}  // namespace

void Plan::ComputeCriticalPath() {
  METRIC_RECORD("ComputeCriticalPath");

  // Convenience class to perform a topological sort of all edges
  // reachable from a set of unique targets. Usage is:
  //
  // 1) Create instance.
  //
  // 2) Call VisitTarget() as many times as necessary.
  //    Note that duplicate targets are properly ignored.
  //
  // 3) Call result() to get a sorted list of edges,
  //    where each edge appears _after_ its parents,
  //    i.e. the edges producing its inputs, in the list.
  //
  struct TopoSort {
    void VisitTarget(const Node* target) {
      Edge* producer = target->in_edge();
      if (producer)
        Visit(producer);
    }

    const std::vector<Edge*>& result() const { return sorted_edges_; }

   private:
    // Implementation note:
    //
    // This is the regular depth-first-search algorithm described
    // at https://en.wikipedia.org/wiki/Topological_sorting, except
    // that:
    //
    // - Edges are appended to the end of the list, for performance
    //   reasons. Hence the order used in result().
    //
    // - Since the graph cannot have any cycles, temporary marks
    //   are not necessary, and a simple set is used to record
    //   which edges have already been visited.
    //
    void Visit(Edge* edge) {
      auto insertion = visited_set_.emplace(edge);
      if (!insertion.second)
        return;

      for (const Node* input : edge->inputs_) {
        Edge* producer = input->in_edge();
        if (producer)
          Visit(producer);
      }
      sorted_edges_.push_back(edge);
    }

    std::unordered_set<Edge*> visited_set_;
    std::vector<Edge*> sorted_edges_;
  };

  TopoSort topo_sort;
  for (const Node* target : targets_) {
    topo_sort.VisitTarget(target);
  }

  const auto& sorted_edges = topo_sort.result();

  // First, reset all weights to 1.
  for (Edge* edge : sorted_edges)
    edge->set_critical_path_weight(EdgeWeightHeuristic(edge));

  // Second propagate / increment weidghts from
  // children to parents. Scan the list
  // in reverse order to do so.
  for (auto reverse_it = sorted_edges.rbegin();
       reverse_it != sorted_edges.rend(); ++reverse_it) {
    Edge* edge = *reverse_it;
    int64_t edge_weight = edge->critical_path_weight();

    for (const Node* input : edge->inputs_) {
      Edge* producer = input->in_edge();
      if (!producer)
        continue;

      int64_t producer_weight = producer->critical_path_weight();
      int64_t candidate_weight = edge_weight + EdgeWeightHeuristic(producer);
      if (candidate_weight > producer_weight)
        producer->set_critical_path_weight(candidate_weight);
    }
  }
}

void Plan::ScheduleInitialEdges() {
  // Add ready edges to queue.
  assert(ready_.empty());
  std::set<Pool*> pools;

  for (std::map<Edge*, Plan::Want>::iterator it = want_.begin(),
           end = want_.end(); it != end; ++it) {
    Edge* edge = it->first;
    Plan::Want want = it->second;
    if (!(want == kWantToStart && edge->AllInputsReady())) {
      continue;
    }

    Pool* pool = edge->pool();
    if (pool->ShouldDelayEdge()) {
      pool->DelayEdge(edge);
      pools.insert(pool);
    } else {
      ScheduleWork(it);
    }
  }

  // Call RetrieveReadyEdges only once at the end so higher priority
  // edges are retrieved first, not the ones that happen to be first
  // in the want_ map.
  for (std::set<Pool*>::iterator it=pools.begin(),
           end = pools.end(); it != end; ++it) {
    (*it)->RetrieveReadyEdges(&ready_);
  }
}

void Plan::PrepareQueue() {
  ComputeCriticalPath();
  ScheduleInitialEdges();
}

void Plan::Dump() const {
  printf("pending: %d\n", (int)want_.size());
  for (map<Edge*, Want>::const_iterator e = want_.begin(); e != want_.end(); ++e) {
    if (e->second != kWantNothing)
      printf("want ");
    e->first->Dump();
  }
  printf("ready: %d\n", (int)ready_.size());
}

struct ShareCommandRunner : public CommandRunner {
  explicit ShareCommandRunner(const BuildConfig& config) : config_(config) {}
  virtual ~ShareCommandRunner() {}
  virtual size_t CanRunMore() const override;
  virtual bool StartCommand(Edge* work) override;
  virtual bool WaitForCommand(Result* result) override;
  virtual vector<Edge*> GetActiveEdges();
  virtual void Abort();

  const BuildConfig& config_;
  ShareThreadSet share_threads_;
  map<ShareThread*, Edge*> thread_to_edge_;
};

vector<Edge*> ShareCommandRunner::GetActiveEdges() {
  vector<Edge*> edges;
  for (map<ShareThread*, Edge*>::iterator e = thread_to_edge_.begin();
       e != thread_to_edge_.end(); ++e)
    edges.push_back(e->second);
  return edges;
}

void ShareCommandRunner::Abort() {
  share_threads_.Clear();
}

size_t ShareCommandRunner::CanRunMore() const {
  size_t subproc_number =
      share_threads_.running_.size() + share_threads_.finished_.size();

  int64_t capacity = config_.parallelism - subproc_number;

  if (config_.max_load_average > 0.0f) {
    int load_capacity = config_.max_load_average - GetLoadAverage();
    if (load_capacity < capacity)
      capacity = load_capacity;
  }

  if (capacity < 0)
    capacity = 0;

  if (capacity == 0 && share_threads_.running_.empty())
    // Ensure that we make progress.
    capacity = 1;

  return capacity;
}

bool ShareCommandRunner::StartCommand(Edge* edge) {
  EdgeCommand c;
  c.command = edge->EvaluateCommand();
  ShareThread* share_thread = share_threads_.Add(c);
  if (!share_thread)
    return false;
  thread_to_edge_.insert(make_pair(share_thread, edge));

  return true;
}

bool ShareCommandRunner::WaitForCommand(Result* result) {
  ShareThread* share_thread;
  while ((share_thread = share_threads_.NextFinished()) == NULL) { //从finish_队列出队一个元素
    bool interrupted = share_threads_.DoWork(); // 将执行完成的share_thread从running_队列移到finish_队列
    if (interrupted)
      return false;
  }

  result->status = share_thread->Finish();
// #ifndef _WIN32
//   result->rusage = *share_thread->GetUsage();
// #endif
  result->output = share_thread->GetOutput(); //拿到 share_thread 的 result_output

  map<ShareThread*, Edge*>::iterator e = thread_to_edge_.find(share_thread);
  result->edge = e->second;
  thread_to_edge_.erase(e);

  delete share_thread;
  return true;
}


struct RealCommandRunner : public CommandRunner {
  explicit RealCommandRunner(const BuildConfig& config) : config_(config) {}
  virtual ~RealCommandRunner() {}
  virtual size_t CanRunMore() const override;
  virtual bool StartCommand(Edge* edge) override;
  virtual bool WaitForCommand(Result* result) override;
  virtual vector<Edge*> GetActiveEdges() override;
  virtual void Abort() override;

  const BuildConfig& config_;
  SubprocessSet subprocs_;
  map<const Subprocess*, Edge*> subproc_to_edge_;
};

vector<Edge*> RealCommandRunner::GetActiveEdges() {
  vector<Edge*> edges;
  for (map<const Subprocess*, Edge*>::iterator e = subproc_to_edge_.begin();
       e != subproc_to_edge_.end(); ++e)
    edges.push_back(e->second);
  return edges;
}

void RealCommandRunner::Abort() {
  subprocs_.Clear();
}

size_t RealCommandRunner::CanRunMore() const {
  size_t subproc_number =
      subprocs_.running_.size() + subprocs_.finished_.size();

  int64_t capacity = config_.parallelism - subproc_number;

  if (config_.max_load_average > 0.0f) {
    int load_capacity = config_.max_load_average - GetLoadAverage();
    if (load_capacity < capacity)
      capacity = load_capacity;
  }

  if (capacity < 0)
    capacity = 0;

  if (capacity == 0 && subprocs_.running_.empty())
    // Ensure that we make progress.
    capacity = 1;

  return capacity;
}

bool RealCommandRunner::StartCommand(Edge* edge) {
  string command = edge->EvaluateCommand();
  Subprocess* subproc = subprocs_.Add(command, edge->use_console());
  if (!subproc)
    return false;
  subproc_to_edge_.insert(make_pair(subproc, edge));

  return true;
}

bool RealCommandRunner::WaitForCommand(Result* result) {
  Subprocess* subproc;
  while ((subproc = subprocs_.NextFinished()) == NULL) {
    bool interrupted = subprocs_.DoWork();
    if (interrupted)
      return false;
  }

  result->status = subproc->Finish();
  result->output = subproc->GetOutput();

  map<const Subprocess*, Edge*>::iterator e = subproc_to_edge_.find(subproc);
  result->edge = e->second;
  subproc_to_edge_.erase(e);

  delete subproc;
  return true;
}
#ifdef CLOUD_BUILD_SUPPORT

constexpr int proportion = 3; //Best result from benchmark

struct CloudCommandRunner : public CommandRunner {
  explicit CloudCommandRunner(const BuildConfig& config)
      : config_(config), remote_procs_(config.parallelism * proportion) {}
  virtual ~CloudCommandRunner() {}
  virtual size_t CanRunMore() const override;
  virtual bool StartCommand(Edge* work) override;
  virtual bool WaitForCommand(Result* result) override;
  virtual vector<Edge*> GetActiveEdges() override;
  virtual void Abort() override;

  const BuildConfig& config_;
  RemoteProcessSet remote_procs_;
  map<const RemoteProcess*, Edge*> remoteproc_to_edge;
};


size_t CloudCommandRunner::CanRunMore() const {
  size_t re_proc_number =
      remote_procs_.running_.size() + remote_procs_.finished_.size();

  int64_t capacity = config_.parallelism - re_proc_number;

  if (config_.max_load_average > 0.0f) {
    int load_capacity = config_.max_load_average - GetLoadAverage();
    if (load_capacity < capacity)
      capacity = load_capacity;
  }

  if (capacity < 0)
    capacity = 0;

  if (capacity == 0 && remote_procs_.running_.empty())
    // Ensure that we make progress.
    capacity = 1;

  return capacity;
}


bool CloudCommandRunner::StartCommand(Edge* edge) {
  string command = edge->EvaluateCommand();
  auto spawn = RemoteExecutor::RemoteSpawn::CreateRemoteSpawn(edge);
  string cmd_rule =spawn->edge->rule().name();
  if(config_.rbe_config.local_only_rules.find(cmd_rule) != config_.rbe_config.local_only_rules.end()){
    SubprocessSet subprocset;
    Subprocess* subproc = subprocset.Add(spawn->command,edge->use_console());
    if (!subproc) {
      return false;
    }   
    return true;
  }
  for(auto &cmd:config_.rbe_config.fuzzy_rules){
    if(cmd.find(cmd_rule)!=std::string::npos){
    SubprocessSet subprocset;
    Subprocess* subproc = subprocset.Add(spawn->command,edge->use_console());
    if (!subproc) {
      return false;
    }   
    return true;
    }
  }
   for(auto &cmd:config_.rbe_config.regex_rules){
       std::regex patternRule(cmd);
    if(std::regex_match(cmd_rule,patternRule)){
    SubprocessSet subprocset;
    Subprocess* subproc = subprocset.Add(spawn->command,edge->use_console());
    if (!subproc) {
      return false;
    }   
    return true;
    }
  }
  RemoteProcess* remoteproc = remote_procs_.Add(spawn);
  if (!remoteproc)
    return false;
  remoteproc_to_edge.insert(make_pair(remoteproc, edge));
  return true;
}

bool CloudCommandRunner::WaitForCommand(Result* result) {
  Subprocess* subproc;
  RemoteProcess* remoteproc;
  SubprocessSet* tmp = new SubprocessSet();

  while (true) {
    if ((remoteproc = remote_procs_.NextFinished()) != NULL)
      break;
    // Dowork 内部会更新 RemoteProcess 的 running_, finished_ 队列
    if (remote_procs_.DoWork(tmp))
      return false;
  }
  assert(remoteproc != NULL);
  result->status = remoteproc->Finish();
  result->output = remoteproc->GetOutput();
  auto e = remoteproc_to_edge.find(remoteproc);
  result->edge = e->second;
  remoteproc_to_edge.erase(e);
  delete remoteproc;
  delete tmp;
  return true;
}

vector<Edge*> CloudCommandRunner::GetActiveEdges() {
  vector<Edge*> edges;
  for (map<const RemoteProcess*, Edge*>::iterator e = remoteproc_to_edge.begin();
       e != remoteproc_to_edge.end(); ++e)
    edges.push_back(e->second);
  return edges;
}

void CloudCommandRunner::Abort() {
  remote_procs_.Clear();
}

#endif // CLOUD_BUILD_SUPPORT


Builder::Builder(State* state, const BuildConfig& config,
                 BuildLog* build_log, DepsLog* deps_log,
                 DiskInterface* disk_interface, Status *status,
                 int64_t start_time_millis)
    : state_(state), config_(config), plan_(this), status_(status),
      start_time_millis_(start_time_millis), disk_interface_(disk_interface),
      scan_(state, build_log, deps_log, disk_interface,
            &config_.depfile_parser_options) {
  lock_file_path_ = ".ninja_lock";
  string build_dir = state_->bindings_.LookupVariable("builddir");
  if (!build_dir.empty())
    lock_file_path_ = build_dir + "/" + lock_file_path_;
}

Builder::~Builder() {
  Cleanup();
}

void Builder::Cleanup() {
  if (command_runner_.get()) {
    vector<Edge*> active_edges = command_runner_->GetActiveEdges();
    command_runner_->Abort();

    for (vector<Edge*>::iterator e = active_edges.begin();
         e != active_edges.end(); ++e) {
      string depfile = (*e)->GetUnescapedDepfile();
      for (vector<Node*>::iterator o = (*e)->outputs_.begin();
           o != (*e)->outputs_.end(); ++o) {
        // Only delete this output if it was actually modified.  This is
        // important for things like the generator where we don't want to
        // delete the manifest file if we can avoid it.  But if the rule
        // uses a depfile, always delete.  (Consider the case where we
        // need to rebuild an output because of a modified header file
        // mentioned in a depfile, and the command touches its depfile
        // but is interrupted before it touches its output file.)
        string err;
        TimeStamp new_mtime = disk_interface_->Stat((*o)->path(), &err);
        if (new_mtime == -1)  // Log and ignore Stat() errors.
          status_->Error("%s", err.c_str());
        if (!depfile.empty() || (*o)->mtime() != new_mtime)
          disk_interface_->RemoveFile((*o)->path());
      }
      if (!depfile.empty())
        disk_interface_->RemoveFile(depfile);
    }
  }

  string err;
  if (disk_interface_->Stat(lock_file_path_, &err) > 0)
    disk_interface_->RemoveFile(lock_file_path_);
}

Node* Builder::AddTarget(const string& name, string* err) {
  Node* node = state_->LookupNode(name);
  if (!node) {
    *err = "unknown target: '" + name + "'";
    return NULL;
  }
  if (!AddTarget(node, err))
    return NULL;
  return node;
}

bool Builder::AddTarget(Node* target, string* err) {
  std::vector<Node*> validation_nodes;
  if (!scan_.RecomputeDirty(target, &validation_nodes, err))
    return false;

  Edge* in_edge = target->in_edge();
  if (!in_edge || !in_edge->outputs_ready()) {
    if (!plan_.AddTarget(target, err)) {
      return false;
    }
  }

  // Also add any validation nodes found during RecomputeDirty as top level
  // targets.
  for (std::vector<Node*>::iterator n = validation_nodes.begin();
       n != validation_nodes.end(); ++n) {
    if (Edge* validation_in_edge = (*n)->in_edge()) {
      if (!validation_in_edge->outputs_ready() &&
          !plan_.AddTarget(*n, err)) {
        return false;
      }
    }
  }

  return true;
}

bool Builder::AlreadyUpToDate() const {
  return !plan_.more_to_do();
}

bool Builder::Build(string* err) {
  assert(!AlreadyUpToDate());
  plan_.PrepareQueue();

  int pending_commands = 0;
  int failures_allowed = config_.failures_allowed;

  // Set up the command runner if we haven't done so already.
  if (!command_runner_.get()) {
    if (config_.dry_run)
      command_runner_.reset(new DryRunCommandRunner);
#ifdef CLOUD_BUILD_SUPPORT
    else if (config_.cloud_run) {
      RemoteExecutor::RemoteSpawn::config = &config_;
      command_runner_.reset(new CloudCommandRunner(config_));
    }
#endif
    else if (config_.share_run) {
        command_runner_.reset(new ShareCommandRunner(config_));
    } else {
        command_runner_.reset(new RealCommandRunner(config_));
    }
  }

  // We are about to start the build process.
  status_->BuildStarted();

  // This main loop runs the entire build process.
  // It is structured like this:
  // First, we attempt to start as many commands as allowed by the
  // command runner.
  // Second, we attempt to wait for / reap the next finished command.
  while (plan_.more_to_do()) {
    // See if we can start any more commands.
    if (failures_allowed) {
        size_t capacity = command_runner_->CanRunMore();
        while (capacity > 0) {
          Edge* edge = plan_.FindWork();
          if (!edge)
            break;

          if (edge->GetBindingBool("generator")) {
            scan_.build_log()->Close();
          }

          if (!StartEdge(edge, err)) {
            Cleanup();
            status_->BuildFinished();
            return false;
          }

          if (edge->is_phony()) {
            if (!plan_.EdgeFinished(edge, Plan::kEdgeSucceeded, err)) {
              Cleanup();
              status_->BuildFinished();
              return false;
            }
          } else {
            ++pending_commands;

            --capacity;

            // Re-evaluate capacity.
            size_t current_capacity = command_runner_->CanRunMore();
            if (current_capacity < capacity)
              capacity = current_capacity;
          }
        }

        // We are finished with all work items and have no pending
        // commands. Therefore, break out of the main loop.
        if (pending_commands == 0 && !plan_.more_to_do()) break;
    }

    // See if we can reap any finished commands.
    if (pending_commands) {
      CommandRunner::Result result;
      if (!command_runner_->WaitForCommand(&result) ||
          result.status == ExitInterrupted) {
        Cleanup();
        status_->BuildFinished();
        *err = "interrupted by user";
        return false;
      }

      --pending_commands;
      if (!FinishCommand(&result, err)) {
        Cleanup();
        status_->BuildFinished();
        return false;
      }

      if (!result.success()) {
        if (failures_allowed)
          failures_allowed--;
      }

      // We made some progress; start the main loop over.
      continue;
    }

    // If we get here, we cannot make any more progress.
    status_->BuildFinished();
    if (failures_allowed == 0) {
      if (config_.failures_allowed > 1)
        *err = "subcommands failed";
      else
        *err = "subcommand failed";
    } else if (failures_allowed < config_.failures_allowed)
      *err = "cannot make progress due to previous errors";
    else
      *err = "stuck [this is a bug]";

    return false;
  }

  status_->BuildFinished();
  return true;
}

bool Builder::StartEdge(Edge* edge, string* err) {
  METRIC_RECORD("StartEdge");
  if (edge->is_phony())
    return true;

  int64_t start_time_millis = GetTimeMillis() - start_time_millis_;
  running_edges_.insert(make_pair(edge, start_time_millis));

  status_->BuildEdgeStarted(edge, start_time_millis);

  TimeStamp build_start = config_.dry_run ? 0 : -1;

  // Create directories necessary for outputs and remember the current
  // filesystem mtime to record later
  // XXX: this will block; do we care?
  for (vector<Node*>::iterator o = edge->outputs_.begin();
       o != edge->outputs_.end(); ++o) {
    if (!disk_interface_->MakeDirs((*o)->path()))
      return false;
    if (build_start == -1) {
      disk_interface_->WriteFile(lock_file_path_, "");
      build_start = disk_interface_->Stat(lock_file_path_, err);
      if (build_start == -1)
        build_start = 0;
    }
  }

  edge->command_start_time_ = build_start;

  // Create response file, if needed
  // XXX: this may also block; do we care?
  string rspfile = edge->GetUnescapedRspfile();
  if (!rspfile.empty()) {
    string content = edge->GetBinding("rspfile_content");
    if (!disk_interface_->WriteFile(rspfile, content))
      return false;
  }

  // start command computing and run it
  if (!command_runner_->StartCommand(edge)) {
    err->assign("command '" + edge->EvaluateCommand() + "' failed.");
    return false;
  }

  return true;
}

// bool Builder::FinishCommand(CommandRunner::Result* result, string* err) {
//   METRIC_RECORD("FinishCommand");

//   Edge* edge = result->edge;

//   // First try to extract dependencies from the result, if any.
//   // This must happen first as it filters the command output (we want
//   // to filter /showIncludes output, even on compile failure) and
//   // extraction itself can fail, which makes the command fail from a
//   // build perspective.
//   vector<Node*> deps_nodes;
//   string deps_type = edge->GetBinding("deps");
//   const string deps_prefix = edge->GetBinding("msvc_deps_prefix");
//   if (!deps_type.empty()) {
//     string extract_err;
//     if (!ExtractDeps(result, deps_type, deps_prefix, &deps_nodes,
//                      &extract_err) &&
//         result->success()) {
//       if (!result->output.empty())
//         result->output.append("\n");
//       result->output.append(extract_err);
//       result->status = ExitFailure;
//     }
//   }

//   int64_t start_time_millis, end_time_millis;
//   RunningEdgeMap::iterator it = running_edges_.find(edge);
//   start_time_millis = it->second;
//   end_time_millis = GetTimeMillis() - start_time_millis_;
//   running_edges_.erase(it);

//   status_->BuildEdgeFinished(edge, start_time_millis, end_time_millis,
//                              result->success(), result->output);

//   // The rest of this function only applies to successful commands.
//   if (!result->success()) {
//     return plan_.EdgeFinished(edge, Plan::kEdgeFailed, err);
//   }

//   // Restat the edge outputs
//   TimeStamp record_mtime = 0;
//   if (!config_.dry_run) {
//     const bool restat = edge->GetBindingBool("restat");
//     const bool generator = edge->GetBindingBool("generator");
//     bool node_cleaned = false;
//     record_mtime = edge->command_start_time_;

//     // restat and generator rules must restat the outputs after the build
//     // has finished. if record_mtime == 0, then there was an error while
//     // attempting to touch/stat the temp file when the edge started and
//     // we should fall back to recording the outputs' current mtime in the
//     // log.
//     if (record_mtime == 0 || restat || generator) {
//       for (vector<Node*>::iterator o = edge->outputs_.begin();
//            o != edge->outputs_.end(); ++o) {
//         TimeStamp new_mtime = disk_interface_->Stat((*o)->path(), err);
//         if (new_mtime == -1)
//           return false;
//         if (new_mtime > record_mtime)
//           record_mtime = new_mtime;
//         if ((*o)->mtime() == new_mtime && restat) {
//           // The rule command did not change the output.  Propagate the clean
//           // state through the build graph.
//           // Note that this also applies to nonexistent outputs (mtime == 0).
//           if (!plan_.CleanNode(&scan_, *o, err))
//             return false;
//           node_cleaned = true;
//         }
//       }
//     }
//     if (node_cleaned) {
//       record_mtime = edge->command_start_time_;
//     }
//   }

//   if (!plan_.EdgeFinished(edge, Plan::kEdgeSucceeded, err))
//     return false;

//   // Delete any left over response file.
//   string rspfile = edge->GetUnescapedRspfile();
//   if (!rspfile.empty() && !g_keep_rsp)
//     disk_interface_->RemoveFile(rspfile);

//   if (scan_.build_log()) {
//     if (!scan_.build_log()->RecordCommand(edge, start_time_millis,
//                                           end_time_millis, record_mtime)) {
//       *err = string("Error writing to build log: ") + strerror(errno);
//       return false;
//     }
//   }

//   if (!deps_type.empty() && !config_.dry_run) {
//     assert(!edge->outputs_.empty() && "should have been rejected by parser");
//     for (std::vector<Node*>::const_iterator o = edge->outputs_.begin();
//          o != edge->outputs_.end(); ++o) {
//       TimeStamp deps_mtime = disk_interface_->Stat((*o)->path(), err);
//       if (deps_mtime == -1)
//         return false;
//       if (!scan_.deps_log()->RecordDeps(*o, deps_mtime, deps_nodes)) {
//         *err = std::string("Error writing to deps log: ") + strerror(errno);
//         return false;
//       }
//     }
//   }
//   return true;
// }
bool Builder::FinishCommand(CommandRunner::Result* result, string* err) {
METRIC_RECORD("FinishCommand");

  Edge* edge = result->edge;
  bool phony_output = edge->IsPhonyOutput();

  vector<Node*> deps_nodes;
  string deps_type = edge->GetBinding("deps");
  if (!phony_output) {
    // First try to extract dependencies from the result, if any.
    // This must happen first as it filters the command output (we want
    // to filter /showIncludes output, even on compile failure) and
    // extraction itself can fail, which makes the command fail from a
    // build perspective.
    const string deps_prefix = edge->GetBinding("msvc_deps_prefix");
    if (!deps_type.empty()) {
      string extract_err;
      if (!ExtractDeps(result, deps_type, deps_prefix, &deps_nodes,
                       &extract_err) &&
          result->success()) {
        if (!result->output.empty())
          result->output.append("\n");
        result->output.append(extract_err);
        result->status = ExitFailure;
      }
    }
  }

  int64_t start_time_millis, end_time_millis;
  RunningEdgeMap::iterator i = running_edges_.find(edge);
  start_time_millis = i->second;
  end_time_millis = GetTimeMillis() - start_time_millis_;
  running_edges_.erase(i);

  // Restat the edge outputs
  TimeStamp output_mtime = 0;
  if (result->success() && !config_.dry_run && !phony_output) {
    bool restat = edge->IsRestat();
    vector<Node*> nodes_cleaned;

    TimeStamp newest_input = 0;
    Node* newest_input_node = nullptr;
    for (vector<Node*>::iterator i = edge->inputs_.begin();
         i != edge->inputs_.end() - edge->order_only_deps_; ++i) {
      TimeStamp input_mtime = (*i)->mtime();
      if (input_mtime == -1)
        return false;
      if (input_mtime > newest_input) {
        newest_input = input_mtime;
        newest_input_node = (*i);
      }
    }

    set<string> declared_symlinks;
    if (config_.uses_symlink_outputs) {
      string symlink_outputs = edge->GetSymlinkOutputs();
      if (symlink_outputs.length() > 0) {
        stringstream ss(symlink_outputs);
        string path;
        /// Naively split symlink_outputs path by the empty ' ' space character.
        /// because the '$ ' escape doesn't exist at this stage. In experimentation
        /// and practice across a number of AOSP configurations, this is OK.
        ///
        /// We could modify the GetBindingImpl/GetSymlinkOutputs API to support lists,
        /// but it'd be an invasive change that'll require a little bit more designing.
        /// For example, how do we expand "${out}.d" if ${out} is a list?
        ///
        /// That said, keep in mind that this is a simple string split that could
        /// fail with paths containing spaces.
        while (getline(ss, path, ' ')) {
          uint64_t slash_bits;
          if (!CanonicalizePath(&path, &slash_bits, err)) {
            return false;
          }
          declared_symlinks.insert(move(path));
        }
      }
    }

    for (vector<Node*>::iterator o = edge->outputs_.begin();
         o != edge->outputs_.end(); ++o) {
      bool is_dir = false;
      bool is_symlink = false;
      TimeStamp old_mtime = (*o)->mtime();
      if (!(*o)->LStat(disk_interface_, &is_dir, &is_symlink, err))
        return false;

      TimeStamp new_mtime = (*o)->mtime();

      if (config_.uses_symlink_outputs) {
        /// Warn or error if created symlinks aren't declared in symlink_outputs,
        /// or if created files are declared in symlink_outputs.
        if (is_symlink) {
          if (declared_symlinks.find((*o)->path()) == declared_symlinks.end()) {
            // Not in declared_symlinks
            if (!result->output.empty())
              result->output.append("\n");
            result->output.append("ninja: " + (*o)->path() + " is a symlink, but it was not declared in symlink_outputs");
            if (config_.undeclared_symlink_outputs_should_err) {
              result->status = ExitFailure;
            }
          } else {
            declared_symlinks.erase((*o)->path());
          }
        } else if (!is_symlink && declared_symlinks.find((*o)->path()) != declared_symlinks.end()) {
          if (!result->output.empty())
            result->output.append("\n");
          result->output.append("ninja: " + (*o)->path() + " is not a symlink, but it was declared in symlink_outputs");
          declared_symlinks.erase((*o)->path());
          if (config_.undeclared_symlink_outputs_should_err) {
            result->status = ExitFailure;
          }
        }
      }

      if (config_.uses_phony_outputs) {
        if (new_mtime == 0) {
          if (!result->output.empty())
            result->output.append("\n");
          result->output.append("ninja: output file missing after successful execution: ");
          result->output.append((*o)->path());
          if (config_.missing_output_file_should_err) {
            result->status = ExitFailure;
          }
        } else if (!restat && new_mtime < newest_input) {
          if (!result->output.empty())
            result->output.append("\n");
          result->output.append("ninja: Missing `restat`? An output file is older than the most recent input:\n output: ");
          result->output.append((*o)->path());
          result->output.append("\n  input: ");
          result->output.append(newest_input_node->path());
          if (config_.old_output_should_err) {
            result->status = ExitFailure;
          }
        }
        if (is_dir) {
          if (!result->output.empty())
            result->output.append("\n");
          result->output.append("ninja: outputs should be files, not directories: ");
          result->output.append((*o)->path());
          if (config_.output_directory_should_err) {
            result->status = ExitFailure;
          }
        }
      }
      if (new_mtime > output_mtime)
        output_mtime = new_mtime;
      if (old_mtime == new_mtime && restat) {
        nodes_cleaned.push_back(*o);
        continue;
      }
    }

    /// Ensure that declared_symlinks is empty after verifying that symlink outputs
    /// were declared in the edge. A non-empty declared_symlinks set indicates that
    /// not all declared symlinks were created by the edge itself (over-specification).
    if (config_.uses_symlink_outputs && declared_symlinks.size() > 0) {
      string missing_outputs;
      for (string symlink : declared_symlinks) {
        missing_outputs = missing_outputs + " " + symlink;
      }
      result->output.append(
        "ninja: not all symlink_outputs were created for this edge:" + missing_outputs);
      if (config_.undeclared_symlink_outputs_should_err) {
        result->status = ExitFailure;
      }
    }

    status_->BuildEdgeFinished(edge, end_time_millis, result);

    if (result->success() && !nodes_cleaned.empty()) {
      for (vector<Node*>::iterator o = nodes_cleaned.begin();
           o != nodes_cleaned.end(); ++o) {
        // The rule command did not change the output.  Propagate the clean
        // state through the build graph.
        // Note that this also applies to nonexistent outputs (mtime == 0).
        if (!plan_.CleanNode(&scan_, *o, err))
          return false;
      }

      // If any output was cleaned, find the most recent mtime of any
      // (existing) non-order-only input or the depfile.
      TimeStamp restat_mtime = newest_input;

      string depfile = edge->GetUnescapedDepfile();
      if (restat_mtime != 0 && deps_type.empty() && !depfile.empty()) {
        TimeStamp depfile_mtime = disk_interface_->Stat(
            // depfile is relative, disk_interface_ uses global paths.
            edge->pos_.scope()->GlobalPath(depfile).h.data(),
            err);
        if (depfile_mtime == -1)
          return false;
        if (depfile_mtime > restat_mtime)
          restat_mtime = depfile_mtime;
      }

      // The total number of edges in the plan may have changed as a result
      // of a restat.
      status_->PlanHasTotalEdges(plan_.command_edge_count());

      output_mtime = restat_mtime;
    }
  } else {
    status_->BuildEdgeFinished(edge, end_time_millis, result);
  }

  if (!plan_.EdgeFinished(edge, result->success() ? Plan::kEdgeSucceeded : Plan::kEdgeFailed, err))
    return false;

  // The rest of this function only applies to successful commands.
  if (!result->success()) {
    return true;
  }

  // Delete any left over response file.
  string rspfile = edge->GetUnescapedRspfile();
  if (!rspfile.empty() && !g_keep_rsp)
    // rspfile is relative, disk_interface_ uses global paths.
    disk_interface_->RemoveFile(
        edge->pos_.scope()->GlobalPath(rspfile).h.data());

  if (scan_.build_log() && !phony_output) {
    if (!scan_.build_log()->RecordCommand(edge, start_time_millis,
                                          end_time_millis, output_mtime)) {
      *err = string("Error writing to build log: ") + strerror(errno);
      return false;
    }
  }

  if (!deps_type.empty() && !config_.dry_run && !phony_output) {
    Node* out = edge->outputs_[0];
    TimeStamp deps_mtime = disk_interface_->LStat(out->globalPath().h.data(), nullptr, nullptr, err);
    if (deps_mtime == -1)
      return false;
    if (!scan_.deps_log()->RecordDeps(out, deps_mtime, deps_nodes)) {
      *err = string("Error writing to deps log: ") + strerror(errno);
      return false;
    }
  }
  return true;
}

bool Builder::ExtractDeps(CommandRunner::Result* result,
                          const string& deps_type,
                          const string& deps_prefix,
                          vector<Node*>* deps_nodes,
                          string* err) {
  if (deps_type == "msvc") {
    CLParser parser;
    string output;
    if (!parser.Parse(result->output, deps_prefix, &output, err))
      return false;
    result->output = output;
    for (set<string>::iterator i = parser.includes_.begin();
         i != parser.includes_.end(); ++i) {
      // ~0 is assuming that with MSVC-parsed headers, it's ok to always make
      // all backslashes (as some of the slashes will certainly be backslashes
      // anyway). This could be fixed if necessary with some additional
      // complexity in IncludesNormalize::Relativize.
      deps_nodes->push_back(state_->GetNode(*i, ~0u));
    }
  } else if (deps_type == "gcc") {
    string depfile = result->edge->GetUnescapedDepfile();
    if (depfile.empty()) {
      *err = string("edge with deps=gcc but no depfile makes no sense");
      return false;
    }

    // Read depfile content.  Treat a missing depfile as empty.
    string content;
    switch (disk_interface_->ReadFile(depfile, &content, err)) {
    case DiskInterface::Okay:
      break;
    case DiskInterface::NotFound:
      err->clear();
      // We only care if the depfile is missing when the tool succeeded.
      if (!config_.dry_run && result->status == ExitSuccess) {
        if (false && config_.missing_depfile_should_err) {
          *err = string("depfile is missing");
          return false;
        } else {
          status_->Warning("depfile is missing (%s for %s)", depfile.c_str(), result->edge->outputs_[0]->path().c_str());
        }
      }
      break;
    case DiskInterface::OtherError:
      return false;
    }
    if (content.empty())
      return true;

    DepfileParser deps(config_.depfile_parser_options);
    if (!deps.Parse(&content, err))
      return false;

    // XXX check depfile matches expected output.
    deps_nodes->reserve(deps.ins_.size());
    for (vector<StringPiece>::iterator i = deps.ins_.begin();
         i != deps.ins_.end(); ++i) {
      uint64_t slash_bits;
      CanonicalizePath(const_cast<char*>(i->str_), &i->len_, &slash_bits);
      deps_nodes->push_back(state_->GetNode(*i, slash_bits));
    }

    if (!g_keep_depfile) {
      if (disk_interface_->RemoveFile(depfile) < 0) {
        *err = string("deleting depfile: ") + strerror(errno) + string("\n");
        return false;
      }
    }
  } else {
    Fatal("unknown deps type '%s'", deps_type.c_str());
  }

  return true;
}

bool Builder::LoadDyndeps(Node* node, string* err) {
  status_->BuildLoadDyndeps();

  // Load the dyndep information provided by this node.
  DyndepFile ddf;
  if (!scan_.LoadDyndeps(node, &ddf, err))
    return false;

  // Update the build plan to account for dyndep modifications to the graph.
  if (!plan_.DyndepsLoaded(&scan_, node, ddf, err))
    return false;

  return true;
}
