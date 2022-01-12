/***********[Graph.cc]
 Copyright (c) 2019 Fahiem Bacchus

 Permission is hereby granted, free of charge, to any person obtaining a
 copy of this software and associated documentation files (the
 "Software"), to deal in the Software without restriction, including
 without limitation the rights to use, copy, modify, merge, publish,
 distribute, sublicense, and/or sell copies of the Software, and to
 permit persons to whom the Software is furnished to do so, subject to
 the following conditions:

 The above copyright notice and this permission notice shall be included
 in all copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ***********/

#include "maxhs/core/Graph.h"
#include <stdlib.h>
#include <algorithm>
#include <iostream>
#include "maxhs/utils/io.h"

using std::cout;
using std::vector;

double sq(double x) { return x * x; }

int Graph::newNode(Var v) {
  ++n_vars;
  int nid = nodes.size();
  nodes.push_back({nid, {v}});
  return nid;
}

int Graph::varToNid(Var v) {
  if (static_cast<size_t>(v) >= var_to_nid.size())
    var_to_nid.resize(v + 1, NONE);
  if (var_to_nid[v] == NONE) {
    var_to_nid[v] = newNode(v);
  }
  return var_to_nid[v];
}

void Graph::addCluster(const vector<Var>& cluster) {
  if (cluster.empty()) return;
  n_vars += cluster.size();
  int nid = nodes.size();
  for (auto v : cluster) {
    if (static_cast<size_t>(v) >= var_to_nid.size())
      var_to_nid.resize(v + 1, NONE);
    var_to_nid[v] = nid;
  }
  nodes.push_back({nid, cluster});
  nodes.back().n_edges = params.abstract_min_cores;
}

void Graph::addEdge(Var v1, Var v2, Weight w) {
  auto nid1 = varToNid(v1);
  auto nid2 = varToNid(v2);
  insertEdge(nid1, nid2, w);
  insertEdge(nid2, nid1, w);
  if (nid1 != nid2) new_cross_node_edges = true;
}

void Graph::insertEdge(int nid1, int nid2, Weight w) {
  graph_total_edge_wt_times2 += w;
  auto& node = nodes[nid1];
  node.total_edge_wt += w;
  ++node.n_edges;
  if (nid1 == nid2)
    node.internal_edge_wt += w;
  else
    insert_into_edge_list(node.edges, {nid2, w});
}

void Graph::insert_into_edge_list(vector<Edge>& edges, const Edge& edge) {
  auto it = std::lower_bound(edges.begin(), edges.end(), edge);
  if (it == edges.end())
    edges.push_back(edge);
  else if (it->nid == edge.nid)
    it->wt += edge.wt;
  else
    edges.insert(it, edge);
}

void Graph::combine_nodes(const vector<vector<Var>>& vars_to_comb) {
  bool nodes_to_rebuild = false;
  for (auto& n : nodes) n.cid = n.nid;
  for (const auto& vars : vars_to_comb) {
    if (vars.size() <= 1) continue;
    if (std::any_of(vars.begin(), vars.end(), [&](Var v) {
          return v >= static_cast<int>(var_to_nid.size()) ||
                 var_to_nid[v] == NONE;
        }))
      continue;
    for (Var v : vars)
      nodes[var_to_nid[v]].cid = nodes[var_to_nid[vars[0]]].cid;
    nodes_to_rebuild = true;
  }
  if (nodes_to_rebuild) rebuild_nodes();
}

double Graph::extractCommunities(vector<vector<Var>>& communities) {
  vector<int> nodesToProcess;
  double modularity_increase{0};
  communities.clear();
  components.clear();
  if (new_cross_node_edges) {
    log(2, "c Abstraction: extractCommunities #nodes =", nodes.size());
    // 1. Assign each node to its own component
    for (auto& n : nodes) {
      n.cid = components.size();
      components.push_back({n.internal_edge_wt,
                            n.total_edge_wt,
                            {n.nid},
                            static_cast<int>(n.cnf_vars.size())});
      if (n.can_be_clustered()) {
        nodesToProcess.push_back(n.nid);
        n.on_ToProcess = true;
      }
    }
    // Louvain greedy modularity improvement
    while (!nodesToProcess.empty()) {
      auto nid = nodesToProcess.back();
      nodesToProcess.pop_back();
      nodes[nid].on_ToProcess = false;
      modularity_increase += louvain_find_components(nid, nodesToProcess);
    }
    log(2, "c total mod increase = ", modularity_increase);

    if (modularity_increase <= 0)
      new_cross_node_edges = false;
    else
      rebuild_nodes();
  } else {
    log(2,
        "c Skipping Louvain as no new cross node edges added since last call");
  }
  for (auto& n : nodes) communities.push_back(n.cnf_vars);
  for (auto& n : nodes)
    if (!n.can_be_clustered() && n.is_clustered())
      cout << "ERROR node: " << n << "\n"
           << " is clustered but doesn't have enough edges\n";
  return modularity_increase;
}

double Graph::louvain_find_components(int nid, vector<int>& nodesToProcess) {
  vector<Weight> comp_wts(components.size(), 0.0);
  // cout << "louvain processing " << nid << "\n";
  auto& nd = nodes[nid];
  for (auto& e : nd.edges) {
    auto& connected_node = nodes[e.nid];
    if (connected_node.can_be_clustered()) comp_wts[connected_node.cid] += e.wt;
    // else
    //  cout << "connected node " << connected_node.nid
    //       << " cannot be clustered\n";
  }
  comp_wts[nd.cid] += nd.internal_edge_wt / 2;

  double best_mod_delta{0.0};
  auto m{graph_total_edge_wt_times2};
  int best_cid{nd.cid};

  for (int cid = 0; static_cast<size_t>(cid) != components.size(); ++cid) {
    if (comp_wts[cid] == 0.0 || cid == nd.cid) continue;
    double mod_delta =
        m ? 2 * ((comp_wts[cid] - comp_wts[nd.cid]) / m +
                 nd.total_edge_wt *
                     (components[nd.cid].total_edge_wt -
                      components[cid].total_edge_wt - nd.total_edge_wt) /
                     sq(m))
          : 0;
    if (mod_delta > best_mod_delta) {
      best_mod_delta = mod_delta;
      best_cid = cid;
    }
  }

  /*if (best_mod_delta > 0)
    cout << "moving " << nid << " from " << nd.cid << " to " << best_cid
         << " mod_delta " << best_mod_delta << "\n";
  else
  cout << "not moving " << nid << "\n";*/

  if (best_mod_delta > 0) {
    // move nd to new component
    assert(best_cid != nd.cid);
    if (components[nd.cid].n_vars + components[best_cid].n_vars > 750) return 0;
    auto old_cid = nd.cid;
    move_node(nd, best_cid, comp_wts);
    nids_to_reprocess(nodesToProcess, old_cid, best_cid, nd.nid);
  }
  return best_mod_delta;
}

void Graph::move_node(Node& nd, int to_cid, const vector<Weight>& comp_wts) {
  auto& cur_comp{components[nd.cid]};
  cur_comp.total_edge_wt -= nd.total_edge_wt;
  cur_comp.internal_edge_wt -= 2 * comp_wts[nd.cid];
  auto& nid_list{cur_comp.nids};
  auto it = std::lower_bound(nid_list.begin(), nid_list.end(), nd.nid);
  assert(it != nid_list.end());
  nid_list.erase(it);
  cur_comp.n_vars -= nd.cnf_vars.size();

  auto& new_comp{components[to_cid]};
  new_comp.total_edge_wt += nd.total_edge_wt;
  new_comp.internal_edge_wt += 2 * comp_wts[to_cid];
  auto& new_nid_list{new_comp.nids};
  it = std::lower_bound(new_nid_list.begin(), new_nid_list.end(), nd.nid);
  new_nid_list.insert(it, nd.nid);
  new_comp.n_vars += nd.cnf_vars.size();
  nd.cid = to_cid;
}

void Graph::nids_to_reprocess(vector<int>& nids, int old_cid, int new_cid,
                              int nid_moved) {
  for (auto nid : components[old_cid].nids)
    if (!nodes[nid].on_ToProcess) {
      nids.push_back(nid);
      nodes[nid].on_ToProcess = true;
    }
  for (auto nid : components[new_cid].nids)
    if (nid != nid_moved && !nodes[nid].on_ToProcess) {
      nids.push_back(nid);
      nodes[nid].on_ToProcess = true;
    }
}

void Graph::rebuild_nodes() {
  vector<int> remap(nodes.size(), NONE);
  int nxt{0};
  for (auto& n : nodes)
    if (remap[n.cid] == NONE) {
      remap[n.cid] = nxt;
      ++nxt;
    }
  vector<Node> new_nodes(nxt);
  for (auto& nd : nodes) {
    auto& new_nd = new_nodes[remap[nd.cid]];
    new_nd.nid = remap[nd.cid];
    for (auto v : nd.cnf_vars) {
      new_nd.cnf_vars.push_back(v);
      var_to_nid[v] = new_nd.nid;
    }
    // THIS BUG CORRECTION MIGHT CHANGE CLUSTERING !
    new_nd.internal_edge_wt += nd.internal_edge_wt;
    new_nd.total_edge_wt += nd.internal_edge_wt;

    for (auto e : nd.edges) {
      e.nid = remap[nodes[e.nid].cid];
      new_nd.total_edge_wt += e.wt;
      if (e.nid == new_nd.nid)
        new_nd.internal_edge_wt += e.wt;
      else
        insert_into_edge_list(new_nd.edges, e);
    }
    new_nd.n_edges += nd.n_edges;
  }
  nodes = new_nodes;
}
