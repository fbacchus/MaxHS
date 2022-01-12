/***********[Graph.h]
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

#ifndef __GRAPH__
#define __GRAPH__

#include <stdint.h>
#include <string.h>
#include <iostream>
#include <utility>
#include <vector>

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

#ifdef GLUCOSE
#include "glucose/core/SolverTypes.h"
#else
#include "minisat/core/SolverTypes.h"
#endif
#include "maxhs/core/MaxSolverTypes.h"

#include "maxhs/utils/Params.h"
#include "maxhs/utils/io.h"

using Minisat::Lit;
using Minisat::Var;
using std::pair;
using std::vector;

class Graph {
 public:
  double extractCommunities(vector<vector<Var>>& communities);
  void addEdge(Lit l1, Lit l2, Weight w) { addEdge(var(l1), var(l2), w); }
  void addEdge(Var v1, Var v2, Weight w);
  int get_n_vars() { return n_vars; }
  void addCluster(const vector<Var>& cluster);
  void combine_nodes(const vector<vector<Var>>& vars_to_combine);

  bool in_graph(Var v) {
    return (static_cast<size_t>(v) < var_to_nid.size() &&
            var_to_nid[v] != NONE);
  }

 private:
  const int NONE{-1};
  struct Edge {
    int nid;
    Weight wt;
  };
  friend bool operator<(const Edge& e1, const Edge& e2);
  friend std::ostream& operator<<(std::ostream&, const Edge&);

  struct Node {
   public:
    int nid;
    vector<Var> cnf_vars;
    vector<Edge> edges{};
    Weight internal_edge_wt{0.0};
    Weight total_edge_wt{0.0};
    int cid{-1};
    int n_edges{0};
    bool on_ToProcess{false};
    bool is_clustered() { return cnf_vars.size() > 1; }
    bool is_empty() { return cnf_vars.size() == 0; }
    bool can_be_clustered() { return n_edges >= params.abstract_min_cores; }
  };
  friend std::ostream& operator<<(std::ostream&, const Node&);

  struct Component {
   public:
    Weight internal_edge_wt{0.0};
    Weight total_edge_wt{0.0};
    vector<int> nids;
    int n_vars;
  };
  friend std::ostream& operator<<(std::ostream&, const Component&);

  int n_vars{0};
  int newNode(Var v);
  int varToNid(Var v);
  void insert_into_edge_list(vector<Edge>& edges, const Edge& edge);
  void insertEdge(int nid1, int nid2, Weight wt);
  double louvain_find_components(int nid, vector<int>& nodesToProcess);
  void move_node(Node& n, int to_cid, const vector<Weight>& comp_wts);
  void nids_to_reprocess(vector<int>& nids, int old_cid, int new_cid,
                         int nid_moved);
  void rebuild_nodes();

  vector<Node> nodes;
  vector<Component> components;
  vector<int> var_to_nid;
  Weight graph_total_edge_wt_times2{0.0};
  bool new_cross_node_edges{false};
};

inline bool operator<(const Graph::Edge& e1, const Graph::Edge& e2) {
  return e1.nid < e2.nid;
}

inline std::ostream& operator<<(std::ostream& os, const Graph::Edge& e) {
  std::cout << "Edge(" << e.nid << ", " << e.wt << ")";
  return os;
}

inline std::ostream& operator<<(std::ostream& os, const Graph::Node& n) {
  std::cout << "Node(" << n.nid << ", iwt=" << wt_fmt(n.internal_edge_wt)
            << ", twt=" << wt_fmt(n.total_edge_wt) << " cid=" << n.cid
            << ") cnf_vars =" << n.cnf_vars << " edges =" << n.edges;
  return os;
}

inline std::ostream& operator<<(std::ostream& os, const Graph::Component& c) {
  std::cout << "comp(iwt=" << wt_fmt(c.internal_edge_wt) << ", twt=" << wt_fmt(c.total_edge_wt)
            << ") nids =" << c.nids;
  return os;
};

#endif
