/***********[SumManager.h]
Copyright (c) 2019, Jeremias Berg, Fahiem Bacchus

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

#ifndef __SUM_MANAGER__
#define __SUM_MANAGER__

#include <stdint.h>
#include <string.h>
#include <map>
#include <queue>
#include <set>
#include <vector>

#include "maxhs/core/Bvars.h"
#include "maxhs/core/Graph.h"
#include "maxhs/core/MaxSolver.h"
#include "maxhs/core/MaxSolverTypes.h"
#include "maxhs/core/SortNet.h"
#include "maxhs/core/SumAuxStruct.h"
#include "maxhs/ds/Packed.h"
#include "maxhs/ifaces/SatSolver.h"

using Minisat::toInt;
using std::map;
using std::vector;

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

class Bvars;
class Graph;
namespace MaxHS_Iface {
class SatSolver;
class Muser;
}  // namespace MaxHS_Iface

class SumManager {
 public:
  SumManager(Bvars& b, MaxHS::MaxSolver* maxhs, MaxHS_Iface::Muser* m,
                   MaxHS_Iface::SatSolver* s);
  bool summations_active() const { return !sums_list.empty(); }
  size_t nb_summations() const { return sums_list.size(); }
  void add_core(const vector<Lit>& core);
  void compute_abstraction(double timebound, bool full = false);
  Lit getNextOLit(Lit l);

  int get_olit_index(Lit l) const {
    assert(isSoutput(l));
    return output_var_to_sout_index[toInt(var(l))];
  }

  vector<Lit> get_ilits_from_olit(Lit l) {
    assert(isSoutput(l));
    return get_olit_sref(l)->getInputs();
  }

  const vector<Lit>& get_olits_from_olit(Lit l) const {
    assert(isSoutput(l));
    return get_olit_sref(l)->getOutputs();
  }

  vector<Lit> get_ilits_from_sidx(int sidx) {
    return sums_list[sidx]->getInputs();
  }

  const vector<Lit>& get_olits_from_sidx(int sidx) {
    return sums_list[sidx]->getOutputs();
  }

  int get_sum_size_from_sidx(int sidx) {
    return sums_list[sidx]->getSize();
  }

  int get_n_true_outs(int sidx) const {
    return sums_list[sidx]->getOutTrue();
  }

  vector<int> get_top_level_sidxes() const;

  bool isSinput(Lit l) const {
    return (static_cast<size_t>(toInt(var(l))) < input_var_to_sref.size()) &&
           input_var_to_sref[toInt(var(l))] != NullSRef;
  }

  int get_Sinput_idx(Lit l) const {
    assert(isSinput(l));
    return input_var_to_sidx[toInt(var(l))];
  }

  Lit get_next_Soutput(int idx, int n_true) {
    assert(static_cast<size_t>(idx) < sums_list.size());
    auto sref = sums_list[idx];
    if (static_cast<size_t>(n_true) < sref->getOutputs().size()) {
      return sref->getOutputs()[n_true];
    } else
      return lit_Undef;
  }

  bool isSoutput(Lit l) const { return isSoutput(var(l)); }

  bool isSoutput(Var v) const {
    return (static_cast<size_t>(toInt(v)) < output_var_to_sref.size()) &&
           output_var_to_sref[toInt(v)] != NullSRef;
  }

  bool isPositiveSoutput(Lit l) const { return isSoutput(l) && !sign(l); }
  bool isNegativeSoutput(Lit l) const { return isSoutput(l) && sign(l); }

  void report_on_summations();
  void unset_all_exhaust_flags();
  bool all_summations_exhausted() const;
  void exhaust_top_level();

  /*TEST*/
  void test();
  /*TEST*/

 private:
  friend class SortNet;
  void start_timer(double timebound);
  double time_bound;
  bool timeout();
  double time_remaining();

  void abstract_cores(bool full);
  SRef build_sum(const vector<Var>&);
  void combine_same_wt_clusters(vector<vector<Var>>&);
  void combine_small_clusters(vector<vector<Var>>&);
  SRef build_sum_1(const vector<Lit>&);
  SOut sum_from_conflict(const vector<Lit>& conflict,
                               vector<SOut>& inProcess_touts);
  SOut make_and_exhaust_base_sum(const vector<Lit>& conf_orig_lits);
  SOut join_and_exhaust_sum(vector<SOut>& conf_touts);
  int exhaustSum(SRef t, double timelimit);
  vector<SRef> get_subSums(SRef t);
  lbool sat_solve_update_assumps(vector<Lit>&, vector<Lit>&);

  SRef get_ilit_sref(Lit l) const {
    assert(isSinput(l));
    return input_var_to_sref[toInt(var(l))];
  }
  SRef get_olit_sref(Lit l) const { return get_olit_sref(var(l)); }
  SRef get_olit_sref(Var v) const {
    assert(isSoutput(v));
    return output_var_to_sref[toInt(v)];
  }
  Weight get_weight_of_lit(Lit l) const {
    if (isSoutput(l)) {
      return get_olit_sref(l)->getWeight();
    } else {
      return bvars.wt(l);
    }
  }
  Weight get_weight_of_var(Var v) const {
    if (isSoutput(v)) {
      return get_olit_sref(v)->getWeight();
    } else {
      return bvars.wt(v);
    }
  }
  void addClausesToSolvers(const vector<vector<Lit>> cnf);
  void update_maps(SRef t, size_t sidx);
  Lit output_to_firstinput(Lit l) { return get_olit_sref(l)->getInputs()[0]; }
  Weight computeSumLB();
  int computeTotSumVars();
  bool allSumsExhausted();
  void addNewNodesToGraph(vector<Lit>& toAdd);
  void updateExistingNodesinGraph(vector<Lit>& lits_to_add);
  void resizeMaps();
  void setValuedOuts(SRef t);
  bool checkOutputs(SRef t);

  bool isSameWt(Lit l1, Lit l2) {
    return get_weight_of_lit(l1) == get_weight_of_lit(l2);
  }

  bool isSameWt(Var v1, Var v2) {
    return get_weight_of_var(v1) == get_weight_of_var(v2);
  }

  bool allSameWt(const vector<Lit>& set) {
    return set.size() < 2 || std::find_if(set.begin(), set.end(), [&](Lit l) {
                               return !isSameWt(l, set[0]);
                             }) == set.end();
  }

  Lit getNewOutputLit() { return mkLit(bvars.newSummationVar()); }

  Bvars& bvars;
  Packed_vecs<Lit> potential_cores;

  // TO add clauses
  MaxHS::MaxSolver* maxsolver;
  MaxHS_Iface::Muser* muser;
  MaxHS_Iface::SatSolver* satsolver;
  Graph core_structure;
  int tl_exhaust_calls{};
  int small_clusters_calls{};
  vector<SRef> sums_list;
  //
  // MAPS
  // var --> summation that var is an input of
  vector<SRef> input_var_to_sref;
  // var --> summation that var is an output of
  vector<SRef> output_var_to_sref;
  // var --> i such that lit is the i-th output of its summation
  vector<int> output_var_to_sout_index;
  // var --> index in sums_list. Internal summations are not in
  // sums_list.
  vector<int> input_var_to_sidx;

  // stats for output
  int seen_sums{0};
};

#endif
