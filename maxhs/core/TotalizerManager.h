/***********[TotalizerManager.h]
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

Some code and ideas from

  Open-WBO, Copyright (c) 2013-2017, Ruben Martins, Vasco Manquinho, Ines Lynce

have been used;
  Open-WBO is subject to the following LICENSE
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
***********/

#ifndef __TOTALIZER_MANAGER__
#define __TOTALIZER_MANAGER__

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
#include "maxhs/core/TotalizerAuxStruct.h"
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

class TotalizerManager {
 public:
  TotalizerManager(Bvars& b, MaxHS::MaxSolver* maxhs, MaxHS_Iface::Muser* m,
                   MaxHS_Iface::SatSolver* s);
  bool totalizers_active() const { return !totalizer_list.empty(); }
  size_t nb_totalizers() const { return totalizer_list.size(); }
  // void clear_cores() { potential_cores.clear(); }
  void add_core(const vector<Lit>& core);
  void add_core_mutex(const vector<Lit>& mx);
  void compute_abstraction(bool full = false);
  Lit getNextOLit(Lit l);

  /*int get_olit_coef(Lit l) {
    assert(isToutput(l));
    return get_olit_index(l)p + 1;
    }*/

  int get_olit_index(Lit l) const {
    assert(isToutput(l));
    return output_var_to_tout_index[toInt(var(l))];
  }

  bool olit_set_in_cplex(Lit l) const {
    assert(isToutput(l));
    return output_added_to_cplex[toInt(var(l))];
  }

  void set_olit_in_cplex(Lit l) {
    assert(isToutput(l));
    output_added_to_cplex[toInt(var(l))] = 1;
  }

  vector<Lit> get_ilits_from_olit(Lit l) {
    assert(isToutput(l));
    return getILits(get_olit_tref(l));
  }

  const vector<Lit>& get_olits_from_olit(Lit l) const {
    assert(isToutput(l));
    return getOLits(get_olit_tref(l));
  }

  vector<Lit> get_ilits_from_tidx(int tidx) {
    return getILits(totalizer_list[tidx]);
  }

  const vector<Lit>& get_olits_from_tidx(int tidx) {
    return getOLits(totalizer_list[tidx]);
  }

  int get_tot_size_from_tidx(int tidx) {
    return getTSize(totalizer_list[tidx]);
  }

  int get_n_true_outs(int tidx) const {
    return getOutTrue(totalizer_list[tidx]);
  }

  vector<int> get_top_level_tidxes() const;

  bool isTinput(Lit l) const {
    return (static_cast<size_t>(toInt(var(l))) < input_var_to_tref.size()) &&
           input_var_to_tref[toInt(var(l))] >= 0;
  }

  int get_Tinput_idx(Lit l) const {
    assert(isTinput(l));
    return input_var_to_tidx[toInt(var(l))];
  }

  Lit get_next_Toutput(int idx, int n_true) {
    assert(static_cast<size_t>(idx) < totalizer_list.size());
    auto tref = totalizer_list[idx];
    if (static_cast<size_t>(n_true) < getOLits(tref).size()) {
      auto cnf{increaseMaxFalse(tref, n_true + 1)};
      addClausesToSolvers(cnf);
      return getOLits(tref)[n_true];
    } else
      return lit_Undef;
  }

  bool isToutput(Lit l) const { return isToutput(var(l)); }

  bool isToutput(Var v) const {
    return (static_cast<size_t>(toInt(v)) < output_var_to_tref.size()) &&
           output_var_to_tref[toInt(v)] >= 0;
  }

  bool isPositiveToutput(Lit l) const { return isToutput(l) && !sign(l); }
  bool isNegativeToutput(Lit l) const { return isToutput(l) && sign(l); }

  /*TEST*/
  void test();
  /*TEST*/

 private:
  friend class Totalizer;

  void abstract_cores(bool full);
  TRef build_totalizer(const vector<Var>&);
  void combine_same_wt_clusters(vector<vector<Var>>&);
  TRef build_totalizer_1(const vector<Lit>&);
  TRef build_mx_totalizer(const vector<Lit>& mx);
  // TRef build_totalizer_2(vector<Lit>&);
  // TRef build_totalizer_3(vector<Lit>&);
  TOut totalizer_from_conflict(const vector<Lit>& conflict,
                               vector<TOut>& inProcess_touts);
  TOut make_and_exhaust_base_totalizer(const vector<Lit>& conf_orig_lits);
  TOut join_and_exhaust_totalizers(vector<TOut>& conf_touts);


  // void find_initial_totalizer(vector<Lit>&, TOut&);
  // void grow_totalizer(vector<Lit>&, TOut&);
  lbool sat_solve_update_assumps(vector<Lit>&, vector<Lit>&);

  TRef get_ilit_tref(Lit l) const {
    assert(isTinput(l));
    return input_var_to_tref[toInt(var(l))];
  }

  TRef get_olit_tref(Lit l) const { return get_olit_tref(var(l)); }

  TRef get_olit_tref(Var v) const {
    assert(isToutput(v));
    return output_var_to_tref[toInt(v)];
  }

  Weight get_weight_of_lit(Lit l) const {
    if (isToutput(l)) {
      return getWeight(get_olit_tref(l));
    } else {
      return bvars.wt(l);
    }
  }

  Weight get_weight_of_var(Var v) const {
    if (isToutput(v)) {
      return getWeight(get_olit_tref(v));
    } else {
      return bvars.wt(v);
    }
  }

  void addClausesToSolvers(const vector<vector<Lit>> cnf);
  int exhaustTotalizer(TRef t);
  void initTotalizer(TRef, int);
  void update_maps(TRef t, size_t tidx);
  Lit output_to_firstinput(Lit l) { return get_ilits_from_olit(l)[0]; }
  Weight computeTotLB();
  // void compute_totalizer_count(TRef t, const vector<int>& counts_in_sol,
  //                              vector<int>& counts);

  void addNewNodesToGraph(vector<Lit>& toAdd);
  void updateExistingNodesinGraph(vector<Lit>& lits_to_add);
  void resizeMaps();

  int getTSize(TRef t) const;
  bool isLeafT(TRef tp) const;
  vector<Lit> getILits(TRef t) const;
  const vector<Lit>& getOLits(TRef t) const;
  const vector<Lit>& getROLits(TRef t) const;
  const vector<Lit>& getLOLits(TRef t) const;
  int getOutTrue(TRef t) const;
  int getOutFalse(TRef t) const;
  bool isTopLevel(TRef t) const;
  void setTopLevel(TRef t);
  void unsetTopLevel(TRef t);

  Weight getWeight(TRef t) const;
  vector<vector<Lit>> increaseMaxFalse(TRef t, int maxFalse);
  vector<vector<Lit>> increaseMaxTrue(TRef t, int maxTrue);
  void setValuedOuts(TRef t);
  bool checkOutputs(TRef t);

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

  Lit getNewOutputLit() { return mkLit(bvars.makeTvar()); }

  bool madeTvars{false};
  Bvars& bvars;
  Packed_vecs<Lit> potential_cores;

  // TO add clauses
  MaxHS::MaxSolver* maxsolver;
  MaxHS_Iface::Muser* muser;
  MaxHS_Iface::SatSolver* satsolver;
  Graph core_structure;

  vector<TRef> totalizer_list;
  //
  // MAPS
  // var --> totalizer that var is an input of
  vector<TRef> input_var_to_tref;
  // var --> totalizer that var is an output of
  vector<TRef> output_var_to_tref;
  // var --> i such that lit is the i-th output of its totalizer
  vector<int> output_var_to_tout_index;
  // var --> true if this totalizer output var has been added to cplex
  vector<char> output_added_to_cplex;
  // var --> index in totalizer_list. Internal totalizers are not in
  // totalizer_list.
  vector<int> input_var_to_tidx;

  // stats for output
  int seen_totalizers{0};
};

#endif
