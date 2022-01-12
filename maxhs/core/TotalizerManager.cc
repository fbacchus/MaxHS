/***********[TotalizerManager.cc]
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

#include "TotalizerManager.h"
#include "Totalizer.h"

#include <stdlib.h>
#include <algorithm>
#include <iostream>
#include <iterator>
#include <utility>
#include "maxhs/ifaces/muser.h"
#include "maxhs/utils/Params.h"

using std::map;
using std::vector;

using MaxHS::MaxSolver;
using MaxHS_Iface::Muser;
using MaxHS_Iface::SatSolver;

TotalizerManager::TotalizerManager(Bvars& b, MaxSolver* maxhs, Muser* m,
                                   SatSolver* s)
    : bvars{b}, maxsolver{maxhs}, muser{m}, satsolver{s} {}

void TotalizerManager::add_core(const vector<Lit>& cnst) {
  // requires that cnst only contain core bvars (true ===> soft clause is
  // falsified) or totalizer output (true ===> some number of soft clauses are
  // falsified)
  if (!params.abstract) return;
  if (cnst.size() > static_cast<size_t>(params.abstract_max_core_size)) {
    if (params.verbosity > 1)
      cout << "c adding large core to graph (size = " << cnst.size()
           << " taking smaller set\n";
    // could select a random subset using std::sample (c++17)
    // but for now just grab the first k elements
    potential_cores.addVec(vector<Lit>(
        cnst.begin(), cnst.begin() + params.abstract_max_core_size));
  } else
    potential_cores.addVec(cnst);
}

void TotalizerManager::add_core_mutex(const vector<Lit>& mx) {
  if(mx.size() <= 1) return;
  if (!madeTvars) {
    bvars.initMaxTvar();
    madeTvars = true;
  }
  vector<Var> mxvars;
  for(auto l: mx) {
    if (!bvars.isCore(l)) return;
    if (!isSameWt(l, mx[0])) return;
    auto v = var(l);
    if (core_structure.in_graph(v)) return;
    mxvars.push_back(v);
  }
  core_structure.addCluster(mxvars);
  TRef t = build_mx_totalizer(mx);
  if(t != NullTRef) {
    if (params.verbosity > 0)
      cout << "c Built mx totalizer: " << getTSize(t)
           << " inputs, " << getOutFalse(t) << " false\n";
    totalizer_list.push_back(t);
    update_maps(t, totalizer_list.size() - 1);
  }
}

void TotalizerManager::compute_abstraction(bool full) {
  if (params.verbosity > 0)
    cout << "c Computing an abstraction with " << potential_cores.size()
         << " new cores\n";
  size_t n_edges{0};
  vector<Lit> core;
  double ave_size = (1.0*potential_cores.total_size())/potential_cores.size();

  /*cout << "ave_size = " << ave_size << " cores_total_size = " << potential_cores.total_size()
    << " num cores = " << potential_cores.size() << "\n";*/
  
  if(ave_size > params.abstract_max_ave_size) {
    if(params.verbosity > 0)
      cout << "c cores too large not abstracting\n";
    potential_cores.clear();
    return;
  }
    
  for (auto cnst : potential_cores) {
    // cout << "Core size: " << cnst.size() << endl;
    core.clear();
    for (Lit l : cnst) {
      if (isToutput(l))
        core.push_back(output_to_firstinput(l));
      else if (bvars.isCore(l) || bvars.isDvar(l))
        core.push_back(l);
    }
    if (core.size() == 0 && params.verbosity > 0) {
      if (params.verbosity > 0)
        cout << "c After processing, orig size " << cnst.size()
             << " no literals left\n";
      continue;
    }
    for (size_t i = 0; i < core.size(); i++)
      for (size_t j = i + 1; j < core.size(); j++)
        if (isSameWt(core[i], core[j])) {
          core_structure.addEdge(core[i], core[j], 1.0);
          ++n_edges;
        }
  }
  potential_cores.clear();
  if (n_edges > 0) {
    if (params.verbosity > 0)
      cout << "c added " << n_edges << " new edges. Abstracting\n";
    abstract_cores(full);
    maxsolver->updateLB(computeTotLB());
  } else if (params.verbosity > 0)
    cout << "c No new edges added skipping abstraction\n";
}

void TotalizerManager::abstract_cores(bool full) {
  if (!madeTvars) {
    bvars.initMaxTvar();
    madeTvars = true;
  }
  vector<vector<Var>> clusters;
  int iter{0};
  bool last_iter{false};
  while (true) {
    auto mod_increase = core_structure.extractCommunities(clusters);
    if (mod_increase <= 0 && !full) break;
    if (mod_increase <= 0) {
      auto n_clusters = clusters.size();
      combine_same_wt_clusters(clusters);
      if (n_clusters == clusters.size()) break;
      else last_iter = true;
    }
    ++iter;
    double tots_built{0};
    double tot_sum_size{};
    double tot_sum_outs_true{};
    int n_tots{0};
    if (params.verbosity > 0)
      cout << "c Cluster Iter " << iter << ". " << clusters.size()
           << " clusters (mod " << mod_increase << ")\n";

    if (params.verbosity > 1) {
      int n_vars_in_clusters{0};
      for (auto& cluster : clusters) n_vars_in_clusters += cluster.size();
      cout << "c Nvars in graph = " << core_structure.get_n_vars()
           << " nvars in cluster = " << n_vars_in_clusters << "\n";
    }

    for (auto& cluster : clusters) {
      if (cluster.size() < static_cast<size_t>(params.abstract_min_size)) {
        continue;
      }
      if (params.verbosity > 1)
        cout << "c building totalizer from cluster of size " << cluster.size()
             << "\n";
      if (params.verbosity > 0 && cluster.size() > 200)
        cout << "c large cluster: " << cluster.size() << "\n";

      TRef t = build_totalizer(cluster);
      if (t != NullTRef) {
        ++tots_built;
        tot_sum_size += getTSize(t);
        tot_sum_outs_true += getOutTrue(t);
        if (params.verbosity > 1)
          cout << "c " << ++n_tots << ". built totalizer: " << getTSize(t)
               << " inputs, " << getOutTrue(t) << " true\n";
        totalizer_list.push_back(t);
        update_maps(t, totalizer_list.size() - 1);
      }
    }

    if (params.verbosity > 0) {
      cout << "c " << tots_built << " new totalizers (out of "
           << clusters.size() << " ), ave. size = " << tot_sum_size / tots_built
           << " ave. true outs " << tot_sum_outs_true / tots_built << "\n";
    }
    if (last_iter) break;
  }
  if (params.verbosity > 0) cout << "c " << iter << ". clustering complete\n";
}

void TotalizerManager::combine_same_wt_clusters(vector<vector<Var>>& clusters) {
  for (auto i = clusters.begin(); i != clusters.end(); ++i)
    for (auto j = clusters.begin(); j != i; j++) {
      if (i->empty() || j->empty()) continue;
      if (isSameWt((*i)[0], (*j)[0])) {
        for (auto& v : *i) j->push_back(v);
        i->clear();
      }
    }
  clusters.erase(std::remove_if(clusters.begin(), clusters.end(),
                                [&](vector<Var>& c) { return c.empty(); }),
                 clusters.end());
}

TRef TotalizerManager::build_totalizer(const vector<Var>& cluster) {
  // cout << "TEST: build_totalizer called with cluster size " <<
  // cluster.size()
  //     << "\n";
  // every var in cluster should be a bvar
  assert(std::find_if(cluster.begin(), cluster.end(), [&](Var v) {
           return !bvars.isBvar(v);
         }) == cluster.end());
  vector<Lit> inputs;  // convert variable cluster to core literals.
  for (auto v : cluster) inputs.push_back(bvars.coreLit(v));
  // every lit should have the same weight.
  assert(allSameWt(inputs));
  inputs.erase(
      std::remove_if(inputs.begin(), inputs.end(),
                     [&](Lit l) { return (satsolver->curVal(l) != l_Undef); }),
      inputs.end());
  if (inputs.size() <= 1) {
    return NullTRef;
  }
  if (!madeTvars) {
    bvars.initMaxTvar();
    madeTvars = true;
  }
  return build_totalizer_1(inputs);
}

TRef TotalizerManager::build_totalizer_1(const vector<Lit>& inputs) {
  vector<Lit> assumps;
  vector<Lit> conflict;
  vector<TOut> inProcess_touts;  // contains all active sub-totalizers that
                                 // remain to be joined into other
                                 // totalizers.
  for (auto l : inputs) {
    if (!isTinput(l))
      assumps.push_back(~l);
    else {
      auto l_tr = get_ilit_tref(l);
      if (std::find_if(inProcess_touts.begin(), inProcess_touts.end(),
                       [&](TOut& tout) { return tout.tr == l_tr; }) ==
          inProcess_touts.end()) {
        auto l_tr_ntrue = getOutTrue(l_tr);
        if (static_cast<size_t>(l_tr_ntrue) < getOLits(l_tr).size()) {
          auto l_out_lit = getOLits(l_tr)[l_tr_ntrue];
          inProcess_touts.push_back({l_out_lit, l_tr_ntrue, l_tr});
          assumps.push_back(~l_out_lit);
        }
      }
    }
  }
  if (assumps.size() <= 1) {
    if (params.verbosity > 1)
      cout << "c build_totalizer_1 already a cluster skipping\n";
    return NullTRef;
  }

  // an invariant in this loop is that every active sub-totalizer
  // (i.e. sub-totalizer not yet absorbed into another totalizer) has a
  // negated output lit in assumps, and every original literal not yet
  // absorbed into a totalizer has its negation in assumps.
  // When all original lits and sub-totalizers have been absorbed into
  // a totalizer, assumps will become empty.

  TOut t0;
  while (!assumps.empty()) {
    conflict.clear();
    if (sat_solve_update_assumps(assumps, conflict) == l_False) {
      if (params.verbosity > 1)
        cout << "c build_totalizer_1 found conflict. Size = " << conflict.size()
             << "\n";
      if (conflict.empty()) {
        cout << "c ERROR, build_totalizer found empty conflict\n";
        return NullTRef;
      }
      // constuct single totalizer from the conflict original lits
      // and sub-totalizer outputs
      t0 = totalizer_from_conflict(conflict, inProcess_touts);
      if (t0.tr != NullTRef && !assumps.empty()) {
        inProcess_touts.push_back(t0);
        assumps.push_back(~t0.out_lit);
      }
    } else {  // remaining assumptions are satisfiable
      assert(!assumps.empty());
      conflict.clear();
      for (auto l : assumps) {
        if (satsolver->curVal(l) == l_Undef) conflict.push_back(~l);
      }
      assumps.clear();
      t0 = totalizer_from_conflict(conflict, inProcess_touts);
    }
  }
  return t0.tr;
}

TRef TotalizerManager::build_mx_totalizer(const vector<Lit>& mx) {
  Weight wt{get_weight_of_lit(mx[0])};
  TRef t = Totalizer::makeTotalizer(*this, mx, wt);
  const vector<Lit>& oLits = getOLits(t);

  cout << " Built mx totalizer outlits = " << oLits << "\n";
  
  satsolver->addClause(~oLits[1]);
  setValuedOuts(t);
  addClausesToSolvers(increaseMaxFalse(t, 2));
  addClausesToSolvers(increaseMaxTrue(t, 1));
  return t;
}

lbool TotalizerManager::sat_solve_update_assumps(vector<Lit>& assumps,
                                                 vector<Lit>& conflict) {
  // sat solve and remove conflict (if found from assumptions)
  conflict.clear();
  lbool sat_result;
  if(params.cpu_per_exhaust < 0)
    sat_result = satsolver->solve(assumps, conflict);
  else if(params.cpu_per_exhaust > 0)
    sat_result = satsolver->solveBudget(assumps, conflict, params.cpu_per_exhaust);
  else
    sat_result = l_Undef;

  if (sat_result == l_False) {
    if (params.min_type == 1 && conflict.size() > 2) {
      if (params.mus_cpu_lim > 0) {
        muser->musBudget(conflict, params.mus_cpu_lim);
      } else {
        muser->mus(conflict);
      }
    }
    satsolver->addClause(conflict);
    std::sort(conflict.begin(), conflict.end());
    auto e = std::remove_if(assumps.begin(), assumps.end(), [&](Lit l) {
      return (satsolver->curVal(l) != l_Undef ||
              std::binary_search(conflict.begin(), conflict.end(), ~l));
    });
    assumps.erase(e, assumps.end());
  } else if (sat_result == l_True) {
    maxsolver->updateUB();
  }
  return sat_result;
}

TOut TotalizerManager::totalizer_from_conflict(const vector<Lit>& conflict,
                                               vector<TOut>& inProcess_touts) {
  // Build a totalizer from the lits in conflict (some of which might be
  // output lits from active sub-totalizer in inProcess_touts.
  assert(!conflict.empty());
  vector<Lit> conf_orig_lits;
  vector<TOut> conf_touts;

  // 1. split conflict
  for (auto l : conflict) {
    auto it = std::find_if(inProcess_touts.begin(), inProcess_touts.end(),
                           [&](TOut t) { return t.out_lit == l; });
    if (it != inProcess_touts.end()) {
      // move the found sub totalizer from inprocess to conf This
      // sub-totalizer will be joined into the final totalizer
      // generated by the conflict so it is no longer going to be
      // active
      conf_touts.push_back(*it);
      *it = inProcess_touts.back();
      inProcess_touts.pop_back();
    } else
      conf_orig_lits.push_back(l);
  }

  // 2. build and exhaust a totalizer over the orig lits
  if (conflict.size() == 1) {
    if (conf_orig_lits.size() == 1) return TOut{};
  }
  if (!conf_orig_lits.empty()) {
    TOut t0 = make_and_exhaust_base_totalizer(conf_orig_lits);
    if (t0.tr != NullTRef) conf_touts.push_back(t0);
  }
  // 3. join and exhaust the totalizer over the orig lits
  //    and all other sub-totalizers found in the conflict.
  //    Return a TOut structure from this totalizer
  return join_and_exhaust_totalizers(conf_touts);
}

/*TEST*/
void TotalizerManager::test() {
  /*vector<Lit> v;
  vector<vector<Lit>> cnf;
  for (int i = 0; i < 6; i++) {
    v.push_back(mkLit(i));
  }
  cnf.clear();
  Totalizer::makeTotalizer(*this, v, cnf, 0, 0, 1.0);
  cout << "Totalizer of size " << v.size() << " cnf = " << cnf << "\n";
  exit(0);*/
  auto vars{bvars.getvars()};
  TRef t = build_totalizer(vars);
  if (t != NullTRef) {
    totalizer_list.push_back(t);
    update_maps(t, totalizer_list.size() - 1);
    const vector<Lit>& iLits = getILits(t);
    const vector<Lit>& oLits = getOLits(t);
    for (auto l : iLits)
      if (!bvars.isCore(l)) {
        cout << "ERROR input to final totalizer is not a core\n";
        exit(1);
      }
    for (auto l : oLits)
      if (!isToutput(l)) {
        cout << "ERROR output to final totalizer is not TOut\n";
        exit(1);
      }
  }
}
/*TEST*/

TOut TotalizerManager::make_and_exhaust_base_totalizer(
    const vector<Lit>& conf_orig_lits) {
  // build a totalizer over this set of lits, then exhaust it.
  // if is_clause, this set of lits are a clause so their totalizer must
  // have its first output set to true.
  assert(!conf_orig_lits.empty());
  assert(allSameWt(conf_orig_lits));
  Weight wt{get_weight_of_lit(conf_orig_lits[0])};
  auto t0 = Totalizer::makeTotalizer(*this, conf_orig_lits, wt);
  int lb = exhaustTotalizer(t0);
  if (lb >= static_cast<int>(getTSize(t0)))
    return TOut{};
  else
    return TOut{getOLits(t0)[lb], lb, t0};
}

TOut TotalizerManager::join_and_exhaust_totalizers(vector<TOut>& conf_touts) {
  // join these totalizers into one. The final totalizer must have one extra
  // output true if uncounted_true
  if (conf_touts.empty()) return TOut{};
  TRef t0{NullTRef};
  for (size_t i = 0; i < conf_touts.size(); i++) {
    int lb{0};
    if (t0 == NullTRef) {
      t0 = conf_touts[i].tr;
      lb = exhaustTotalizer(t0);
    } else {
      t0 = Totalizer::makeTotalizer(*this, t0, conf_touts[i].tr);
      lb = exhaustTotalizer(t0);
    }
    if (lb >= getTSize(t0)) t0 = NullTRef;
  }
  if (t0 == NullTRef)
    return TOut{};
  else {
    int nTrue{getOutTrue(t0)};
    return TOut{getOLits(t0)[nTrue], nTrue, t0};
  }
}

int TotalizerManager::exhaustTotalizer(TRef tot) {
  // cout << "TEST: exhausting totalizer " << (*tot) << "\n";
  const vector<Lit>& oLits = getOLits(tot);
  setValuedOuts(tot);
  int lb = getOutTrue(tot);
  // cout << "TEST: lb = " << lb << "\n";
  vector<Lit> assumps(1);
  while (lb < static_cast<int>(getOLits(tot).size())) {
    addClausesToSolvers(increaseMaxFalse(tot, lb + 1));
    assumps[0] = ~oLits[lb];
    vector<Lit> discard;
    lbool res;
    if(params.cpu_per_exhaust < 0)
      res = satsolver->solve(assumps, discard);
    else if(params.cpu_per_exhaust > 0)
      res = satsolver->solveBudget(assumps, discard, params.cpu_per_exhaust);
    else
      res = l_Undef;
    // cout << "TEST in exhaust loop sat solver returns " << res << "\n";
    // cout << " lb = " << lb << "\n";
    if (res == l_False) {
      satsolver->addClause(oLits[lb]);
      ++lb;
    } else {
      if (res == l_True) maxsolver->updateUB();
      break;
    }
  }
  (*tot).setNOutTrue(lb);
  addClausesToSolvers(increaseMaxTrue(tot, lb));
  return lb;
}

/*void TotalizerManager::initTotalizer(TRef tot, int ntrue) {
  // call if you have an initial lb bound on totalizer
  setValuedOuts(tot);
  if (ntrue > getOutTrue(tot)) {
    const vector<Lit>& oLits = getOLits(tot);
    for (int i = getOutTrue(tot); i < ntrue && i < getTSize(tot); ++i)
      if (satsolver->curVal(oLits[i]) != l_True) {
        satsolver->addClause(oLits[i]);
      }
    int lb = getOutTrue(tot);
    addClausesToSolvers(increaseMaxFalse(tot, lb + 1));
  }
  }*/

void TotalizerManager::addClausesToSolvers(const vector<vector<Lit>> cnf) {
  for (const auto& clause : cnf) {
    satsolver->addClause(clause);
    muser->addClause(clause);
  }
}

void TotalizerManager::update_maps(TRef t, size_t tidx) {
  // t is a new top level totalizer
  resizeMaps();
  setTopLevel(t);

  auto iLits = getILits(t);
  auto oLits = getOLits(t);

  for (Lit l : iLits) {
    assert(bvars.isBvar(l));
    if(input_var_to_tref[toInt(var(l))] != -1)
      unsetTopLevel(input_var_to_tref[toInt(var(l))]);
    input_var_to_tref[toInt(var(l))] = t;
    input_var_to_tidx[toInt(var(l))] = tidx;
  }

  for (size_t j = 0; j < oLits.size(); j++) {
    Lit o = oLits[j];
    output_var_to_tref[toInt(var(o))] = t;
    output_var_to_tout_index[toInt(var(o))] = j;
  }
}

// void TotalizerManager::compute_totalizer_count(
//     TRef tot, const vector<int>& bvars_in_sol_counts, vector<int>& counts) {
//   /* set counts[i] to be the maximum number of true inputs possible
//      for totalizer i.
//   */
//   if (counts[tot] >= 0) return;
//   auto ilit{getILits(tot)};
//   // bvars_in_sol_counts does not include inputs that are outputs of other
//   // totalizers
//   int num_falsified{bvars_in_sol_counts[tot]};
//   for (Lit l : ilit) {
//     if (isToutput(l)) {
//       // check if this input (that is an output of another totalizer is
//       // also falsified)
//       TRef tref_o = get_olit_tref(l);
//       int tref_o_index = get_olit_index(l);
//       if (counts[tref_o] < 0)
//         compute_totalizer_count(tref_o, bvars_in_sol_counts, counts);
//       if (counts[tref_o] <= tref_o_index) {
//         num_falsified++;
//       }
//     }
//   }
//   int baseCount =
//       std::max(static_cast<int>(ilit.size()) - num_falsified, getOutTrue(tot));
//   // cout << "Index " << index <<  " Base count " << baseCount << "\n";
//   counts[tot] = baseCount;
// }

Lit TotalizerManager::getNextOLit(Lit l) {
  assert(isToutput(l));
  TRef tot = get_olit_tref(l);
  int nextOutputIdx = get_olit_index(l) + 1;
  if (nextOutputIdx >= static_cast<int>(getOLits(tot).size()))
    return lit_Undef;
  else {
    auto cnf{increaseMaxFalse(tot, nextOutputIdx + 1)};
    addClausesToSolvers(cnf);
    return getOLits(tot)[nextOutputIdx];
  }
}

void TotalizerManager::resizeMaps() {
  size_t sz = bvars.n_vars();
  if (input_var_to_tref.size() < sz) {
    input_var_to_tref.resize(sz, -1);
    input_var_to_tidx.resize(sz, -1);
    output_var_to_tref.resize(sz, -1);
    output_var_to_tout_index.resize(sz, -1);
    output_added_to_cplex.resize(sz, 0);
  }
}

// TODO change code so that TRef objects have a -> operator
// so that, e.g., t->getSize() can be used instead of (*t).getSize()
// But this will require refactoring the headers since -> operators
// must be member functions of the TRef class.

void TotalizerManager::setValuedOuts(TRef t) {
  // update the ouputs of t to their forced values.
  int lrfalse{0}, lrtrue{0};
  TRef r{(*t).getRight()};
  TRef l{(*t).getLeft()};

  if (r != NullTRef) {
    setValuedOuts(r);
    lrtrue += getOutTrue(r);
    lrfalse += getOutFalse(r);
  }
  if (l != NullTRef) {
    setValuedOuts(l);
    lrtrue += getOutTrue(l);
    lrfalse += getOutFalse(l);
  }
  const vector<Lit>& oLits = getOLits(t);
  int ntrue{0};
  for (; ntrue < lrtrue; ++ntrue) {
    if (satsolver->curVal(oLits[ntrue]) != l_True)
      satsolver->addClause(oLits[ntrue]);
  }
  for (; ntrue < static_cast<int>(oLits.size()); ntrue++) {
    if (satsolver->curVal(oLits[ntrue]) != l_True) break;
  }
  (*t).setNOutTrue(ntrue);

  int nfalse{0};
  auto last{oLits.size() - 1};
  for (; nfalse < lrfalse; nfalse++) {
    if (satsolver->curVal(oLits[last - nfalse]) != l_False)
      satsolver->addClause(~oLits[last - nfalse]);
  }
  for (; nfalse < static_cast<int>(oLits.size()); nfalse++) {
    if (satsolver->curVal(oLits[last - nfalse]) != l_False) break;
  }
  (*t).setNOutFalse(nfalse);

  assert(checkOutputs(t));
}

Weight TotalizerManager::computeTotLB() {
  Weight w{};
  for(auto t : totalizer_list) 
    if(isTopLevel(t)) 
      w += getOutTrue(t) * getWeight(t);
  return w;
}

vector<int> TotalizerManager::get_top_level_tidxes() const {
  vector<int> tidxs;
  for(size_t i = 0; i < totalizer_list.size(); ++i)
    if(isTopLevel(totalizer_list[i]))
      tidxs.push_back(i);
  return tidxs;
}

bool TotalizerManager::checkOutputs(TRef t) {
  // outputs should be true first undef next false last.
  auto oLits{getOLits(t)};
  int type{-1}, nxt_type{-1};
  for (int i = 0; i < static_cast<int>(oLits.size()); i++) {
    auto val = satsolver->curVal(oLits[0]);
    if (val == l_True)
      nxt_type = 0;
    else if (val == l_Undef)
      nxt_type = 1;
    else if (val == l_False)
      nxt_type = 3;
    if (nxt_type < type) return false;
    type = nxt_type;
  }
  return true;
}

int TotalizerManager::getTSize(TRef t) const { return (*t).getSize(); }
bool TotalizerManager::isLeafT(TRef t) const { return (*t).isLeaf(); }

int TotalizerManager::getOutTrue(TRef t) const { return (*t).getOutTrue(); }

int TotalizerManager::getOutFalse(TRef t) const { return (*t).getOutFalse(); }

vector<Lit> TotalizerManager::getILits(TRef t) const {
  return (*t).getInputs();
}
const vector<Lit>& TotalizerManager::getOLits(TRef t) const {
  return (*t).getOutputs();
}

const vector<Lit>& TotalizerManager::getROLits(TRef t) const {
  auto rt = (*t).getRight();
  return (*rt).getOutputs();
}

const vector<Lit>& TotalizerManager::getLOLits(TRef t) const {
  auto lt = (*t).getLeft();
  return (*lt).getOutputs();
}

Weight TotalizerManager::getWeight(TRef t) const { return (*t).getWeight(); }
vector<vector<Lit>> TotalizerManager::increaseMaxFalse(TRef t, int maxFalse) {
  return (*t).increaseMaxFalse(maxFalse);
}
vector<vector<Lit>> TotalizerManager::increaseMaxTrue(TRef t, int maxTrue) {
  return (*t).increaseMaxFalse(maxTrue);
}

bool TotalizerManager::isTopLevel(TRef t) const { return (*t).isTopLevel(); }
void TotalizerManager::setTopLevel(TRef t)  { return (*t).setTopLevel(); }
void TotalizerManager::unsetTopLevel(TRef t)  { return (*t).unsetTopLevel(); }

/*TRef TotalizerManager::build_totalizer_2(vector<Lit>& orig_inputs) {
  // We look for a conflict and try to build sub-totalizers over these
  // conflicts finally joining up the sub-totalizers.
  vector<Lit> assumps(orig_inputs.size());
  std::transform(orig_inputs.begin(), orig_inputs.end(), assumps.begin(),
                 [](Lit l) { return ~l; });

  vector<Lit> conflict;
  // conflict will be partitioned into original lits
  // and created sub-totalizer outputs
  TOut current_T{};

  while (!assumps.empty()) {
    // cout << "TEST: assumps.size() = " << assumps.size() << "\n";
    conflict.clear();
    if (sat_solve_update_assumps(assumps, conflict) == l_False) {
      if (params.verbosity > 0)
        cout << "c build_totalizer_2 found conflict. Size = " <<
  conflict.size()
             << "\n";
      if (conflict.empty()) {
        cout << "c ERROR, build_totalizer_2 found empty conflict\n";
        return NullTRef;
      } else if (conflict.size() == 1) {
        if (params.verbosity > 0) cout << "c in build_totalizer_2 found
  unit\n";
        // satsolver->addClause(conflict[0]);
        if (conflict[0] == current_T.out_lit) {
          if (params.verbosity > 0)
            cout << "c conflict is current totalizer output index "
                 << current_T.toutIdx << "\n";
          auto tot{current_T.tr};
          auto oLits{getOLits(tot)};
          initTotalizer(tot, current_T.toutIdx);
          auto nxt_idx{current_T.toutIdx + 1};
          if (nxt_idx < getTSize(tot)) {
            current_T = TOut{oLits[nxt_idx], nxt_idx, tot};
            assumps.push_back(~current_T.out_lit);
          } else {
            current_T = TOut{};  // exhausted this totalizer
          }
        }
      } else {  // non-unit conflict of size > 1
        auto it =
            std::remove(conflict.begin(), conflict.end(), current_T.out_lit);
        if (params.verbosity > 0) {
          if (it == conflict.end())
            cout << "c found conflict not including current totalizer\n";
          else
            cout << "c found conflict including current totalizer\n";
        }
        conflict.erase(it, conflict.end());

        // build new totalizer and then join with current totalizer.
        auto tout = make_and_exhaust_base_totalizer(conflict);
        auto t0 = tout.tr;
        auto lb = getOutTrue(t0);
        if (current_T.tr != NullTRef) {
          auto nTrue = getOutTrue(current_T.tr) + getOutTrue(t0);
          t0 = Totalizer::makeTotalizer(*this, current_T.tr, t0);
          initTotalizer(t0, nTrue);
          lb = exhaustTotalizer(t0);
        }
        assumps.erase(
            std::remove(assumps.begin(), assumps.end(), ~current_T.out_lit),
            assumps.end());
        if (static_cast<size_t>(lb) < getOLits(t0).size()) {
          current_T = TOut{getOLits(t0)[lb], lb, t0};
          assumps.push_back(~current_T.out_lit);
        } else {
          current_T = TOut{};
        }
      }
    } else {
      assert(!assumps.empty());
      // the sat solver did not find a new conflict.  Collect remaining
      // lits into a totalizer and then join with current totalizer
      if (assumps.size() == 1) {
        assert(assumps[0] == ~current_T.out_lit);
        assumps.clear();
      } else {
        conflict.clear();
        for (auto l : assumps) {
          if (satsolver->curVal(l) == l_Undef && l != ~current_T.out_lit)
            conflict.push_back(~l);
        }
        auto tout = make_and_exhaust_base_totalizer(conflict);
        auto t0 = tout.tr;
        auto lb = getOutTrue(t0);
        if (current_T.tr != NullTRef) {
          auto nTrue = getOutTrue(current_T.tr) + getOutTrue(t0);
          t0 = Totalizer::makeTotalizer(*this, current_T.tr, t0);
          initTotalizer(t0, nTrue);
          lb = exhaustTotalizer(t0);
        }
        assumps.clear();
        if (static_cast<size_t>(lb) < getOLits(t0).size()) {
          current_T = TOut{getOLits(t0)[lb], lb, t0};
        } else {
          current_T = TOut{};
        }
      }
    }
  }
  return current_T.tr;
  }*/

/*TRef TotalizerManager::build_totalizer_3(vector<Lit>& orig_inputs) {
  if (params.verbosity > 0)
    cout << "c build_totalizer type 3 on " << orig_inputs.size() << "
  inputs\n"; vector<Lit> assumps(orig_inputs.size());
  std::transform(orig_inputs.begin(), orig_inputs.end(), assumps.begin(),
                 [](Lit l) { return ~l; });

  vector<Lit> conflict;
  TOut current_T{};
  while (!assumps.empty()) {
    if (current_T.tr == NullTRef) {
      find_initial_totalizer(assumps, current_T);
    } else {
      grow_totalizer(assumps, current_T);
    }
  }
  return current_T.tr;
  }*/

/*void TotalizerManager::find_initial_totalizer(vector<Lit>& assumps,
                                              TOut& current_T) {
  vector<Lit> conflict{};
  while (!assumps.empty()) {
    if (sat_solve_update_assumps(assumps, conflict) == l_False) {
      if (params.verbosity > 0)
        cout << "c initial_totalizer found conflict. Size = " <<
  conflict.size()
             << "\n";
      if (conflict.empty()) {
        cout << "c ERROR, build_totalizer found empty conflict\n";
        current_T = TOut{};
        assumps.clear();
        return;
      } else if (conflict.size() == 1) {
        // satsolver->addClause(conflict[0]);
      } else {
        Weight wt{get_weight_of_lit(conflict[0])};
        auto t0 = Totalizer::makeTotalizer(*this, conflict, wt);
        // this totalizer already has one true input.
        initTotalizer(t0, 1);
        auto lb = exhaustTotalizer(t0);
        // if all inputs of totalizer are forced to be true we don't
        // need the totalizer
        if (lb >= getTSize(t0))
          current_T = TOut{};
        else {
          current_T = TOut{getOLits(t0)[lb], lb, t0};
          return;
        }
      }
    } else {  // no conflict in this call. Build final totalizer.
      if (params.verbosity > 0)
        cout << "c initial_totalizer found sat over remaining "
             << assumps.size() << " assumptions\n";
      current_T = TOut{};
      if (assumps.size() > 1) {
        conflict.clear();
        for (auto l : assumps) {
          if (satsolver->curVal(l) == l_Undef) conflict.push_back(~l);
        }
        Weight wt{get_weight_of_lit(conflict[0])};
        auto t0 = Totalizer::makeTotalizer(*this, conflict, wt);
        initTotalizer(t0, 0);
        current_T = TOut{getOLits(t0)[0], 0, t0};
      }
      assumps.clear();
      return;
    }
  }
  }*/

/*void TotalizerManager::grow_totalizer(vector<Lit>& assumps, TOut& current_T)
  {
  // grow the totalizer in current_T by successively adding literals from
  // assumps that are falsified by the current model.
  vector<Lit> incremental_assumps;
  vector<Lit> conflict;
  incremental_assumps.push_back(~current_T.out_lit);
  while (!assumps.empty()) {
    auto it = std::find_if(assumps.begin(), assumps.end(), [&](Lit l) {
      return satsolver->modelValue(l) != l_True;
    });
    if (it == assumps.end()) {
      if (params.verbosity > 0)
        cout << "c grow_totalizer found sat over "
             << assumps.size() + incremental_assumps.size()
             << " remaining assumptions (" << assumps.size() << ","
             << incremental_assumps.size() << ")\n";
      conflict.clear();
      for (auto l : assumps) {
        if (satsolver->curVal(l) == l_Undef) conflict.push_back(~l);
      }
      for (auto l : incremental_assumps)
        if (satsolver->curVal(l) == l_Undef) conflict.push_back(~l);
      Weight wt{get_weight_of_lit(conflict[0])};
      auto t0 = Totalizer::makeTotalizer(*this, conflict, wt);
      initTotalizer(t0, 0);
      t0 = Totalizer::makeTotalizer(*this, current_T.tr, t0);
      initTotalizer(t0, getOutTrue(current_T.tr));
      current_T = TOut{getOLits(t0)[getOutTrue(t0)], getOutTrue(t0), t0};
      assumps.clear();
      return;
    } else {  // test for new conflict
      incremental_assumps.push_back(*it);
      *it = assumps.back();
      assumps.pop_back();
      if (sat_solve_update_assumps(incremental_assumps, conflict) == l_False)
  { if (params.verbosity > 0) cout << "c grow totalizer found conflict. Size =
  " << conflict.size()
               << "\n";
        if (conflict.empty()) {
          cout << "c ERROR, build_totalizer found empty conflict\n";
          current_T = TOut{};
          assumps.clear();
          return;
        } else if (conflict.size() == 1) {
          // satsolver->addClause(conflict[0]);
          if (conflict[0] == current_T.out_lit) {
            if (params.verbosity > 0)
              cout << "c grow_totalizer conflict is totalizer output\n";
            auto tot = current_T.tr;
            ++current_T.toutIdx;
            if (current_T.toutIdx < getTSize(tot)) {
              current_T.out_lit = getOLits(tot)[current_T.toutIdx];
              incremental_assumps[0] = ~current_T.out_lit;
            } else {
              // this totalizer is exhausted return to find new
              // totalizer over remaining assumptions
              for (size_t i = 1; i < incremental_assumps.size(); i++)
                assumps.push_back(incremental_assumps[i]);
              current_T = TOut{};
              return;
            }
          } else {
            if (params.verbosity > 0)
              cout << "c grow_totalizer found ordinary unit\n";
          }
        } else {  // non-unit conflict
          auto it =
              std::remove(conflict.begin(), conflict.end(),
  current_T.out_lit); bool disjoint_conflict = (it == conflict.end());
          conflict.erase(it, conflict.end());
          Weight wt{get_weight_of_lit(conflict[0])};
          auto t0 = Totalizer::makeTotalizer(*this, conflict, wt);
          initTotalizer(t0, (disjoint_conflict ? 1 : 0));
          t0 = Totalizer::makeTotalizer(*this, current_T.tr, t0);
          auto lb = exhaustTotalizer(t0);
          if (lb > getTSize(t0)) {
            for (size_t i = 1; i < incremental_assumps.size(); i++)
              assumps.push_back(incremental_assumps[i]);
            current_T = TOut{};
            return;
          } else {
            current_T = TOut{getOLits(t0)[lb], lb, t0};
            incremental_assumps[0] = ~current_T.out_lit;
          }
        }
      } else {
        if (params.verbosity > 0)
          cout << "c grow_totalizer satisfied incremental assumption "
                  "growing "
                  "incrementals\n";
      }
    }
  }
  }*/
