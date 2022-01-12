/***********[cadicalSatSolver.cc]
Copyright (c) 2012-2013 Jessica Davies, Fahiem Bacchus

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

/* Interface to minisat.
 */

#include <algorithm>
#include <ostream>
#include <vector>

#include "cadical/src/cadical.hpp"
#include "maxhs/ifaces/cadicalSatSolver.h"
#include "maxhs/utils/Params.h"
#include "maxhs/utils/io.h"
#include "minisat/core/SolverTypes.h"

using namespace MaxHS_Iface;
using sat_solver = CaDiCaL::Solver;
using Minisat::mkLit;
using Minisat::var;

/*************************************************/
// Private
int cadicalSolver::var2cadi(const Var v) const { return v + 1; }
int cadicalSolver::lit2cadi(const Lit l) const {
  int v = var(l) + 1;
  return sign(l) ? -v : v;
}

Var cadicalSolver::cadi2var(int c) const { return abs(c) - 1; }
Lit cadicalSolver::cadi2lit(int c) const {
  int v = cadi2var(c);
  return c < 0 ? mkLit(v, true) : mkLit(v);
}

void cadicalSolver::mark_var_in_solver(Var v) {
  if (static_cast<size_t>(v) >= v_in_s.size()) {
    v_in_s.resize(v + 1, 0);
    var_fixed_vals.resize(v + 1, l_Undef);
  }
  v_in_s[v] = 1;
}

/*************************************************/
// Solver interface routines

lbool cadicalSolver::solve_(const vector<Lit>& assumps, vector<Lit>& conflict,
                            int64_t confBudget, int64_t propagationBudget) {
  // cout << "cadicalSolver confBudget = " << confBudget << " propagationBudget
  // "
  //      << propagationBudget << "\n";
  // reset_assumptions();
  conflict.clear();
  for (auto l : assumps) {
    // if lit not in solver then it can't impose any restriction when assumed
    mark_lit_in_solver(l);
    sat_solver::assume(lit2cadi(l));
  }
  limit("conflicts", confBudget);
  limit("propagations", propagationBudget);
  int res = sat_solver::solve();
  if (res == 0) return l_Undef;
  if (res == 10) return l_True;

  for (auto l : assumps)
    // find all lits in conflict (they are all negated assumptions)
    if (lit_in_solver(l) && in_conflict(~l)) conflict.push_back(~l);
  return l_False;
}

bool cadicalSolver::in_conflict(Lit l) {
  // l is in the conflict if ~l is a failed assumption
  return (sat_solver::failed(lit2cadi(~l)));
}

lbool cadicalSolver::simplify(int rounds) {
  int res = sat_solver::simplify(rounds);
  if (res == 10) return l_True;
  if (res == 20)
    return l_False;
  else
    return l_Undef;
}

bool cadicalSolver::findImplications(const vector<Lit>& assumps,
                                     vector<Lit>& imps) {
  vector<int> iassumps, iimps;
  for (auto lit : assumps) {
    if (lit_in_solver(lit)) iassumps.push_back(lit2cadi(lit));
  }
  auto res = sat_solver::find_up_implicants(iassumps, iimps);
  imps.clear();
  if (res)
    for (auto ilit : iimps) imps.push_back(cadi2lit(ilit));
  // else
  // cout << "findImplications bad result " << assumps << " res " << res <<
  // '\n';
  return res;
}

bool cadicalSolver::unit_propagate() {
  auto res = sat_solver::root_level_propagate();
  return res;
}

void cadicalSolver::addClause(const vector<Lit>& lts) {
  for (auto lt : lts) {
    mark_lit_in_solver(lt);
    add(lit2cadi(lt));
  }
  add(0);
}

void cadicalSolver::setPolarity(lbool pol, Var v) {
  // cout << "setPolarity(" << v << "," << pol << ")\n";
  if (!var_in_solver(v)) return;
  int cvar = var2cadi(v);
  if (pol == l_Undef)
    sat_solver::unphase(cvar);
  else
    sat_solver::phase(pol == l_False ? -cvar : cvar);
  // cout << "cadi = " << var2cadi(v)
  //      << " cadilit = " << lit2cadi(mkLit(v, pol == l_True ? true : false))
  //      << "\n";
}

lbool cadicalSolver::modelValue(Lit p) const {
  if (!lit_in_solver(p) || status() != 10) return l_Undef;
  int res = val(lit2cadi(p));
  return res > 0 ? l_True : l_False;
}

lbool cadicalSolver::modelValue(Var x) const {
  if (!var_in_solver(x) || status() != 10) return l_Undef;
  int res = val(var2cadi(x));
  return res > 0 ? l_True : l_False;
}

lbool cadicalSolver::internal_fixedValue(Var x) const {
  if (!var_in_solver(x)) return l_Undef;
  int res = sat_solver::fixed(var2cadi(x));
  return !res ? l_Undef : (res > 0 ? l_True : l_False);
}

lbool cadicalSolver::internal_fixedValue(Lit p) const {
  if (!lit_in_solver(p)) return l_Undef;
  int res = sat_solver::fixed(lit2cadi(p));
  return !res ? l_Undef : (res > 0 ? l_True : l_False);
}

lbool cadicalSolver::fixedValue(Var x) {
  if (!var_in_solver(x)) return l_Undef;
  updateFixed();
  return var_fixed_vals[x];
}

lbool cadicalSolver::fixedValue(Lit p) {
  if (!lit_in_solver(p)) return l_Undef;
  updateFixed();
  auto val = var_fixed_vals[var(p)];
  return sign(p) ? val.neg() : val;
}

bool cadicalSolver::get_ith_clause(vector<Lit>& cls, size_t i) const {
  vector<int> icls;
  cls.clear();
  auto res = sat_solver::get_ith_clause(icls, i);
  for (auto ilt : icls) cls.push_back(cadi2lit(ilt));
  return res;
}

namespace MaxHS_Iface {
class Units_in_witnesses : public CaDiCaL::WitnessIterator {
 public:
  Units_in_witnesses(cadicalSolver* s) : slv{s} {}
  bool witness(const vector<int>& clause,
               [[maybe_unused]] const vector<int>& witness) {
    Lit unit;
    int unset_count{0};
    for (auto cad_lit : clause) {
      Lit l = slv->cadi2lit(cad_lit);
      auto var_val = slv->var_fixed_vals[var(l)];
      if (var_val == l_Undef) {
        ++unset_count;
        if (unset_count > 1)
          return true;  // clause not unit done with
                        // it
        unit = l;
      } else if (var_val == (sign(l) ? l_False : l_True)) {
        return true;  // clause is sat done with it.
      }
    }
    // found unit in extension stack
    slv->var_fixed_vals[var(unit)] = sign(unit) ? l_False : l_True;
    slv->fixed_lits.push_back(unit);
    return true;
  }
  cadicalSolver* slv;
};
}  // namespace MaxHS_Iface

//This should be called whenever the sat solver could fix more
//variables, e.g., after solve. 

void cadicalSolver::updateFixed() {
  if (n_internal_fixed() == n_ifixed) {
    //nothing new was fixed in solver since last call.
    return;
  }
  auto prev_fixed{fixed_lits.size()};
  const vector<int>& ex_units = solver_units();
  for( ; n_ifixed < ex_units.size(); n_ifixed++) {
    Lit fixedLit = cadi2lit(ex_units[n_ifixed]);
    if (var_fixed_vals[var(fixedLit)] == l_Undef) {
      fixed_lits.push_back(fixedLit);
      var_fixed_vals[var(fixedLit)] = sign(fixedLit) ? l_False : l_True;
    }
  }
  
  if (params.verbosity > 2 && prev_fixed < fixed_lits.size())
    cout << "c cadical found " << fixed_lits.size() - prev_fixed
         << " forced lits\n";
  //auto prev1_fixed{fixed_lits.size()};

  //Units_in_witnesses uw{this};
  //sat_solver::traverse_witnesses_backward(uw);

  //if (params.verbosity > 2 && prev1_fixed < fixed_lits.size())
  //  cout << "c cadical extension stack yielded " << fixed_lits.size() - prev1_fixed
  //       << " additional forced lits\n"
  //       << "fixed_lits.size() = " << fixed_lits.size() << '\n';

}

vector<Lit> cadicalSolver::getForced(int index) {
  vector<Lit> forced{};
  updateFixed();
  for (size_t i = index; i < fixed_lits.size(); i++)
    forced.push_back(fixed_lits[i]);
  return forced;
}
