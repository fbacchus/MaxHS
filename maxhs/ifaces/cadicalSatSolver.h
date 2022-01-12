/***********[cadicalSatSolver.h]
Copyright (c) 2012-2020 Fahiem Bacchus

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

/* Cadical interface
 */

#ifndef CADICALSATSOLVER_H
#define CADICALSATSOLVER_H

#include "cadical/src/cadical.hpp"
#include "maxhs/ifaces/SatSolver.h"

#ifdef GLUCOSE
#include "glucose/core/SolverTypes.h"
#else
#include "minisat/core/SolverTypes.h"
#endif
#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

using Minisat::lit_Undef;
using Minisat::mkLit;
using Minisat::var_Undef;
using Minisat::vec;

namespace MaxHS_Iface {

// Minisat Solver
class cadicalSolver : public SatSolver, protected CaDiCaL::Solver {
 public:
  cadicalSolver() = default;
  ~cadicalSolver() = default;

  // TESTER FUNCTION
  const char* input_dimacs(const char* path, int& vars, int strict) {
    return read_dimacs(path, vars, strict);
  }
  bool theory_is_unsat() const { return status() == 20; }
  bool in_conflict(Lit l);
  lbool simplify(int rounds);
  //return false if assumps are inconsistent (i.e., cause a conflict)
  bool findImplications(const vector<Lit>& assumps, vector<Lit>& unitImps);
  //backtrack the solver to level 0 and run unit prop (useful to obtain
  //effects of propagation effects added unit clauses)
  bool unit_propagate();
  void addClause(const vector<Lit>& lts);
  void setPolarity(lbool pol, Var v);
  lbool modelValue(Lit p) const;
  lbool modelValue(Var x) const;
  lbool fixedValue(Var x);
  lbool fixedValue(Lit x);
  vector<Lit> getForced(int);
  int64_t getNPropagations() const { return n_propagations(); }
  int64_t getNDecisions() const { return n_decisions(); }
  int64_t getNConflicts() const { return n_conflicts(); }
  int64_t getNEliminated() const { return n_eliminated(); }
  int64_t getNSubstituted() const { return n_substituted(); }
  int64_t getNFixed() const { return fixed_lits.size(); }
  int64_t getNRedundant() const { return redundant(); }
  int64_t getNIrredundant() const { return irredundant(); }


  // if you want to force an update of which literals are fixed
  // most routines call this automatically.
  void updateFixed();

  // preprocessing freeze and or melt both polarities.
  void freezeLit(Lit l) { freeze(lit2cadi(l)); freeze(lit2cadi(~l)); }
  void thawLit(Lit l) { melt(lit2cadi(l)); melt(lit2cadi(~l)); }

  // get clauses of sat solver
  size_t getNclauses() const { return n_clauses(); }
  bool get_ith_clause(vector<Lit>& cls, size_t i) const;

  // output
  void print_options() { CaDiCaL::Solver::options(); }
  void print_resource_usage() { CaDiCaL::Solver::resources(); }
  void print_statistics() { CaDiCaL::Solver::statistics(); }
  bool set_option(const char* name, int val) {
    return CaDiCaL::Solver::set(name, val);
  }
  int get_option(const char* name) { return CaDiCaL::Solver::get(name); }

 private:
  friend class CaDiCaL::WitnessIterator;
  friend class Units_in_witnesses;

  lbool solve_(const vector<Lit>& assumps, vector<Lit>& conflict,
               int64_t confBudget, int64_t propagationBudget);
  vector<int8_t> v_in_s{};
  bool lit_in_solver(Lit l) const { return var_in_solver(var(l)); }
  bool var_in_solver(Var v) const {
    return (static_cast<size_t>(v) < v_in_s.size() && v_in_s[v]);
  }
  void mark_var_in_solver(Var v);
  void mark_lit_in_solver(Lit l) { mark_var_in_solver(var(l)); }
  size_t n_ifixed{};
  lbool internal_fixedValue(Var v) const;
  lbool internal_fixedValue(Lit l) const;
  vector<lbool> var_fixed_vals{};
  vector<Lit> fixed_lits{};
  int lit2cadi(Lit) const;
  Lit cadi2lit(int) const;
  int var2cadi(Var) const;
  Var cadi2var(int) const;
};

}  // namespace MaxHS_Iface

#endif
