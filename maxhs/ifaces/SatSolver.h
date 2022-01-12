/***********[SatSolver.h]
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

/* Generic interface for maxhs to use a satsolver.
   Access to a particular sat solver is implemented by defining a
   derived class.

   The interface maintains a mapping between interally numbered
   variables and externally numbered variables.
   This is to ensure that the internal variables are consecutively ordered,
   so that the external theory can be fed to the sat solver in parts with
   generating huge gaps in the variable numbering.

   This also means however, that not all external variables will be given a
   value by a found sat model.

 */

#ifndef IFACESAT_H
#define IFACESAT_H

#include <algorithm>
#include <iostream>
#include <memory>
#include <vector>

#ifdef GLUCOSE
#include "glucose/core/SolverTypes.h"
#include "glucose/utils/System.h"
#else
#include "minisat/core/SolverTypes.h"
#include "minisat/utils/System.h"
#endif

#include "maxhs/utils/io.h"

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

using Minisat::cpuTime;
using Minisat::l_False;
using Minisat::l_True;
using Minisat::l_Undef;
using Minisat::lbool;
using Minisat::Lit;
using Minisat::mkLit;
using Minisat::Var;
using std::cout;
using std::vector;

namespace MaxHS {
class MaxSolver;
}

namespace MaxHS_Iface {

constexpr int64_t init_props_per_sec_guess{1024*1024*24};
class SatSolver {
 public:
  SatSolver() = default;
  virtual ~SatSolver() = default;
  // TESTER FUNCTION
  virtual const char* input_dimacs(const char* path, int& vars, int strict) = 0;

  // Return false if unsat already detected (solver is in inconsistent state)
  virtual bool theory_is_unsat() const = 0;

  // Solve with assumptions. Track statistics.
  // conflict and propagation budgets == -1 means no budget
  // Return l_true/l_false/l_Undef formula is sat/unsat/budget-exceeded
  //   If UNSAT put conflict clause into conflict (mapped to external numbering)
  //   if SAT, the "modelValue" function allow access to satisfying assignment
  lbool solveBudget(const vector<Lit>& assumps, vector<Lit>& conflict,
                    int64_t confBudget, int64_t propBudget);
  // satsolvers runtime is not very predictable. So if no complex solves have
  // been done before odds are the time taken will far from the timeLimit. The
  // accuracy of the timeLimit gets better as more solves are executed.
  lbool solveBudget(const vector<Lit>& assumps, vector<Lit>& conflict,
                    double timeLimit);
  lbool solve(const vector<Lit>& assumps, vector<Lit>& conflict) {
    return solveBudget(assumps, conflict, -1, -1);
  }
  lbool solve() {
    vector<Lit> tc;
    return solve(vector<Lit>{}, tc);
  }
  lbool solveBudget(double timeLimit) {
    vector<Lit> tc;
    return solveBudget(vector<Lit>{}, tc, timeLimit);
  }
  lbool solvePropBudget(int64_t pBudget) {
    vector<Lit> tc;
    return solveBudget(vector<Lit>{}, tc, -1, pBudget);
  }
  lbool solvePropBudget(const vector<Lit>& assumps, vector<Lit>& conflict,
                        int64_t pBudget) {
    return solveBudget(assumps, conflict, -1, pBudget);
  }
  lbool solve(const vector<Lit>& assumps) {
    vector<Lit> tc;
    return solve(assumps, tc);
  }
  lbool solve(Lit l) {
    vector<Lit> tc;
    return solve(vector<Lit>{l}, tc);
  }

  int64_t props_per_time_period(double period) {
    // try to estimate the number of props that would be done by the
    // solver in period seconds. (Used to convert time bounds to prop
    // bounds for the solver. If very few props or very little time has
    // been spent on solving return a guess.
    if(props_per_second_uncertain())
      return init_props_per_sec_guess * period;
    else
      return (getNPropagations() / totalTime) * period;
  }
  bool props_per_second_uncertain() {
    return getNPropagations() < init_props_per_sec_guess || totalTime < 1.0;
  }

  virtual bool in_conflict(Lit l) = 0;

  // Preprocessing
  virtual lbool simplify(int rounds) = 0;
  virtual void freezeLit(Lit l) = 0;
  void freezeVar(Var v) { freezeLit(mkLit(v)); }
  virtual void thawLit(Lit l) = 0;
  void thawVar(Var v) { thawLit(mkLit(v)); }

  // access to Unit prop
  // Root level unit prop (to propagate original unit clauses)
  virtual bool unit_propagate() = 0;

  // use unit prop to find literals implied by a conjunction of literals
  // "assumps: return false if assumps causes contradiction ---> ~assumps is
  // forced
  virtual bool findImplications(const vector<Lit>& assumps,
                                vector<Lit>& imps) = 0;
  bool findImplications(Lit p, vector<Lit>& unitImps) {
    vector<Lit> tmp{p};
    return findImplications(tmp, unitImps);
  }
  bool findImplications(Lit p, Lit q, vector<Lit>& unitImps) {
    vector<Lit> tmp{p, q};
    return findImplications(tmp, unitImps);
  }

  // add clause to theory, return theory status
  virtual void addClause(const vector<Lit>& lts) = 0;
  void addClause(Lit p) {
    vector<Lit> tmp{p};
    addClause(tmp);
  }
  void addClause(Lit p, Lit q) {
    vector<Lit> tmp{p, q};
    addClause(tmp);
  }

  // set default polarity of variable during decisions
  // lbool b = l_Undef == unset polarity.
  //         = l_True || l_False ---set variable true or false
  virtual void setPolarity(lbool b, Var v) = 0;

  // obtain truth assignments of last model found by SAT solver.
  // The SAT solver will only set those variables it has been given, so
  // values for external variables the SAT solver does not know about
  // will be l_Undef.
  virtual lbool modelValue(Lit p) const = 0;
  virtual lbool modelValue(Var x) const = 0;

  // true if literal is fixed (return l_Undef if variable is not
  // forced)
  virtual lbool fixedValue(Var x) = 0;
  virtual lbool fixedValue(Lit p) = 0;
  virtual vector<Lit> getForced(int) = 0;
  virtual void updateFixed() = 0;

  // get clauses of sat solver
  virtual size_t getNclauses() const = 0; 
  virtual bool get_ith_clause(vector<Lit>& cls, size_t i) const = 0;


  // output and options
  virtual void print_options() = 0;
  virtual void print_resource_usage() = 0;
  virtual void print_statistics() = 0;
  virtual bool set_option(const char* name, int val) = 0;
  virtual int get_option(const char* name) = 0;

  // get stats about solver and mus usage.
  // Use startTimer and elapTime to accumulate time over a set of SAT solver
  // calls. nSolves() counts number of calls since startTimer solveTime for time
  // of most recent call.
  void startTimer() {
    timer = totalTime;
    prevSolves = solves;
  }
  double elapTime() { return totalTime - timer; }
  double solveTime() { return totalTime - prevTotalTime; }
  double total_time() {
    if (stime >= 0) {
      //handle cass where interrupt happens in middle of sat solve
      totalTime += cpuTime() - stime;
      stime = -1;
    }
    return totalTime;
  }
  int nSolvesSinceTimer() { return (int)solves - prevSolves; }
  int nSolves() { return solves; }

  virtual int64_t getNPropagations() const = 0;
  virtual int64_t getNDecisions() const = 0;
  virtual int64_t getNConflicts() const = 0;
  virtual int64_t getNEliminated() const = 0;
  virtual int64_t getNSubstituted() const = 0;
  virtual int64_t getNFixed() const = 0;
  virtual int64_t getNRedundant() const = 0;
  virtual int64_t getNIrredundant() const = 0;

 protected:
  // interface to solver
  virtual lbool solve_(const vector<Lit>& assumps, vector<Lit>& conflict,
                       int64_t confBudget, int64_t propBudget) = 0;
  // stats
  double timer{}, totalTime{}, prevTotalTime{}, stime{-1};
  int solves{}, prevSolves{};
};  // Class SatSolver

typedef std::unique_ptr<SatSolver> SatSolver_uniqp;

}  // namespace MaxHS_Iface

#endif
