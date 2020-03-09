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
   
   This also means however, that not all external variables will be given a value
   by a found sat model.
 
*/

#ifndef IFACESAT_H
#define IFACESAT_H

#include <vector>
#include <iostream> 
#include <memory>

#ifdef GLUCOSE
#include "glucose/core/SolverTypes.h"
#include "glucose/core/Solver.h"
#include "glucose/utils/System.h"
#else
#include "minisat/core/SolverTypes.h"
#include "minisat/core/Solver.h"
#include "minisat/utils/System.h"
#endif

#include "maxhs/utils/io.h"

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

using Minisat::Lit;
using Minisat::lbool;
using Minisat::Var;
using Minisat::l_Undef;
using Minisat::l_True;
using Minisat::l_False;
using Minisat::cpuTime;

using std::vector;
using std::cout;

namespace MaxHS {
  class MaxSolver;
}

namespace MaxHS_Iface {
  class SatSolver;
  typedef std::unique_ptr<SatSolver> SatSolver_uniqp;

  class SatSolver {
  public:
    SatSolver(): timer {0}, totalTime {0}, prevTotalTime {0}, stime{-1}, solves {0}, prevSolves{0} {}
    virtual ~SatSolver() {}

    virtual bool status() const = 0;
    //Return false if unsat already detected (solver is in inconsistent state)

    lbool solveBudget(const vector<Lit>& assumps, vector<Lit>& conflict,
                      int64_t confBudget, int64_t propBudget);
    // Solve with assumptions. Track statistics.
    // can set conflict and propagation budgets (-1 = no budget)
    //   Return l_true/l_false/l_Undef formula is sat/unsat/budget-exceeded

    //   If unsat put conflict clause into conflict (mapped to external numbering)
    //   if sat, the "modelValue" function allow access to satisfying assignment

    lbool solveBudget(const vector<Lit>& assumps, vector<Lit>& conflict, double timeLimit);
      //minisat's runtime is not very predictable. So if no complex solves have been done before
      //odds are the time taken will far from the timeLimit. 
      //The accuracy of the timeLimit gets better as more solves are executed.

    lbool solve(const vector<Lit>& assumps, vector<Lit>& conflict)
      { return  solveBudget(assumps, conflict, -1, -1); }
    
    lbool solve()
      { vector<Lit> tc; return solve(vector<Lit>{}, tc); }

    lbool solveBudget(double timeLimit)
      { vector<Lit> tc; return solveBudget(vector<Lit>{}, tc, timeLimit); }

    lbool solvePropBudget(int64_t propBudget)
      { vector<Lit> tc; return solveBudget(vector<Lit>{}, tc, -1, propBudget); }

    lbool solve(const vector<Lit> & assumps)
      { vector<Lit> tc; return solve(assumps, tc); }

    lbool solve(Lit l) 
      { vector<Lit> tc; return solve(vector<Lit> {l}, tc); }

    lbool relaxSolve(const vector<Lit>& assumps, const vector<Lit>& branchLits, double timeLimit);
      //Do relaxed solve (where sat solver must initially branch on branchLits

    virtual lbool relaxSolve_(const vector<Lit>& assumps, const vector<Lit>& branchLits,
                              int64_t propBudget) = 0;


    //preprocessing
    virtual void freezeVar(Var v) = 0;
    virtual bool eliminate(bool turn_off_elim) = 0;
    virtual int nEliminated() = 0;
    
    //simplify clauses according to detected forced literals.
    //return false if unsat already detected
    virtual bool simplify() = 0;
    
    //use unit prop to find literals implied by a conjunction of literals "assumps:
    //return false if assumps causes contradiction ---> ~assumps is forced

    virtual bool findImplications(const vector<Lit> &assumps, vector<Lit>& imps) = 0;
    virtual bool findImplications(const Lit p, vector<Lit>& imps) {
      vector<Lit> tmp {p}; return findImplications(tmp, imps); }

    virtual vector<Lit> getForced(int index) = 0; 

    //data from the solver
    virtual bool inSolver(Lit lt) const { return inSolver(var(lt)); } //the solver knows about these variables
    virtual bool inSolver(Var v) const = 0;
    virtual int nAssigns() const = 0; //# assigned variables
    virtual int nClauses() const = 0; //# original clauses
    virtual int nInVars() const = 0;    //# internal variables
    virtual size_t nVars() const = 0;   //# number of external variables known to the solver.
    virtual bool activeVar(Var v) const = 0; //Is this external variable active in the solver? 
                                             //inactive if never added, eliminated by preprocessing
                                             //or forced.


    //get upper bound on number of clauses in solver DB (some might be deleted or satisfied)
    int getNClauses(bool learnts) { return learnts ? get_learnts_size() : get_clauses_size(); }
    virtual int get_clauses_size() const = 0;
    virtual int get_learnts_size() const = 0;
    //get the ith clause from solvers DB (converted to external variables)
    //if the empty vector is returned then there is no ith clause (was deleted or satisfied)
    //or i is to large.
    vector<Lit> getIthClause(int ith, bool learnts) { 
      return learnts ? getIth_learnts(ith) :getIth_clauses(ith); }
    virtual vector<Lit> getIth_clauses(int ith) const = 0;
    virtual vector<Lit> getIth_learnts(int ith) const = 0;
    
    //Reduce a sequence of lits by values forced at decision level 0.
    //   ==> true if sequence has true or complimentary lits
    //   ==> false otherwise, but also reset lts to remove any falsified lits.
    //
    virtual bool reduceClause(vector<Lit>& lts) const = 0;
    
    //add clause to theory, return theory status
    virtual bool addClause(const vector<Lit>& lts) = 0;
    bool addClause(Lit p) { vector<Lit> tmp {p}; return(addClause(tmp)); }
    bool addClause(Lit p, Lit q) { vector<Lit> tmp {p,q}; return(addClause(tmp)); }

    //set polarity of variable (lbool b = l_True if we give it a sign---set to false)
    virtual void setPolarity(Var v, lbool b) = 0;

    //set Var as decision (variable should already be known to the solver, e.g., in added clause)
    virtual void setDecisionVar(Var v, bool b) = 0;

    //install variable b as a new control variables. b must not have been previously added
    //if decisionVar is false the solver won't branch on b, if polarity is set when the solver
    //does branch on b it will set its value to polarity (l_Undef lets the solver pick)
    virtual void newControlVar(Var b, bool decisionVar=true, lbool polarity=l_Undef) = 0;

    //free variable by setting l to TRUE, simplifying, and freeing var(l)
    //to be available for future use.
    virtual void freeVar(Lit l)  = 0;

    //get info from clause
    virtual void printLit(Lit l) const = 0;
    
    //Reverse heuristic ordering of variables
    virtual void invertVarActivities() = 0;
    
    //prune learnts 
    virtual void pruneLearnts() = 0;
    
    //obtain truth assignments of last model found by SAT solver.
    //The SAT solver will only set those variables it has been given, so
    //values for external variables the SAT solver does not know about 
    //will be l_Undef.
    virtual lbool modelValue(Lit p) const = 0;
    virtual lbool modelValue(Var x) const = 0;
    
    //get current truth values (only set if variable is forced)
    virtual lbool curVal(const Var x) const = 0;
    lbool curVal(const Lit p) const { return curVal(var(p)) ^ sign(p); }
    
    //stats
    //Use startTimer and elapTime to accumulate time over a set of SAT solver calls.
    //nSolves() counts number of calls since startTimer
    //solveTime for time of most recent call.
    void startTimer() { timer = totalTime; prevSolves = solves; }
    double elapTime() { return totalTime-timer; }
    double solveTime() { return totalTime-prevTotalTime; }
    double total_time() {
      if (stime >=0) {
        totalTime += cpuTime() - stime;
        stime = -1;
      }
      return totalTime;
    }
    int nSolvesSinceTimer() { return (int) solves-prevSolves; }
    int nSolves() { return (int) solves; }
	
    virtual uint64_t getProps() const  = 0;
    virtual uint64_t getConfs() const  = 0;
    
  protected:
    //interface to solver
    virtual lbool solve_(const vector<Lit>& assumps, vector<Lit>& conflict,
                         int64_t confBudget, int64_t propBudget) = 0;
    
    //stats
    double timer, totalTime, prevTotalTime, stime;
    int solves;
    int prevSolves;

  }; //Class SatSolver


} //namespace

#endif
