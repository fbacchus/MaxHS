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
   
   Note, design using virtual functions to interact in even simple ways with 
   the sat solver is only viable if maxhs only calls the satsolver a few
   thousand times. 
*/

#ifndef IFACESAT_H
#define IFACESAT_H

#include <vector>
#include "minisat/core/SolverTypes.h"
#include "minisat/utils/System.h"

using namespace Minisat;
using namespace std;

namespace MaxHS {
  class MaxSolver;
}

namespace MaxHS_Iface {
class SatSolver {
public:
  SatSolver() : totalTime {0}, solves {0} {}
  virtual ~SatSolver() {}

  virtual bool status() const = 0;
  //if false if unsat already detected (solver is in inconsistent state)

  //solve under assumptions---track CPU time and number of calls.
  //Give conflict and propagation budgets (-1 = no budget)
  //return l_true/l_false/l_Undef formula is sat/unsat/budget-exceeded
  //If unsat conflict is set.
  //if sat use model and modelValue functions to get satisfying assignment
  lbool solveBudget(const vector<Lit>& assumps, vector<Lit>& conflict,
			   int64_t confBudget, int64_t propBudget) {
    /*******************************************************************
     Solve with assumptions. Track statistics.
     can set conflict and propagation budgets (-1 = no budget)
     Return l_true/l_false/l_Undef formula is sat/unsat/budget-exceeded
     
     If unsat put conflict clause into conflict (mapped to external numbering)
     if sat, the "modelValue" function allow access to satisfying assignment
     *******************************************************************/
    double stime = cpuTime();
    lbool val = solve_(assumps, conflict, confBudget, propBudget);
    totalTime += cpuTime() - stime;
    solves++;
    return val; 
  }
  
  lbool solveBudget(const vector<Lit>& assumps,
			   int64_t confBudget, int64_t propBudget)
    { double stime = cpuTime();
      lbool val = solve_(assumps, confBudget, propBudget);
      totalTime += cpuTime() - stime;
      solves++;
      return val; }


  lbool solveBudget(const vector<Lit>& assumps, vector<Lit>& conflict, double timeLimit)  {
    int64_t propBudget, props;
    props = getProps();
    if(props > 0 && totalTime > 0)
      propBudget = props/totalTime * timeLimit;
    else
      propBudget = 1024*128;
    
    double stime = cpuTime();
    lbool val = solve_(assumps, conflict, -1, propBudget);
    if(props == 0 && val == l_Undef && totalTime > 0 && (getProps()*timeLimit)/totalTime > 1024*128) {
      //if we couldn't compute a propBudget from past experience,
      //try again with a properly computed propBudget---if we will do more work this time
      val =  solve_(assumps, conflict, -1, (int64_t) (getProps()*timeLimit)/totalTime);
      solves++;
    }
    totalTime += cpuTime() - stime;
    solves++;
    return val; 
  }

  lbool solveBudget(const vector<Lit>& assumps, double timeLimit)  {
    int64_t propBudget, props;
    props = getProps();
    if(props > 0 && totalTime > 0)
      propBudget = props/totalTime * timeLimit;
    else
      propBudget = 1024*128;
    
    double stime = cpuTime();
    lbool val = solve_(assumps, -1, propBudget);
    if(props == 0 && val == l_Undef && totalTime > 0 && (getProps()*timeLimit)/totalTime > 1024*128) {
      //if we couldn't compute a propBudget from past experience,
      //try again with a properly computed propBudget---if we will do more work this time
      val =  solve_(assumps, -1, (int64_t) (getProps()*timeLimit)/totalTime);
      solves++;
    }
    totalTime += cpuTime() - stime;
    solves++;
    return val; 
  }

  bool solve(const vector<Lit>& assumps, vector<Lit>& conflict)  {
    return  solveBudget(assumps, conflict, -1, -1) == l_True; 
  }

  bool solve(const vector<Lit>& assumps)
    { return  solveBudget(assumps, -1, -1) == l_True; }

  //actual interface to sat solver.
  virtual lbool solve_(const vector<Lit>& assumps, vector<Lit>& conflict,
			   int64_t confBudget, int64_t propBudget) = 0;
  //access conflict directly
  virtual lbool solve_(const vector<Lit>& assumps, 
			   int64_t confBudget, int64_t propBudget) = 0;

  virtual LSet& getConflict() = 0;
  
  //simplify clauses according to detected forced literals.
  //return false if unsat already detected
  virtual bool simplify() = 0;

  //use unit prop to find implied literals of 'p'
  //return false if p causes contradiction ---> ~p is forced
  virtual bool findUnitImps(const Lit p, vector<Lit>& unitImps) = 0;

  //data from the solver
  virtual int nAssigns() = 0; //# assigned variables
  virtual int nClauses() = 0; //# original clauses
  virtual int nVars() = 0;    //# variables

//Reduce a sequence of lits by values forced at decision level 0.
//   ==> true if sequence has true or complimentary lits
//   ==> false otherwise, but also reset lts to remove any falsified lits. 
//
  virtual bool reduceClause(vector<Lit>& lts) = 0;

//Define a variable in solver for every lit. 
  virtual void addVars(const vector<Lit>& lts) = 0;
  void addVar(Lit p) { vector<Lit> tmp (1, p); addVars(tmp); }

//add clause to theory, return theory status
  virtual bool addClause(vector<Lit> lts) = 0;
  bool addClause(Lit p) { vector<Lit> tmp = {p}; return(addClause(tmp)); }

//get info from clause
  virtual int clsSize(const int clsIndex) const = 0;
  virtual Lit clsLit(const int clsIndex, const int litindex) const = 0;
  virtual void printLit(const Lit l) const = 0;

//Reverse heuristic ordering of variables
  virtual void invertVarActivities() = 0;

//prune learnts
  virtual void pruneLearnts(MaxHS::MaxSolver *S) = 0;

//obtain last model (get full model if you need to get many)
  virtual vector<lbool> model() = 0;
  virtual lbool modelValue(Lit p) const = 0; 
  virtual lbool modelValue(Var x) const = 0; 
  
//get current truth values (get all values if you need to get many)
  virtual vector<lbool> curVals() = 0;
  virtual lbool curVal(Var x) = 0;
  lbool curVal(Lit p) { return curVal(var(p)) ^ sign(p); }

//stats
  double totalTime;
  uint64_t solves;
  virtual uint64_t getProps() const  = 0;
  virtual uint64_t getConfs() const  = 0;

//utilities 
  template<typename T>
  void vector2vec(const vector<T> &from, vec<T> &to)
    {
      to.clear();
      for(size_t i = 0; i < from.size(); i++) to.push(from[i]);
    }

  template<typename T>
  void vec2vector(const vec<T> &from, vector<T> &to)
    {
      to.clear();
      for(int i = 0; i < from.size(); i++) to.push_back(from[i]);
    }

}; //Class SatSolver

} //namespace

#endif 
