/***********[muser.h]
Copyright (c) 2012-2014 Jessica Davies, Fahiem Bacchus

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

/* muser---compute a mus for maxhs.
  TODO?: The timer/budget interface is idential to Satsolver
         The internal to external mapping is identical to minisatsolver
         Don't want to inherit from these classes as the functionality 
	 for muser is quite different. Potentially these functions could 
	 be abstracted so that they can be shared. 
*/

#ifndef MUSER_H
#define MUSER_H

#include <ostream>
#include <string>
#ifdef GLUCOSE
#include "glucose/simp/SimpSolver.h"
#include "glucose/core/SolverTypes.h"
#else
#include "minisat/simp/SimpSolver.h"
#include "minisat/core/SolverTypes.h"
#endif
#include "maxhs/core/Wcnf.h"
#include "maxhs/core/Bvars.h"

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
using Minisat::vec;

using std::vector;

namespace MaxHS_Iface {

class Muser : protected Minisat::SimpSolver {
public:
  Muser(const Wcnf* f, Bvars& b);
  virtual ~Muser() {}
  
  bool musBudget(vector<Lit>& conflict, int64_t propBudget) {
    /*******************************************************************
     Reduce a conflict (a set of blits) to a MUS. Try to remove
     elements of conflict in the order given (try removing conflict[0]
     before conflict[1] etc.). So if there is a priority for
     reductions pass a sorted conflict vector. 

     Set total propagation budget for computing the MUS.  (-1 = no budget).

     Return reduced conflict vector. Return true if the returned
     vector is a MUS, false if only a partial reduction was done.
    *******************************************************************/
    stime = cpuTime();
    prevTotalTime = totalTime;
    auto val = mus_(conflict, propBudget);
    totalTime += cpuTime() - stime;
    stime = -1;
    solves++;
    if(val)
      succ_solves++;
    return val; 
  }
  
  bool musBudget(vector<Lit>& conflict, double timeLimit)  {
    int64_t propBudget, props;
    props = getProps(); //returns total number of props done by solver
    bool didTrial {false};

    if(props > 0 && totalTime > 0)
      propBudget = props/totalTime * timeLimit;
    else {
      propBudget = 1024*1024*10;
      didTrial = true;
    }

    stime = cpuTime();
    prevTotalTime = totalTime; 
    auto val = mus_(conflict, propBudget);
    solves++;
    if(val) 
      succ_solves++;
    else {
      double solvetime1 = cpuTime() - stime;
      if(didTrial && !val && solvetime1 < timeLimit*.60) {
	auto moreProps = int64_t((getProps()-props)/solvetime1 * timeLimit - propBudget);
	if (moreProps > propBudget*0.5) {
	  //try again 
	  val =  mus_(conflict, moreProps);
	  solves++;
	  if(val) 
	    succ_solves++;
	}
      }
    }
    totalTime += cpuTime() - stime;
    stime = -1;
    return val; 
  }
  
  bool mus(vector<Lit>& conflict)
    { return  musBudget(conflict, static_cast<int64_t>(-1)); }

  vector<Lit> getForced(int index);
  void updateForced(vector<Lit>& frc);
  bool addClause(const vector<Lit>& lts);
  lbool curVal(Var x) const;
  lbool curVal(Lit x) const;

  
  //stats
  //Use startTimer and elapTime to accumulate time over a set of muser calls.
  //nSolves() counts number of calls since startTimer
  //solveTime for time of most recent call.
  void startTimer() { timer = totalTime; prevSolves = solves; prevSatSolves = satSolves; }
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
  int nSucc_Solves() { return (int) succ_solves; }
  int nSatSolvesSinceTimer() { return (int) satSolves - prevSatSolves; }
  int nSatSolves() { return (int) satSolves; }
  
 protected:
  const Wcnf* theWcnf;
  Bvars& bvars;

  vector<Lit> forced;

  //Stats. 
  double timer, totalTime, prevTotalTime, stime;
  double m_timer, m_stime, m_prevTotalTime, m_totalTime;
  
  int solves, succ_solves, prevSolves, satSolves, prevSatSolves;

  //External to internal variable mapping.
  vector<Var>in2ex_map;
  vector<Var>ex2in_map;
  void ensure_mapping(Var ex);
  void ensure_mapping(Lit lt) {
    ensure_mapping(var(lt));
  }
  Lit in2ex(Lit lt) const;
  Var in2ex(Var v) const;
  
  //In most applications every internal literal of the SatSolver
  //is associated with an external literal on creation.
  //So this array function is safe...i.e., won't add var_Undef to output
  //vector. An array version of ex2in is typically not safe in this way
  //so is not provided.
    
  void in2ex(const vec<Lit> &from, vector<Lit> &to) const;
  void in2ex(const vec<Var> &from, vector<Var> &to) const;

  Var ex2in(Var v) const;
  Lit ex2in(Lit lt) const;

  //computation routines
  bool doPreprocessing() const;
  bool inSolver(Lit lt) const;
  bool inSolver(Var v) const;
  bool mus_(vector<Lit>& conflict, int64_t propBudget);
  void ensureSoftCls(vector<Lit>& conflict);
  void ensureSoftCls(Lit lt);
  uint64_t getProps() const { return propagations; }
  vector<Lit> addAmoUnk(vector<Lit>& unknowns);
  void addMoreCrits(vector<Lit>& conflict, int64_t propBudget);
  void preProcessConflict(vector<Lit>& conflict);
  //void analyzeFinal(Lit p, Minisat::LSet& out_conflict);
  void setPropBudget(bool haveBudget, int64_t propBudget) {
    propagation_budget = haveBudget ? propBudget + propagations : -1;
  }
}; //Class Muser
  
} //namesspace
#endif 
