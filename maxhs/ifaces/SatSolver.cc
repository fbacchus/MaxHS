/***********[SatSolver.cc]
 Copyright (c) 2012-2018 Jessica Davies, Fahiem Bacchus

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

#include "maxhs/ifaces/SatSolver.h"

namespace MaxHS_Iface {
    lbool SatSolver::solveBudget(const vector<Lit>& assumps, vector<Lit>& conflict,
                                 int64_t confBudget, int64_t propBudget) {
        /*******************************************************************
     Solve with assumptions. Track statistics.
     can set conflict and propagation budgets (-1 = no budget)
     Return l_true/l_false/l_Undef formula is sat/unsat/budget-exceeded

     If unsat put conflict clause into conflict (mapped to external numbering)
     if sat, the "modelValue" function allow access to satisfying assignment
        *******************************************************************/
      stime = cpuTime();
      prevTotalTime = totalTime;
      lbool val = solve_(assumps, conflict, confBudget, propBudget);
      totalTime += cpuTime() - stime;
      stime = -1;
      solves++;
      return val;
    }

    lbool SatSolver::solveBudget(const vector<Lit>& assumps, vector<Lit>& conflict, double timeLimit)  {
      //minisat's runtime is not very predictable. So if no complex solves have been done before
      //odds are the time taken will far from the timeLimit.
      //The accuracy of the timeLimit gets better as more solves are executed.
      int64_t propBudget, props;
      props = getProps(); //returns total number of props done by solver
      bool didTrial {false};

      if(solves > 0 && props > 0) {
        propBudget = props/totalTime * timeLimit;
      }
      else {
        propBudget = 1024*1024*10;
        didTrial = true;
      }
      stime = cpuTime();
      prevTotalTime = totalTime;
      lbool val = solve_(assumps, conflict, -1, propBudget);
      solves++;
      double solvetime1 = cpuTime() - stime;
      if(didTrial && val == l_Undef && solvetime1 < timeLimit*.60) {
        auto moreProps = int64_t((getProps()-props)/solvetime1 * timeLimit - propBudget);
        if (moreProps > propBudget*0.5) {
          val =  solve_(assumps, conflict, -1, moreProps);
        }
        solves++;
      }
      totalTime += cpuTime() - stime;
      stime = -1;
      return val;
    }

    lbool SatSolver::relaxSolve(const vector<Lit>& assumps, const vector<Lit>& branchLits, double timeLimit) {
        //Do relaxed solve (where sat solver must initially branch on branchLits
      int64_t propBudget, props;
      if(timeLimit <= 0)
        propBudget = -1;
      else {
        props = getProps(); //returns total number of props done by solver
        if(solves > 0 && props > 0)
          propBudget = props/totalTime * timeLimit;
        else
          propBudget = 1024*1024*10;
      }
      stime = cpuTime();
      prevTotalTime = totalTime;
      auto val = relaxSolve_(assumps, branchLits, propBudget);
      solves++;
      totalTime += cpuTime() - stime;
      stime = -1;
      return val;
    }
} //namespace
