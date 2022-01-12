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

   This also means however, that not all external variables will be given a
   value by a found sat model.

*/

#include "maxhs/ifaces/SatSolver.h"
#include "maxhs/utils/Params.h"
#include "maxhs/utils/io.h"

namespace MaxHS_Iface {
lbool SatSolver::solveBudget(const vector<Lit>& assumps, vector<Lit>& conflict,
                             int64_t confBudget, int64_t propagationBudget) {
  /*******************************************************************
  Solve with assumptions. Track statistics.
  can set conflict and propagation budgets (-1 = no budget)
  Return l_true/l_false/l_Undef formula is sat/unsat/budget-exceeded

  If unsat put conflict clause into conflict (mapped to external numbering)
  if sat, the "modelValue" function allow access to satisfying assignment
   *******************************************************************/
  stime = cpuTime();
  prevTotalTime = totalTime;

  if(params.verbosity > 3) {
    cout << "SatSolver confBudget = " << confBudget << " propagationBudget " <<
      propagationBudget << "\n";
  }

  lbool val = solve_(assumps, conflict, confBudget, propagationBudget);
  totalTime += cpuTime() - stime;
  stime = -1;
  solves++;
  return val;
}

lbool SatSolver::solveBudget(const vector<Lit>& assumps, vector<Lit>& conflict,
                             double timeLimit) {
  // sat solver runtime is not very predictable. So if no complex solves have
  // been done before odds are the time taken will far from the timeLimit. The
  // accuracy of the timeLimit gets better as more solves are executed.
  prevTotalTime = totalTime;
  bool try_2nd_trial{props_per_second_uncertain()};
  int64_t propagationBudget{props_per_time_period(timeLimit)};
  if (params.verbosity > 2) {
    cout << "SatSolver 1. timelimit = " << time_fmt(timeLimit) << " confBudget = -1 "
         << "propagationBudget = " << propagationBudget << '\n';
  }
  stime = cpuTime();
  lbool val = solve_(assumps, conflict, -1, propagationBudget);
  auto solvetime = cpuTime() - stime;
  totalTime += solvetime;
  stime = -1;
  solves++;

  if (try_2nd_trial && val == l_Undef && solvetime < timeLimit * .6) {
    timeLimit -= solvetime;
    int64_t morePropagations = props_per_time_period(timeLimit);
    if (morePropagations > propagationBudget * 0.5) {
      stime = cpuTime();
      val = solve_(assumps, conflict, -1, morePropagations);
      totalTime += cpuTime() - stime;
      stime = -1;
      solves++;
      if (params.verbosity > 2) {
        cout << "SatSolver 2. timelimit = " << time_fmt(timeLimit) << " confBudget = -1"
             << " propagationBudget " << morePropagations << "\n";
      }
    }
  }
  return val;
}

}  // namespace MaxHS_Iface
