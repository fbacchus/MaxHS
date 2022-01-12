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
#include "glucose/core/SolverTypes.h"
#include "glucose/utils/System.h"
#else
#include "minisat/core/SolverTypes.h"
#include "minisat/utils/System.h"
#endif

#include "maxhs/core/Bvars.h"
#include "maxhs/ifaces/SatSolver.h"
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
using Minisat::Var;
using Minisat::vec;

using std::cout;
using std::vector;

namespace MaxHS_Iface {

class Muser {
 public:
  Muser(SatSolver* satslv, Bvars& b) : satsolver{satslv}, bvars{b} {};

  bool musBudget(vector<Lit>& conflict, int64_t propBudget);
  /* Try to minimize conflict using a sat solver budget of up to propBudget
     propagations in total. */
  bool mus(vector<Lit>& conflict) {
    return musBudget(conflict, static_cast<int64_t>(-1));
  }
  bool musBudget(vector<Lit>& conflict, double timeLimit);

  // stats
  // Use startTimer and elapTime to accumulate time over a set of muser calls.
  // nSolves() counts number of calls since startTimer
  // solveTime for time of most recent call.
  void startTimer() {
    timer = totalTime;
    prevSolves = solves;
    prevSatSolves = satSolves;
  }
  double elapTime() { return totalTime - timer; }
  double solveTime() { return totalTime - prevTotalTime; }
  double total_time() {
    if (stime >= 0) {
      totalTime += cpuTime() - stime;
      stime = -1;
    }
    return totalTime;
  }
  int nSolvesSinceTimer() { return (int)solves - prevSolves; }
  int nSolves() { return (int)solves; }
  int nSucc_Solves() { return (int)succ_solves; }
  int nSatSolvesSinceTimer() { return (int)satSolves - prevSatSolves; }
  int nSatSolves() { return (int)satSolves; }

 protected:
  SatSolver* satsolver;
  Bvars& bvars;

  // Stats.
  double timer{}, totalTime{}, prevTotalTime{}, stime{-1};
  int solves{}, succ_solves{}, prevSolves{}, satSolves{}, prevSatSolves{};

  //

  // computation routines
  bool mus_(vector<Lit>& conflict, int64_t propBudget);
  vector<Lit> addAmoUnk(vector<Lit>& unknowns);
  void addMoreCrits(vector<Lit>& assumptions, vector<Lit>& conflict, int64_t propBudget);
  bool preProcessConflict(vector<Lit>& conflict);
};  // Class Muser

}  // namespace MaxHS_Iface
#endif
