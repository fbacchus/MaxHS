/***********[muser.cc]
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

#include "maxhs/ifaces/muser.h"
#include <algorithm>
#include <vector>
#include "maxhs/utils/Params.h"
#include "maxhs/utils/io.h"

#ifdef GLUCOSE
#include "glucose/utils/Options.h"
#else
#include "minisat/utils/Options.h"
#endif

using namespace MaxHS_Iface;

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

using namespace Minisat;

bool Muser::musBudget(vector<Lit>& conflict, int64_t propBudget) {
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
  if (val) succ_solves++;
  return val;
}

bool Muser::musBudget(vector<Lit>& conflict, double timeLimit) {
  prevTotalTime = totalTime;
  bool try_2nd_trial{satsolver->props_per_second_uncertain()};
  int64_t propagationBudget{satsolver->props_per_time_period(timeLimit)};
  if (params.mverbosity) {
    cout << "Muser 1. timelimit = " << timeLimit << " confBudget = -1 "
         << "propagationBudget = " << propagationBudget << '\n';
  }
  stime = cpuTime();
  auto val = mus_(conflict, propagationBudget);
  double solvetime = cpuTime() - stime;
  totalTime += solvetime;
  stime = -1;
  solves++;

  if (val)
    succ_solves++;
  else {
    if (try_2nd_trial && !val && solvetime < timeLimit * .60) {
      timeLimit -= solvetime;
      auto moreProps = satsolver->props_per_time_period(timeLimit);
      if (moreProps > propagationBudget * 0.5) {
        stime = cpuTime();
        val = mus_(conflict, moreProps);
        totalTime += cpuTime() - stime;
        stime = -1;
        solves++;
        if (val) succ_solves++;
        if (params.mverbosity) {
          cout << "Muser 2. timelimit = " << timeLimit << " confBudget = -1 "
               << "propagationBudget = " << moreProps << '\n';
        }
      }
    }
  }
  return val;
}

bool Muser::preProcessConflict(vector<Lit>& conflict) {
  // check for trivial conflicts and remove false literals from the conflict.
  // return true if conflict is already minimal.
  auto i = conflict.begin();
  for (auto lt : conflict) {
    auto val = satsolver->fixedValue(lt);
    if (val == l_Undef) {
      *i++ = lt;
    } else if (val == l_True) {
      conflict.empty();
      conflict.push_back(lt);
      return true;
    }
  }
  conflict.erase(i, conflict.end());
  return conflict.size() == 1;
}

bool Muser::mus_(vector<Lit>& conflict, int64_t propBudget) {
  // reduce conflict to a MUS, return true if we succeeded.
  // don't use more than propBudget props to do so.
  bool isMus{true};
  if (preProcessConflict(conflict)) return isMus;
  if (conflict.empty()) {
    cout << "c ERROR: MUSER found empty conflict\n";
    return !isMus;
  }
  assert(conflict.size() > 1);
  bool haveBudget{propBudget >= 0};
  int64_t perTestBudget{propBudget / 16};
  int64_t initialProps{satsolver->getNPropagations()};
  vector<Lit> assumptions{};
  vector<Lit> conf{};
  auto notInCon = [this](Lit l) { return !satsolver->in_conflict(l); };
  while (conflict.size() > 0) {
    if (params.mverbosity > 2)
      cout << "mus_ loop conflict = " << conflict << " assumptions "
           << assumptions << "\n";

    if (haveBudget && (satsolver->getNPropagations() - initialProps >=
                       propBudget)) {  // timed out
      if (params.mverbosity > 1) cout << "mus_ loop timed out\n";
      for (auto l : conflict)
        // act like all remaining conflict lits are critical and end loop
        assumptions.push_back(~l);
      conflict.clear();
      isMus = false;
    } else {
      // test next conflict literal for criticality
      Lit test = conflict.back();
      conflict.pop_back();
      // lits in assumptions are already known to be critical
      int ncrits = assumptions.size();
      for (size_t i = 0; i < conflict.size(); i++)
        assumptions.push_back(~conflict[i]);
      if (params.mverbosity > 2)
        cout << "mus_ loop assumptions = " << assumptions
             << " ncrits = " << ncrits << '\n';
      auto val = satsolver->solvePropBudget(assumptions, conf,
                                            haveBudget ? perTestBudget : -1);
      satSolves++;

      if (params.mverbosity > 1) {
        cout << "Conflict = " << conflict << "\n";
        cout << "Assumptions = " << assumptions << "\n";
        cout << "found conflict = " << conf << "\n";
        cout << "Prop budget for test " << perTestBudget << "\n";
        cout << "test = " << test << " val = " << val << "\n";
      }

      // restore assumptions to crits only
      assumptions.resize(ncrits);
      if (val == l_Undef) {            // this test timed out.
        assumptions.push_back(~test);  // assume test is critical.
        isMus = false;                 // don't know if we have a mus any more.
      } else if (val == l_False) {     // redundant
        auto p = std::remove_if(conflict.begin(), conflict.end(), notInCon);
        conflict.erase(p, conflict.end());
      } else {  // l_True:
        assumptions.push_back(~test);
        addMoreCrits(assumptions, conflict, haveBudget ? perTestBudget : -1);
      }
    }
  }
  assert(conflict.size() == 0);
  // convert assumptions back into a conflict.
  for (size_t i = 0; i < assumptions.size(); i++)
    conflict.push_back(~assumptions[i]);

  if (params.mverbosity > 1)
    cout << "mus_ returns conflict: " << conflict << " isMus = " << isMus
         << '\n';

  return isMus;
}

void Muser::addMoreCrits(vector<Lit>& assumptions, vector<Lit>& conflict,
                         int64_t propBudget) {
  if (conflict.size() <= 1) return;
  int critsFnd{0};
  // Insert removable most one constraint over conflicts to more criticals
  int aInitSize = assumptions.size();
  vector<Lit> clits = addAmoUnk(conflict);
  lbool critVal;
  vector<char> isCrit(conflict.size(), false);
  assumptions.push_back(~clits[0]);  // activate at-most-one

  vector<Lit> conf;
  int64_t initialProps{satsolver->getNPropagations()};
  bool haveBudget{propBudget >= 0};
  while ((critVal = satsolver->solvePropBudget(assumptions, conf,
                                               propBudget)) == l_True) {
    satSolves++;
    for (size_t j = 0; j < conflict.size(); j++) {
      if (satsolver->modelValue(conflict[j]) == l_True) {
        isCrit[j] = true;
        assumptions.push_back(~conflict[j]);
        break;
      }
    }
    if (haveBudget) {
      propBudget -= satsolver->getNPropagations() - initialProps;
      if (propBudget <= 0) break;
    }
  }
  satSolves++;
  //for (auto lt : clits) satsolver->addClause(lt);

  assumptions.resize(aInitSize);
  size_t j{0};  // move lits detected to be critical into assumptions
  for (size_t i = 0; i < conflict.size(); i++) {
    if (isCrit[i]) {
      critsFnd++;
      assumptions.push_back(~conflict[i]);
    } else
      conflict[j++] = conflict[i];
  }
  conflict.resize(j);
  if (critVal == l_False && conflict.size() > 0)
    // If we detected unsat even when any one of the remaining conflict lits
    // was allowed to be relaxed, then we can remove any one of these lits.
    conflict.pop_back();

  if (params.mverbosity > 1) cout << "addMoreCrits added " << critsFnd << "\n";
}

vector<Lit> Muser::addAmoUnk(vector<Lit>& unknowns) {
  // Add an at-most-one constraint to the solver.
  //  at most one unknown lit can be TRUE.
  // In:  unknowns.size() > 1
  // Out: clits[0] is the control lit that deletes all clauses
  //     clits[1]...are the other auxiliary variables
  //     added to encode the constraint.

  vector<Lit> clits;
  for (size_t i = 0; i < unknowns.size(); i++) {
    Var c = bvars.newCtrlVar();
    clits.push_back(mkLit(c, false));
  }

  vector<Lit> cls(3);
  for (size_t i = 0; i < unknowns.size() - 1; i++) {
    cls[0] = ~unknowns[i];  // unk_i --> clit_i+1
    cls[1] = clits[i + 1];  //~clit_i+1 >> ~unk_i
    cls[2] = clits[0];
    satsolver->addClause(cls);
  }

  for (size_t i = 1; i < clits.size() - 1; i++) {
    cls[0] = ~clits[i];     // clit_i --> clit_i+1
    cls[1] = clits[i + 1];  //~clit_i+1 --> ~clit_i
    cls[2] = clits[0];
    satsolver->addClause(cls);
  }

  for (size_t i = 1; i < clits.size(); i++) {
    cls[0] = ~clits[i];     // clit_i --> ~unk_i
    cls[1] = ~unknowns[i];  // unk_i --> ~clit_i
    cls[2] = clits[0];
    satsolver->addClause(cls);
  }
  return clits;
}
