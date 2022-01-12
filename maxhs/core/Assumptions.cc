/***********[Assumptions.cc]
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
#include "maxhs/core/Assumptions.h"
#include "maxhs/core/Bvars.h"
#include "maxhs/core/SumManager.h"
#include "maxhs/utils/Params.h"

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

using Minisat::l_False;
using Minisat::l_True;
using Minisat::l_Undef;
using Minisat::lbool;
using Minisat::Lit;
using Minisat::lit_Undef;
using Minisat::var;

Assumps::Assumps(MaxHS_Iface::SatSolver* s, Bvars& b, SumManager* t)
    : satsolver{s}, bvars(b), summations{t}, map(bvars.n_vars(), -1) {}

void Assumps::init(vector<Lit> lits) {
  // initialize assumptions with set of b-lits. coreType determines
  // what kind of conflicts we are looking for. If looking for cores,
  // add only noncore vars (conflict will be negation == core), etc.
  assumps = std::move(lits);
  if (params.verbosity > 1)
    cout << "c Init assumptions with " << assumps.size() << " lits\n";
  // cout << "size of assumps: " << assumps.size() << "\n";
  // printAssumps();
  setMap();
  // printMap();
}

void Assumps::all_softs_true() {
  // harden all softs not yet forced.
  assumps.clear();
  for (size_t i = 0; i < bvars.n_bvars(); i++)
    if (satsolver->fixedValue(bvars.varOfCls(i)) == l_Undef)
      assumps.push_back(~bvars.litOfCls(i));
  setMap();
}

void Assumps::permute() {
  std::random_shuffle(assumps.begin(), assumps.end());
  setMap();
}

void Assumps::exclude(const vector<Lit>& ex) {
  // Unlike update exclude removes the lits without regard for its polarity.
  for (auto l : ex)
    if (getIndex(l) >= 0) assumps[getIndex(l)] = lit_Undef;
  removeUndefs();
  setMap();
}

void Assumps::update(const vector<Lit>& conflict, bool rm) {
  // Update assumptions with set of literals in conflict. Flip
  // flip the assumptions--if using Fb or remove the assumptions if
  // using Fbeq
  if (rm)
    remove(conflict);
  else
    flip(conflict);
}

void Assumps::flip(const vector<Lit>& conflict) {
  // conflict variables must be in assumps. Update assumptions to agree
  // with conflict.
  for (auto l : conflict) {
    if (checkUpdate(l)) {
      if (assumps[getIndex(l)] == l)
        cout << "c WARNING conflict agrees with assumption---no real update in "
                "flip assumptions\n";
      assumps[getIndex(l)] = l;
    }
  }
}

void Assumps::remove(const vector<Lit>& conflict) {
  // conflict variables must be in assumps.
  // perserve order of assumps.
  if (params.abstract_assumps == 0) {
    for (auto l : conflict)
      if (checkUpdate(l)) assumps[getIndex(l)] = lit_Undef;
  } else if (params.abstract_assumps == 1) {
    for (auto l : conflict)
      if (checkUpdate(l)) {
        assumps[getIndex(l)] = lit_Undef;
        if (summations->isSoutput(l)) {
          Lit ln = summations->getNextOLit(l);
          if (ln != lit_Undef)
            assumps.push_back(~ln);  // lit_Undef cannot be negated!
        }
      }
  } else if (params.abstract_assumps == 2) {
    bool sum_relaxed{false};
    for (auto l : conflict)
      if (checkUpdate(l)) {
        if (bvars.isBvar(l))
          assumps[getIndex(l)] = lit_Undef;
        else if (summations->isSoutput(l) && !sum_relaxed) {
          assumps[getIndex(l)] = lit_Undef;
          Lit ln = summations->getNextOLit(l);
          if (ln != lit_Undef) assumps.push_back(~ln);
          sum_relaxed = true;
        }
      }
  }
  removeUndefs();
  setMap();
}

void Assumps::clearIndex(Lit l) {
  assert(var(l) < static_cast<int>(map.size()));
  map[var(l)] = -1;
}

int Assumps::getIndex(Lit l) {
  assert(var(l) < static_cast<int>(map.size()));
  return map[var(l)];
}

bool Assumps::removeUndefs() {
  auto isUndef = [](Lit l) { return l == lit_Undef; };
  auto p = std::remove_if(assumps.begin(), assumps.end(), isUndef);
  if (p != assumps.end()) {
    assumps.erase(p, assumps.end());
    return true;
  }
  return false;
}

void Assumps::setMap() {
  std::fill(map.begin(), map.end(), -1);
  for (size_t i = 0; i < assumps.size(); i++) {
    if (static_cast<size_t>(var(assumps[i])) >= map.size())
      map.resize(var(assumps[i]) + 1, -1);
    map[var(assumps[i])] = i;
  }
}

void Assumps::printMap() {
  for (size_t i = 0; i < map.size(); i++)
    std::cout << "a map[" << i << "] = " << map[i] << "\n";
}

bool Assumps::checkUpdate(Lit l) {
  if (getIndex(l) < 0) {
    cout << "c ERROR tried to update literal not in assumptions: " << l
         << " to int: " << toInt(l) << "\n";
    if (summations->isSoutput(l))
      cout << "c ERROR " << l << " is summations output\n";
    return false;
  }
  return true;
}

void Assumps::printAssumps() { cout << "c assumps:\n" << assumps << "\n"; }
