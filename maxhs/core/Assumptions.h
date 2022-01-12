/***********[Assumptions.h]
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

#ifndef ASSUMPTIONS_h
#define ASSUMPTIONS_h

#include <algorithm>
#include <vector>

#include "maxhs/core/MaxSolverTypes.h"
#include "maxhs/ifaces/SatSolver.h"

class Bvars;
class SumManager;

namespace MaxHS_Iface {
class Cplex;
class SatSolver;
}  // namespace MaxHS_Iface

using std::vector;

class Assumps {
  // MaxSolver helper class
 public:
  Assumps(MaxHS_Iface::SatSolver* s, Bvars& b, SumManager* t);
  // initialize assumptions to make all softs true, or set of passed softs
  void init(vector<Minisat::Lit> lits);
  void all_softs_true();
  void permute();

  // update requires that lits in conflict currently appear negated in
  // assumptions Warns this is not the case.
  // exclude ensures these variables corresponding to these lits are
  // not part of assumption
  void exclude(const vector<Minisat::Lit>& ex);
  void update(const vector<Minisat::Lit>& conflict, bool remove);
  const vector<Minisat::Lit>& vec() const { return assumps; }
  template <class Compare>
  void sort(Compare comp) {
    std::sort(assumps.begin(), assumps.end(), comp);
    setMap();
  }
  friend std::ostream& operator<<(std::ostream& os, const Assumps& a);

 private:
  MaxHS_Iface::SatSolver* satsolver;
  Bvars& bvars;
  SumManager* summations;
  vector<Minisat::Lit> assumps;
  vector<int> map;
  vector<int> sum_index;
  vector<int> counts;
  vector<int> coeff;
  void flip(const vector<Minisat::Lit>& conflict);
  void remove(const vector<Minisat::Lit>& conflict);

  void clearIndex(Minisat::Lit l);
  int getIndex(Minisat::Lit l);
  bool removeUndefs();
  void setMap();
  void printMap();
  bool checkUpdate(Minisat::Lit l);
  void printAssumps();
};

inline std::ostream& operator<<(std::ostream& os, const Assumps& a) {
  os << "Assumps" << a.assumps;
  return os;
}

#endif
