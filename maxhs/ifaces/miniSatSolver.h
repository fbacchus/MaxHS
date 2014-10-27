/***********[miniSatSolver.h]
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

/* minisat interface
*/

#ifndef MINISATSOLVER_H
#define MINISATSOLVER_H

#include "minisat/core/Solver.h"
#include "maxhs/ifaces/SatSolver.h"

using namespace Minisat;
namespace MaxHS_Iface {

//Minisat Solver
class miniSolver : public SatSolver, protected Minisat::Solver {
public:
  miniSolver();
  virtual ~miniSolver();
  bool status() const;
  lbool solve_(const vector<Lit>& assumps, vector<Lit>& conflict,
			   int64_t confBudget, int64_t propBudget);
  lbool solve_(const vector<Lit>& assumps, 
			   int64_t confBudget, int64_t propBudget);
  LSet& getConflict();
  bool simplify();
  bool findUnitImps(const Lit p, vector<Lit>& unitImps);
  int nAssigns();
  int nClauses();
  int nVars();
  bool reduceClause(vector<Lit>& lts);
  void addVars(const vector<Lit>& lts);
  bool addClause(const vector<Lit> lts);
  int clsSize(const int clsIndex) const;
  Lit clsLit(const int clsIndex, const int litIndex) const;
  void printLit(const Lit l) const;
  void invertVarActivities();
  void pruneLearnts(MaxHS::MaxSolver *S);
  vector<lbool> model();
  lbool modelValue(Lit p) const;
  lbool modelValue(Var x) const;
  vector<lbool> curVals();
  lbool curVal(Var x);
  uint64_t getProps() const { return propagations; }
  uint64_t getConfs() const { return conflicts; }
  



protected:
  void cancelTrail(const int level, vector<Lit> &bt_lits);
};

}
#endif 
