/***********[Wcnf.h]
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

#ifndef WCNF_H
#define WCNF_H

#include <string>
#include <vector>
#include <limits>
#include <iostream>
#include "maxhs/ds/Packed.h"
#include "maxhs/core/MaxSolverTypes.h"
#include "minisat/core/SolverTypes.h"
#include "maxhs/ifaces/miniSatSolver.h"


using std::cout;
using Minisat::Lit;
using Minisat::toInt;
using Minisat::var;
using Minisat::l_Undef;
using Minisat::lbool;
using MaxHS_Iface::miniSolver;

/* Store a weighted CNF formula */
enum class MStype { undef, ms, pms, wms, wpms };

class Bvars; //Bvars.h loads this header.

class Wcnf
{
public:
  Wcnf();  
  bool inputDimacs(std::string filename) {
    return inputDimacs(filename, false);
  }

  //input clauses
  void addDimacsClause(vector<Lit> &lits, Weight w); //Changes input vector lits
  void set_dimacs_params(int nvars, int nclauses, Weight top = std::numeric_limits<Weight>::max());
  double parseTime() const { return parsing_time; }
  Weight dimacsTop() const { return dimacs_top; }

  //api-support for adding hard or soft clauses
  void addHardClause(vector<Lit> &lits);
  void addSoftClause(vector<Lit> &lits, Weight w);

  void addHardClause(Lit p) { vector<Lit> tmp {p}; addHardClause(tmp); }
  void addSoftClause(Lit p, Weight w) { vector<Lit> tmp {p}; addSoftClause(tmp, w); }

  //modify Wcnf. This might add new variables. But all variables
  //in the range 0--dimacs_nvars-1 are preserved. New variables
  //only exist above that range.
  //TODO: for incremental solving we need a map from external to internal
  //      variables so that new clauses with new variables can be
  //      added on top of any added new variables arising from transformations
  
  void simplify();

  //print info
  void printFormulaStats();
  void printSimplificationStats();
  void printFormula(std::ostream& out = std::cout) const;
  void printFormula(Bvars&, std::ostream& out = std::cout) const;

  //data setters and getters mainly for solver
  void rewriteModelToInput(vector<lbool>& ubmodel); //convert model to model of input formula

  //  check model against input formula. Use fresh copy of input formula!
  //  checkmodelfinal delete current data structures to get space for input formula.
  //  This makes the WCNF unusable so only use if the program is about to exit
  Weight checkModel(vector<lbool>& ubmodel, int& nfalseSofts) {
    return checkModel(ubmodel, nfalseSofts, false); }
  Weight checkModelFinal(vector<lbool>& ubmodel, int& nfalseSofts) {
    return checkModel(ubmodel, nfalseSofts, true); }
  Weight checkModel(vector<lbool>&, int&, bool);
  
  const Packed_vecs<Lit>& hards() const { return hard_cls; }
  const Packed_vecs<Lit>& softs() const { return soft_cls; }
  const vector<Weight>& softWts() const { return soft_clswts; }
  vector<Lit> getSoft(int i) const { return soft_cls.getVec(i); }
  vector<Lit> getHard(int i) const { return hard_cls.getVec(i); }

  Weight getWt(int i) const { return soft_clswts[i]; }
  size_t softSize(int i) const { return soft_cls.ithSize(i); }
  size_t hardSize(int i) const { return hard_cls.ithSize(i); }

  Weight totalWt() const { return baseCost() + totalClsWt(); }
  Weight totalClsWt() const { return total_cls_wt; }
  Weight baseCost() const { return base_cost; }

  //info about wcnf
  size_t nHards() const { return hard_cls.size(); }
  size_t nSofts() const { return soft_cls.size(); }
  int nVars() const { return maxvar+1; }      //including extra variables added via transformations
  Var maxVar() const { return maxvar; }          //Users should regard this as being the number of vars

  Weight minSftWt() const { return wt_min; }
  Weight maxSftWt() const { return wt_max; }
  int nDiffWts() const { return diffWts.size(); }
  const vector<Weight>& getDiffWts() { return diffWts; }

  MStype mstype() const { return ms_type; }
  Weight aveSftWt() const { return wt_mean; }
  Weight varSftWt() const { return wt_var; }

  bool isUnsat() { return unsat; }
  const std::string& fileName() const { return instance_file_name; }

  //mutexes...each mutex is a set of literals x such that either x or
  //   -x is a unit soft clause. If x is a unit soft then the mutex is
  //   a non-core Mutex (at most one of these soft clauses can be
  //   satisfied. If -x is a unit soft then the mutex is a core mutex.

  const vector<vector<Lit>>& getMxs() { return mutexes; }
//  const vector<Var>& getMxDvars() { return mutexDvars; }

private:
  bool inputDimacs(std::string filename, bool verify); 
  void computeStats();

  //preprocessing routines
  void subEqs();
  void remDupCls();
  void rmUnits();
  void mxBvars();
  vector<vector<Lit>> mxFinder(Bvars&);
  void processMxs(vector<vector<Lit>>, Bvars&);
  void addSoftClauseZeroWt(Lit p); //special for internal processing only

  Var maxOrigVar() const { return maxorigvar; }     //input variables
  size_t nOrigVars() const { return maxorigvar+1; } //are for private use.

  Packed_vecs<Lit> reduceClauses(Packed_vecs<Lit>& cls, miniSolver& slv, bool softs);
  int maxorigvar, maxvar;
  int dimacs_nvars;
  int dimacs_nclauses;
  MStype ms_type;
  double parsing_time;
  Weight total_cls_wt; //Weight of soft clauses after simplifications.
  Weight base_cost;
  Weight dimacs_top;  //weight of a hard clause...typically sum of soft clause weights + 1
  Weight wt_var, wt_mean, wt_min, wt_max;
  std::string instance_file_name;
  bool unsat;
  bool noDups;
  int nhard_units;
  vector<Weight> diffWts;
  vector<lbool> tvals;
  vector<Lit> eqLit;
  void eqLitResize(int nVars);
  Lit eqRoot(Lit l) { 
    Lit x = l;
    while(eqLit[toInt(x)] != x) 
      x = eqLit[toInt(x)];
    eqLit[toInt(l)] = x; //make another eqRoot(l) call more efficient
    return x;
  }
  Packed_vecs<Lit> hard_cls;
  Packed_vecs<Lit> soft_cls;
  vector<Weight> soft_clswts;
  bool prepareClause(vector<Lit> & lits);

  struct ClsData {
    uint32_t index;
    uint32_t hash;
    Weight w; //weight < 1 ==> hard. weight == 0 redundant
    bool origHard;
    ClsData(uint32_t i, uint32_t h, Weight wt, bool oh) : index {i}, hash {h}, w {wt}, origHard{oh} {}
  };
  
  void initClsData(vector<ClsData>& cdata);
  bool eqVecs(const ClsData& a, const ClsData& b);

  //mutexes
  vector<vector<Lit>> mutexes;
//  vector<Var> mutexDvars;
};

#endif
