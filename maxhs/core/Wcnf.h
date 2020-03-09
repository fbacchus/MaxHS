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

#ifdef GLUCOSE
#include "glucose/core/SolverTypes.h"
#else
#include "minisat/core/SolverTypes.h"
#endif

#include "maxhs/ds/Packed.h"
#include "maxhs/core/MaxSolverTypes.h"
#include "maxhs/ifaces/miniSatSolver.h"

using std::cout;

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif


using Minisat::Lit;
using Minisat::toInt;
using Minisat::var;
using Minisat::l_Undef;
using Minisat::lbool;
using MaxHS_Iface::SatSolver_uniqp;

/* Store a weighted CNF formula */
enum class MStype { undef, ms, pms, wms, wpms };

class Bvars; //Bvars.h loads this header.

class SC_mx {
  /* The blits are such that if they are made
     true the correesponding soft clause is
     relaxed. Thus we incur the cost of
     the soft clause.
  */
public:
    SC_mx(vector<Lit> blits, bool is_core, Lit dlit)
      : _blits { blits},
        _dlit { dlit },
        _is_core { is_core }
    {}
    //if is_core then
    //  at most one of the blits can be true (at most one of the
    //  corresponding soft clauses can be falsified)
    //  and if dlit is true one of the blits is true.

    //if !is_core then
    //  at most one of the blits can be false (at most one of the
    //  corresponding soft clauses can be satisfied)
    //  and if dlit is false then one of the blits is false.

    const vector<Lit>& soft_clause_lits() const { return _blits; }
    bool is_core() const { return _is_core; }
    Lit encoding_lit() const { return _dlit; }

private:
    vector<Lit> _blits;
    Lit _dlit;
    bool _is_core;
};

inline ostream& operator<<(ostream& os, const SC_mx& mx) {
  os << (mx.is_core() ? "Core Mx: " : "Non-Core-Mx: ")
     << "Defining Lit = " << mx.encoding_lit()
     << " blits = " << mx.soft_clause_lits();
  return os;
}

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
  int dimacsNvars() const { return dimacs_nvars; }

  //api-support for adding hard or soft clauses
  void addHardClause(vector<Lit> &lits);
  void addSoftClause(vector<Lit> &lits, Weight w);
  void addHardClause(Lit p) { vector<Lit> tmp {p}; addHardClause(tmp); }
  void addHardClause(Lit p, Lit q) { vector<Lit> tmp {p, q}; addHardClause(tmp); }
  void addSoftClause(Lit p, Weight w) { vector<Lit> tmp {p}; addSoftClause(tmp, w); }
  void addSoftClause(Lit p, Lit q, Weight w) { vector<Lit> tmp {p, q}; addSoftClause(tmp, w); }

  //modify Wcnf. This might add new variables. But all variables
  //in the range 0--dimacs_nvars-1 are preserved. New variables
  //only exist above that range.
  //TODO: for incremental solving we need a map from external to internal
  //      variables so that new clauses with new variables can be
  //      added on top of any added new variables arising from transformations
  
  void simplify();

  //print info
  void printFormulaStats();
  void printSimpStats();
  void printFormula(std::ostream& out = std::cout) const;
  void printFormula(Bvars&, std::ostream& out = std::cout) const;
  void printDimacs(std::ostream& out = std::cout) const;

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
  const vector<int>& getDiffWtCounts() { return diffWtCounts; }
  const vector<Weight>& getTransitionWts() { return transitionWts; }

  MStype mstype() const { return ms_type; }
  Weight aveSftWt() const { return wt_mean; }
  Weight varSftWt() const { return wt_var; }

  bool isUnsat() { return unsat; }
  bool integerWts() { return intWts; }
  const std::string& fileName() const { return instance_file_name; }

  //mutexes
  const vector<SC_mx>& get_SCMxs() const { return mutexes; }
  int n_mxes() const { return mutexes.size(); }
  const SC_mx& get_ith_mx(int i) const {return mutexes[i]; }
  int ith_mx_size(int i) const {return mutexes[i].soft_clause_lits().size(); }

private:
  bool inputDimacs(std::string filename, bool verify); 
  void update_maxorigvar(vector<Lit>& lits);
  bool prepareClause(vector<Lit> & lits);
  void _addHardClause(vector<Lit>& lits);
  void _addHardClause(Lit p) { vector<Lit> tmp {p}; _addHardClause(tmp); }
  void _addHardClause(Lit p, Lit q) { vector<Lit> tmp {p, q}; _addHardClause(tmp); }
  void _addSoftClause(vector<Lit>& lits, Weight w);
  void _addSoftClause(Lit p, Weight w) { vector<Lit> tmp {p}; _addSoftClause(tmp, w); }
  void _addSoftClause(Lit p, Lit q, Weight w) { vector<Lit> tmp {p, q}; _addSoftClause(tmp, w); }
  void computeWtInfo();

  //preprocessing routines
  bool subEqs();
  vector<Lit> get_binaries(SatSolver_uniqp& sat_solver);
  vector<Lit> get_units();
  Packed_vecs<Lit> reduce_by_eqs_and_units(Packed_vecs<Lit>& cls, bool softs, 
                                           vector<vector<Lit>>& sccs, vector<Lit> units);
  vector<vector<Lit>> binary_scc(vector<vector<Lit>>& edges);
  void remDupCls();
  void simpleHarden();
  void rmUnits();
  void mxBvars();
  vector<vector<Lit>> mxFinder(Bvars&);
  void processMxs(vector<vector<Lit>>, Bvars&);
  Var maxOrigVar() const { return maxorigvar; }     //input variables
  size_t nOrigVars() const { return maxorigvar+1; } //are for private use.

  Packed_vecs<Lit> reduce_by_units(Packed_vecs<Lit>& cls, SatSolver_uniqp& slv, bool softs);
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
  bool intWts; 
  int nhard_units;
  vector<Weight> diffWts;
  vector<int> diffWtCounts;
  vector<Weight> transitionWts; //weights w s.t. sum of soft clauses with weight less that w is less than w
  Packed_vecs<Lit> hard_cls;
  Packed_vecs<Lit> soft_cls;
  vector<Weight> soft_clswts;

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
  vector<SC_mx> mutexes;
};

#endif
