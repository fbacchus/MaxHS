/***********[MaxSolver.h]
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

#ifndef MaxSolver_h
#define MaxSolver_h

#include <string>
#include <sstream>
#include <set>
#include <ext/hash_map>
#include "minisat/mtl/Heap.h"
#include "minisat/mtl/Alg.h"
#include "minisat/utils/Options.h"
#include "minisat/core/SolverTypes.h"
#include "maxhs/core/MaxSolverTypes.h"
#include "maxhs/ifaces/SatSolver.h"
#include "maxhs/ifaces/Cplex.h"
#include "maxhs/core/dlink.h"
#include "minisat/utils/System.h"

using namespace __gnu_cxx;
using namespace MaxHS_Iface;
using namespace Minisat;

namespace MaxHS { 

class MaxSolver {
public:
  MaxSolver(MaxHS_Iface::SatSolver* s);
  ~MaxSolver();

  MaxHS_Iface::SatSolver* satsolver;
  Cplex *cplex;

  Weight opt;
  Weight baseCost;
  Weight LB;
  Weight UB;
  vector<lbool> UBmodel;
  vector<Weight> bvar_weights; 
  vector<int> bvars;
  bool weighted;
  
  // Options
  int verbosity;
  int min_type;
  bool sort_min;
  bool delete_hard_learnts;
  bool disjoint_phase;
  bool disjoint_always;
  bool invertAct;
  bool resetLearnts;
  bool invertAct_rerefute;
  bool resetLearnts_rerefute;
  bool compare_assumps;
  int  nAssumpsShuffle;
  bool shuffleFirstTime;
  // Noncore Options
  bool noncore_constraints;
  bool seed_valued;
  bool seed_equiv;
  bool seed_implications;
  int  seed_reverse;
  bool seed_cores_only;
  bool seed_noncores_only;
  // Nonoptimal Options
  int nonoptimal;
  double nonopt_frac_to_relax;
  int nonopt_plateaus;
     
 
  // Statistics
  int amountConflictMin; 
  int totalConstraintSize;   // The total size of all constraints added to cplex
  int numConstraints;        // The number of constraints added to cplex
  int numPlateaus;           // The number of different LB values encountered. 
  double initialTime;
  double beginCplexTime;
  double beginSATtime;

  int numOrigVars;
  int numBVars;
  vector<vector<Lit> > origSoftClauses;
  vector<Weight> origSoftClsWeights;
  string inputFileName;
  // Noncore stuff
//  int numOrigClauses;
  int numHardClauses;
  int numOrigUnitSofts;
  int beginIndexOfBVarEquivClauses;
  int endIndexOfBVarEquivClauses;
  vector<vector<Lit> > equivClauses;
  hash_map<int, int> lit_equiv_bvar;

  /* For sorting the conflict before it is minimized
     Can't make all lits in conflict true. Neg bvars:
     must make one true == relax one of these
     soft clauses. So try to remove low weight neg bvars
     so that we must relax a high weight soft.
  
     Pos bvar: must make one false == can't relax
     one of these softs. So try to remove high weight pos
     bvars, so that we are blocked only from relaxing low 
     weight softs.

     Forcing relaxations is better than blocking.
     So try to remove all positives first.

     We remove from the end, so sort to put best removals at the end*/

  struct minConflictLt {
    const vector<Weight>& bweights;
    const int &offset; 
    bool operator () (Lit i, Lit j) const { 
      bool case1 = (sign(i) && !sign(j));
      bool case2 = sign(i) && sign(j) && (bweights[var(i)-offset] < bweights[var(j)-offset]); 
      bool case3 =  !sign(i) && !sign(j) && (bweights[var(i)-offset] > bweights[var(j)-offset]);
      return case1 || case2 || case3;  } 
    minConflictLt(const vector<Weight> &bw, const int &nv) : bweights(bw), offset(nv) { }
  };
  minConflictLt  minconflict_comp;

  struct minwtLt {
    const vector<Weight>& bweights;
    const int &offset; 
    bool operator () (Lit i, Lit j) const { 
      return bweights[var(i)-offset] < bweights[var(j)-offset]; }
    minwtLt(const vector<Weight> &bw, const int &nv) : bweights(bw), offset(nv) { }
  };
  minwtLt  minwt_comp;

  // Nonoptimal stuff
  bool nonopt_solveexactly;
  bool karp_do_greedy;
  bool wasOptimalSolution;
  double lastGreedyTime;
  int satCallsSinceCplex;
  int satCallsSinceGreedy;

  vector<int> bvarOccur;      // The number of *true* cores each bvar appears in
  struct BVarOccurLt {
    const vector<int> &bvaroccur;
    bool operator () (int x, int y) const { return bvaroccur[x] > bvaroccur[y]; }
    BVarOccurLt(const vector<int> &occ) : bvaroccur(occ) { }
  };
  Heap<int,BVarOccurLt> occ_heap;
  dlink_matrix *coresmatrix; 
  enum { nonopt_rand = 1, nonopt_maxoccur, nonopt_frac, nonopt_greedy, nonopt_karp, nonopt_cplex };

  // To sort b-variables so that negative ones come before the positive, and within each group they are sorted by var index 
  struct bvarNegFirstLt {
    bool operator () (Lit i, Lit j) const { return (sign(i) && !sign(j)) || ((sign(i) == sign(j)) && (var(i) < var(j))); } 
    bvarNegFirstLt() { }
  };
  bvarNegFirstLt  bvar_negfirst_comp;

  // Used by Dimacs.h during parsing of the input file
  void setNumOrigVars(int n) { numOrigVars = n; }
  void setHardWeight(Weight w) { if (w < UB) UB = w; }
  Weight getHardWeight() { return UB; }
  bool addClause(vector<Lit> &lits, Weight w);
   
  void setUBToHardClauseSolution();
  Weight getModelWt();
 
  void solve_maxsat(const char *inputfilename);

  // Called by the SAT solver to tell whether or not a learnt clause can be deleted
  bool deleteLearntTest(const Clause &c) const;
  bool addBVarConstraint(vector<Lit> &cls);
  void addBVarConstraint(Lit blit, vector<Lit> &impl);

  void printStatsAndExit(int signum, int exitType);
  void printOutput(const char *msg, Weight val);
  void printOutput(const char *msg, const char *val);
  void printErrorAndExit(const char *msg);
  void printComment(const char *msg);
  void printSolution(const vector<lbool> model);

protected:

  bool ok;    //If FALSE either LB>UB---supplied upper bound or Hards are UNSAT.
  void checkParams();    
  void printInputStats();
  bool relax(vector<int> &bvars, vector<Weight> &bvarcoeffs);
  bool disjointPhase(const vector<int> &bvars);
  void seqOfSAT_maxsat();
  // Noncore stuff
  void initBVarEquiv();
  void seed_valued_bvars(const vector<int> &bvars);
  void seed_equivalence();
  void seed_b_implications(const vector<int> &bvars, const vector<vector<Lit> > &b_impls);
  void seed_rev_implications(vector<vector<Lit> > &rev_impls);
  void advancedSeedCplex(vector<int> &bvars);
  // Nonoptimal stuff
  void approxBVarSolution(vector<Lit> &soln);
  void approxBVarSolution(vector<Lit> &soln, vector<Lit> &newestcore);
  void incrBVarOccurrences(vector<Lit> &core);
  Lit  maxOccurringInCore(vector<Lit> &core);
  void fracOfCore(vector<Lit> &core, double fracToReturn, vector<Lit> &maxoccur);

  void updateLB(vector<Lit> &assumps);
  void reportCplex(vector<Lit> &oldassumps, vector<vector<Lit> > &cplexsolns);
  void reportSAT(vector<Lit> &conflict);

  bool satsolve(vector<Lit> &inAssumps, vector<Lit> &outConflict);
  bool satsolve_min(vector<Lit> &inAssumps, vector<Lit> &outConflict);
  lbool satsolve_min_budget(vector<Lit> &inAssumps, vector<Lit> &outConflict, double timeLim);
  void minimize_rerefute(vector<Lit> &con);
  void minimize_greedy(vector<Lit> &con);
  bool testRemoval(const vector<Lit> &con, size_t indexToRemove);
    
  void outputConflict(const vector<Lit> &conf);

  bool isOrigLit  (Lit l) const;
  int  bvarIndex(Lit l) const;
  Lit  bvarIndexToLit(int i, bool sign) const;
  void finished();
  // Noncore stuff
  bool bvar_clause_and_check_core(int clsIndex, vector<Lit> &bvarcls);
  bool advanced_bvar_clause_and_check_core(int clsIndex, vector<Lit> &bvarcls, vector<vector<Lit> > &rev_impls);
  void build_b_implications(const vector<int> &bvars, vector<vector<Lit> > &b_impls);
  void build_rev_implications(vector<int> &bvars, vector<vector<Lit> > &b_impls, vector<vector<Lit> > &rev_impls);

  //TODO move this to a utilities module
  double elapTime(double stime) { return cpuTime() - stime; }
};

inline bool MaxSolver::isOrigLit(Lit l) const { return var(l) < numOrigVars; }
inline int MaxSolver::bvarIndex(Lit l) const { return var(l) - numOrigVars; }
inline Lit MaxSolver::bvarIndexToLit(int i, bool sign) const { return mkLit(i + numOrigVars, sign);  }

} //namespace

#endif
