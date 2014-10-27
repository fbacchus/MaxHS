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
#include <vector>

using std::vector;

#include "minisat/core/SolverTypes.h"
#include "maxhs/core/MaxSolverTypes.h"
#include "maxhs/ifaces/SatSolver.h"
#include "maxhs/ifaces/muser.h"
#include "maxhs/ifaces/Cplex.h"
#include "maxhs/core/Wcnf.h"
#include "maxhs/core/Bvars.h"
#include "maxhs/utils/Params.h"
#include "maxhs/core/Assumptions.h"
#include "maxhs/ds/Packed.h"

using namespace MaxHS_Iface;
using namespace Minisat;

namespace MaxHS { 

class MaxSolver {
public:
  MaxSolver(Wcnf *f);
  ~MaxSolver();
  void solve_maxsat();  //Solve the initialized Wcnf
  Weight UB() { return theWcnf->totalWt() - sat_wt; }
  Weight LB() { return lower_bnd; }
  bool isSolved() { return solved; }
  bool isUnsat() { return unsat; }
  const vector<lbool>& getBestModel() { return UBmodel; }
  const Wcnf* getWcnf() { return theWcnf; }
  
  //Not private but not for general users.
  //Used by interrupt trap
  void printStatsAndExit(int signum, int exitType);
  // Called by the SAT solver to tell whether or not a learnt clause
  // can be deleted
  bool deleteLearntTest(const vector<Lit>& c) const;
  Bvars bvars;

protected:
  Wcnf* theWcnf;
  SatSolver* satsolver;
  SatSolver* greedysolver;
  Muser* muser;
  Cplex* cplex;
  //BOUNDS
  Weight sat_wt;     //wt of soft clauses known to be satisfiable.
  Weight lower_bnd;  //lower bound on wt false soft clauses.
  lbool  hards_are_sat; //
  void updateLB(Weight wt) { if (wt > lower_bnd) lower_bnd = wt; }
  Weight updateUB();
  Weight getForcedWt(int trail_index = 0);
  Weight getSatClsWt();
  Weight getWtOfBvars(const vector<Lit>& blits);

  vector<lbool> UBmodel;
  void setUBModel();

  //SAT solver interaction
  void addHards(SatSolver*);
  void addHards(SatSolver*, const vector<int>& indicies);

  //include b-var in softs. Boolean flag true
  //means sat solver is allowed to use the b-vars
  //as decisions.
  void addSofts(SatSolver*, bool b_var_decision); 
  void addSofts(SatSolver*, bool b_var_decision, const vector<int>& indicies);

  //add and remove b-var equivalent clauses
  //must call rmSoftEqs before every addSoftEqs except for first call.
  Var eqCvar; //control variable for b-var equivalences.
  void addSoftEqs(SatSolver*, bool removable); 
  void addSoftEqs(SatSolver*, bool removable, const vector<int>& indicies);
  void rmSoftEqs(SatSolver* slv) {
    //assert eqCvar and thus remove all eq clauses after 
    //a call to simplify
    slv->freeVar(mkLit(eqCvar, false));
  }
  Lit activateSoftEqLit() { 
    //return assumption that activates the soft equivalent clauses 
    return mkLit(eqCvar, true); } 

  //set up var--> satisfied softs map.
  void initSftSatisfied();

  //turn off b vars as decisions.
  void setNoBvarDecisions();

  int nextNewVar; //for adding additional variables beyond the b-vars
		  //+ original vars + eqCvar to the maxsat theory.;
  
  int getNextNewVar() { return nextNewVar++; }

  // Statistics
  int amountConflictMin; 

  //Manage Cplex and Greedy solver Clauses.
  vector<int> bLitOccur; 
  Packed_vecs<Lit> cplexClauses;
  Packed_vecs<int> sftSatisfied; //map from ordinary var --> satisfied sft clauses

  //TODO better abstraction to transfer unit clauses (or other clauses)
  //     between solvers
  void greedyAddNewForcedBvars();
  void cplexAddNewForcedBvars();
  void satSolverAddNewForcedVars();
  void muserAddNewForcedVars();
  //If using fb (no eq clauses) force negated b-vars from satisfied softs.
  void satSolverAddBvarsFromSofts();

  
  void cplexAddNewClauses();
  bool cplexAddCls(const vector<Lit>& cls);
  void storeCplexCls(const vector<Lit>& cls);

  //output routines
  void printErrorAndExit(const char *msg);
  void printSolution(const vector<lbool>& model);
  void printCurClause(const vector<Lit> &cls);
  void reportCplex(Weight solnWt);
  void reportSAT_min(lbool result, double iTime, size_t orig_size, int nMins, double mTime, size_t final_size);
  void reportForced(vector<Lit> &forced, Weight wt);
  void outputConflict(const vector<Lit> &conf);
  void optFound(std::string reason);
  void unsatFound();

  //status flags
  bool solved;   //True when finished solving.
  bool unsat;    //Hards are UNSAT or no solution of cost < dimacs top

  //internal Subroutines
  void disjointPhase();
  void seqOfSAT_maxsat();
  void feedCplex(int gIter, Assumps& a, int nSoFar, size_t sizeSoFar);

  // Noncore stuff
  void seed_equivalence();
  vector<Lit> getBvarEqs();
  bool isCore(const vector<Lit>& core);

  // Accumulate Cores 
  vector<Lit> getAssumpUpdates(int sinceCplex, int sinceGreedy, vector<Lit>& core);
  vector<Lit> greedySoln();
  vector<Lit> fracOfCore(int nCplex, int nGreedy, vector<Lit> &core);
  Lit maxOccurring(const vector<Lit>& core);
  void incrBLitOccurrences(const vector<Lit> &core);
  lbool satsolve_min(const Assumps &inAssumps, vector<Lit> &outConflict, double sat_cpu_lim, double mus_cpu_lim);
  void minimize_muser(vector<Lit> &con, double mus_cpu_lim);
  void check_mus(vector<Lit> &con);
};

} //namespace

#endif
