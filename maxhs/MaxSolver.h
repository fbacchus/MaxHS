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
#include "minisat/mtl/Vec.h"
#include "minisat/mtl/Heap.h"
#include "minisat/mtl/Alg.h"
#include "minisat/utils/Options.h"
#include "minisat/core/SolverTypes.h"

#ifndef Minisat_Solver_h 
#include "minisat/core/Solver.h"
#endif

#ifndef CPLEX_H
#include "maxhs/Cplex.h"
#endif

#ifndef DLINK_H
#include "maxhs/dlink.h"
#endif

using namespace __gnu_cxx;

namespace Minisat { 

class MaxSolver {
public:

    Solver satsolver;
    Cplex *cplex;

    Weight opt;
    Weight baseCost;
    Weight LB;
    Weight UB;
    vec<lbool> UBmodel;
    vector<Weight> bvar_weights; 
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
    hash_map<int, Weight> unitSofts;
    vector<vector<Lit> > origSoftClauses;
    vector<Weight> origSoftClsWeights;
    string inputFileName;
    // Noncore stuff
    int numOrigClauses;
    int numHardClauses;
    int numOrigUnitSofts;
    int beginIndexOfBVarEquivClauses;
    int endIndexOfBVarEquivClauses;
    vector<vector<Lit> > equivClauses;
    hash_map<int, int> lit_equiv_bvar;

    // For sorting the conflict before it is minimized
    struct minConflictLt {
        const vector<Weight>& bweights;
        const int &offset; 
        bool operator () (Lit i, Lit j) const { 
            bool case1 = (!sign(i) && sign(j));
            bool case2 = sign(i) && sign(j) && (bweights[var(i)-offset] > bweights[var(j)-offset]); 
            bool case3 =  !sign(i) && !sign(j) && (bweights[var(i)-offset] < bweights[var(j)-offset]);
            return case1 || case2 || case3;  } 
        minConflictLt(const vector<Weight> &bw, const int &nv) : bweights(bw), offset(nv) { }
    };
    minConflictLt  minconflict_comp;

    // Nonoptimal stuff
    bool nonopt_solveexactly;
    bool karp_do_greedy;
    bool wasOptimalSolution;
    vec<int> bvarOccur;      // The number of *true* cores each bvar appears in
    struct BVarOccurLt {
        const vec<int> &bvaroccur;
        bool operator () (int x, int y) const { return bvaroccur[x] > bvaroccur[y]; }
        BVarOccurLt(const vec<int> &occ) : bvaroccur(occ) { }
    };
    Heap<BVarOccurLt> occ_heap;
    dlink_matrix *coresmatrix; 
    enum { nonopt_rand = 1, nonopt_maxoccur, nonopt_frac, nonopt_greedy, nonopt_karp, nonopt_cplex };

    // To sort b-variables so that negative ones come before the positive, and within each group they are sorted by var index 
    struct bvarNegFirstLt {
        bool operator () (Lit i, Lit j) const { return (sign(i) && !sign(j)) || ((sign(i) == sign(j)) && (var(i) < var(j))); } 
        bvarNegFirstLt() { }
    };
    bvarNegFirstLt  bvar_negfirst_comp;

public:

    MaxSolver();
    ~MaxSolver();

    // Used by Dimacs.h during parsing of the input file
    void setNumOrigVars(int n) { numOrigVars = n; }
    void setHardWeight(Weight w) { if (w < UB) UB = w; }
    Weight getHardWeight() { return UB; }
    bool addClause(vec<Lit> &lits, Weight w);
   
    void setUBToHardClauseSolution();
 
    void solve_maxsat(const char *inputfilename);

    // Called by the SAT solver to tell whether or not a learnt clause can be deleted
    bool deleteLearnt(Clause &c) const;
    bool addBVarConstraint(vec<Lit> &cls);
    void addBVarConstraint(Lit blit, vec<Lit> &impl);

    void printStatsAndExit(int signum, int exitType);
    void printOutput(const char *msg, Weight val);
    void printOutput(const char *msg, const char *val);
    void printErrorAndExit(const char *msg);
    void printComment(const char *msg);
    void printSolution(vec<lbool> &model);
//private:

    void checkParams();    
    void printInputStats();
    bool relax(vector<int> &bvars, vector<Weight> &bvarcoeffs);
    bool disjointPhase(vector<int> &bvars);
    void seqOfSAT_maxsat();
    // Noncore stuff
    void initBVarEquiv();
    void seed_valued_bvars(vector<int> &bvars);
    void seed_equivalence();
    void seed_b_implications(vector<int> &bvars, vector<vector<Lit> > &b_impls);
    void seed_rev_implications(vector<vector<Lit> > &rev_impls);
    void advancedSeedCplex(vector<int> &bvars);
    // Nonoptimal stuff
    void approxBVarSolution(vector<Lit> &soln);
    void approxBVarSolution(vector<Lit> &soln, vec<Lit> &newestcore);
    void incrBVarOccurrences(vec<Lit> &core);
    Lit  maxOccurringInCore(vec<Lit> &core);
    void fracOfCore(vec<Lit> &core, double fracToReturn, vector<Lit> &maxoccur);

    void updateLB(vector<Lit> &assumps);
    void reportCplex(vector<Lit> &oldassumps, vector<vector<Lit> > &cplexsolns);
    void reportSAT(vec<Lit> &conflict);

    bool satsolve(vector<Lit> &inAssumps, vec<Lit> &outConflict);
    bool satsolve_min(vector<Lit> &inAssumps, vec<Lit> &outConflict);
    void minimize_rerefute(vec<Lit> &con);
    void minimize_greedy(vec<Lit> &con);
    bool testRemoval(vec<Lit> &con, int indexToRemove);
    
    void outputConflict(vector<Lit> &conf);
    void outputConflict(vec<Lit> &con);

    bool isOrigLit  (Lit l) const;
    int  bvarIndex(Lit l) const;
    Lit  bvarIndexToLit(int i, bool sign) const;
    void addUnit(vec<Lit> &p, Weight w);
    void finished();
    // Noncore stuff
    bool bvar_clause_and_check_core(int clsIndex, vec<Lit> &bvarcls);
    bool advanced_bvar_clause_and_check_core(int clsIndex, vec<Lit> &bvarcls, vector<vector<Lit> > &rev_impls);
    void build_b_implications(vector<int> &bvars, vector<vector<Lit> > &b_impls);
    void build_rev_implications(vector<int> &bvars, vector<vector<Lit> > &b_impls, vector<vector<Lit> > &rev_impls);

};

inline bool MaxSolver::isOrigLit(Lit l) const { return var(l) < numOrigVars; }
inline int MaxSolver::bvarIndex(Lit l) const { return var(l) - numOrigVars; }
inline Lit MaxSolver::bvarIndexToLit(int i, bool sign) const { return mkLit(i + numOrigVars, sign);  }

} // namespace Minisat
#endif
