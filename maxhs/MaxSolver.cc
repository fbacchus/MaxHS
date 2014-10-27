/***********[MaxSolver.cc]
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

#include <math.h>
#include <iostream> // JD
#include <iomanip>
#include <algorithm>
#include <zlib.h>
#include "minisat/utils/ParseUtils.h"
#include "minisat/core/Dimacs.h"
#ifndef MaxSolver_h
#include "maxhs/MaxSolver.h"
#endif

#include "minisat/mtl/Sort.h"

// JD for cpuTime()
#include "minisat/utils/System.h"

using namespace Minisat;


static const char* category_seq = "Sequence of SAT";
static IntOption     opt_mintype            (category_seq, "mintype", "JD: 0 = no minimization of constraints/cores,  1 = re-refutation, 2 = find minimal constraint/core, 3 = re-refute and then find minimal", 3);
static BoolOption    opt_sortmin (category_seq, "sortmin", "JD: Used with -mintype=2 or -mintype=3. Try removing the b-variables with largest weights first when minimizing the conflicts.", false);

static IntOption     verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
static BoolOption    opt_delete_hard_learnts (category_seq, "del-hard-learnts", "JD: Delete the hard learnt clauses when resetLearnts is called", true);
static BoolOption    opt_disjoint (category_seq, "disjoint", "JD: Find disjoint cores in a first phase.", true);
static BoolOption    opt_disjointalways (category_seq, "disjoint-always", "JD: For each CPLEX solution, find a set of disjoint constraints it violates.", false);

static BoolOption    opt_invert   (category_seq, "invert", "JD: Invert var activities between refutations.", true);
static BoolOption    opt_reset    (category_seq, "reset", "JD: Delete all learnt clauses between refutations.", true);
static BoolOption    opt_invert_reref   (category_seq, "invert-reref", "JD: Invert var activities between re-refutations.", true);
static BoolOption    opt_reset_reref    (category_seq, "reset-reref", "JD: Delete all learnt clauses between re-refutations.", true);

static BoolOption    opt_compareassumps    (category_seq, "diff-assumps", "JD: Compare the solution returned by CPLEX to the previous one and report the number of differences.", false);
static IntOption     opt_nshuffle (category_seq, "nshuffle", "JD: The number of times to randomly shuffle the assumptions and then find another refutation.", 0, IntRange(1, INT32_MAX));
static BoolOption    opt_shufflefirst    (category_seq, "shuffle-first", "JD: Shuffle the assumptions the first time (i.e. if false, use the assumptions in the order returned by CPLEX the first time)", false);

// Noncore and Seeding Options
static BoolOption    opt_noncore            (category_seq, "noncore", "JD: Learn non-core constraints and add them to the CPLEX model", false);
static BoolOption    opt_seedvalued         (category_seq, "valued-seed", "JD: Seed CPLEX with any valued b-literals", true);
static BoolOption    opt_equivseed          (category_seq, "equiv-seed", "JD: Use Equivalence Seeding", true);
static BoolOption    opt_implseed           (category_seq, "impl-seed", "JD: Use Implication Seeding", false);
static BoolOption    opt_revseed            (category_seq, "rev-seed", "JD: Use Reverse Seeding", false);
static BoolOption    opt_seedcoresonly     (category_seq, "sd-cores-only", "JD: Only seed the constraints that are cores (must use -equiv-seed and/or -rev-seed)", false);
static BoolOption    opt_seednoncoresonly     (category_seq, "sd-noncores-only", "JD: Only seed the constraints that are non-cores (must use -equiv-seed and/or -rev-seed)", false);

// Nonopt Options
static IntOption    opt_nonopt     (category_seq, "nonopt", "JD: Use non-optimal solutions to the current b-var constraints when possible (0 = always solve exactly, 1 = random clause from core, 2 = the clause with max occurrences so far, 3 = relax a fraction of each core, 4 = calculate the greedy approximation to the min hitting set, 5 = mixture of 2 and 4 (max occurring clause, then greedy), 6 = CPLEX feasible solution", 5, IntRange(0,6));
static DoubleOption  opt_relaxfrac  (category_seq, "relaxfrac", "JD: Choose this percentage of the newest core, favouring the bvars that appear most frequently, in order to augment the non-optimal hitting set (must use -nonopt=3).", 0, DoubleRange(0, true, 1.0, true));
static IntOption    opt_nonopt_plat (category_seq, "nonopt-plat", "JD: Use non-optimal solutions only when the LB plateaus for more than this number of iterations (must use -nonopt > 0)", 0, IntRange(0, INT32_MAX));


MaxSolver::MaxSolver() :
    satsolver(this)
  , cplex(NULL)
  , opt(-1)
  , baseCost(0)
  , LB(0)
  , UB(INT64_MAX)
  , weighted(false)
  , verbosity(verb)
  , min_type(opt_mintype)
  , sort_min(opt_sortmin)
  , delete_hard_learnts(opt_delete_hard_learnts)
  , disjoint_phase    (opt_disjoint)
  , disjoint_always   (opt_disjointalways)
  , invertAct         (opt_invert)
  , resetLearnts      (opt_reset)
  , invertAct_rerefute (opt_invert_reref)
  , resetLearnts_rerefute (opt_reset_reref)
  , compare_assumps   (opt_compareassumps)
  , nAssumpsShuffle   (opt_nshuffle)
  , shuffleFirstTime  (opt_shufflefirst)
  , noncore_constraints (opt_noncore)
  , seed_valued       (opt_seedvalued)
  , seed_equiv        (opt_equivseed)
  , seed_implications (opt_implseed)
  , seed_reverse      (opt_revseed)
  , seed_cores_only   (opt_seedcoresonly)
  , seed_noncores_only (opt_seednoncoresonly)
  , nonoptimal        (opt_nonopt)
  , nonopt_frac_to_relax  (opt_relaxfrac)
  , nonopt_plateaus   (opt_nonopt_plat)
  , amountConflictMin (0)
  , totalConstraintSize  (0)
  , numConstraints       (0)
  , numPlateaus          (0) 
  , initialTime          (-1)
  , beginCplexTime       (-1)
  , beginSATtime         (-1)
  , numOrigVars          (0)
  , numOrigClauses       (0)
  , numHardClauses       (0)
  , numOrigUnitSofts     (0)
  , beginIndexOfBVarEquivClauses (-1)
  , endIndexOfBVarEquivClauses (-1)
  , minconflict_comp     (bvar_weights, numOrigVars)
  , nonopt_solveexactly  (true)
  , karp_do_greedy       (false)
  , wasOptimalSolution   (true)
  , occ_heap             (BVarOccurLt(bvarOccur))  
  , coresmatrix          (NULL)
{
  cplex = new Cplex();
  checkParams(); // requires Cplex to have been created so its param values are known
}

void MaxSolver::checkParams() {
    int multipleSolns = 0;
    multipleSolns = cplex->getMaxNSolns() > 1 ? 1 : 0;
    int shuffling = nAssumpsShuffle > 1 ? 1 : 0;
    int disjalways = disjoint_always ? 1 : 0;
    int nonopt = nonoptimal > 0 ? 1 : 0;
    int sumOfMutExcl = multipleSolns + shuffling + disjalways + nonopt;
    if (sumOfMutExcl > 1) {
        printErrorAndExit("c ERROR: The options nshuffle, disjoint-always, nsolns and nonopt > 0 are mutually exclusive");
    }
    if (seed_cores_only && seed_noncores_only) {
        printErrorAndExit("c ERROR: The options -sd-cores-only and -sd-noncores-only can not be used together");
    }
    if ((seed_cores_only || seed_noncores_only) && !seed_equiv && !seed_reverse) {
        printErrorAndExit("c ERROR: The options -sd-cores-only and -sd-noncores-only must be used with at least one of -equiv-seed or -rev-seed");
    }
    if (!noncore_constraints && (seed_reverse || seed_implications)) {
        printErrorAndExit("c ERROR: The options -rev-seed and -impl-seed require the option -noncore to be used");  
    }
}

MaxSolver::~MaxSolver() {
    if (cplex != NULL) {
        delete cplex;
    }
    if (coresmatrix != NULL) {
        delete coresmatrix;
    }
}

void MaxSolver::solve_maxsat(const char *inputfilename) {

    initialTime = cpuTime();
    printOutput("c Instance", inputfilename);
    inputFileName = string(inputfilename);

    gzFile in = gzopen(inputfilename, "rb");
    if (in == NULL) {
        printErrorAndExit("c ERROR: Could not open input file");
    } 
       
    if (parse_DIMACS(in, this)) {
        // The cost of the falsified clauses exceeds the Dimacs file's Top. Since Top is greater than the 
        // sum of the costs of the soft clauses, this means that at least one hard clause has been violated. 
        // Therefore, the hard clauses are unsatisfiable.
        printComment("c Solved during parsing.");
        printf("s UNSATISFIABLE\n"); fflush(stdout);
        finished();
        return;
    }
    gzclose(in);

    // baseCost was updated during parsing
    printf("c LB %.0lf\n", LB);  // For Evaluation
    printComment("c Parsing of input finished."); 
    fflush(stdout);

    if (verbosity > 0) {
        printInputStats(); 
    }
    // Check that the hard clauses are satisfiable
    vector<Lit> emptyassumps;
    vec<Lit> tempconflict;
    if (!satsolver.solve(emptyassumps, tempconflict)) {
        if (verbosity > 0) printComment("c Contradiction detected in hard clauses.");
        printf("s UNSATISFIABLE\n"); fflush(stdout); // For Evaluation
        LB = UB;
        finished();
        return;
    } 
    printComment("c Hard clauses are satisfiable."); fflush(stdout);
    // Save the model of the hard clauses, and set its cost to the UB
    setUBToHardClauseSolution();

    // remove hard clauses that are satisfied
    satsolver.removeSatisfied();
    if (verbosity > 0) {
        printOutput("c PostHardSATCheck nAssigns()", satsolver.nAssigns());
        printOutput("c PostHardSATCheck nClauses()", satsolver.nClauses());
    }
    
    vector<int> bvars;
    if (relax(bvars, bvar_weights)) {
        printComment("c Solved during relaxation.");
        printf("o %.0lf\n", UB); fflush(stdout);
        printf("s OPTIMUM FOUND\n"); fflush(stdout); // hards are known to be satisfiable
        printSolution(UBmodel);
        finished(); 
        return;
    }
    printf("c LB %.0lf\n", LB); // For Evaluation
    printComment("c Finished creating the relaxed formula.");
    fflush(stdout);

    cplex->initCplex(bvars, bvar_weights);

    if (nonoptimal == nonopt_greedy || nonoptimal == nonopt_karp) {
        coresmatrix = new dlink_matrix(bvar_weights);
    } 
    if (nonoptimal == nonopt_frac || nonoptimal == nonopt_maxoccur || nonoptimal == nonopt_karp) {
        for (int i = 0; i < numBVars; i++) {
            bvarOccur.push(0);
        }
    } 

    if (disjoint_phase) {
        if (disjointPhase(bvars)) {
            printComment("c Solved during disjoint phase.");
            printf("o %.0lf\n", UB); fflush(stdout);
            printf("s OPTIMUM FOUND\n"); fflush(stdout); // For Evaluation
            printSolution(UBmodel);
            finished(); // the hard clauses are known to be satisfiable 
            return;
        }    
    }
    printOutput("c Finished the disjoint core phase. Total number of constraints is", numConstraints); fflush(stdout);

    // Build $\F^b_{eq}$
    if (noncore_constraints) {  
        initBVarEquiv();
        printComment("c Finished augmenting the relaxed formula with b-variable equivalences."); fflush(stdout);
    }
    
    if (seed_valued && !seed_implications && !seed_reverse) {
        seed_valued_bvars(bvars);
    }
    if (seed_implications || seed_reverse) { 
        // build the implications. We know that noncore_constraints is true and the bvar-equivalences have been set up.
        vector<vector<Lit> > b_impls;
        build_b_implications(bvars, b_impls);
        if (seed_valued) {
            seed_valued_bvars(bvars); // more b-vars may become valued during build_b_implications
        } 
        if (seed_implications) {
            seed_b_implications(bvars, b_impls);
        }
        if (seed_reverse) {
            vector<vector<Lit> > rev_impls;
            build_rev_implications(bvars, b_impls, rev_impls);
            seed_rev_implications(rev_impls);
        }
    }
    if (!seed_reverse && seed_equiv) { // (seed_reverse would have already done the job of seed_equiv)
        seed_equivalence();
    }
    if (seed_valued || seed_reverse || seed_implications || seed_equiv) {
        printOutput("c Finished seeding CPLEX with constraints. Total number of constraints is", numConstraints); fflush(stdout); 
    }
   
    seqOfSAT_maxsat();
}



// Called by Dimacs.h (dimacs parser)
bool MaxSolver::addClause(vec<Lit> &lits, Weight w) {

    if (satsolver.reduceClause(lits)) {
        if (lits.size() == 0) {
            baseCost += w;
            LB = baseCost;
            if (LB >= UB) {
                return true;
            }
        } else if (lits.size() == 1) {
            addUnit(lits, w);
        } else {
            if (w < UB) {
                vector<Lit> lits_vector;
                for (int i = 0; i < lits.size(); i++) {
                    lits_vector.push_back(lits[i]);
                }
                origSoftClauses.push_back(lits_vector);
                origSoftClsWeights.push_back(w);
                satsolver.addVarsForClause(lits); 
            } else { 
                satsolver.addClause_(lits, true);
            }
        }
    } // else the clause was a tautology or already satisfied
 
    return false;
}


bool MaxSolver::disjointPhase(vector<int> &bvars) {

    vector<Lit> assumps;
    vec<Lit> conflict;
    Weight costDueToDisjoints = 0;

    int prevNumConstraints = numConstraints;
    int prevTotalConstraintSize = totalConstraintSize;
    int prevAmountConflictMin = amountConflictMin;
 
    double beginTime = cpuTime();

    for (size_t i = 0; i < bvars.size(); i++) {
        assumps.push_back(mkLit(bvars[i], true));
    }
    bool solveRet = true;
    beginSATtime = cpuTime();
    while ((solveRet = MaxSolver::satsolve_min(assumps, conflict)) == false) { 
        reportSAT(conflict);
        Weight minWeight = -1;
        for (int i = 0; i < conflict.size(); i++) {
//            assumps.erase(find(assumps.begin(), assumps.end(), ~conflict[i]));
//            assumps.push_back(conflict[i]);
            assumps[bvarIndex(conflict[i])] = conflict[i];
            wasOptimalSolution = true;
            if (minWeight < 0 || bvar_weights[bvarIndex(conflict[i])] < minWeight) {
                minWeight = bvar_weights[bvarIndex(conflict[i])];
            }
        }
        costDueToDisjoints += minWeight; // This way of figuring out the MWHS of the disjoints relies on the fact that there are no noncores yet during the disjoint phase
        if (baseCost + costDueToDisjoints > LB) {
            LB = baseCost + costDueToDisjoints;
            printf("c LB %.0lf\n", LB); fflush(stdout); //For Evaluation
        }
        if (LB >= UB) {
            return true;
        } 
        addBVarConstraint(conflict);
        beginSATtime = cpuTime();
    }

    if (verbosity > 0) {
        printOutput("c Disjoint Num Cores", numConstraints - prevNumConstraints);
        printOutput("c Disjoint Avg Core Size", (totalConstraintSize - prevTotalConstraintSize)/((double) (numConstraints - prevNumConstraints)));
        printOutput("c Disjoint Avg Core Min", (amountConflictMin - prevAmountConflictMin)/((double) (numConstraints - prevNumConstraints)));
        printOutput("c Time for disjoint cores phase", cpuTime() - beginTime);
    }
    return false;
}

void MaxSolver::approxBVarSolution(vector<Lit> &soln) {
    soln.clear();
    if (!cplex->approx(soln)) {
        printErrorAndExit("c ERROR: cplex->approx() failed");
    }
}

// Meant to be called only when newestcore is a true core
void MaxSolver::approxBVarSolution(vector<Lit> &soln, vec<Lit> &newestcore) {
    if (nonoptimal == nonopt_greedy || (nonoptimal == nonopt_karp && karp_do_greedy)) {
        set<int> hs;
        coresmatrix->greedy_hs(hs);
        soln.clear(); 
        for (int i = 0; i < numBVars; i++) {
            soln.push_back(bvarIndexToLit(i, true));
        } 
        for (set<int>::iterator iter = hs.begin(); iter != hs.end(); iter++) {
            soln[*iter] = bvarIndexToLit(*iter, false); 
        }
          // JD: this was a bug
        /*if (nonoptimal == nonopt_karp) {
            karp_do_greedy = false;
        }*/
    } else if (nonoptimal == nonopt_maxoccur || nonoptimal == nonopt_karp) {
        Lit max = maxOccurringInCore(newestcore);
        soln[bvarIndex(max)] = max;  
        // If there are non-core constraints, and soln is an optimal solution returned by CPLEX, it
        // is also a hitting set of the known cores. We just make more of the negative b-vars positive.
    } else if (nonoptimal == nonopt_frac) {
        vector<Lit> maxoccurbvars; 
        fracOfCore(newestcore, nonopt_frac_to_relax, maxoccurbvars); 
        for (size_t i = 0; i < maxoccurbvars.size(); i++) {
            soln[bvarIndex(maxoccurbvars[i])] = maxoccurbvars[i];
        }
    } else {
        soln[bvarIndex(newestcore[0])] = newestcore[0];
    }   
}

// Meant to be called only on true cores (only positive b-vars)  
void MaxSolver::incrBVarOccurrences(vec<Lit> &core) {
    for (int i = 0; i < core.size(); i++) {
        bvarOccur[bvarIndex(core[i])]++;
    }
}

Lit MaxSolver::maxOccurringInCore(vec<Lit> &core) {
    int maxoccur = 0;
    for (int i = 0; i < core.size(); i++) {
        if (bvarOccur[bvarIndex(core[maxoccur])] < bvarOccur[bvarIndex(core[i])]) {
            maxoccur = i;
        }
    }
    return core[maxoccur];
}

// Using a heap here instead of sorting a vector because the core is of type "vec" so we would have to copy 
// all elements to a std::vector anyway.
void MaxSolver::fracOfCore(vec<Lit> &core, double fracToReturn, vector<Lit> &maxoccur) {
    occ_heap.clear();
    int nToReturn = ceil(fracToReturn*((double) core.size()));
    for (int i = 0; i < core.size(); i++) {
        occ_heap.insert(bvarIndex(core[i]));
    }
    for (int i = 0; i < nToReturn; i++) {   
        maxoccur.push_back(bvarIndexToLit(occ_heap.removeMin(), false));
    }
}

void MaxSolver::seqOfSAT_maxsat() {

    vector<vector<Lit> > cplexsolns;
    vec<Lit> conflict; 
    vector<Lit> oldcplexsoln;

//    double beginTime = cpuTime();


    Weight prevLB = -1;
    int curPlateauLength = 0;
    int iterations = 0;
    while (1) {
        if (verbosity > 0) { printOutput("c *****Iteration ", iterations); }
        iterations++;
        // Find next setting of the b-vars to try. First time through, solvexactly==true 
        if (nonopt_solveexactly || curPlateauLength < nonopt_plateaus) {
            prevLB = LB;
            beginCplexTime = cpuTime();
            if (compare_assumps && cplexsolns.size() > 0) {
                oldcplexsoln.clear();
                oldcplexsoln = cplexsolns[0];
            }
            Weight cplexSolveResult = cplex->solve(cplexsolns);
            if (cplexSolveResult < 0) {
                printErrorAndExit("c ERROR: Cplex::solve() failed");
            }
            updateLB(cplexsolns[0]);
            reportCplex(oldcplexsoln, cplexsolns);
            if (LB == prevLB) {
                curPlateauLength++;
            } else if (LB > prevLB) {
                numPlateaus++;
                if (verbosity > 0) { printOutput("c End of plateau of length", curPlateauLength); }
                printf("c LB %.0lf\n", LB); //For the Evaluation
                fflush(stdout);
                curPlateauLength = 0;
            } else {
                 printErrorAndExit("c ERROR: LB is less than previous");
            }
            wasOptimalSolution = true;    
        } else {
            // find a b-var setting in some other way. Assumes that cplexsolns is of size at least 1
            if (nonoptimal == nonopt_cplex) {
                approxBVarSolution(cplexsolns[0]);
            } else {
                // conflict should always be a core here
                approxBVarSolution(cplexsolns[0], conflict); 
            }
            wasOptimalSolution = false;
        }
        

        if (invertAct) satsolver.invertVarActivities();
        if (resetLearnts) satsolver.resetLearnts();

        // These features are mutually exclusive        
        if (cplexsolns.size() > 1) {
            for (size_t i = 0; i < cplexsolns.size(); i++) {
                if (satsolve(cplexsolns[i], conflict)) {
                    break; 
                }
            }
        } else if (nAssumpsShuffle > 0) {
            for (int i = 0; i < nAssumpsShuffle; i++) {
                if (shuffleFirstTime || i > 0) {
                    random_shuffle(cplexsolns[0].begin(), cplexsolns[0].end());
                }
                if (satsolve(cplexsolns[0], conflict)) {
                    break;
                }
            }
        } else if (disjoint_always) {
            bool foundConflict = false;
            vector<Lit> assumps = cplexsolns[0];
            while (! satsolve(assumps, conflict)) {
                foundConflict = true;
                for (int i = 0; i < conflict.size(); i++) {
                    vector<Lit>::iterator findIndex = find(assumps.begin(), assumps.end(), ~(conflict[i]));
                    if (! noncore_constraints) {
                        *findIndex = conflict[i];
                    } else {
                        assumps.erase(findIndex); 
                    }
                }
            } 
        } else {
            satsolve(cplexsolns[0], conflict);
        }
        if (opt >= 0) break;
    }
}

bool MaxSolver::satsolve(vector<Lit> &inAssumps, vec<Lit> &outConflict) {
    beginSATtime = cpuTime();
    bool solveRet = satsolve_min(inAssumps, outConflict); 
    reportSAT(outConflict); 

    if (wasOptimalSolution) {
        if (solveRet) {
            printf("o %.0lf\n", LB); fflush(stdout); 
            printf("s OPTIMUM FOUND\n"); fflush(stdout); // For Evaluation
            printSolution(satsolver.model);
            finished();
        } else {
            addBVarConstraint(outConflict);
            // JD: in the feb27 version of the code, I forgot to set nonopt_solveexactly to false here! So it was always using optimal calculations.
            if (nonoptimal > 0) {
                nonopt_solveexactly = false;
            }
        }
    } else {
        // non-optimal solution was used
        if (solveRet) {
            if (nonoptimal == nonopt_karp) {
                if (karp_do_greedy) {
                    nonopt_solveexactly = true;
                    karp_do_greedy = false;
                } else {
                    karp_do_greedy = true;
                    nonopt_solveexactly = false;
                }
            } else {
                nonopt_solveexactly = true;
            }
        } else { 
            // conflict was returned in response to non-optimal solution
            bool isNonCore = addBVarConstraint(outConflict);
            if (isNonCore) { // if non-optimal and noncore, go back to exact solution  
                nonopt_solveexactly = true;
                karp_do_greedy = false; 
            } else {
                nonopt_solveexactly = false;
                karp_do_greedy = false;
            }
        }
    }
    return false;
}

bool MaxSolver::addBVarConstraint(vec<Lit> &cls) {
    totalConstraintSize += cls.size();
    numConstraints++;
    bool isNonCore = cplex->add_clausal_constraint(cls);
    if (!isNonCore && (nonoptimal == nonopt_maxoccur || nonoptimal == nonopt_frac || nonoptimal == nonopt_greedy || nonoptimal == nonopt_karp)) {
        if (coresmatrix) {
            set<int> core;
            for (int i = 0; i < cls.size(); i++) {
                core.insert(bvarIndex(cls[i]));
            }
            coresmatrix->add_row(numConstraints-1, core);
        }
        if (nonoptimal == nonopt_karp || nonoptimal == nonopt_maxoccur || nonoptimal == nonopt_frac) {
            incrBVarOccurrences(cls);
        }
    }
    return isNonCore;
}

void MaxSolver::addBVarConstraint(Lit blit, vec<Lit> &impl) {
    totalConstraintSize += (impl.size()+1);
    numConstraints++;
    cplex->add_impl_constraint(blit, impl);
}

void MaxSolver::seed_valued_bvars(vector<int> &bvars) {
    int num_ForcedBs = 0;
    for (size_t i = 0; i < bvars.size(); i++) {
        if (satsolver.value(bvars[i]) != l_Undef) {
            vec<Lit> unitB;
            if (satsolver.value(bvars[i]) == l_False && seed_cores_only) {
                continue;
            }
            unitB.push((satsolver.value(bvars[i]) == l_True) ? mkLit(bvars[i], false): mkLit(bvars[i], true) );
            num_ForcedBs++;
            addBVarConstraint(unitB);
        }
    }
    if (verbosity > 0) {
        printOutput("c ValuedSeed: Number of Forced B's", num_ForcedBs);
    }
}

void MaxSolver::build_b_implications(vector<int> &bvars, vector<vector<Lit> > &b_impls) {
    b_impls.resize(satsolver.nVars()*2);
    for (size_t i = 0; i < bvars.size(); i++) {
        Lit posB = mkLit(bvars[i], false);
        bool posBResult = true;
        bool negBResult = true;
        if (satsolver.value(posB) == l_Undef) {
            posBResult = satsolver.findUnitImps(posB, b_impls[toInt(posB)]);
            if (!posBResult) {
                satsolver.uncheckedEnqueue(~posB);
            }
        } 
        if (satsolver.value(~posB) == l_Undef) {
            negBResult = satsolver.findUnitImps(~posB, b_impls[toInt(~posB)]);
            if (!negBResult) {
                satsolver.uncheckedEnqueue(posB);
            }
        } 
    }
    //debug
    /*
    for(size_t i = 0; i < b_impls.size(); i++) {
      cout << "Implications of Lit ";
      satsolver.printLit(toLit(i));
      cout << ", ";
      if(var(toLit(i)) >= numOrigVars) {
	cout << "BVAR (" << var(toLit(i)) - numOrigVars << ")" << endl;
      }
      for(size_t j = 0; j < b_impls[i].size(); j++) {
	satsolver.printLit(b_impls[i][j]);
	cout << ", ";
      }
      if(b_impls[i].size() > 0) cout << endl;
    }
    */
    //debug
}

void MaxSolver::build_rev_implications(vector<int> &bvars, vector<vector<Lit> > &b_impls, vector<vector<Lit> > &rev_impls) {
    rev_impls.resize(satsolver.nVars()*2);

    for (size_t i = 0; i < bvars.size(); i++) {
        Lit posB = mkLit(bvars[i], false);
        for (size_t j = 0; j < b_impls[toInt(posB)].size(); j++) {
            rev_impls[toInt(b_impls[toInt(posB)][j])].push_back(posB);    
        }
        Lit negB = mkLit(bvars[i], true);
        for (size_t j = 0; j < b_impls[toInt(negB)].size(); j++) {
            rev_impls[toInt(b_impls[toInt(negB)][j])].push_back(negB);    
        }
    }
}

void MaxSolver::seed_b_implications(vector<int> &bvars, vector<vector<Lit> > &b_impls) {
    int num_Impls  = 0;
    double total_impls_size = 0.0;

    for (size_t i = 0; i < bvars.size(); i++) {
        if (satsolver.value(bvars[i]) == l_Undef) {
            vec<Lit> impls;
            Lit posB = mkLit(bvars[i], false);
            
            for (size_t j = 0; j < b_impls[toInt(posB)].size(); j++) {
                if (! isOrigLit(b_impls[toInt(posB)][j])) {
                    impls.push(b_impls[toInt(posB)][j]);
                } 
            }  
            if (impls.size() > 0) {
                num_Impls++;
                total_impls_size += impls.size();
                addBVarConstraint(posB, impls);
            }
            Lit negB = mkLit(bvars[i], true);
            impls.clear();
            for (size_t j = 0; j < b_impls[toInt(negB)].size(); j++) {
                if (! isOrigLit(b_impls[toInt(negB)][j])) {
                    impls.push(b_impls[toInt(negB)][j]);
                } 
            }  
            if (impls.size() > 0) {
                num_Impls++;
                total_impls_size += impls.size();
                addBVarConstraint(negB, impls);
            }
        }
    }
    if (verbosity > 0) {
        printOutput("c ImplSeed: Number of implication constraints", num_Impls);
        printOutput("c ImplSeed: Avg num of implications/constraint", total_impls_size/num_Impls);
    } 
} 

void MaxSolver::seed_rev_implications(vector<vector<Lit> > &rev_impls) {    
    int num_b_clauses = 0;
    double total_b_clause_size = 0.0;
    int maxClsIndex = numOrigClauses; // so we don't check the b-var equivalency clauses 
    
    for (int i = 0; i < maxClsIndex; i++) {
        vec<Lit> bvarcls;
        if (advanced_bvar_clause_and_check_core(i, bvarcls, rev_impls)) {
            num_b_clauses++;
            total_b_clause_size += bvarcls.size();
            addBVarConstraint(bvarcls);
        }
    }
    if (verbosity > 0) { 
        printOutput("c RevSeed: Num new b-clauses", num_b_clauses);
        printOutput("c RevSeed: Avg length of new b-clause", total_b_clause_size/num_b_clauses);
    }
}

void MaxSolver::seed_equivalence() {
    int prev_numConstraints = numConstraints;
    int prev_numNonCore = cplex->numNonCoreConstraints;
    int prev_nonCoreLength = cplex->totalNonCoreLength;

    int maxClsIndex = numOrigClauses; // so we don't check the b-var equivalency clauses 
    for (int i = 0; i < maxClsIndex; i++) {
        vec<Lit> bvarcls;
        if (bvar_clause_and_check_core(i, bvarcls)) {
            addBVarConstraint(bvarcls);
        }
    }
    if (verbosity > 0) {
        printOutput("c EquivSeed: Number of seeded constraints", numConstraints - prev_numConstraints);
        printOutput("c EquivSeed: Number of non-core seeds", cplex->numNonCoreConstraints - prev_numNonCore);
        printOutput("c EquivSeed: Average length of non-core seed", ((cplex->totalNonCoreLength) - prev_nonCoreLength)/((double) (cplex->numNonCoreConstraints) - prev_numNonCore));
    }
}

void MaxSolver::updateLB(vector<Lit> &assumps) {
    Weight cost = 0;
    for (size_t i = 0; i < assumps.size(); i++) {
        if (!isOrigLit(assumps[i]) && !sign(assumps[i])) {
            cost += bvar_weights[bvarIndex(assumps[i])];
        }
    }
    if (cost + baseCost > LB) {
        LB = cost + baseCost;
    }
}

bool litcompare(Lit l1, Lit l2) {
    return toInt(l1) < toInt(l2);
}

void MaxSolver::printStatsAndExit(int signum, int exitType) {
    static int onceOnly = 0;
    if (onceOnly == 0) { 
        onceOnly = 1;
        double cpu_time = cpuTime();
        double mem_used = memUsedPeak();
     
        //satsolver.printStats(cpu_time);
        printOutput("c INTERRUPTED signal", signum);
        printOutput("c Current LB", LB);
        printOutput("c Total number of constraints given to CPLEX", numConstraints);
        if (verbosity > 0) printOutput("c Avg constraint size", totalConstraintSize/(double)numConstraints);
        if (verbosity > 0) printOutput("c Avg amount constraint minimized", amountConflictMin/(double) numConstraints); 
        if (cplex) printOutput("c Number of non-core constraints", cplex->numNonCoreConstraints);
        if (verbosity > 0 && cplex) printOutput("c Average length of non-core constraints", (cplex->totalNonCoreLength)/((double) (cplex->numNonCoreConstraints)));
        
        if (verbosity > 0) {
            printOutput("c Final UB", UB);
            printOutput("c Num plateaus", numPlateaus);
            printOutput("c Avg plateau length", numConstraints/((double)numPlateaus));
        }
        printOutput("c Number of SAT calls", satsolver.solves);
        printOutput("c Total SAT time", satsolver.totalTime);
        if (cplex) {
            printOutput("c Number of CPLEX calls", cplex->numSolves);
            printOutput("c Total CPLEX time", cplex->totalTime);
            if (verbosity > 0) printOutput("c Number of CPLEX solutions", cplex->totalNumOptSolutions);
        }
        printOutput("c Interrupted CPLEX solving", beginCplexTime > 0 ? cpuTime() - beginCplexTime : -1);
        printOutput("c Interrupted SAT solving", beginSATtime > 0 ? cpuTime() - beginSATtime : -1);
        printOutput("c Memory used (MB)", mem_used);
        printOutput("c CPU time", cpu_time);
    }
    fflush(stdout);
    fflush(stderr);
    /*if (exitType == 0) {
        exit(0);
    } else {*/
        _exit(exitType);
    //}
}

void MaxSolver::printInputStats() {
    printOutput("c PostParse nVars()", satsolver.nVars());
    printOutput("c PostParse nAssigns()", satsolver.nAssigns());
    printOutput("c PostParse nClauses()", satsolver.nClauses());     
    printOutput("c PostParse numOrigUnitSofts", numOrigUnitSofts);
    printOutput("c PostParse origSoftClauses.size()", origSoftClauses.size());
    printOutput("c PostParse LB", LB);
    printOutput("c PostParse UB", UB); 
    printOutput("c Parse time", cpuTime() - initialTime);  
}

void MaxSolver::reportCplex(vector<Lit> &oldassumps, vector<vector<Lit> > &cplexsolns) {
    if (verbosity > 0) { 
        printOutput("c Cplex time: ", cpuTime() - beginCplexTime);
        printOutput("c LB: ", LB);
        printOutput("c Num Cplex solutions: ", cplexsolns.size()); 
    }
    if (compare_assumps && oldassumps.size() > 0) {
        int numDiff = 0;
        for (size_t i = 0; i < cplexsolns[0].size(); i++) {
            if (cplexsolns[0][i] != oldassumps[i]) {
                numDiff++;
            }
        }
        printOutput("c Num differences in assumptions: ", numDiff);
    }
    beginCplexTime = -1;
}

void MaxSolver::reportSAT(vec<Lit> &conflict) {
    if (verbosity > 0) {
        printOutput("c SAT solving time: :", cpuTime() - beginSATtime);
        printOutput("c conflict.size(): ", conflict.size()); 
    }
    beginSATtime = -1;
    outputConflict(conflict);
}

bool MaxSolver::satsolve_min(vector<Lit> &inAssumps, vec<Lit> &outConflict) {
   
    if (nonoptimal > 0 && !wasOptimalSolution /*wasOptimal==true during disjoint phase*/ && noncore_constraints) {
        sort(inAssumps.begin(), inAssumps.end(), bvar_negfirst_comp);
    } 
    bool result = satsolver.solve(inAssumps, outConflict);
    if (!result) {
        int origsize = outConflict.size();
        if (min_type == 1) {
            minimize_rerefute(outConflict); 
        } else if (min_type == 2) {
            minimize_greedy(outConflict);
        } else if (min_type == 3) {
            minimize_rerefute(outConflict);
            minimize_greedy(outConflict);
        }
        amountConflictMin += origsize - outConflict.size();
    }
    return result;
}

void MaxSolver::minimize_rerefute(vec<Lit> &con) {

    int prev_size = -1;
    vector<Lit> assumps;
    bool solveRet = false; 
    do {
        assumps.clear();
        for (int i = 0; i < con.size(); i++) {
            assumps.push_back(~con[i]);
        }
        if (invertAct_rerefute) satsolver.invertVarActivities();
        if (resetLearnts_rerefute) satsolver.resetLearnts();
        prev_size = con.size();
        con.clear();
        solveRet = satsolver.solve(assumps, con);
    } while ((con.size() < prev_size) && !solveRet);
}

void MaxSolver::minimize_greedy(vec<Lit> &con) {

    int i = con.size()-1;
    if (sort_min) {
        vector<Lit> sortedcon;
        for (int j = 0; j < con.size(); j++) {
            sortedcon.push_back(con[j]);
        }
        sort(sortedcon.begin(), sortedcon.end(), minconflict_comp);
        con.clear();
        for (size_t j = 0; j < sortedcon.size(); j++) {
            con.push(sortedcon[j]);
        }
    }
    while (con.size() > 1 && i >= 0) {
        if (testRemoval(con, i)) {
            con.remove(i);
        }
        i--;
    }
}

// See if con without its last element is still a conflict clause
bool MaxSolver::testRemoval(vec<Lit> &con, int indexToRemove) {

    vector<Lit> assumps;
    for (int i = 0; i < con.size(); i++) {
        if (i != indexToRemove) {
            assumps.push_back(~con[i]);
        }
    }
    //if (invertAct) satsolver.invertVarActivities();
    //if (resetLearnts) satsolver.resetLearnts();
    vec<Lit> tempcon;
    return (satsolver.solve(assumps, tempcon) == false);
}



void MaxSolver::outputConflict(vector<Lit> &con) {
    if (verbosity > 1) {
        printf("conflict clause: ");
        for (size_t i = 0; i < con.size(); i++) {
            satsolver.printLit(con[i]); printf(" ");
        }
        printf("\n");
        fflush(stdout);
    }
}

void MaxSolver::outputConflict(vec<Lit> &con) {
    if (verbosity > 1) {
        printf("conflict clause: ");
        for (int i = 0; i < con.size(); i++) {
            satsolver.printLit(con[i]); printf(" ");
        }
        printf("\n");
        fflush(stdout);
    }
}

bool MaxSolver::relax(vector<int> &bvars, vector<Weight> &bvarcoeffs) {

    int bvar = numOrigVars;
    Weight totalWeight = 0;
    int numSatisfiedSofts = 0;
    int numUnitSofts = 0;
    int numNonUnitSofts = 0; 
    Weight knownW = -1;

    numHardClauses = satsolver.nClauses();

    for (hash_map<int,Weight>::iterator i = unitSofts.begin(); i != unitSofts.end(); i++) {
        Lit curLit = toLit((*i).first);
        Weight curW = (*i).second;
        if (satsolver.value(curLit) == l_False) {
            baseCost += curW;
            LB = baseCost;
            // LB is being updated here but wait until the end of relax() to output the new LB 
            if (LB >= UB) {
                return true;
            }
            totalWeight += curW;
        } else if (satsolver.value(curLit) == l_Undef) {
            // add a b-var and make it a real clause
            Lit newBLit = mkLit(bvar++, false);
            bvars.push_back(var(newBLit));
            bvarcoeffs.push_back(curW);
            if (knownW < 0) {
                knownW = curW;
            } 
            if (knownW != curW) {
                weighted = true; 
            }
            vec<Lit> ps;
            ps.push(curLit);
            ps.push(newBLit);
            satsolver.addClause_(ps, true);
            numUnitSofts++;
            totalWeight += curW;
            if (noncore_constraints || seed_equiv) {
                lit_equiv_bvar[toInt(curLit)] = toInt(~newBLit);
            }
            if (noncore_constraints) {
                vector<Lit> ecls;
                ecls.push_back(~curLit);
                ecls.push_back(~newBLit);
                equivClauses.push_back(ecls);
            }
        } else {
            numSatisfiedSofts++;
        }   
    }
    unitSofts.clear(); // not supposed to use anymore

    for (size_t i = 0; i < origSoftClauses.size(); i++) {
        vec<Lit> origsoft_ps;
        for (size_t j = 0; j < origSoftClauses[i].size(); j++) {
            origsoft_ps.push(origSoftClauses[i][j]);
        }
        if (satsolver.reduceClause(origsoft_ps)) {
            if (origsoft_ps.size() == 0) {
                baseCost += origSoftClsWeights[i];
                LB = baseCost; // wait until end of relax() to output the LB
                if (LB >= UB) {
                    return true;
                }
                totalWeight += origSoftClsWeights[i]; 
            } else {
                Lit newBLit = mkLit(bvar++, false);
                bvars.push_back(var(newBLit));
                bvarcoeffs.push_back(origSoftClsWeights[i]); 
                if (knownW < 0) {
                    knownW = origSoftClsWeights[i];
                } 
                if (knownW != origSoftClsWeights[i]) {
                    weighted = true; 
                }
                origsoft_ps.push(newBLit);
                satsolver.addClause_(origsoft_ps, true);
                if (origsoft_ps.size() > 2) { 
                    numNonUnitSofts++;
                } else {
                    numUnitSofts++;
                }
                totalWeight += origSoftClsWeights[i];
    
                if ((noncore_constraints || seed_equiv) && (origsoft_ps.size() == 2)) {
                    lit_equiv_bvar[toInt(origsoft_ps[0])] = toInt(~newBLit);
                }
                if (noncore_constraints) {
                    for (int j = 0; j < origsoft_ps.size()-1; j++) {
                        vector<Lit> ps;
                        ps.push_back(~origsoft_ps[j]);
                        ps.push_back(~newBLit);
                        equivClauses.push_back(ps);
                    }
                }
            }
        } else {
            numSatisfiedSofts++;
        } 
    }
    origSoftClauses.clear();
    origSoftClsWeights.clear();

    // April 4, 2013: Now we know that UB is set to the cost of a model of the hard clauses.
    if (totalWeight < UB) {
        //UB = totalWeight;
        printErrorAndExit("c ERROR: the total weight of the soft clauses is somehow less than the cost of a model of the hard clauses?!");
    }
    
    if (LB >= UB) {
        return true;
    }
    numOrigClauses = satsolver.nClauses();
    numBVars = bvars.size();

    if (verbosity > 0) {
        printOutput("c PostRelax LB", LB);
        printOutput("c PostRelax totalWeight", totalWeight);
        printOutput("c PostRelax UB", UB);  
        printOutput("c PostRelax numSatisfiedSofts", numSatisfiedSofts);
        printOutput("c PostRelax num unit softs", numUnitSofts);
        printOutput("c PostRelax num non-unit softs", numNonUnitSofts);
        printOutput("c PostRelax numConstraints", numConstraints);
    }
    return false;
}

void MaxSolver::initBVarEquiv() {

    beginIndexOfBVarEquivClauses = satsolver.nClauses();
    for (size_t i = 0; i < equivClauses.size(); i++) {
        satsolver.addClause_(equivClauses[i], true);
    }
    equivClauses.clear();
    endIndexOfBVarEquivClauses = satsolver.nClauses();
}
void MaxSolver::addUnit(vec<Lit> &ps, Weight w) {
    satsolver.addVarsForClause(ps);
    Lit p = ps[0];
 
    if (w < UB) {
        //while (unitSofts.size() <= toInt(p)) unitSofts.push(0);
        if (unitSofts.find(toInt(p)) == unitSofts.end()) {
            numOrigUnitSofts++;
            unitSofts[toInt(p)] = 0;
        }
        unitSofts[toInt(p)] += w;
    } else {
        satsolver.uncheckedEnqueue(p);
    }
}

// Also check if the bvarcls will be a core or a non-core
// If it already contains a b-var, it must have at least two non-b variables
bool MaxSolver::advanced_bvar_clause_and_check_core(int clsIndex, vec<Lit> &bvarcls, vector<vector<Lit> > &rev_impls) {

    bvarcls.clear();
   
    int numB = 0;
    int numNonB = 0; 
    for (int i = 0; i < satsolver.clsSize(clsIndex); i++) {
        Lit curLit = satsolver.clsLit(clsIndex, i); 
        if (!isOrigLit(curLit)) {
            numB++;
        } else {
            numNonB++;
            if (rev_impls[toInt(~curLit)].size() == 0) {
                return false;
            }
        }
    }
    // It was a unit soft clause
    if (numB > 0 && numNonB < 2) {
        return false;
    }

    set<Lit> equivSet;

/*
    for (int i = 0; i < satsolver.clsSize(clsIndex); i++) {
        Lit curLit = satsolver.clsLit(clsIndex, i);
        if (isOrigLit(curLit)) {
            Lit equivLit = rev_impls[toInt(~curLit)][0];
            equivSet.insert(~equivLit);  
        } else {
            equivSet.insert(curLit);
        }
    } 

*/
    bool isNonCore = false;

    for (int i = 0; i < satsolver.clsSize(clsIndex); i++) {
        Lit curLit = satsolver.clsLit(clsIndex, i);
        if (isOrigLit(curLit)) {
	  Lit equivLit;
	  hash_map<int, int>::iterator iter;
	  if ((iter = lit_equiv_bvar.find(toInt(curLit))) != lit_equiv_bvar.end()) {
	    equivLit = toLit(iter->second); 
	  } else if ((iter = lit_equiv_bvar.find(toInt(~curLit))) != lit_equiv_bvar.end()) {
	    equivLit = ~toLit(iter->second); 
	  } else {
	    equivLit = ~(rev_impls[toInt(~curLit)][0]);
	  }
	  equivSet.insert(equivLit);
        } else {
	  equivSet.insert(curLit);
        }
    } 

    for (set<Lit>::iterator iter = equivSet.begin(); iter != equivSet.end(); iter++) {
        if (sign(*iter)) {
            isNonCore = true;
        }
        bvarcls.push(*iter);
    }
   
    bool coreCondition = (seed_cores_only && !isNonCore) || (seed_noncores_only && isNonCore) || (!seed_cores_only && !seed_noncores_only);

    return coreCondition;
}


// Also check if the bvarcls will be a core or a non-core
// If it already contains a b-var, it must have at least two non-b variables
bool MaxSolver::bvar_clause_and_check_core(int clsIndex, vec<Lit> &bvarcls) {

    bvarcls.clear();
   
    int numB = 0;
    int numNonB = 0; 
    for (int i = 0; i < satsolver.clsSize(clsIndex); i++) {
        Lit curLit = satsolver.clsLit(clsIndex, i); 
        if (!isOrigLit(curLit)) {
            numB++;
        } else {
            numNonB++;
            if ((lit_equiv_bvar.find(toInt(curLit)) == lit_equiv_bvar.end()) && (lit_equiv_bvar.find(toInt(~curLit)) == lit_equiv_bvar.end())) {
                return false;
            }
        }
    }
    if (numB > 0 && numNonB < 2) {
        return false;
    }

    bool isNonCore = false;

    for (int i = 0; i < satsolver.clsSize(clsIndex); i++) {
        Lit curLit = satsolver.clsLit(clsIndex, i);
        if (isOrigLit(curLit)) {
            Lit eqlit;
            hash_map<int, int>::iterator iter = lit_equiv_bvar.find(toInt(curLit));
            if (iter != lit_equiv_bvar.end()) {
                eqlit =  toLit(iter->second);
            } else {
                iter = lit_equiv_bvar.find(toInt(~curLit));
                eqlit =  ~(toLit(iter->second));
            }
            if (sign(eqlit)) {
                isNonCore = true;
            }
            bvarcls.push(eqlit);
        } else {
            if (sign(curLit)) {
                isNonCore = true;
            }
            bvarcls.push(curLit);
        }
    } 
    bool coreCondition = (seed_cores_only && !isNonCore) || (seed_noncores_only && isNonCore) || (!seed_cores_only && !seed_noncores_only);
    return coreCondition;
}

// Sometimes we want to keep the hard learnt clauses
bool MaxSolver::deleteLearnt(Clause &c) const {

    if (!delete_hard_learnts) {
        bool containsBVar = false;
        for (int i = 0; i < c.size(); i++) {
            if (!isOrigLit(c[i])) {
               containsBVar = true;
               break;
            }
        }
        // It doesn't contain a b-var, so it is a hard learnt. We don't want to delete it.
        if (!containsBVar) {
            return false;
        }
    } 
    return true;
}

void MaxSolver::finished() {
    opt = LB;
    printOutput("c Optimum", LB);
    fflush(stdout);
}



void MaxSolver::printOutput(const char *msg, const char *val) {

    printf("%s: %s\n", msg, val); 
}

void MaxSolver::printOutput(const char *msg, Weight val) {
    printf("%s: %.2lf\n", msg, val); 
}

void MaxSolver::printErrorAndExit(const char *msg) {
    cerr << msg << endl;
    fflush(stderr);
    printStatsAndExit(-1, 1);
}

void MaxSolver::printComment(const char *msg) {
    cout << msg << endl;
}

// For the Evaluation. Prints the "v " line, which contains the last satisfying assignment found by the SAT solver (only original literals, no b-vars)
void MaxSolver::printSolution(vec<lbool> &model) {
    printf("v");
    for (int i = 0; i < numOrigVars; i++) {
        printf(" %s%d", model[i] == l_True ? "" : "-", i+1);
    }
    printf("\n");
    fflush(stdout);
}

void MaxSolver::setUBToHardClauseSolution() {
    Weight costOfHardModel = baseCost; // cost of falsified softs found during parsing
    // Store the model
    UBmodel.growTo(numOrigVars);
    for (int i = 0; i < numOrigVars; i++) {
        UBmodel[i] = satsolver.model[i];
    }
    for (size_t i = 0; i < origSoftClauses.size(); i++) {
        bool isSat = false;
        for (size_t j = 0; j < origSoftClauses[i].size(); j++) {
            if (satsolver.modelValue(origSoftClauses[i][j]) == l_True) {
                isSat = true;
                break;
            }
            if (satsolver.modelValue(origSoftClauses[i][j]) == l_Undef) {
                printErrorAndExit("c ERROR: the model of the hard clauses does not assign a value to every variable.");
            }
        }
        if (!isSat) {
            costOfHardModel += origSoftClsWeights[i];
        }
    }
    for (hash_map<int,Weight>::iterator i = unitSofts.begin(); i != unitSofts.end(); i++) {
        Lit curLit = toLit((*i).first);
        Weight curW = (*i).second;
        if (satsolver.modelValue(curLit) == l_False) {
            costOfHardModel += curW;
        }
    } 
    if (UB < costOfHardModel) {
        printErrorAndExit("c ERROR: the cost of a model of the hard clauses exceeds the Dimacs file's Top.");
    }
    UB = costOfHardModel;
}
