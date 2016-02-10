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

#include <cmath>
#include <algorithm>
#include <map>
#include <unordered_set>
#include <zlib.h>
#include <iostream> 
#include <iomanip>


#include "maxhs/core/MaxSolver.h"
#include "maxhs/utils/io.h"
#include "maxhs/ifaces/miniSatSolver.h"
#include "maxhs/ifaces/GreedySolver.h"
//#include "maxhs/ifaces/greedySatSolver.h"
#include "minisat/utils/System.h"

//using namespace Minisat;
using namespace MaxHS;
using namespace MaxHS_Iface;

using std::endl;
using std::cout;

MaxSolver::MaxSolver(Wcnf *f) : //many of are already default initialized...but for clarity
  theWcnf {f},
  bvars {f},
  satsolver {new MaxHS_Iface::miniSolver{}},
  greedysolver {nullptr},
  //  greedySatSolver {nullptr},
  muser {new MaxHS_Iface::Muser{theWcnf, bvars}},
  sat_wt {0.0},
  forced_wt {0.0},
  lower_bnd {0.0},
  UBmodel (theWcnf->nVars(), l_Undef),
  UBmodelSofts (theWcnf->nSofts(), l_False),
  tmpModelSofts (theWcnf->nSofts(), l_False),
  haveUBModel {false},
  eqCvar {static_cast<Var>(bvars.maxvar()+1)},
  eqCvarPos (lit_Undef),
  nextNewVar {eqCvar+1},
  bLitOccur (bvars.nlits(), 0),
  cplexClauses {},
  sftSatisfied {},
  cplexNU {}, 
  greedyNU {}, 
  muserNU {},
  satNU {},
  satBvarNU {},
  forcedWtNU {},
  amountConflictMin {0},
  globalStartTime {0},
  printStatsExecuted {false},
  solved {false},
  unsat {false},
  nFailedLits {0},
  nForcedByBounds {0},
  m_sum_reduced_frac {0},
  mtime {0.0},
  mcalls {0},
  doMin {true},
  blit_lt {&bLitOccur, bvars, false},
  blit_gt {&bLitOccur, bvars, true}
  { 
    params.instance_file_name = theWcnf->fileName();
    cplex  = new Cplex {bvars, UBmodelSofts};
    if(!cplex->is_valid())
       cout << "c ERROR. Problem initializing CPLEX solver\n";
    /*if(theWcnf->getMxs().size() > 0)
      greedySatSolver = new MaxHS_Iface::GreedySatSolver{bvars};
      else */
    greedysolver = new MaxHS_Iface::GreedySolver{bvars};
  }

MaxSolver::~MaxSolver() {
  if (satsolver) 
    delete satsolver;
  if (greedysolver)
    delete greedysolver;
  //if (greedySatSolver)
  //  delete greedySatSolver;
  if (cplex)
    delete cplex;
}

bool MaxSolver::doPreprocessing() {
  //test if we should do preprocessing.
  //We have to freeze all unit softs. So if this spans all variables we won't
  //be able to eliminate any variables in preprocessing.
  if(!params.preprocess)
    return false;

  const int dne {0}, nfrz {1}; //markers dne==does not exist, nfrz==not frozen. 
  int toBeFrozen {0}, totalVars {0}; //
  vector<char> varStatus(theWcnf->nVars(), dne); 

  for(auto hc: theWcnf->hards())
    for(auto lt: hc) 
      if(varStatus[var(lt)] == dne) {
	++totalVars;
	varStatus[var(lt)] = nfrz;
      }
  for(auto sc: theWcnf->softs())
    if(sc.size() > 1) //unit softs that don't exist elsewhere treated as dne
      for(auto lt: sc)
	if(varStatus[var(lt)] == dne) {
	  ++totalVars;
	  varStatus[var(lt)] = nfrz;
	}
  for(auto sc: theWcnf->softs())
    if(sc.size() == 1) { //now count units softs that will be frozen. Don't count if they don't exist elsewhere
      Var v = var(sc[0]);
      if(varStatus[v] == nfrz) {
	++toBeFrozen;
	varStatus[v] = dne;
      }
    }
  if(params.verbosity > 0)
    cout << "c Total used vars = " << totalVars << " vars to be frozen = " << toBeFrozen << "\n";
  return toBeFrozen < totalVars;
}

void MaxSolver::solve() {
  globalStartTime = cpuTime();

  if(theWcnf->isUnsat()) {
    cout << "c Unsat Found by theWcnf\n";
    unsatFound();
    return;
  }

  if(!doPreprocessing()) 
    satsolver->eliminate(true);

  addHards(satsolver);
  addSofts(satsolver);

  //add eq clauses if using fbeq.
  if(params.fbeq)
    addSoftEqs(satsolver, false); //permanent eq clauses

  //Otherwise we will add forced negated b-vars to the sat solver
  //after sat solving episodes. Not as powerful as dynamic inferences
  //made by eq clauses. But better than leaving negated b-vars
  //uninferred.
  if(params.fb)
    initSftSatisfied(); 

  if(params.preprocess) {
    auto start = cpuTime();
    satsolver->eliminate(true);
    if(params.verbosity > 0)
      cout << "c MiniSat Preprocess eliminated " << satsolver->nEliminated() << " variables. took " << cpuTime()-start << " sec.\n";
  }

  //* Compute an initial lower and upper bound by solving
  auto hards_are_sat = satsolver->solve();
  if(hards_are_sat == l_False) {
    unsatFound();
    return;
  }
  
  //update Bounds
  cout << "c Init Bnds: SAT Time " << satsolver->solveTime() << "\n";
  improveModel();
  updateLB(getForcedWt()); //get forced weight. 
  updateUB();
  
  if(LB() >= UB()) { 
    optFound("c Solved by Init Bnds.");
    return;
  }

  cout << "c Init Bnds: LB = " << LB() << " UB = " << UB() << "\n";
  if (params.verbosity > 0) 
    cout << "c Init Bnds: Forced " << satsolver->nAssigns() << " literals.\n";
  //DEBUG 
  //cout << "Init Bnds: Forced " << satsolver->nAssigns() << " literals.\n"
  // << satsolver->getForced(0) << "\n";
  //

  if(params.fb) //add forced negated b-vars to sat solver. Can be useful for seeding and disjoint phase
    satSolverAddBvarsFromSofts();

  //For mutex processing.
  processMutexes();

  //2. Compute seeding constraints. 
  if (params.seedType != SeedType::none)
    seed_equivalence();

  //DEBUG
  // if(greedysolver) { 
  //   greedysolver->printDS();
  //   cout << " Greedy Solution " << greedysolver->solve() << "\n";
  // }

  //3. Clean up
  if (!satsolver->simplify()) 
    printErrorAndExit("c ERROR: UNSAT detected when simplify clauses");

  //4. Do disjoint Phase if required
  if (params.dsjnt_phase)
    disjointPhase();

  //5. Now solve.
  seqOfSAT_maxsat();
}

void MaxSolver::disjointPhase() {
//  Assumps assumps(satsolver, bvars,inMx);
  Assumps assumps(satsolver, bvars);
  int num {0};
  int len {0};
  
  if (params.verbosity > 0) 
    cout << "c Disjoint Phase\n";

  double beginTime = cpuTime();
  assumps.initAllSofts();
  if(params.sort_assumps == 1) 
    assumps.sort(blit_gt);
  else if(params.sort_assumps == 2)
    assumps.sort(blit_lt);

  vector<Lit> conflict;
  lbool val;
  while((val = satsolve_min(assumps, conflict, params.dsjnt_cpu_per_core, params.dsjnt_mus_cpu_lim))
	== l_False) {

    if(params.verbosity > 1) {
      cout << "c Disjoint Conflict size = " << conflict.size() << "\n";
      cout << "c conflict = " << conflict << "\n";
    }

    storeCplexCls(conflict); 
    //assumps.update(conflict, params.fbeq);
    //Must remove assumptions now that we are adding forced negated bvars
    assumps.update(conflict, true); 
    num++;
    len += conflict.size();
  }

  //update Bounds (only UB could have changed)
  if(val == l_True) {
    improveModel();
    updateUB();
  }
  
  if (params.verbosity > 0) {
    cout << "c Dsjnt: #Cores " << num << "\n";
    if(num > 0)
      cout << "c Dsjnt: Avg Core Size " <<  len/((double) num) << "\n";
    cout << "c Dsjnt: Time " << cpuTime() - beginTime << "\n";
  }
}

void MaxSolver::seqOfSAT_maxsat() {
  vector<Lit> cplexsoln;
  vector<Lit> conflict;
//  Assumps assumps(satsolver, bvars, inMx);
  Assumps assumps(satsolver, bvars);
  int iteration {0};

  while (1) { //exit by return
    //1. Call Cplex
    if (params.verbosity > 0)
      cout << "c **********Iter: " << iteration << " Elapsed Time = "
	   << cpuTime() - globalStartTime << "\n"; 
    iteration++;

    //Update Cplex...note all previous satsolves have added the forced bvars to the sat solver
    cplexAddNewForcedBvars();
    cplexAddNewClauses();
    /*if(params.bestmodel_mipstart) {
      cplex->clearOldStarts();
      cplex->addStart(UBModel);
    }*/
    Weight cplexSolveResult = cplex->solve(cplexsoln);
    if (cplexSolveResult < 0) {
      printErrorAndExit("c ERROR: Cplex::solve() failed");
    }
    reportCplex(cplexSolveResult);

    //2. Update and check Bounds
    bool lbNotImproved = true;
    auto cplexSolnWt = getWtOfBvars(cplexsoln);
    //Note that cplex might now model some forced bvars directly---these
    //will be accounted for when it constructs its returned solution.
    //so the weight returned is not necessarily the real weight of the solution.
    if(cplexSolnWt > LB()) {
      lbNotImproved = false;
      updateLB(getWtOfBvars(cplexsoln));
    }
    if(haveUBModel && LB() >= UB()) { //if !haveUBModel we don't have sat model of hards as yet.
      optFound("c Solved by detecting LB>=UB.");
      return;
    }
    cout << "c Bnds: LB = " << LB() << " UB = " << UB() << "\n";
    
    //3. Set up assumptions.
    
    assumps.init(cplexsoln, params.coreType);
    if(params.sort_assumps == 1) 
      assumps.sort(blit_gt);
    else if(params.sort_assumps == 2)
      assumps.sort(blit_lt);
    
    if(params.verbosity > 3) {
      cout << "cplex solution: " << cplexsoln << "\n";
      cout << "c assumps after Cplex soln: " << assumps.vec() << "\n";
    }
	
    //4. Check if CPLEX's model yields sat
    if(satsolve_min(assumps, conflict, params.noLimit, params.mus_cpu_lim) == l_True) {
      updateUB();
      optFound("c Solved by Cplex Model");
      return;
    }
    else {
      //5. Process first conflict and find more for Cplex
      if(params.verbosity > 0)
	cout << "c FeedCplex " << iteration << ".0\n";
      if(params.verbosity > 2)
	cout << "c   conflict: " << conflict << "\n";

      storeCplexCls(conflict);

      //5a. Try populate?
      if(params.trypop == 2 ||(params.trypop == 1 && lbNotImproved))
	 tryPopulate(conflict, cplexSolnWt);
      if(solved)
	return;
      
      //5b. Now iteratively critique conflict arising from last cplex solution 
      //    processed using non-optimal hitting sets.
      auto tmp = getAssumpUpdates(1, 1, conflict);
      //Must remove assumptions now that we are adding forced negated bvars
      //assumps.update(tmp, params.fbeq);
      assumps.update(tmp, true);

      if(params.verbosity > 2) {
	cout << "c FeedCplex Conflict updates: " << tmp << "\n";
	if(params.verbosity > 3)
	  cout << "c FeedCplex Updated Assumps: " << assumps.vec() << "\n";
      }

      feedCplex(iteration, assumps, 1, conflict.size());
      if (solved)
	return;
    }
  }
}

int MaxSolver::feedCplex(int gIter, Assumps& assumps,
			  int nSoFar, size_t sizeSoFar) {
  //accumulate some conflicts for CPLEX. Return number found.
  //Pre: Assumps is not know to be SAT.
  //     last two parameters are for collecting statistics only.

  vector<Lit> conflict;
  int iter {1}; //On call we already found one constraint for CPLEX
  int nCon {nSoFar};
  int nSinceGreedy {1}; //Count CPLEX as a greedy call
  int64_t totalCnfSize { static_cast<int64_t>(sizeSoFar) };

  double start_time = cpuTime();
  while(1) {
    iter++;
    if(iter > params.max_cores_before_cplex
       || cpuTime() - start_time > params.max_cpu_before_cplex)
      return nCon;

    lbool val = satsolve_min(assumps, conflict, params.optcores_cpu_per, params.mus_cpu_lim);
    if(val == l_True) {
      improveModel();
      Weight w = updateUB();
      if(params.verbosity > 0) {
	cout << "c New SAT solution found, cost = " << w
	     << " UB =" << UB() << " LB = " << LB() << "\n";
      }

      if(LB() >= UB()) {
	optFound("c Solved by Sat Solution equal to LB");
	return nCon;
      }
      else if(nSinceGreedy == 0) //greedy solution was solvable. No
	return nCon;		 //more clauses to feed to cplex

      else { //start with new set of assumptions
	auto tmp = greedySoln();
	assumps.init(tmp, params.coreType);
	if(params.sort_assumps == 1) 
	  assumps.sort(blit_gt);
	else if(params.sort_assumps == 2)
	  assumps.sort(blit_lt);

	if(params.verbosity > 3) {
	  cout << "Greedy Solution: " << tmp << "\n";
	  cout << "Assumps after Greedy Solution" << assumps.vec() << "\n";
	}
	nSinceGreedy = 0;
      }
    } 
    else if(val == l_False) {
      nCon++;
      nSinceGreedy++;
      totalCnfSize += conflict.size();
      storeCplexCls(conflict);

      if (params.verbosity > 1
	  || (params.verbosity > 0  && (iter % 50) == 0))
	cout << "c FeedCplex: " << gIter << "." << iter
	     << " (#cons = " << nCon << " ave size = "
	     << totalCnfSize/nCon << ").\n";
      
      auto tmp = getAssumpUpdates(nCon, nSinceGreedy, conflict);
      //Must remove assumptions now that we are adding forced negated bvars
      //assumps.update(tmp, params.fbeq);
      assumps.update(tmp, true);

      if(params.verbosity > 2) {
	cout << "c FeedCplex conflict: " << conflict << "\n";
	cout << "c FeedCplex Conflict updates: " << tmp << "\n";
	if(params.verbosity > 3)
	  cout << "c FeedCplex Updated Assumps: " << assumps.vec() << "\n";
      }
    }
    else { //timed out
      if(params.verbosity > 0) 
	cout << "c feedCplex finding new core timedout\n";
      return nCon;
    }
  }
}


//This routine must be called right after an optimal cplex solution is
//computed.  We know that that solution satisfies all current cores
//(and non-cores).  A cplex solution is a complete setting of Bvars:
//i.e., it is a model.  If each of the new solutions in the pool are
//optimal, then all of them also satisfy all prior cores.

//We can stop any redundant cores from being generated by making sure
//that every solution we examine satisfies all new conflicts
//generated.  On entry we have one new conflict C0---the conflict that
//refuts the original optimal CPLEX solution. So we can discard a
//solution from the pool S0 if it fails to satisfy C0---C0 will block S0
//as well.  Otherwise we can refute S0---or if S0 is optimal and
//satisfiable we can declare S to be a maxsat solution.

//In refuting S0 we obtain another conflict C1. Now for the next
//solution from the pool S1, we should really check that S1 is not
//blocked by either C0 or C1. Similary for Sk from the solution pool
//we should check that it is not blocked by all prior conflicts
//generated in this routine.

//We preform this test as cplex often generated multiple copies of the
//same solution in the solution pool.

void MaxSolver::tryPopulate(vector<Lit>& conflict, double cplexOptSolnWt) {
  //Got conflict for first cplex solution. Try populate and see if we can't
  //get some more conflicts. Return the last one to initiate greedy feeding
  //of cplex.

  //Allow for non-optimal solution in solution pool. But
  //if solution is optimal (equal to the passed optimal solution weight
  //computed from an optimal solve) we can use it to declare that
  //a solution has been found.
  if(params.verbosity > 0)
    cout << "c Trying populate\n";
  int nsolns = cplex->populate(params.cplex_pop_cpu_lim);
  vector<Lit> cplexsoln;
  vector<vector<Lit>> foundConflicts;
  vector<Lit> newConflict;
  vector<Lit> solnMap(bvars.n(), lit_Undef);
  int nadded = 0;
  int nOpt = 0;
  int nOptAdded = 0;

  foundConflicts.push_back(std::move(conflict)); //empties conflict must restore.

  for(int i = 0; i < nsolns; i++) {
    cplex->getPopulatedSolution(i, cplexsoln);
    if(cplexsoln.size() == 0) {
      cout << "c WARNING Cplex populate could not find solution " << i << "\n";
      continue;
    }
    auto solnwt = getWtOfBvars(cplexsoln);
    bool isOpt = (solnwt == cplexOptSolnWt);
    if(isOpt)
      ++nOpt;
    
    for(auto l : cplexsoln) 
      solnMap[bvars.clsIndex(l)] = l;
    bool isBlocked=false;
    for(auto con: foundConflicts) {
      isBlocked = true;
      for(auto l: con) 
	if(solnMap[bvars.clsIndex(l)] == l) 
	  isBlocked = false;
      if(isBlocked) break;
    }
    if(!isBlocked) { //can obtain new conflict from this solution
      ++nadded;
      if(isOpt) ++nOptAdded;
      //Assumps assumps(satsolver, bvars, inMx);
      Assumps assumps(satsolver, bvars);
      assumps.init(cplexsoln, params.coreType);
      if(params.sort_assumps == 1) 
	assumps.sort(blit_gt);
      else if(params.sort_assumps == 2)
	assumps.sort(blit_lt);
      if(satsolve_min(assumps, newConflict, params.noLimit, params.mus_cpu_lim) == l_True) {
	updateUB();
	if(isOpt) {
	  optFound("c Solved by one of Cplex populated models");
	  return;
	}
	else
	  cout << "c Non optimal CPLEX populated model was SAT\n";
      }
      else {
	storeCplexCls(newConflict);
	foundConflicts.push_back(std::move(newConflict));
      }
    }
  }
  if(params.verbosity>0)
    cout << "c populate added " << nadded << " conflicts\n";
  
  conflict = std::move(foundConflicts[0]);
}

vector<Lit> MaxSolver::getAssumpUpdates(int nSinceCplex, int nSinceGreedy,
					vector<Lit>& core) {
  //return a subset of the core to update assumptions. Core should be
  //a conflict returned by trying to see if assumptions are
  //satisfiable...so it will contain only negations of the assumption
  //literals. Uses core for computation---modifies it!
  assert(!(params.coreType == CoreType::cores) || isCore(core));
  
  switch(params.coreRelaxFn) {
  case CoreRelaxFn::maxoccur:
    return vector<Lit> { maxOccurring(core) };
  case CoreRelaxFn::frac:
    return fracOfCore(nSinceCplex, nSinceGreedy, core);
  default:
    return vector<Lit> { core[0] };
  }
}

vector<Lit> MaxSolver::fracOfCore(int nSinceCplex, int nSinceGreedy, vector<Lit> &core) {
  double fracToReturn = params.frac_to_relax;
  int nToReturn {1};
  if(nSinceCplex > params.frac_rampup_start) {
    if(nSinceCplex < params.frac_rampup_end)
      fracToReturn *= (nSinceCplex - params.frac_rampup_start)/(1.0 * (params.frac_rampup_end - params.frac_rampup_start));
    nToReturn = ceil(fracToReturn*((double) core.size()));
  }
  if(nToReturn == 1) 
    return vector<Lit> { maxOccurring(core) };

  //auto maxOccur = [this](Lit l1, Lit l2) { return bLitOccur[bvars.toIndex(l1)] < bLitOccur[bvars.toIndex(l2)]; };
  //use a heap here instead of fully sorting the vector.
  //std::make_heap(core.begin(), core.end(), maxOccur);
  std::make_heap(core.begin(), core.end(), blit_lt);

  vector<Lit> retVec;
  for (int i = 0; i < nToReturn; i++) {
    retVec.push_back(core.front());
    //std::pop_heap(core.begin(), core.end()-i, maxOccur);
    std::pop_heap(core.begin(), core.end()-i, blit_lt);
  }
  if(params.verbosity > 1) 
    cout << "c fracOfCore returns a relaxation of size " << retVec.size() << "\n";
  return retVec;
}

Lit MaxSolver::maxOccurring(const vector<Lit>& core) {
  //return literal of core that appears in largest number of accumulated CPLEX clauses
  Lit max = core[0];
  for(auto l : core) 
    //if(bLitOccur[bvars.toIndex(l)] > bLitOccur[bvars.toIndex(max)])
    //
    if(blit_gt(l, max)) //Note blit_lt(max, l) is not same as blit_gt(l, max)
      max = l;
  return max;
}


void MaxSolver::incrBLitOccurrences(const vector<Lit> &core) {
  for (auto l : core) 
    bLitOccur[bvars.toIndex(l)] += 1;
}


//TODO: Consider unifying the add clause/add new forced bvar
//      across all solvers (including CPLEX).
//      Perhaps a solver class that CPLEX and SAT derive from.
//
bool MaxSolver::cplexAddCls(vector<Lit>&& cls) {
  bool isNonCore = cplex->add_clausal_constraint(cls);
  if(params.verbosity > 2) {
    cout << "c Added clause to Cplex:\n";
    outputConflict(cls);
  }
  return isNonCore;
}

//TODO Better abstraction to facilitate sharing of unit or other clauses between solvers. 
//
void MaxSolver::cplexAddNewForcedBvars() {
  //We pass only forced b-vars to cplex

  cplexNU.update(satsolver);
  vector<Lit>& forced = cplexNU.forced; 

  /*static int notSeen {0};
  vector<Lit> forced { satsolver->getForced(notSeen) }; //Get unprocessed forced
  notSeen  += forced.size();*/

  /*cout << "Cplex Forced units [ ";
  for(auto l : forced) cout << l << "(" << satsolver->curVal(l) << ") ";
  cout << "]\n";*/
  
  int nf {0};
  for(auto l : forced) 
    if(bvars.isBvar(l)) {
      nf++;
      cplexAddCls({l});
      //cout << "Adding unit to CPLEX " << l << " current value " << satsolver->curVal(l) << "\n";
    }
  if (params.verbosity > 0) {
    if(nf > 0)
      cout << "c Add to CPLEX " << nf << " Forced bvars.\n";
  }
}

void MaxSolver::greedyAddNewForcedBvars() {
  //We pass only forced b-vars to the greedy solver

  greedyNU.update(satsolver);
  vector<Lit>& forced = greedyNU.forced; 

  /*static int notSeen {0};
  vector<Lit> forced { satsolver->getForced(notSeen) }; //Get unprocessed forced
  notSeen  += forced.size();*/

  /*cout << "Greedy Forced units [ ";
  for(auto l : forced) cout << l << "(" << satsolver->curVal(l) << ") ";
  cout << "]\n";*/

  int nf {0};
  for(auto l : forced) 
    if(bvars.isBvar(l)) {
      nf++;
      //if(greedysolver)
      greedysolver->addClause({l});
      //else
//	greedySatSolver->addClauseGreedy({l}, false);
      //cout << "Adding unit to GREEDY " << l << " current value " << satsolver->curVal(l) << "\n";
    }
  if (params.verbosity > 0) {
    if(nf > 0)
      cout << "c Add to greedysolver " << nf << " Forced bvars.\n";
  }
}

void MaxSolver::muserAddNewForcedVars() {
  //We pass on ordinary variables and b-variables to the muser. 
  //Note the sat solver might have addition control variables that
  //have been forced on its trail e.g., eqCVar. These should not be
  //sent to the muser.

  muserNU.update(satsolver);
  vector<Lit>& forced = muserNU.forced; 

  /*static int notSeen {0};
  vector<Lit> forced { satsolver->getForced(notSeen) }; //Get unprocessed forced
  notSeen  += forced.size();*/

  if(params.verbosity > 2)
    cout << "Adding forced units to MUSER " << forced << "\n";

  int nf {0};
  for(auto l : forced) 
    //Note muser might not know about l, but we inform it of l and its value
    //in case later on the muser has to deal with clauses involving l.
    //don't add forced control variables
    if((bvars.isBvar(l) || bvars.isOvar(l)) && muser->curVal(l) == l_Undef) {
      nf++;
      if(!muser->addClause({l})) {
	cout << "c ERROR: Adding unit to MUSER " << l << " current value "
	     << muser->curVal(l) << " Caused UNSAT\n";
      }
    }
  if (params.verbosity > 0) {
    if(nf > 0)
      cout << "c Add to muser " << nf << " newly forced vars.\n";
  }
}

void MaxSolver::satSolverAddNewForcedVars() {
  //We pass on ordinary variables and b-variables from the muser to the sat solver. 
  //muser control variables are ignored (They shouldn't be any that get through
  //the getForced interface in any event).

  satNU.update(muser);
  vector<Lit>& forced = satNU.forced; 

  /*static int notSeen {0};
  vector<Lit> forced { muser->getForced(notSeen) }; //Get unprocessed forced
  notSeen  += forced.size();*/

  if(params.verbosity > 2)
    cout << "Adding forced units to satsolver " << forced << "\n";

  int nf {0};
  for(auto l : forced) 
    //don't add control variables
    if((bvars.isBvar(l) || bvars.isOvar(l)) && satsolver->curVal(l) == l_Undef) {
      nf++;
      satsolver->addClause({l});
      //cout << "Adding unit to satSolver " << l << "\n";
    }
  if (params.verbosity > 0) {
    if(nf > 0)
      cout << "c Add to satSolver " << nf << " newly forced from muser.\n";
  }
}

void MaxSolver::satSolverAddBvarsFromSofts() {
  //If we are using only the Fb theory, when a soft is satisfied by forced literals
  //the corresponding b-variable will not be set. Use this routine to add these forced 
  //b-variables to the sat solver. (This allows the sat solver to delete these softs
  //And also to pass the forced b-vars to CPLEX, the muser and the greedy solver
  //perhaps helping them as well.) Note we can only process ordinary variables
  //from the sat solver.

  satBvarNU.update(satsolver);
  vector<Lit>& forced = satBvarNU.forced; 

  /*static int notSeen {0};
  vector<Lit> forced { satsolver->getForced(notSeen) }; //Get unprocessed forced
  notSeen += forced.size();*/
  
  if(params.verbosity > 2)
    cout << "Processing new forced units for adding satisfied softs to satsolver " << forced << "\n";
  
  int nf {0};
  for(auto l : forced) 
    if(bvars.isOvar(l)) {
      for(auto sftIdx : sftSatisfied[toInt(l)]) {
	Lit blit = bvars.litOfCls(sftIdx);
	if(satsolver->curVal(blit) == l_Undef) {
	  ++nf;
	  satsolver->addClause({~blit});
	  //debug
	  //cout << "Adding forced negated blit to satsolver " << ~blit << "\n";
	}
      }
    }
  if(params.verbosity > 0 && nf > 0) 
    cout << "c Add to satsolver " << nf << " forced negated bvars.\n";
}

void MaxSolver::cplexAddNewClauses() {
  if (params.verbosity > 0) {
    cout << "c CPLEX: += " << cplexClauses.size() << " Clauses.\n";
  }
  for(size_t i = 0; i < cplexClauses.size(); i++)
    cplexAddCls(cplexClauses.getVec(i));
  cplexClauses.clear();
}

/*vector<Lit> MaxSolver::getBvarEqs() {
  //MODIFY TO USE UNIT SOFTS DIRECTELY AS BVARS.
  //TODO: Consider converting to variable based indexing.
  //returns mapping from original lits to b-lit equivalents 
  vector<Lit> beqs(theWcnf->nVars()*2, lit_Undef);
  for (size_t i = 0; i < theWcnf->nSofts(); i++) 
    if (theWcnf->softSize(i) == 1) {
      Lit unitL = theWcnf->softs()[i][0];
      beqs[toInt(unitL)] = ~bvars.litOfCls(i); //(l,b) => l == -b
      beqs[toInt(~unitL)] = bvars.litOfCls(i); //(l,b) => -l == b
    }
  return beqs;
  }*/

void MaxSolver::processMutexes() {
  //each vector in mxs is a set of literals that are a mutex.
  //These literals will all be bvars, either cores (b1, b2, b3...) or
  //non cores (-b1, -b2, ...). Insert them in to Cplex and also insert
  //the definitional clauses for the corresponding d-variables.
  //(as seed_equivalence might not have added these due to limits on how
  //many clauses it seeds).

  auto& mxs = theWcnf->getMxs();
  //auto& mxDvars = theWcnf->getMxDvars();

  for(size_t i=0; i < mxs.size(); i++) {
    auto mx = mxs[i];     //get copy
    cplex->add_mutex_constraint(mx);
    /*
    auto dvar = mxDvars[i];
    bool isCore = bvars.isCore(mx[0]);   //to cplex and greedy solvers (here we must also add dvar encoding)
    cout << "c MaxSolver feeding mx " << mx 
	 << " Dvar " << dvar+1 << (isCore ? " core" : " noncore") << "\n";
    //cout << " bin clauses:\n";
    Lit dlit = isCore ? mkLit(dvar) : ~mkLit(dvar);
    setInMutex(dlit, inMxdvar);
    setInMutex(~dlit, inMxdvar);
    vector<Lit> binCls (2);
    binCls[1] = dlit;
    for(auto b : mx) {
      binCls[0] = ~b;
      cplex->add_clausal_constraint(binCls);
      greedySatSolver->addClauseGreedy(binCls, false); //don't use in greedy heuristic
      if(bvars.isCore(b))
	setInMutex(~b,inMxbvar);
      else
	setInMutex(b,inMxbvar);
    }
    //cout << "Mutex = " << mx << "\n";
    cplex->add_mutex_constraint(mx);
    greedySatSolver->addMutex(mx, dvar);
    mx.push_back(~dlit);
    cplex->add_clausal_constraint(mx);
    greedySatSolver->addClauseGreedy(mx, false); //don't use in greedy heuristic
    //cout << "disjunction = " << mx << "\n";*/
  }
}

void MaxSolver::seed_equivalence() {
  vector<vector<Lit>> cplexCoreConstraints;
  vector<vector<Lit>> cplexNonCoreConstraints;
  vector<vector<Lit>> cplexMixedConstraints;
  bool nonCore;
  bool core;
  
  if(params.verbosity > 0)
    cout << "c Before solving sat solver has " << satsolver->getNClauses(0) << " clauses and " 
	 << satsolver->getNClauses(1) << " learnts\n";

  if(params.prepro_output) {
    for(int isLearnt=0; isLearnt < (params.seed_learnts ? 2 : 1); isLearnt++) {
      for(int i =0; i < satsolver->getNClauses(isLearnt); i++) {
	auto seedingCls = satsolver->getIthClause(i, isLearnt);
	cout << (isLearnt ? "l#" : "c#") << i << " [ ";
	for (auto l : seedingCls) {
	  cout << l;
	  if(bvars.isBvar(l))
	    cout << " (B " << bvars.wt(l) << "), ";
	  else
	    cout << ", ";
	}
	cout << "] (" << seedingCls.size() << ")\n";
      }
    }
  }

  size_t cc {0}, cn {0}, cm{0};
  for(int isLearnt=0; isLearnt < (params.seed_learnts ? 2 : 1); isLearnt++) {
    if(isLearnt) {
      //remember stats for non-learnts
      cc = cplexCoreConstraints.size();
      cn = cplexNonCoreConstraints.size();
      cm = cplexMixedConstraints.size();
    }
    for(int i =0; i < satsolver->getNClauses(isLearnt); i++) {
      auto seedingCls = satsolver->getIthClause(i, isLearnt);
      nonCore = false;
      core = false;
      //cout << (isLearnt ? "l#" : "c#") << i << ". " << seedingCls << "\n";
      for(auto l : seedingCls) {
	if (!bvars.isBvar(l)) {
	  seedingCls.clear(); //not seedable
	  break;
	}
	if(bvars.isNonCore(l)) 
	  nonCore = true;
	else
	  core = true;
      }
      /*if(seedingCls.size() > 0)
	cout << "Seeded " << (core ? " core " : " noncore" ) << "\n";*/
      
      if (seedingCls.size() > 0) {
	if(core && !nonCore) 
	  cplexCoreConstraints.push_back(seedingCls);
	else if(!core && nonCore && params.seedType != SeedType::cores) 
	  cplexNonCoreConstraints.push_back(seedingCls);
	else if(params.seedType == SeedType::mixed)
	  cplexMixedConstraints.push_back(seedingCls);
      }
    }

    if(params.verbosity > 0) {
      auto lc  = cplexCoreConstraints.size() -  cc;
      auto ln = cplexNonCoreConstraints.size() - cn;
      auto lm = cplexMixedConstraints.size() - cm;

      cout << "c found " << cc+cn+cm+lc+ln+lm << " seedable constraints from " << (isLearnt ? " learnts\n" : "clauses\n");
      cout << "c from clauses " << cc << " cores " << cn << " noncores " << cm << " mixed\n";
      cout << "c from learnts " << lc << " cores " << ln << " noncores " << lm << " mixed\n";
    }
  }
  
  //Now add the accumulated seed constraints up to the supplied limit.
  //prioritize. cores before nonCores before Mixed.
  //Short constraints before long ones.
  auto vecSizeLt = [](const vector<Lit> &v1, const vector<Lit>& v2){ return v1.size() < v2.size(); };
  auto addUpTo = [vecSizeLt, this](vector<vector<Lit> > &c, size_t &lim, size_t &nAdd) { 
    //add up to lim constraints to cplex. Update lim and number
    //added, return total length of constraints added
    double tl {0};
    if(lim > 0 && c.size() > lim)
      sort(c.begin(), c.end(), vecSizeLt);
    size_t i {0};
    for(i = 0; i < c.size() && i < lim; i++) {
      tl += c[i].size();
      storeCplexCls(c[i]);
    }
    nAdd = i;
    lim -= i;
    return tl;
  };
  size_t nCores {0}, nNonCores {0}, nMixed {0};
  double lCores {0.0}, lNonCores {0.0}, lMixed {0.0};

  size_t limit {static_cast<size_t>(params.seed_max)};
  lCores = addUpTo(cplexCoreConstraints, limit, nCores);
  lNonCores = addUpTo(cplexNonCoreConstraints, limit, nNonCores);
  lMixed = addUpTo(cplexMixedConstraints, limit, nMixed);  

  if (params.verbosity > 0) {
    cout << "c EqSeed: #seed constraints " <<  nCores + nNonCores + nMixed << "\n";
    cout << "c EqSeed: cores       " <<  nCores <<  " Ave length " << (nCores > 0 ? lCores/nCores : 0.0) << "\n";
    cout << "c EqSeed: non-cores   " <<  nNonCores <<  " Ave length " << (nNonCores > 0 ? lNonCores/nNonCores : 0.0) << "\n";
    cout << "c EqSeed: mixed-cores " <<  nMixed <<  " Ave length " << (nMixed > 0 ? lMixed/nMixed : 0.0) << "\n";
  }
}

void MaxSolver::printStatsAndExit(int signum, int exitType) {
  if (!printStatsExecuted) { 
    printStatsExecuted = true;
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
     
    if(signum >= 0) {
      cout << "c INTERRUPTED signal " <<  signum << "\n";
    }
    if(!solved) {
      cout << "c unsolved\n";
      cout << "c Best LB Found: " << LB() << "\n";
      cout << "c Best UB Found: " << UB() << "\n";
      if(params.printBstSoln) {
	  cout << "c Best Model Found:\n";
	  if(haveUBModel) {
	    cout << "c ";
	    for (int i = 0; i < theWcnf->nVars(); i++) 
	      cout << (UBmodel[i] == l_True ? "" : "-")  << i+1 << " ";
	    cout << "\n";
	  }
	  else 
	    cout << "c No Model of hard clauses found\n";
      }
    }

    cout << "c CPLEX: #constraints " << cplex->nCnstr()  << "\n";
    cout << "c CPLEX: Avg constraint size "
	 << cplex->totalCnstrSize()/(double)cplex->nCnstr()  << "\n"; 
    cout << "c CPLEX: #non-core constraints " << cplex->nNonCores() << "\n";
    cout << "c CPLEX: Ave non-core size " 
	 << (cplex->totalNonCore())/((double) (cplex->nNonCores())) << "\n";

    cout << "c SAT: #calls " << satsolver->nSolves() << "\n";
    cout << "c SAT: Total time " << satsolver->total_time() + muser->total_time() << "\n";
    cout << "c SAT: #muser calls " << muser->nSolves() << " ("
	 << muser->nSucc_Solves()*100.0/muser->nSolves() << " % successful)\n";
    cout << "c SAT: Minimize time " << muser->total_time()
	 << " (" << muser->total_time()*100/(satsolver->total_time()+muser->total_time()) << "%)\n";
    cout << "c SAT: Avg constraint minimization "
	 << amountConflictMin/(double) cplex->nCnstr()  << "\n";
    cout << "c CPLEX: #calls " << cplex->nSolves() << "\n";
    cout << "c CPLEX: Total time " << cplex->total_time() << "\n";
//    cout << "c GREEDY: #calls " 
//	 << (greedysolver ? greedysolver->nSolves() : greedySatSolver->nSolves()) << "\n";;
//    cout << "c GREEDY: Total time " 
//	 << (greedysolver ? greedysolver->total_time() : greedySatSolver->total_time()) << "\n";
    cout << "c GREEDY: #calls " << greedysolver->nSolves() << "\n";;
    cout << "c GREEDY: Total time " << greedysolver->total_time() << "\n";

    cout << "c MEM MB: " << mem_used << "\n";
    cout << "c CPU: " << cpu_time << "\n";
  }
  fflush(stdout);
  fflush(stderr);
  _exit(exitType);
}

void MaxSolver::reportCplex(Weight solnWt) {
  if (params.verbosity > 0) { 
    cout <<"c CPLEX: soln cost = " << solnWt
	 << " time = " << cplex->solveTime() << "\n";
  }
}

void MaxSolver::reportSAT_min(lbool result, double iTime, size_t orig_size, int nMins, double mTime, size_t final_size) {
  if (params.verbosity > 1) {
    cout << "c SAT_MIN: " << result;
    if(result==l_False)
      cout << ", In cnf size = " << orig_size << ", reduction = " << orig_size - final_size;
    cout  << ", Init Sat time: " << iTime
	  << ", Min calls: " << nMins
	  << ", Min time: " << mTime << "\n";
  }
}

void MaxSolver::reportForced(const vector<Lit> &forced, Weight wt) {
  if (params.verbosity > 0 && forced.size() > 0) {
    cout << "c Forced Soft Clauses (#" << forced.size() << ", wt = " << wt << "\n";
    if (params.verbosity > 2) 
      outputConflict(forced);
  }
}

lbool MaxSolver::satsolve_min(const Assumps& inAssumps, vector<Lit>& outConflict,
			      double sat_cpu_lim, double mus_cpu_lim) {
  double isatTime {0};
  
  lbool result = (sat_cpu_lim > 0) ?
    satsolver->solveBudget(inAssumps.vec(), outConflict, sat_cpu_lim) :
    satsolver->solve(inAssumps.vec(), outConflict);

  if(params.fb)
    satSolverAddBvarsFromSofts();

  size_t orig_size { outConflict.size() };
  isatTime = satsolver->solveTime();
  muser->startTimer();
  if (result == l_False && params.min_type == 1 && outConflict.size() > 2) {
    int origsize = outConflict.size();
    minimize_muser(outConflict, mus_cpu_lim); 
    amountConflictMin += origsize - outConflict.size();
  }
  reportSAT_min(result, isatTime, orig_size, muser->nSatSolvesSinceTimer(), muser->elapTime(), outConflict.size());
  return result;
}

void MaxSolver::minimize_muser(vector<Lit> &con, double mus_cpu_lim) {
  /* Muser tries to remove lits from end of con first.
     Sort so that better lits to remove are later in the vector.
*/

  /*static auto minConf = [this](Lit l1, Lit l2) {
    int sc1 = bLitOccur[bvars.toIndex(l1)]+1;
    int sc2 = bLitOccur[bvars.toIndex(l2)]+1;
    if(bvars.wt(l1) == 0 && bvars.wt(l2) == 0)
      return sc1 < sc2;
    else
      return bvars.wt(l1)/sc1 > bvars.wt(l2)/sc2;
  };*/

  muserAddNewForcedVars();
  if(!doMin)
    return;

  size_t reduction {0};
  size_t osize {0};

  if(doMin) {
    osize = con.size();
    //std::sort(con.begin(), con.end(), minConf);
    std::sort(con.begin(), con.end(), blit_lt);
    if(mus_cpu_lim > 0)
      muser->musBudget(con, mus_cpu_lim);
    else
      muser->mus(con);
    //debug
    //check_mus(con);
    satSolverAddNewForcedVars();
    if(params.fb)
      satSolverAddBvarsFromSofts();
    reduction = osize - con.size();
  }

  if(osize > 1) {
    mtime += muser->solveTime();
    ++mcalls;
    m_sum_reduced_frac += static_cast<double>(reduction)/static_cast<double>(osize);
  }
  
  doMin = params.mus_min_red <= 0
    //|| (mtime < 124.0) //give muser some time to allow rate computation to be more accurate
    //|| mcalls < 64
    || (mtime < 64.0) //give muser some time to allow rate computation to be more accurate
    || (m_sum_reduced_frac/mcalls) > params.mus_min_red;

  if(params.verbosity > 1)
    cout << "c doMin = " << doMin << " mtime = " << mtime
	 << " average reduction = " << m_sum_reduced_frac/mcalls << "\n";
}

void MaxSolver::check_mus(vector<Lit> &con) {
  //Test to see if con is a MUS (DEBUGGING)
  size_t orig_size = con.size();
  vector<Lit> assumps;
  vector<Lit> critical;
  vector<Lit> tmp;
  auto litHash = [](const Lit l) { return std::hash<int>()(toInt(l)); };
  std::unordered_set<Lit,decltype(litHash)> inCon(con.size(), litHash);
  auto findInCon = [&inCon](Lit l){ return inCon.find(l) == inCon.end(); };
  
   // For sorting the conflict before it is minimized
   //   Can't make all lits in conflict true. Neg bvars:
   //   must make one true == relax one of these
   //   soft clauses. So try to remove low weight neg bvars
   //   so that we must relax a high weight soft.
  
   //   Pos bvar: must make one false == can't relax
   //   one of these softs. So try to remove high weight pos
   //   bvars, so that we are blocked only from relaxing low 
   //   weight softs.

   //   Forcing relaxations is better than blocking.
   //   So try to remove all positives first.

   //   We remove from the end, so sort to put best removals at the end

  // auto mConf = [this](Lit i, Lit j) {
  //   return
  //   (sign(i) && !sign(j))    
  //   || (sign(i) && sign(j) && (bvars.wt(var(i)) < bvars.wt(var(j))))
  //   || (!sign(i) && !sign(j) && (bvars.wt(var(i)) > bvars.wt(var(j)))); };
    
  //std::sort(con.begin(), con.end(), mConf);
  assumps.clear();
  for (size_t i = 0; i < con.size(); i++) 
      assumps.push_back(~con[i]);
  if(satsolver->solve(assumps,tmp) == l_True)
    cout << "check_mus: ERROR mus not unsatisfiable\n";

  while(con.size() > 0) {
    Lit min = con.back();
    con.pop_back();
      
    assumps.clear();
    for (size_t i = 0; i < critical.size(); i++)
      assumps.push_back(~critical[i]);
    for (size_t i = 0; i < con.size(); i++) 
      assumps.push_back(~con[i]);

    if(satsolver->solve(assumps, tmp) == l_True) {
      //min was critical
      critical.push_back(min);
    }
    else {
      inCon.clear();
      for(auto lt : tmp)
	inCon.insert(lt);
     auto p = std::remove_if(con.begin(), con.end(), findInCon);
     con.erase(p, con.end());
    }
  }
  con = critical;
  
  if(con.size() != orig_size) {
    cout << "check_mus: ERROR mus not minimal orig size = " << orig_size
	 << " reduced size = " << con.size() << "\n";
    cout << " conflict = " << con << "\n";
  }
}  

void MaxSolver::outputConflict(const vector<Lit> &con) {
  cout << "conflict clause (" << con.size() << "): ";
  for (size_t i = 0; i < con.size(); i++) {
    satsolver->printLit(con[i]);
    cout << " ";
  }
  cout << "\n";
}

//Currently not used. But if we call satsolver->pruneLearnts 
//This function will be used to determine which learnts to delete
//Potentially inefficient if called frequently...requires copying
//Sat solver's clause into passed std:vector. 
bool MaxSolver::deleteLearntTest(const vector<Lit> &c) const {
  if (c.size() == 2)
    return false;
  //keep hard learnts
  //if (!params.delete_hard_learnts) {
  bool containsBVar = false;
  for (size_t i = 0; i < c.size(); i++) {
    if (bvars.isBvar(c[i])) {
      containsBVar = true;
      break;
    }
  }
  // no b-var==> hard learnt
  if (!containsBVar) {
    return false;
  }
  return true;
}

void MaxSolver::unsatFound() {
  cout << "c Hard Clauses are UNSAT.\n";
  cout << "s UNSATISFIABLE\n";
  updateLB(theWcnf->dimacsTop());
  unsat = true;
  solved = true;
  cout << "c Final LB: " << LB() << "\n";
  cout << "c Final UB: " << UB() << "\n";
  fflush(stdout);
}

void MaxSolver::optFound(std::string reason) {
  cout << reason << "\n";
  Weight solCost = UB() + theWcnf->baseCost();
  Weight intPart;
  auto p = cout.precision();
  if(modf(solCost, &intPart) > 0)
    cout << "o " << solCost << "\n";
  else
    cout << "o " << std::fixed << std::setprecision(0) << solCost << "\n";
  cout.precision(p);
  cout.unsetf(std::ios::fixed);
  cout << "s OPTIMUM FOUND\n";
  solved = true;
  theWcnf->rewriteModelToInput(UBmodel);

  for(size_t i=0; i < UBmodel.size(); i++)
    if(UBmodel[i] == l_Undef)
      UBmodel[i] = l_True; //set unset vars to arbitary value (true)

  printSolution(UBmodel);  
  fflush(stdout);
  int nfalseSofts;
  if(theWcnf->checkModelFinal(UBmodel, nfalseSofts) != UB() + theWcnf->baseCost()) //we cannot use wcnf after this!
    cout << "c ERRROR incorrect model reported" << endl;
  else
      cout << "c Solved: Number of falsified softs = " << nfalseSofts << "\n";
}
  

void MaxSolver::printCurClause(const vector<Lit>& cls) {
  cout << "[";
  for (size_t i = 0; i < cls.size()-1; i++) {
    satsolver->printLit(cls[i]);
    cout << ", ";
  }
  if (cls.size() > 0) 
    satsolver->printLit(cls.back());
  cout << "]";
}


void MaxSolver::printErrorAndExit(const char *msg) {
  cout << msg << "\n";
  printStatsAndExit(-1, 1);
}

void MaxSolver::printSolution(const vector<lbool>& model) {
  // For the Evaluation. Prints the "v " line, which contains the last
  // satisfying assignment found by the SAT solver (only original
  // literals, no b-vars). 
  // Typically model is filled in before calling, but if model is
  // incomplete (contains l_Undef) these vars will be printed as false
  // in the code below.
  if(!params.printSoln)
    return;
  
  cout << "v";
  for (size_t i = 0; i < model.size(); i++) {
    cout << " " << (model[i] == l_True ? "" : "-") << i+1;
  }
  cout << endl;
}

void MaxSolver::configBvar(Var bvar, SatSolver* slv) {
  //Configure any blits after they have been added to the sat solver
  //Should be passed literal appearing in soft clause (i.e.,
  //blit=false ==> enforce clause)
  if(params.preprocess)
    slv->freezeVar(bvar);

  if(!params.bvarDecisions && !bvars.isOvar(bvar))
    //keep unit b-vars (ordinary vars as decisions)
    slv->setDecisionVar(bvar, false);

  //setPolarity determines if sign should be true!  So if bvar appears
  //positively in clause, we want to set its default sign to true
  //(making it false and activating the clause by defaults)

  slv->setPolarity(bvar, bvars.isPos(bvar) ? l_True : l_False);
}

void MaxSolver::addHards(SatSolver* slv) {
  for (size_t i = 0; i < theWcnf->nHards(); i++) {
    if (!slv->addClause(theWcnf->getHard(i))) {
      cout << "c Adding hard clauses caused unsat.\n";
      return;
    }
    for(auto lt : theWcnf->hards()[i])
      if(bvars.isBvar(lt))
	configBvar(var(lt), slv);
  }
}


void MaxSolver::addHards(SatSolver* slv, const vector<int>& indicies) {
  for(auto i : indicies) {
    if (!slv->addClause(theWcnf->getHard(i))) {
      cout << "c Adding hard clauses caused unsat.\n";
      return;
    }
    for(auto lt : theWcnf->hards()[i]) 
      if(bvars.isBvar(lt))
	configBvar(var(lt), slv);
  }
}

void MaxSolver::addSofts(SatSolver* slv) {
  for (size_t i = 0; i < theWcnf->nSofts(); i++) {
    Lit blit = bvars.litOfCls(i);

    /*cout << "Soft clause " << i << " " << theWcnf->getSoft(i) << "\n"
      << "blit = " << blit << "\n";*/

    if(theWcnf->softSize(i) > 1) {
      //Only non-unit softs get added to solver (units are handled in the assumptions)
      vector<Lit> sftCls {theWcnf->getSoft(i)};
      sftCls.push_back(blit);
      if(!slv->addClause(sftCls)) {
	cout << "c ERROR: soft clause " << i << " caused solver UNSAT state!\n";
	printCurClause(sftCls);
	return;
      }
      for(auto lt : sftCls) 
	if(bvars.isBvar(lt))
	  configBvar(var(lt), slv);
    }
  }
}

void MaxSolver::addSofts(SatSolver* slv, const vector<int>& indicies) {
  for (auto i : indicies) {
    Lit blit = bvars.litOfCls(i);
    if(theWcnf->softSize(i) > 1) {
      //Only non-unit softs get added to solver (units are handled in the assumptions)
      vector<Lit> sftCls {theWcnf->getSoft(i)};
      sftCls.push_back(blit);
      if(!slv->addClause(sftCls)) {
	cout << "c ERROR: soft clause " << i << " caused solver UNSAT state!\n";
	printCurClause(sftCls);
	return;
      }
      for(auto lt : sftCls) 
	if(bvars.isBvar(lt))
	  configBvar(var(lt), slv);
    }
  }
}

void MaxSolver::addSoftEqs(SatSolver* slv, bool removable) {
  //add eqs to solver. Optionally make them removable
  //Note all softs processed here should have already been added
  //to the solver to config their b-vars.
  vector<Lit> eqcls(removable ? 3 : 2, lit_Undef);
  for (size_t i = 0; i < theWcnf->nSofts(); i++) 
    if(theWcnf->softSize(i) > 1) {
      if(removable && eqCvarPos == lit_Undef) {
	slv->newControlVar(eqCvar, false); //not a decision variable
	eqCvarPos = mkLit(eqCvar, false);
      }
      Lit bneg = ~bvars.litOfCls(i);
      for(auto l: theWcnf->softs()[i]) {
	eqcls[0] = ~l; eqcls[1] = bneg; 
	if(removable) eqcls[2] = eqCvarPos;
	//note addClause modifies eqcls
	if(!slv->addClause(eqcls)) {
	  cout << "c ERROR: equality clause (" << eqcls[0] << " " 
	       << eqcls[1];
	  if(removable) 
	    cout << " " << eqcls[2];
	  cout << ") causes solver UNSAT state!\n";
	  return;
	}
      }
    }
}

void MaxSolver::addSoftEqs(SatSolver* slv, bool removable,
			   const vector<int>& indicies) {
  //Note all softs processed here should have already been added
  //to the solver to config their b-vars.
  vector<Lit> eqcls(removable ? 3 : 2, lit_Undef);
  for (auto i : indicies) 
    if(theWcnf->softSize(i) > 1) {
      if(removable && eqCvarPos == lit_Undef) {
	slv->newControlVar(eqCvar, false); //not a decision variable
	eqCvarPos = mkLit(eqCvar, false);
      }
      Lit bneg = ~bvars.litOfCls(i);
      for(auto l: theWcnf->softs()[i]) {
	eqcls[0] = ~l; eqcls[1] = bneg; 
      if(removable) eqcls[2] = eqCvarPos;
      //note addClause modifies eqcls
      if(!slv->addClause(eqcls)) {
	cout << "c ERROR: equality clause (" << eqcls[0] << " " 
	     << eqcls[1];
	if(removable) 
	  cout << " " << eqcls[2];
	cout << ") causes satsolver UNSAT state!\n";
	return;
      }
    }
  }
}

void MaxSolver::initSftSatisfied() {
  vector<vector<int>> satByLit(theWcnf->nVars()*2, vector<int>{});
  for(size_t i = 0; i < theWcnf->nSofts(); i++) 
    for(auto lt: theWcnf->softs()[i]) 
      satByLit[toInt(lt)].push_back(i);
  for(auto& v : satByLit)
    sftSatisfied.addVec(v);
  //Debug
  /*cout << "Softs\n";
  cout << theWcnf->softs();
  cout << "\nFinal occurance list\n";
  cout << sftSatisfied;*/
}


void MaxSolver::setNoBvarDecisions() {
  for (size_t i = 0; i < theWcnf->nSofts(); i++) {
    Var b = bvars.varOfCls(i);
    if(!bvars.isOvar(b)) //don't change ordinary b-vars (from units)?
      satsolver->setDecisionVar(b, false);
  }
}

void MaxSolver::improveModel() {
  //Sat solver has found a model. Try to improve the cost of that model by computing a muc.
  if(!params.improve_model)
    return;

  vector<Lit> assumps;
  vector<Lit> branchLits;
  Weight prevWt {0};
  if(params.verbosity  > 1) {
    cout << "c Improving Model\n";
    //cout << "totalClsWt() = " << theWcnf->totalClsWt() << " getSatClsWt() = " << getSatClsWt() << "\n";
    prevWt = theWcnf->totalClsWt() - getSatClsWt();
    cout << "c Current Model weight = " << prevWt << "\n";
  }

  for(size_t i = 0; i < bvars.n(); i++) {
    /*cout << "soft clause #" << i << " litofCls = " << bvars.litOfCls(i) 
      << " model value = " << satsolver->modelValue(bvars.litOfCls(i)) << "\n";*/
    if(satsolver->curVal(bvars.litOfCls(i)) == l_Undef) { //only try to change un-forced b's
      auto tval = satsolver->modelValue(bvars.litOfCls(i));
      if(tval == l_True)
	branchLits.push_back(~bvars.litOfCls(i)); //try to negate these bvars
      else 
	assumps.push_back(~bvars.litOfCls(i)); //these bvars must remain false
    }
  }

  if(params.verbosity > 1) {
    cout << "c assumptions size = " << assumps.size() << " branchlits size = " << branchLits.size() << "\n";
    /*cout << "Assumps = " << assumps << "\n";
      cout << "branchlits = " << branchLits << "\n";*/
  }

  if(params.improve_model_max_size > 0 && static_cast<int>(branchLits.size()) > params.improve_model_max_size)
    return;

  auto val = satsolver->relaxSolve(assumps, branchLits, params.improve_model_cpu_lim);

  if(params.verbosity > 1) {
    cout << "c Relaxation search yielded " << val << "\n";
    Weight newWt = theWcnf->totalClsWt() - getSatClsWt();
    cout << "c Old wt = " << prevWt << " new wt = " << newWt << " improvement = " << prevWt - newWt << "\n";
  }
}

Weight MaxSolver::updateUB() { 
  //return weight of new model...update UB if it is a better model.
  Weight w = getSatClsWt();
  if (!haveUBModel || w > sat_wt) {
    sat_wt = w;
    if(params.verbosity > 0) {
      cout << "c New UB found " << UB() << "\n";
      cout << "c Elapsed time " << cpuTime() - globalStartTime << "\n";
    }
    setUBModel();
    if(params.find_forced)
      findForced();
  }
  return theWcnf->totalClsWt() - w;
}

void MaxSolver::setUBModel() {
  //copy sat solvers model to UBmodel; Note sat solver's model might
  //be incomplete resulting in l_Undef as the value of some variables
  haveUBModel = true;
  for(int i = 0; i < theWcnf->nVars(); i++)
    UBmodel[i] = satsolver->modelValue(i);
  for(size_t i = 0; i < theWcnf->nSofts(); i++)
    UBmodelSofts[i] = tmpModelSofts[i];
}

Weight MaxSolver::getSatClsWt() {
  //return sum of weight of satisfied clauses. 
  //Note sat solver's model might be incomplete.
  //and bvars might not be set.
  Weight w {0.0};
  for(size_t i = 0; i < theWcnf->nSofts(); i++) {
    bool is_sat = false;
    //calling theWcnf->softs() avoids copying soft clauses.
    for(auto ell : theWcnf->softs()[i]) 
      if(satsolver->modelValue(ell) == l_True) {
	is_sat = true;
	break;
      }
    if(is_sat) {
      w += theWcnf->getWt(i);
      tmpModelSofts[i] = l_True;
    }
    else
      tmpModelSofts[i] = l_False;
    /*else {
      cout << i << "-th soft falsified bvar = "
	   << bvars.litOfCls(i) << " value = " 
	   << satsolver->modelValue(bvars.litOfCls(i)) << "\n";
      cout << "[ ";
      for(auto ell : theWcnf->softs()[i]) {
	cout << ell << satsolver->modelValue(ell) << " ";
      }
      cout << "]\n";
      }*/
  }
  //cout << "Computed wt = " << w << " total wt = " << theWcnf->totalClsWt() << "\n";
  return w;
}

Weight MaxSolver::getForcedWt() {
  //return weight of forced b-vars. Note that
  //this works with both fb and fbeq. In fb the solver could set some
  //b-vars arbitrarily. But it can't force them to be true.

  forcedWtNU.update(satsolver);
  vector<Lit>& forced = forcedWtNU.forced;

  /*static int notSeen {0};
  vector<Lit> forced { satsolver->getForced(notSeen) };
  notSeen += forced.size();*/

  for(auto l : forced) {
    if(bvars.isBvar(l)) 
      forced_wt += bvars.wt(l); //If l is negated b-var its wt is zero.
  }
  return forced_wt;
}

Weight MaxSolver::getWtOfBvars(const vector<Lit>& blits) {
  Weight w {0};
  for(auto b : blits) {
    if(bvars.isBvar(b))
      w += bvars.wt(b);
  }
  return w;
}

void MaxSolver::storeCplexCls(const vector<Lit>& cls) {
  //clauses of size 1 are forced in sat solver and will
  //be added by AddNewForcedBvars;
  if(cls.size() <= 1) 
    return;
  cplexClauses.addVec(cls);
  incrBLitOccurrences(cls);
  bool core {true};
  for(auto lt : cls) 
    if(bvars.isNonCore(lt)) {
      core = false;
      break;
    }
  if(core) {
    //if(greedysolver)
    greedysolver->addClause(cls);
    //else
    // greedySatSolver->addClauseGreedy(cls, true); //use in greedy heuristic
  }
  //Try this
  //satsolver->addClause(cls);
}

vector<Lit> MaxSolver::greedySoln() {
  //return a greedy solution of the clauses fed (and pending) to CPLEX
  if(params.verbosity > 0) {
    cout << "c Computing Greedy Solution\n";
  }
  vector<Lit> soln;
  greedyAddNewForcedBvars();
  //if(greedysolver)
  soln = greedysolver->solve();
  /*else {
    auto val = greedySatSolver->solve(); 
    if(val == l_False) 
      cout << "c ERROR. CPLEX clauses have no solution (or greedy solver couldn't find one)\n";
    for(size_t i = 0; i < bvars.n(); i++) {
      Var v = bvars.varOfCls(i);
      lbool val = greedySatSolver->modelValue(v);
      if(val == l_True) 
	soln.push_back(mkLit(v, false));
      else if(val == l_False)
	soln.push_back(mkLit(v, true));
      else if(val == l_Undef)
	soln.push_back(~bvars.litOfCls(i)); //harden clause if no value assigned
    }
  }*/
  if(params.verbosity > 0) {
    cout << "c Greedy: soln cost = " << getWtOfBvars(soln) << "\n";
  }
  return soln;
}

bool MaxSolver::isCore(const vector<Lit>& core) {
  for(auto l : core)
    if(bvars.isNonCore(l))
      return(false);
  return true;
}

void MaxSolver::findForced() {
  //Check if new UB allows any variables to be forced.
  //Try ordinary variables if there are few enough of them
  //else try only b-vars. Does not account for future forced lits changing the implication wt.
  auto nf = nFailedLits;
  auto nb = nForcedByBounds;
  for(size_t i = 0; i < satsolver->nVars(); i++) {
    if(!satsolver->activeVar(i))
      continue;
    for(int sign = 0; sign < 2; sign++) {
      Lit l = mkLit(i, sign);

      /*cout << " Active Lit " << l;
      cout << (impWtIsUnk(l) ? " Unknown Wt " : 
	       (impWtIsUB(l) ? " Upperbound " : " Exact "));
      if(!impWtIsUnk(l) && !impWtIsUB(l) && !impWtIsExact(l))
	cout << " ERROR weight type not set properly\n";
      else if(!impWtIsUnk(l))
      cout << " weight = " << getImpWt(l) << "\n";*/

      if(impWtIsUnk(l)) { //not computed. Compute now
	if(findImpWt(l))
	  break; //was forced
      }
      else if(impWtIsUB(l)) {
	if(getImpWt(l) > UB()) {
	  //potentially forced. Refine now
	  if(findImpWt(l))
	    break;
	}
      }
      else {//is exact
	assert(impWtIsExact(l));
	if(getImpWt(l) > UB()) {
	  satsolver->addClause({~l});
	  ++nForcedByBounds;
	  break;
	}
      }
    }
  }
  if(params.verbosity>0)
    cout << "c findForced found " << nFailedLits-nf << " failed lits and "
	 << nForcedByBounds-nb << " lits forced by bounding\n";
}

bool MaxSolver::findImpWt(Lit l) {
  vector<Lit> imps;
  //compute implied weight of l by UP. Return true if l was forced
  if(!satsolver->findImplications(l, imps)) {
    satsolver->addClause({~l});
    ++nFailedLits;
    return true;
  }
  auto wt = getWtOfBvars(imps);
  if(wt > UB()) {
    satsolver->addClause({~l});
    ++nForcedByBounds;
    return true;
  }
  setImpWt(l, wt, impWtExact);
  for(auto x : imps) 
    if(impWtIsUnk(x) || (impWtIsUB(x) && wt < getImpWt(x))) 
      setImpWt(x, wt, impWtUB);
  return false;
}

bool MaxSolver::BLitOrderLt::operator() (const Lit l1, const Lit l2) const {
  //must be strict weak order:
  
  int oc1 = (*occurCount)[bvars.toIndex(l1)];
  int oc2 = (*occurCount)[bvars.toIndex(l2)];
  double wt1 = bvars.wt(l1);
  double wt2 = bvars.wt(l2);
  bool retval {0};
  
  if(wt1 == 0 && oc1 > 0) {   //l1 is super---satisfies cores at zero cost
    if(wt2 == 0 && oc2 > 0)  //so is l2
      if(oc1 == oc2) 
	retval = (l1 < l2); //order lits the same for gt and lt 
    //when discriminators are equal
      else
	retval = (oc1 < oc2) ^ gt; //XOR: we know that oc1 !=
    //oc2. So if (oc1 < oc2) == 0,
    //then l1 > l2.
    else //l2 is not super
      retval = gt; //l1 > l2
  }
  else if(wt2 == 0 && oc2 > 0) //l1 is not super but l2 is
    retval = !gt; //l1 < l2
  else {
    //Neither is super compute merit
    double m1 {0.0};
    double m2 {0.0};
    
    //note since lits not super wt == 0 ==> oc == 0; no division by 0
    m1 = (oc1==0) ? -wt1 : oc1/wt1; 
    m2 = (oc2==0) ? -wt2 : oc2/wt2;
    
    if(m1 == m2) {
      if(bvars.clsSize(l1) == bvars.clsSize(l2))
	retval =  (l1 < l2);
      else
	retval = (bvars.clsSize(l1) < bvars.clsSize(l2)) ^ gt;
    }
    else
      retval = (m1 < m2) ^ gt;
  }
  return retval;
}  
