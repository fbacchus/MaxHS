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
#include <algorithm>
#include <map>
#include <unordered_set>
#include <zlib.h>
#include <iostream> 
#include <iomanip>


#include "maxhs/core/MaxSolver.h"
#include "maxhs/utils/io.h"
#include "maxhs/ifaces/miniSatSolver.h"
#include "maxhs/ifaces/greedySatSolver.h"
#include "minisat/utils/System.h"

//using namespace Minisat;
using namespace MaxHS;
using namespace MaxHS_Iface;

using std::endl;
using std::cout;

MaxSolver::MaxSolver(Wcnf *f) :
  bvars {f},
  theWcnf {f},
  satsolver {new MaxHS_Iface::miniSolver{}},
  greedysolver {new MaxHS_Iface::GreedySolver{bvars}},
  muser {new MaxHS_Iface::Muser{theWcnf, bvars}},
  cplex {new Cplex{bvars}},
  sat_wt {0.0},
  lower_bnd {0.0},
  hards_are_sat { l_Undef},
  UBmodel(theWcnf->nOrigVars(), l_Undef),
  

  eqCvar {static_cast<Var>(theWcnf->nOrigVars() + theWcnf->nSofts())},
  nextNewVar {eqCvar+1},
  amountConflictMin (0),
  bLitOccur (bvars.nlits(), 0),
  cplexClauses {},
  sftSatisfied {},
  solved (false),
  unsat (false)
  { 
    params.instance_file_name = theWcnf->fileName();
    if(!cplex->is_valid())
       cout << "c ERROR. Problem initializing CPLEX solver\n";
  }

MaxSolver::~MaxSolver() {
  if (satsolver) 
    delete satsolver;
  if (greedysolver)
    delete greedysolver;
  if (cplex)
    delete cplex;
}

void MaxSolver::solve_maxsat() {
  //1. Compute an initial lower and upper bound by solving
  //   $F_b^{eq}$ (the reified theory). 
  addHards(satsolver);
  addSofts(satsolver, params.bvarDecisions);    
  addSoftEqs(satsolver, params.fb);  //removable softs if using Fb
  initSftSatisfied(); 

  lbool val = params.fb ?
    satsolver->solve(activateSoftEqLit())
    : satsolver->solve();
  hards_are_sat = val;
  if(val == l_False) {
    unsatFound();
    return;
  }
  cout << "c Init Bnds: SAT Time " << satsolver->solveTime() << "\n";

  //update Bounds
  updateLB(getForcedWt()); //get forced weight
  updateUB();

  if(LB() >= UB()) {
    optFound("c Solved by Init Bnds.");
    return;
  }
  cout << "c Init Bnds: LB = " << LB() << " UB = " << UB() << "\n";
  if (params.verbosity > 0) {
    cout << "c Init Bnds: Forced " << satsolver->nAssigns() << " literals.\n";
  }
  if(params.fb) 
    satSolverAddBvarsFromSofts();

  //2. Initialize CPLEX and seed constraints. 
  //cplex->initCplex(bvars.getvars(), theWcnf->softWts());
  cplexAddNewForcedBvars();

  if (params.seedType != SeedType::none)
    seed_equivalence();

  //3. Clean up

  if(params.fb)
    rmSoftEqs(satsolver); 

  if (!satsolver->simplify()) 
    printErrorAndExit("c ERROR: UNSAT detected when simplify clauses");

  //4. Do disjoint Phase if required
  if (params.dsjnt_phase)
    disjointPhase();

  //5. Now solve.
  seqOfSAT_maxsat();
}

void MaxSolver::disjointPhase() {
  Assumps assumps(satsolver, bvars);
  int num {0};
  int len {0};
  
  if (params.verbosity > 0) 
    cout << "c Disjoint Phase\n";

  double beginTime = cpuTime();
  assumps.initAllSofts();
  vector<Lit> conflict;
  while(satsolve_min(assumps, conflict, params.dsjnt_cpu_per_core, params.dsjnt_mus_cpu_lim)
	== l_False) {

    if(params.verbosity > 1)
      cout << "c Disjoint Conflict size = " << conflict.size() << "\n";
    if(params.verbosity > 2)
      cout << "c conflict = " << conflict << "\n";

    storeCplexCls(conflict); 
    assumps.update(conflict, params.fbeq);
    num++;
    len += conflict.size();
  }
  //update Bounds (only UB could have changed)
  updateUB();
  
  if (params.verbosity > 0) {
    cout << "c Dsjnt: #Cores " << num << "\n";
    cout << "c Dsjnt: Avg Core Size " <<  len/((double) num) << "\n";
    cout << "c Dsjnt: Time " << cpuTime() - beginTime << "\n";
  }
}

void MaxSolver::seqOfSAT_maxsat() {
  vector<Lit> cplexsoln;
  vector<Lit> conflict;
  Assumps assumps(satsolver, bvars);
  int iteration {0};

  while (1) { //exit by return
    //1. Call Cplex
    if (params.verbosity > 0)
      cout << "c **********Iter: " << iteration << "\n"; 
    iteration++;

    //Update Cplex
    cplexAddNewForcedBvars();
    cplexAddNewClauses();
    Weight cplexSolveResult = cplex->solve(cplexsoln);
    if (cplexSolveResult < 0) {
      printErrorAndExit("c ERROR: Cplex::solve() failed");
    }
    reportCplex(cplexSolveResult);

    //2. Update and check Bounds
    updateLB(getWtOfBvars(cplexsoln));
    if(LB() >= UB()) {
      optFound("c Solved by detecting LB>=UB.");
      return;
    }
    cout << "c Bnds: LB = " << LB() << " UB = " << UB() << "\n";
    
    //3. Set up assumptions.
    assumps.init(cplexsoln, params.coreType);
    if(params.verbosity > 3) {
      cout << "cplex solution: " << cplexsoln << "\n";
      cout << "c assumps after Cplex soln: " << assumps.vec() << "\n";
    }
	
    //4. Check if CPLEX's model yields sat
    if(satsolve_min(assumps, conflict, params.noTimeLimit, params.mus_cpu_lim) == l_True) {
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

      auto tmp = getAssumpUpdates(1, 1, conflict);
      assumps.update(tmp, params.fbeq);
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

void MaxSolver::feedCplex(int gIter, Assumps& assumps,
			  int nSoFar, size_t sizeSoFar) {
  //accumulate some conflicts for CPLEX. 
  //Pre: Assumps is not know to be SAT.
  //     last two parameters are for collecting statistics only.

  vector<Lit> conflict;
  int iter {1}; //On call we already found one constraint for CPLEX
  int nCon {nSoFar};
  int nSinceGreedy {1}; //Count CPLEX as a greedy call
  int64_t totalCnfSize { static_cast<int64_t>(sizeSoFar) };
/*  const int gsN {4};
  Weight gsWts[gsN] = {};
  Weight gsTotalWt {0.0};
  int gsIndex {0};*/

  while(1) {
    iter++;
    if(iter > params.max_before_cplex)
      return;

    lbool val = satsolve_min(assumps, conflict, params.optcores_cpu_per, params.mus_cpu_lim);
    if(val == l_True) {
      Weight w = updateUB();
      if(params.verbosity > 0) {
	cout << "c New SAT solution found, cost = " << w
	     << " UB =" << UB() << " LB = " << LB() << "\n";
      }

      if(LB() >= UB()) {
	optFound("c Solved by Sat Solution equal to LB");
	return;
      }
      else if(nSinceGreedy == 0) //greedy solution was solvable. No
	return;			 //more clauses to feed to cplex

      else { //start with new set of assumptions
	auto tmp = greedySoln();

	//return for another CPLEX soln. if greedy solutions are not good.
	/*Weight solWt = getWtOfBvars(tmp);
	gsTotalWt += solWt - gsWts[gsIndex];
	gsWts[gsIndex] = solWt;
	gsIndex = (gsIndex+1) % gsN;
	if(gsTotalWt/gsN > UB()) {
	  if(params.verbosity > 0) {
	  cout << "c Recent Ave Greedy Solution wt is greater than UB,"
	           " returning to call CPLEX\n";
	  }
	  return;
	}
	*/
	assumps.init(tmp, params.coreType);
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
	     << totalCnfSize/nCon << ")\n";
      
      auto tmp = getAssumpUpdates(nCon, nSinceGreedy, conflict);
      assumps.update(tmp, params.fbeq);

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
      return;
    }
  }
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

  auto maxOccur = [this](Lit l1, Lit l2) { return bLitOccur[bvars.toIndex(l1)] < bLitOccur[bvars.toIndex(l2)]; };
  //use a heap here instead of fully sorting the vector.
  std::make_heap(core.begin(), core.end(), maxOccur);

  vector<Lit> retVec;
  for (int i = 0; i < nToReturn; i++) {
    retVec.push_back(core.front());
    std::pop_heap(core.begin(), core.end()-i, maxOccur);
  }
  if(params.verbosity > 1) 
    cout << "c fracOfCore returns a relaxation of size " << retVec.size() << "\n";
  return retVec;
}

Lit MaxSolver::maxOccurring(const vector<Lit>& core) {
  //return literal of core that appears in largest number of accumulated CPLEX clauses
  Lit max = core[0];
  for(auto l : core) 
    if(bLitOccur[bvars.toIndex(l)] > bLitOccur[bvars.toIndex(max)])
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
bool MaxSolver::cplexAddCls(const vector<Lit> &cls) {
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
  static int notSeen {0};
  vector<Lit> forced { satsolver->getForced(notSeen) }; //Get unprocessed forced
  notSeen  += forced.size();

  /*cout << "Cplex Forced units [ ";
  for(auto l : forced) cout << l << "(" << satsolver->curVal(l) << ") ";
  cout << "]\n";*/


  int nf {0};
  vector<Lit> unitB(1,lit_Undef);
  for(auto l : forced) 
    if(bvars.isBvar(l)) {
      nf++;
      unitB[0]=l;
      cplexAddCls(unitB);

      //cout << "Adding unit to CPLEX " << unitB << " current value " << satsolver->curVal(unitB[0]) << "\n";

    }
  if (params.verbosity > 0) {
    if(nf > 0)
      cout << "c Add to CPLEX " << nf << " Forced bvars.\n";
  }
}

void MaxSolver::greedyAddNewForcedBvars() {
  //We pass only forced b-vars to the greedy solver
  static int notSeen {0};
  vector<Lit> forced { satsolver->getForced(notSeen) }; //Get unprocessed forced
  notSeen  += forced.size();

  /*cout << "Greedy Forced units [ ";
  for(auto l : forced) cout << l << "(" << satsolver->curVal(l) << ") ";
  cout << "]\n";*/

  int nf {0};
  vector<Lit> unitB(1,lit_Undef);
  for(auto l : forced) 
    if(bvars.isBvar(l)) {
      nf++;
      unitB[0]=l;
      greedysolver->addClause(unitB);

      //cout << "Adding unit to GREEDY " << unitB << " current value " << satsolver->curVal(unitB[0]) << "\n";


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

  static int notSeen {0};
  vector<Lit> forced { satsolver->getForced(notSeen) }; //Get unprocessed forced
  notSeen  += forced.size();

  if(params.verbosity > 2)
    cout << "Adding forced units to MUSER " << forced << "\n";

  int nf {0};
  vector<Lit> unit(1,lit_Undef);
  for(auto l : forced) 
    //Note muser might not know about l, but we inform it of l and its value
    //in case later on the muser has to deal with clauses involving l.
    if((bvars.isBvar(l) || bvars.isOvar(l)) && muser->curVal(l) == l_Undef) {
      nf++;
      unit[0]=l;
      if(!muser->addClause(unit)) {
	cout << "c ERROR: Adding unit to MUSER " << unit << " current value "
	     << muser->curVal(unit[0]) << " Caused UNSAT\n";
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
  static int notSeen {0};
  vector<Lit> forced { muser->getForced(notSeen) }; //Get unprocessed forced
  notSeen  += forced.size();

  if(params.verbosity > 2)
    cout << "Adding forced units to satsolver " << forced << "\n";

  int nf {0};
  vector<Lit> unit(1,lit_Undef);
  for(auto l : forced) 
    if((bvars.isBvar(l) || bvars.isOvar(l)) && satsolver->curVal(l) == l_Undef) {
      nf++;
      unit[0]=l;
      satsolver->addClause(unit);
      //cout << "Adding unit to satSolver " << unit << "\n";
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
  //and also to pass the forced b-vars to CPLEX, the muser and the greedy solver
  //perhaps helping them as well.) Note we can only process ordinary variables
  //from the sat solver.
  static int notSeen {0};
  vector<Lit> forced { satsolver->getForced(notSeen) }; //Get unprocessed forced
  notSeen += forced.size();
  
  if(params.verbosity > 2)
    cout << "Processing new forced units for adding satisfied softs to satsolver " << forced << "\n";
  
  int nf {0};
  vector<Lit> unit(1, lit_Undef);
  for(auto l : forced) 
    if(bvars.isOvar(l)) {
      for(auto sftIdx : sftSatisfied[toInt(l)]) {
	Lit blit = bvars.litOfCls(sftIdx);
	if(satsolver->curVal(blit) == l_Undef) {
	  ++nf;
	  unit[0] = ~blit;
	  satsolver->addClause(unit);
	  //debug
	  //cout << "Adding forced negated blit to satsolver " << ~blit << "\n";
	}
      }
    }
  if(params.verbosity > 0 && nf > 0) 
    cout << "c Add to satsolver " << nf << " forced negated bvars.\n";
}

void MaxSolver::cplexAddNewClauses() {
  if (params.verbosity > 0) 
    cout << "c CPLEX: += " << cplexClauses.size() << " Clauses.\n";
  for(size_t i = 0; i < cplexClauses.size(); i++)
    cplexAddCls(cplexClauses.getVec(i));
  cplexClauses.clear();
}

vector<Lit> MaxSolver::getBvarEqs() {
  //TODO: Consider converting to variable based indexing.
  //returns mapping from original lits to b-lit equivalents 
  vector<Lit> beqs(theWcnf->nOrigVars()*2, lit_Undef);
  for (size_t i = 0; i < theWcnf->nSofts(); i++) 
    if (theWcnf->softs()[i].size() == 1) {
      Lit unitL = theWcnf->softs()[i][0];
      beqs[toInt(unitL)] = ~bvars.litOfCls(i); //(l,b) => l == -b
      beqs[toInt(~unitL)] = bvars.litOfCls(i); //(l,b) => -l == b
    }
  return beqs;
}

void MaxSolver::seed_equivalence() {
  //Forced Bvars have already been added to CPLEX.
  vector<Lit> beqs { getBvarEqs() };
  vector<Lit> seedingCls;
  int prev_numConstraints = cplexClauses.size();
  int nNonCores {0};
  double nonCoreLength {0};
  vector<vector<Lit>> cplexConstraints;
  bool nonCore;
  bool core;

  for(size_t i = 0; i < theWcnf->nHards(); i++) {
    seedingCls.clear();
    nonCore = false;
    core = false;
    for(auto l : theWcnf->hards()[i]) {
      lbool lVal = satsolver->curVal(l);
      if(lVal == l_False)
	continue;
      Lit eqB = beqs[toInt(l)];
      if (eqB == lit_Undef || lVal == l_True) {
	seedingCls.clear();
	break;
      }
      else {
	seedingCls.push_back(eqB);
	if(bvars.isNonCore(eqB)) 
	  nonCore = true;
	else
	  core = true;
	if(nonCore && params.seedType == SeedType::cores) {
	  seedingCls.clear();
	  break;
	}
      }
    }
    if (seedingCls.size() > 0) {
      cplexConstraints.push_back(seedingCls);
      if(nonCore) {
	nNonCores++;
	nonCoreLength += seedingCls.size();
      }
    }
  }
  
  for(size_t i = 0; i < theWcnf->nSofts(); i++) {
    if (theWcnf->softs()[i].size() == 1 || 
	satsolver->curVal(bvars.litOfCls(i)) != l_Undef)
      //unit softs yield tautological constraints.  If the clause is
      //satisfied its blit is l_false, and there is no constraint.  If
      //the clause is falsified its blit is l_true and the constraints
      //is already in cplex's model (via the forced Blit added with
      //AddNewlyForcedBvars())
      continue;
    seedingCls.clear();
    nonCore = false;
    core = false;
    for(auto l : theWcnf->softs()[i]) {
      lbool lVal = satsolver->curVal(l);
      if(lVal == l_False)
	continue;
      Lit eqB = beqs[toInt(l)];
      if (eqB == lit_Undef) {
	seedingCls.clear();
	break;
      }
      else {
	seedingCls.push_back(eqB);
	if(bvars.isNonCore(eqB)) 
	  nonCore=true;
	else 
	  core=true;
	if(nonCore && params.seedType == SeedType::cores) {
	  seedingCls.clear();
	  break;
	}
      }
    }
    if (seedingCls.size() > 0) {
      seedingCls.push_back(bvars.litOfCls(i)); //soft clauses include their b-lit.
      cplexConstraints.push_back(seedingCls);
      if(nonCore) {
	nNonCores++;
	nonCoreLength += seedingCls.size();
      }
    }
  }
  
  if(cplexConstraints.size() > static_cast<size_t>(params.seed_max))
    sort(cplexConstraints.begin(), cplexConstraints.end(),
	 [](const vector<Lit> &v1, const vector<Lit>& v2){return v1.size() < v2.size();}
	 );

  for(size_t i = 0; i < cplexConstraints.size() && i < static_cast<size_t>(params.seed_max); i++)
    storeCplexCls(cplexConstraints[i]);

  if (params.verbosity > 0) {
    cout << "c EqSeed: #seed constraints " <<  cplexClauses.size() - prev_numConstraints << "\n";
    cout << "c EqSeed: #non-cores " <<  nNonCores << "\n";
    cout << "c EqSeed: Average non-core length " << (nNonCores > 0 ? nonCoreLength/nNonCores : 0) << "\n";
  }
}

void MaxSolver::printStatsAndExit(int signum, int exitType) {
  static int onceOnly = 0;
  if (onceOnly == 0) { 
    onceOnly = 1;
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
     
    if(signum >= 0) {
      cout << "c INTERRUPTED signal " <<  signum << "\n";
    }
    if(hards_are_sat == l_Undef)
      cout << "c No model of hard clauses found\n";
    else if(!solved) {
      cout << "c Best LB Found: " << LB() << "\n";
      cout << "c Best UB Found: " << UB() << "\n";
      if(params.printBstSoln) {
	cout << "c Best Model Found:\n";
	cout << "c ";
	for (int i = 0; i < theWcnf->nOrigVars(); i++) 
	  cout << (UBmodel[i] == l_True ? "" : "-")  << i+1 << " ";
	cout << "\n";
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

void MaxSolver::reportForced(vector<Lit> &forced, Weight wt) {
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
  static int64_t mreduced {0};
  static int mcalls {0};
  static double mtime {0.0};
  static auto minConf = [this](Lit l1, Lit l2) {
    int sc1 = bLitOccur[bvars.toIndex(l1)]+1;
    int sc2 = bLitOccur[bvars.toIndex(l2)]+1;
    if(bvars.wt(l1) == 0 && bvars.wt(l2) == 0)
      return sc1 < sc2;
    else
      return bvars.wt(l1)/sc1 > bvars.wt(l2)/sc2;
  };
  static bool doMin {true};

  muserAddNewForcedVars();
  if(!doMin)
    return;

  size_t reduction {0};
  size_t osize {0};

//  if(mcalls < 64 || params.mus_lits_per_sec <= 0 ||
//     mreduced*1.0/mtime > params.mus_lits_per_sec) 
    
  if(doMin) {
    osize = con.size();
    std::sort(con.begin(), con.end(), minConf);
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

  mtime += muser->solveTime();
  ++mcalls;
  mreduced += reduction;
  
  doMin = params.mus_lits_per_sec <= 0
    || (mtime < 50.0) //give muser some time to allow rate computation to be more accurate
    || mreduced*1.0/mtime > params.mus_lits_per_sec;

  if(params.verbosity > 1)
    cout << "c doMin = " << doMin << " mcalls = " << mcalls
	 << " reduction rate = " << mreduced*1.0/mtime << "\n";
}

void MaxSolver::check_mus(vector<Lit> &con) {
  //Test to see if it is a con is a MUS
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
    satsolver->printLit(con[i]); printf(" ");
  }
  printf("\n");
  fflush(stdout);
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
  printf("o %.0lf\n", UB());
  printf("s OPTIMUM FOUND\n");
  printSolution(UBmodel);  
  cout << "c Final LB: " << LB() << "\n";
  cout << "c Final UB: " << UB() << "\n";
  solved = true;
  fflush(stdout);
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
  // literals, no b-vars). Note that model might be incomplete.  with
  // l_Undef for some variables. Print these as an arbitrary value (in
  // the code below they are printed as false)
  if(!params.printSoln)
    return;
  
  printf("v");
  for (int i = 0; i < theWcnf->nOrigVars(); i++) {
    printf(" %s%d", model[i] == l_True ? "" : "-", i+1);
  }
  printf("\n");
  fflush(stdout);
}

void MaxSolver::addHards(SatSolver* slv) {
  for (size_t i = 0; i < theWcnf->nHards(); i++) {
    if (!slv->addClause(theWcnf->getHard(i))) {
      cout << "c Adding hard clauses caused unsat.\n";
      return;
    }
  }
}

void MaxSolver::addHards(SatSolver* slv, const vector<int>& indicies) {
  for(auto i : indicies) {
    if (!slv->addClause(theWcnf->getHard(i))) {
      cout << "c Adding hard clauses caused unsat.\n";
      return;
    }
  }
}

void MaxSolver::addSofts(SatSolver* slv, bool b_var_d) {
  for (size_t i = 0; i < theWcnf->nSofts(); i++) {
    Lit blit = bvars.litOfCls(i);
    //set polarity to make soft clause active, i.e., falsify blit
    slv->newControlVar(bvars.varOfCls(i), b_var_d, 
			     sign(blit) ? l_True : l_False);
    vector<Lit> sftCls {theWcnf->getSoft(i)};
    sftCls.push_back(blit);
    if(!slv->addClause(sftCls)) {
      cout << "c ERROR: soft clause " << i << " caused solver UNSAT state!\n";
      printCurClause(sftCls);
      return;
    }
  }
}

void MaxSolver::addSofts(SatSolver* slv, bool b_var_d,
			 const vector<int> & indicies) {
  for (auto i : indicies) {
    Lit blit = bvars.litOfCls(i);
    slv->newControlVar(bvars.varOfCls(i), b_var_d,
		       sign(blit) ? l_True : l_False);
    vector<Lit> sftCls {theWcnf->getSoft(i)};
    sftCls.push_back(blit);
    if(!slv->addClause(sftCls)) {
      cout << "c ERROR: soft clause " << i << " caused solver UNSAT state!\n";
      printCurClause(sftCls);
      return;
    }
  }
}

void MaxSolver::addSoftEqs(SatSolver* slv, bool removable) {
  //add eqs to solver. Optionally make them removable
  if(removable) {
    slv->newControlVar(eqCvar, false); //not a decision variable
  }
  Lit eqCvarPos = mkLit(eqCvar, false); 

  vector<Lit> eqcls(removable ? 3 : 2, lit_Undef);
  for (size_t i = 0; i < theWcnf->nSofts(); i++) {
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
  //TODO simplify if can always use fbeq.
  if(removable) {
    slv->newControlVar(eqCvar, false); //not a decision variable
   }
  Lit eqCvarPos = mkLit(eqCvar, false); 
  
  vector<Lit> eqcls(removable ? 3 : 2, lit_Undef);
  for (auto i : indicies) {
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
  vector<vector<int>> satByLit(theWcnf->nOrigVars()*2, {});
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
    satsolver->setNoDecision(b);
  }
}

Weight MaxSolver::updateUB() { 
  //return weight of new model...update UB if it is a better model.
  Weight w = getSatClsWt();
  if (w > sat_wt) {
    sat_wt = w;
    setUBModel();
  }
  return theWcnf->totalWt() - w;
}

void MaxSolver::setUBModel() {
  //copy sat solvers model to UBmodel; Note sat solver's model might
  //be incomplete resulting in l_Undef as the value of some variables
  for(int i = 0; i < theWcnf->nOrigVars(); i++)
     UBmodel[i] = satsolver->modelValue( static_cast<Var>(i) );
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
    if(is_sat) 
      w += theWcnf->getWt(i);
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
  //cout << "Computed wt = " << w << " total wt = " << theWcnf->totalWt() << "\n";
  return w;
}

Weight MaxSolver::getForcedWt(int trail_index) {
  //return weight of b-vars forced at trail_index and below
  vector<Lit> forced { satsolver->getForced(trail_index) };
  Weight w {0};
  for(auto l : forced) {
    if(bvars.isBvar(l)) 
      w += bvars.wt(l);
  }
  return w;
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
  if(cls.size() > 1) {
    cplexClauses.addVec(cls);
    incrBLitOccurrences(cls);
    if(!params.greedy_cores_only)
      greedysolver->addClause(cls);
    else {
      bool core {true};
      for(auto lt : cls) 
	if(bvars.isNonCore(lt)) {
	  core = false;
	  break;
	}
      if(core)
	greedysolver->addClause(cls);
    }

    //Try this
    //satsolver->addClause(cls);
  }
}

vector<Lit> MaxSolver::greedySoln() {
  //return a greedy solution to the clauses fed to CPLEX including those about to be fed
  if(params.verbosity > 0) {
    cout << "c Computing Greedy Solution\n";
  }
  greedyAddNewForcedBvars();
  auto val = greedysolver->solve(); 
  if(val == l_False) 
    cout << "c ERROR. CPLEX clauses have no solution (or greedy solver couldn't find one)\n";
  vector<Lit> soln;
  for(size_t i = 0; i < theWcnf->nSofts(); i++) {
    Var v = bvars.varOfCls(i);
    lbool val = greedysolver->modelValue(v);
    if(val == l_True) 
      soln.push_back(mkLit(v, false));
    else if(val == l_False)
      soln.push_back(mkLit(v, true));
    else if(val == l_Undef)
      soln.push_back(~bvars.litOfCls(i)); //harden clause if no value assigned
  }
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
