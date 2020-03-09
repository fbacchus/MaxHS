/***********[muser.cc]
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

#include <vector>
#include <algorithm>
#include "maxhs/ifaces/muser.h"
#include "maxhs/utils/io.h"
#include "maxhs/utils/Params.h"

#ifdef GLUCOSE
#include "glucose/utils/Options.h"
#else
#include "minisat/utils/Options.h"
#endif

using namespace MaxHS_Iface;

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

using namespace Minisat;

Muser::Muser(const Wcnf* f, Bvars& b):
  theWcnf{f}, bvars (b), timer {0}, totalTime {0},
  prevTotalTime {0},  stime{-1}, solves {0}, succ_solves {0}, prevSolves{0},
  satSolves {0}, prevSatSolves{0}
{
  bool doPre = doPreprocessing();
  if(!doPre)
    eliminate(true);

  //Initialize MUS underlying sat solver with hard clauses of Wcnf.
  vec<Lit> ps;
  int nHards {0};

  for(auto hc : theWcnf->hards()) {
    ps.clear();
    nHards++;
    for(auto lt: hc) {
      ensure_mapping(var(lt));
      ps.push(ex2in(lt));
    }

    //cout << "Muser: adding hard clause " << ps << "\n";

    if(!addClause_(ps)) 
      cout << "c WARNING Adding Hard clauses to muser caused unsat.\n";
  }
  if(params.mverbosity > 0)
    cout << "c Muser added " << nHards << " hard clauses\n";

  if(doPre) {
    for(auto sc: theWcnf->softs())
      for(auto lt: sc) { //the muser must freeze all variables appearing in soft clauses
	Var v = var(ex2in(lt));
	if(v != var_Undef) { //if var not in hards the initial eliminate will not affect
	  //cout << " MUSER freezing " << v << "\n";
	  freezeVar(v);
	}
      }
    auto start = cpuTime();
    eliminate(true);
    if(params.verbosity > 0)
      cout << "c Muser Preprocess eliminated " << eliminated_vars << " variables. took " << cpuTime()-start << " sec.\n";
  }
}

bool Muser::doPreprocessing() const {
  //test if we should do preprocessing.
  //We have to freeze all vars appearing in the softs. So if this spans all variables we won't
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
    for(auto lt: sc)
      if(varStatus[var(lt)] == nfrz) {
	++toBeFrozen;
	varStatus[var(lt)] = dne;
      }
  if(params.verbosity > 0)
    cout << "c Muser: Vars of hards = " << totalVars << " vars to be frozen = " << toBeFrozen << "\n";
  return toBeFrozen < totalVars;
}


inline Lit Muser::in2ex(Lit lt) const
{
  if(var(lt) >= static_cast<Var>(in2ex_map.size()) ||
     in2ex_map[var(lt)] == var_Undef)
    return lit_Undef;
  else
    return mkLit(in2ex_map[var(lt)], sign(lt));
}

inline Var Muser::in2ex(Var v) const
{
  if(v >= static_cast<Var>(in2ex_map.size()))
    return var_Undef;
  else
    return in2ex_map[v];
}
  
inline void Muser::in2ex(const vec<Lit> &from, vector<Lit> &to) const 
{
  to.clear();
  for(int i = 0; i < from.size(); i++)
    to.push_back(in2ex(from[i]));
}
  
inline void Muser::in2ex(const vec<Var> &from, vector<Var> &to) const 
{
  to.clear();
  for(int i = 0; i < from.size(); i++)
      to.push_back(in2ex(from[i]));
}
  
inline Var Muser::ex2in(Var v) const 
{
  if(v >= static_cast<Var>(ex2in_map.size()))
      return var_Undef;
    else
      return ex2in_map[v]; 
}
  
inline Lit Muser::ex2in(Lit lt) const
{
  if(var(lt) >= static_cast<Var>(ex2in_map.size()) ||
     ex2in_map[var(lt)] == var_Undef)
    return lit_Undef;
  else
      return mkLit(ex2in_map[var(lt)], sign(lt));
}

inline bool Muser::inSolver(Lit lt) const
{
  return inSolver(var(lt));
}

inline bool Muser::inSolver(Var v) const 
{
  return ex2in(v) != var_Undef;
}

void Muser::ensure_mapping(const Var ex)
{
  if (ex >= static_cast<Var>(ex2in_map.size()))
    ex2in_map.resize(ex+1,var_Undef);
  
  if(ex2in_map[ex] == var_Undef) {
    Var in {newVar()};
    ex2in_map[ex] = in;
    if (in >= static_cast<Var>(in2ex_map.size()))
      in2ex_map.resize(in+1, var_Undef);
    in2ex_map[in] = ex;
  }
}

vector<Lit> Muser::getForced(int index) {
  //if(params.mverbosity > 3) 
  //  cout << "getForced: forced.size() = " << forced.size() << "\n";
  updateForced(forced);
  //if(params.mverbosity > 3)
  //  cout <<  "getForced new forced.size() = " << forced.size() << "\n"
  // <<  " forced = " << forced << "\n";

  vector<Lit> tmp;
  for(size_t i = index; i < forced.size(); i++)
    tmp.push_back(in2ex(forced[i]));
  return tmp;
}

void Muser::updateForced(vector<Lit>& frc) {
  int limit = trail_lim.size() > 0 ?
    trail_lim[0] : trail.size();
  int i {0};

  //if(params.mverbosity>3)
  //cout << "updateForced: trail = " << trail << "\n"
  // << "  frc.size() = " << frc.size() << "\n";
  
  if(frc.size() > 0) {
    i = frc.size() - 1;
    //if(params.mverbosity>3)
    //cout << "  frc.back() = " << frc.back() << "\n";
    while(i < limit && trail[i++] != frc.back());
  }

  //if(params.mverbosity>3)
  //cout << " set i to " << i << "\n";

  for( ; i < limit; i++)
    if(in2ex(trail[i]) != lit_Undef)
      frc.push_back(trail[i]);
}

bool Muser::addClause(const vector<Lit>& lts) 
{
  //if a b-var is refereed to make sure we add the equivalent softcls.
  vec<Lit> ps;
  for(auto lt: lts) {
    if(bvars.isBvar(lt))
      ensureSoftCls(lt);
    else
      ensure_mapping(lt);
    ps.push(ex2in(lt));
  }
  //cout << "muser addCls: ext=" << lts << " int=" << ps << "\n";
  return addClause_(ps); 
}

lbool Muser::curVal(Var x) const {
  Var in = ex2in(x);
  if(in == var_Undef)
    return l_Undef;
  else  
    return value(in);
}

lbool Muser::curVal(Lit x) const {
  Lit in = ex2in(x);
  if(in == lit_Undef)
    return l_Undef;
  else  
    return value(in);
}

void Muser::ensureSoftCls(vector<Lit>& conflict) {
  //Ensure that all soft clauses referenced by conflict are in the solver. 
  //This means that we incrementally add only the soft clauses of the theory
  //that are actually involved in minimizations.
  for(auto blit : conflict)
    ensureSoftCls(blit);
}

void Muser::ensureSoftCls(Lit blit) {
  //Ensure that all soft clauses referenced by conflict are in the solver. 
  //This means that we incrementally add only the soft clauses of the theory
  //that are actually involved in minimizations.
  vec<Lit> ps;
  vec<Lit> eqCls;
  if(inSolver(blit))
    return;
  
  if(!bvars.isBvar(blit))
    cout << "c ERROR conflict does not contain only bvars\n";
  
  auto clsI = bvars.clsIndex(blit);
  //if(params.mverbosity > 4) 
  //cout << "ensureSoftCls adding sft clause"
  // << theWcnf->getSoft(clsI) << "\n";
  
  Lit b = bvars.litOfCls(clsI); //note that blit might be ~bvars.litOfCls(clsI)
  ensure_mapping(b);
  Lit inbPos = ex2in(b);
  ps.clear();
  ps.push(inbPos); 
  for(auto lt: theWcnf->softs()[clsI]) {
    ensure_mapping(lt);
    Lit inLt = ex2in(lt);
    ps.push(inLt);
    eqCls.clear();
    eqCls.push(~inbPos); eqCls.push(~inLt);
    //if(params.mverbosity > 4) 
    //cout << "eq cls: [ " << eqCls[0] << "/" << value(eqCls[0]) 
    //   << " " << eqCls[1] << "/" << value(eqCls[1]) << " ]\n";
    if(!addClause_(eqCls))
      cout << "c ERROR minimize equality clause caused UNSAT\n";
  }
  //if(params.mverbosity > 4) {
  //  cout << "Adding sft cls: [";
  //  for(int i = 0; i < ps.size(); i++) 
  //    cout << ps[i] << "/" << value(ps[i]) << " ";
  //  cout << "]\n";
  // }
  

  if(!addClause_(ps))
    cout << "c ERROR Adding soft clauses of conflict to muser caused unsat.\n";
}

void Muser::preProcessConflict(vector<Lit>& conflict) {
  //Convert conflict to internal variables. Remove any false variables.
  //If member of conflict is true in MUSER, that literal is a minimal
  //conflict.

  size_t j {0};
  for(auto lt : conflict) {
    auto val = value(ex2in(lt));
    if(val == l_Undef) 
      conflict[j++] = ex2in(lt);
    else if(val == l_True) {
      conflict = vector<Lit> { ex2in(lt) };
      return;
    }
  }
  conflict.resize(j);
}

bool Muser::mus_(vector<Lit>& conflict, int64_t propBudget) {
  //reduce conflict to a MUS, return true if we succeeded. 
  //don't use more than probBudget props to do so.
  bool isMus {true};
  ensureSoftCls(conflict);
  preProcessConflict(conflict);

  if(conflict.size() <= 1) {
    if(conflict.size() == 0)
      cout << "c ERROR: MUSER found false conflict\n";
    if(conflict.size() == 1) {
      cout << "c MUSER found unit conflict on input\n";
      conflict[0] = in2ex(conflict[0]);
    }
    return isMus;
  }
  auto notInCon = [this](Lit l){ return !SimpSolver::conflict.has(l); };
  bool haveBudget = propBudget > 0;
  int64_t perTestBudget = propBudget/16;
  uint64_t initialProps = propagations;

  assumptions.clear();
  while(conflict.size() > 0) {
    if(haveBudget && (propagations - initialProps >= static_cast<uint64_t>(propBudget))) { //timed out
      for(size_t i = 0; i < conflict.size(); i++)
        //act like all remaining conflict lits are critical and end loop
	assumptions.push(~conflict[i]); 
      conflict.clear();
      isMus = false;
    }
    else {
      //test next conflict literal for criticality
      Lit test = conflict.back();
      conflict.pop_back();
      //lits in assumptions are already known to be critical
      int ncrits = assumptions.size(); 
      for(size_t i = 0; i < conflict.size(); i++) 
	assumptions.push(~conflict[i]);
      setPropBudget(haveBudget, perTestBudget);
      auto val = solve_();
      satSolves++;

      if(params.mverbosity > 3) {
	cout << "Conflict = " << conflict << "\n";
        cout << "Assumptions = " << assumptions << "\n";
	cout << "Prop budget for test " << perTestBudget << "\n";
        cout << "test = " << test << " val = " << val << "\n";
      }
      
      assumptions.shrink(assumptions.size() - ncrits); //restore assumptions to crits only
      if(val == l_Undef) { //this test timed out. 
	assumptions.push(~test); //assume test is critical.
	isMus = false; //don't know if we have a mus any more.
      }
      else if(val == l_False) { //redundant
	auto p = std::remove_if(conflict.begin(), conflict.end(), notInCon);
	conflict.erase(p, conflict.end()); 
      }
      else { // l_True:
	assumptions.push(~test); 
	addMoreCrits(conflict, haveBudget ? perTestBudget : -1);
      }
    }
  }
  
  assert(conflict.size() == 0);
  //convert assumptions back into a conflict.
  for(int i = 0; i < assumptions.size(); i++)
    conflict.push_back(in2ex(~assumptions[i]));
  
  //if(params.mverbosity > 1) 
  //  cout << "mus_ returns conflict: " << conflict << "\n";
  
  return isMus;
}

void Muser::addMoreCrits(vector<Lit>& conflict, int64_t propBudget)
{
  if(conflict.size() <= 1) 
    return;

  int critsFnd {0};

  //Insert removable most one constraint over conflicts to more criticals
  int aInitSize = assumptions.size();
  vector<Lit> clits = addAmoUnk(conflict);
  lbool critVal;
  vector<char> isCrit(conflict.size(), false);
  
  assumptions.push(~clits[0]); //activate at-most-one
  setPropBudget(propBudget > 0, propBudget);

  while((critVal = solve_()) == l_True) {
    satSolves++;
    for(size_t j = 0; j < conflict.size(); j++) {
      if(modelValue(conflict[j]) == l_True) {
	isCrit[j] = true;
	assumptions.push(~conflict[j]);
	break;
      }
    }
  }
  satSolves++;
  //Note that clits don't go through the ex-to-in interface. They are internal variables only.
  for(auto lt : clits)
    releaseVar(lt);

  assumptions.shrink(assumptions.size() - aInitSize);
  size_t j {0}; //move lits detected to be critical into assumptions
  for(size_t i = 0; i < conflict.size(); i++) {
    if(isCrit[i]) {
      critsFnd++;
      assumptions.push(~conflict[i]);
    }
    else
      conflict[j++] = conflict[i];
  }
  conflict.resize(j);
  if(critVal == l_False && conflict.size()  > 0)
    //If we detected unsat even when any one of the remaining conflict lits
    //was allowed to be relaxed, then we can remove any one of these lits.
    conflict.pop_back(); 

  if(params.mverbosity>1) 
    cout << "addMoreCrits added " << critsFnd << "\n";
}

vector<Lit> Muser::addAmoUnk(vector<Lit>& unknowns) {
  //Add an at-most-one constraint to the solver.
  //  at most one unknown lit can be TRUE.
  //In:  unknowns.size() > 1
  //Out: clits[0] is the control lit that deletes all clauses
  //     clits[1]...are the other auxiliary variables
  //     added to encode the constraint.
  
  vector<Lit> clits;
  for(size_t i = 0; i < unknowns.size(); i++) {
    Var c = newVar(l_Undef, false);
    clits.push_back(mkLit(c, false));
    if(c >= static_cast<Var>(in2ex_map.size()))
      in2ex_map.resize(c+1, var_Undef); //space reserved in in2ex_map for these internal only vars
  }
  
  vec<Lit> cls(3);
  for(size_t i = 0; i < unknowns.size()-1 ; i++) {
    cls[0] = ~unknowns[i];  //unk_i --> clit_i+1
    cls[1] = clits[i+1];  //~clit_i+1 >> ~unk_i
    cls[2] = clits[0];
    addClause_(cls);
  }
  
  for(size_t i = 1; i < clits.size()-1 ; i++) {
    cls[0] = ~clits[i];   //clit_i --> clit_i+1
    cls[1] = clits[i+1];  //~clit_i+1 --> ~clit_i
    cls[2] = clits[0];
    addClause_(cls);
  }
  
  for(size_t i = 1; i < clits.size(); i++) {
    cls[0] = ~clits[i];  //clit_i --> ~unk_i
    cls[1] = ~unknowns[i]; //unk_i --> ~clit_i
    cls[2] = clits[0];    
    addClause_(cls);
  }

  return clits;
}
  

//REMOVE FOR NOW
#if 0
void Muser::analyzeFinal(Lit p, LSet& out_conflict)
{
  //Changes from original: stop resolving backwards when we hit an
  //assumption literal.

  out_conflict.clear();
  out_conflict.insert(p);
  
  if (decisionLevel() == 0)
    return;
  
  seen[var(p)] = 1;

  LSet assumps;
  for(int i = 0; i < assumptions.size(); i++) {
    assumps.insert(assumptions[i]);
  }
  
  for (int i = trail.size()-1; i >= trail_lim[0]; i--){
    Var x = var(trail[i]);
    if (seen[x]){
      if (reason(x) == CRef_Undef || assumps.has(trail[i])){
	//note assumptions has ~p in it and p was forced. So when trail[i] == p, assumps.has(...) is not true
	assert(level(x) > 0);
	assert(x != var(p));
	out_conflict.insert(~trail[i]);
      }else{
	Clause& c = ca[reason(x)];
	for (int j = 1; j < c.size(); j++)
	  if (level(var(c[j])) > 0)
	    seen[var(c[j])] = 1;
      }
      seen[x] = 0;
    }
  }
  
  seen[var(p)] = 0;
}
#endif



