/***********[Wcnf.cc]
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

#include <ostream>
#include <cmath>
#include <algorithm>
#include <set>
#include "maxhs/core/Wcnf.h"
#include "minisat/utils/System.h"
#include "maxhs/utils/io.h"
#include "maxhs/core/Dimacs.h"
#include "minisat/core/SolverTypes.h"
#include "maxhs/ifaces/miniSatSolver.h"
#include "maxhs/utils/hash.h"
#include "maxhs/utils/Params.h"
#include "maxhs/core/Bvars.h"

using Minisat::sign;
using Minisat::mkLit;
using MaxHS_Iface::miniSolver;

Wcnf::Wcnf() :
  maxorigvar{0},
  maxvar{0},
  dimacs_nvars{0},
  dimacs_nclauses{0},
  ms_type{MStype::undef},
  parsing_time{0},
  total_cls_wt {0},
  base_cost {0},
  dimacs_top{std::numeric_limits<Weight>::max()},
  wt_var {0},
  wt_mean {0},
  wt_min {0},
  wt_max {0},
  unsat {false},
  noDups {true},
  nhard_units {0}
{}
    
void Wcnf::set_dimacs_params(int nvars, int nclauses, Weight top) {
  dimacs_nvars = nvars;
  dimacs_nclauses = nclauses;
  dimacs_top = top;
  tvals.resize(nvars, l_Undef);
  eqLitResize(nvars);
}

bool Wcnf::inputDimacs(std::string filename, bool verify) {
  instance_file_name = filename;
  double start_time = Minisat::cpuTime();
  gzFile input = gzopen(filename.c_str(), "rb");
  if (input == NULL) {
    cout << "c ERROR: problem opening input file: " << instance_file_name << "\n";
    return false;
  }
  if(!parse_DIMACS(input, this)) {
    cout << "c ERROR: Parsing error on input file: " << instance_file_name << "\n";
    return false;
  }
  if(!verify) {
    computeStats();
    parsing_time = Minisat::cpuTime() - start_time;
    if(params.verbosity>0)
      printFormulaStats();
    simplify();
  }
  return true;
}

void Wcnf::addDimacsClause(vector<Lit> &lits, Weight w) {
  //This routine needs to know dimacs_top (so set_dimacs_params should
  //have been called first) to determine if the clause is soft or hard
  for(auto l : lits)
    if(var(l) > maxorigvar) 
      maxorigvar = maxvar = var(l);

  if (w >= dimacs_top) 
    addHardClause(lits);
  else
    addSoftClause(lits, w);
}


bool Wcnf::prepareClause(vector<Lit>& lits) {
  if(lits.size() > 1) {
    std::sort(lits.begin(), lits.end());
    size_t cur_size, examine;
    for(cur_size = examine = 1; examine < lits.size(); examine++) {
      if(lits[cur_size-1] == ~lits[examine]) {
	return false; //Tautologies
      }
      if(lits[cur_size-1] != lits[examine])
	lits[cur_size++] = lits[examine];
    }
    lits.resize(cur_size);
  }
  return true;
}

void Wcnf::addHardClause(vector<Lit> &lits) {
  if(unsat) return;
  if(!prepareClause(lits)) return; //skip tautologies
  hard_cls.addVec(lits);
  for(auto l : lits) {
    if(var(l) >= static_cast<int>(tvals.size())) {
      tvals.resize(var(l)+1, l_Undef);
      eqLitResize(var(l)+1);
    }
    if(maxvar < var(l))
      maxvar = var(l); //don't adjust maxorigvars.
  }
  noDups=false;
}


void Wcnf::addSoftClause(vector<Lit> &lits, Weight w) {
  if(unsat) return;
  if(!prepareClause(lits)) return; //skip tautologies
  if (w < 0) 
    cout << "c ERROR: soft clause cannot have negative weight: " << w << "\n";
  else if (w > 0) { //zero weight softs are tautological
    if(lits.size() > 0) {
      soft_cls.addVec(lits);
      soft_clswts.push_back(w);
      total_cls_wt += w;
      for(auto l : lits) {
	if(var(l) >= static_cast<int>(tvals.size())) {
	  tvals.resize(var(l)+1, l_Undef);
	  eqLitResize(var(l)+1);
	}
	if(maxvar < var(l))
	  maxvar = var(l);
      }
    }
    else base_cost += w;
  }
  noDups=false;
}

void Wcnf::addSoftClauseZeroWt(Lit p) { //special for introduced d-vars. Don't introduce duplicates!
  if(unsat) return;
  vector <Lit> lits { p };
  soft_cls.addVec(lits);
  soft_clswts.push_back(0);

  if(var(p) >= static_cast<int>(tvals.size())) {
    tvals.resize(var(p)+1, l_Undef);
    eqLitResize(var(p)+1);
  }
  if(maxvar < var(p))
    maxvar = var(p);
}

void Wcnf::eqLitResize(int nVars) {
  //size is in # of variables (not lits!) can be stored
  int old = eqLit.size()/2; //two lits per var
  if(old < nVars) {
    eqLit.resize(2*nVars);
    for(int i = old; i < nVars; ++i) {
      eqLit[toInt(mkLit(i,false))] = mkLit(i,false);
      eqLit[toInt(mkLit(i,true))] = mkLit(i,true);
    }
  }
}

void Wcnf::simplify() {
  //We allow a Wcnf to transform itself in various model equivalent ways.
  //Only the remaining hard and soft clauses after simplification will be passed
  //to the solver. After the solver has found a solution, it will need to ask
  //the Wcnf to complete that solution for it, by accounting for variables and soft clauses 
  //removed by simplification.
  //
  //We assume that the variable numbering remains the same in the solver as in the
  //Wcnf.
  //
  if(params.wcnf_eqs)
    subEqs();
  if(params.wcnf_units)
    rmUnits();
  remDupCls(); //needed for correctness if unit softs do not generate bvars
  if(params.wcnf_mx_bvars)
    mxBvars();
  if(params.verbosity>0)
    cout << "c WCNF base cost = " << baseCost() << "\n";
}

void Wcnf::subEqs() {
  //Find and remove equalities.
  int neqs {0};
  BinClsTable bins;

  for(const auto hc : hards())
    if(hc.size() == 2)
      bins.insert(hc[0], hc[1]);
  for(auto& b : bins) 
    if(b.second.size() > 2) {
      vector<Lit>& v = b.second;
      auto v1 = b.first.first;
      auto v2 = b.first.second;
      if(v1 == v2)
	cout << "c Wcnf ERROR found binary clause with identical variables "
	     << v << "\n";
      bool c00 {false}, c01 {false}, c10 {false}, c11 {false};
      for(size_t i=0; i < v.size(); i+=2) {
	if      (sign(v[i]) && sign(v[i+1]))   c00 = true;
	else if (sign(v[i]) && !sign(v[i+1]))  c01 = true;
	else if (!sign(v[i]) && sign(v[i+1]))  c10 = true;
	else if (!sign(v[i]) && !sign(v[i+1])) c11 = true;
      }
      vector<Lit> unit(1);
      if(c00 && c01) {
	unit[0] = mkLit(v1, true);
	addHardClause(unit);
      }
      if(c00 && c10) {
	unit[0] = mkLit(v2, true);
	addHardClause(unit);
      }
      if(c01 && c11) {
	unit[0] = mkLit(v2, false);
	addHardClause(unit);
      }
      if(c10 && c11) {
	unit[0] = mkLit(v1, false);
	addHardClause(unit);
      }

      if(c00 && c11 && !c01 && !c10) {
	eqLit[toInt(mkLit(v2,true))] = mkLit(v1,false);
	eqLit[toInt(mkLit(v2,false))] = mkLit(v1,true);
	++neqs;
      }
      if(c01 && c10 && !c00 && !c11) {
	eqLit[toInt(mkLit(v2,true))] = mkLit(v1,true);
	eqLit[toInt(mkLit(v2,false))] = mkLit(v1,false);
	++neqs;
      }
    }
  //The added units will do the appropriate reductions. For the
  //equalities we now rewrite the formula.
  for(auto c: hard_cls)
    for(size_t i = 0; i < c.size(); i++) 
      c[i] = eqRoot(c[i]);

  for(auto c: soft_cls)
    for(size_t i = 0; i < c.size(); i++) 
      c[i] = eqRoot(c[i]);

  //debug
  //cout << "EQSUB\n";
  //printFormula();
  //
  if(params.verbosity > 0)
    cout << "c WCNF found " << neqs << " equalities\n";
}
 
void Wcnf::rmUnits() {
  if(unsat) return;

  miniSolver slv;
  for(size_t i = 0; i < nHards(); i++) 
    if(!slv.addClause(getHard(i))) {
      unsat = true;
      return;
    }
  auto units  = slv.getForced(0);
  nhard_units = units.size();
  for (auto l : units) {
    tvals[var(l)] = sign(l) ? l_False : l_True;
  }
  auto ph = hard_cls.size();
  auto ps = soft_cls.size();
  if(nhard_units > 0) {
    hard_cls = reduceClauses(hard_cls, slv, false);
    soft_cls = reduceClauses(soft_cls, slv, true);
  }
  total_cls_wt = 0;
  for(auto wt : soft_clswts)
    total_cls_wt += wt;
  
  if(params.verbosity > 0)
    cout << "c WCNF found " << nhard_units << " units and removed "
	 << ph - hard_cls.size() << " Hards and "
	 << ps - soft_cls.size() << " softs\n";
}
      
Packed_vecs<Lit> Wcnf::reduceClauses(Packed_vecs<Lit>& cls, miniSolver& slv, bool softs) {
  //auxilary function for rmUnits
  Packed_vecs<Lit> tmp;

  if(unsat) return tmp;

  size_t j = 0;
  vector<Lit> c;
  for(size_t i = 0; i < cls.size(); i++) {
    c.clear();
    bool isSat {false};
    for(auto l : cls[i]) 
      if(slv.curVal(l) == l_Undef)
	c.push_back(l);
      else if(slv.curVal(l) == l_True) {
	isSat = true;
	break;
      }
    if(isSat)
      continue;
    else if(c.empty()) {
      if(!softs) cout << "c ERROR: Wcnf::reduceClauses found empty hard clause\n";
      base_cost += soft_clswts[i];
    }
    else if(softs || c.size() > 1) {
      tmp.addVec(c); 
      if(softs) 
	soft_clswts[j++] = soft_clswts[i];
    }
  }
  if(softs) {
    soft_clswts.resize(j);
    soft_clswts.shrink_to_fit();
  }
  return tmp;
}

void Wcnf::remDupCls() {
  /*compute hash code for each clause. Use this to detect identical
    clauses hash code for units is the hash code of the var---so that
    -x and x get the same hash code and we can detect this clash. */
  if(noDups || unsat)
    return;
  noDups=true;

  vector<ClsData> cdata;
  initClsData(cdata);
  auto byHash = [](const ClsData& a, const ClsData &b)
    { return a.hash < b.hash; };
  sort(cdata.begin(), cdata.end(), byHash);

  Packed_vecs<Lit> tmpH, tmpS;
  vector<Weight> tmp_wts;

  for(size_t i=0; i < cdata.size(); i++) {
    if(cdata[i].w == 0)
      continue; //w==0 indicates clause is deleted;


    uint32_t i_index { cdata[i].index };
    bool ihard { cdata[i].w < 0};
    auto vi = ihard ? hard_cls[i_index] : soft_cls[i_index];
    for(size_t j=i+1; j < cdata.size() && cdata[i].hash==cdata[j].hash; j++) {
      if(cdata[j].w == 0)
	continue;

      uint32_t j_index {cdata[j].index};
      bool jhard {cdata[j].w < 0};
      auto vj = jhard ? hard_cls[j_index] : soft_cls[j_index];
      if(vi.size() == 1 && vi[0] == ~vj[0]) { //contradictory units
	if(ihard && jhard) {
	  unsat = true;
	  return;
	}
	else if(ihard || jhard) { //soft is falsified
	  if(jhard) vi[0] = vj[0];
	  auto cost = jhard ? getWt(i_index) : getWt(j_index);
	  base_cost += cost;
	  cdata[j].w = 0;
	  cdata[i].w = -1;
	}
	else { //neither is hard. This is a resolution of unit softs.
	  Weight cost {}, residue {};
	  if(cdata[i].w < cdata[j].w) {
	    vi[0] = vj[0]; //higher cost unit is preserved
	    cost = cdata[i].w;
	    residue = cdata[j].w - cost;
	  }
	  else { //note that if costs are equal residue becomes 0 and both clauses vanish
	    cost = cdata[j].w;
	    residue = cdata[i].w - cost;
	  }
	  base_cost += cost;
	  cdata[i].w = residue;
	  cdata[j].w = 0;
	}
      }

      else if(eqVecs(cdata[i], cdata[j])) { //equal clauses are merged.
	if(ihard || jhard) { //hard subsumes both soft and hard.
	  cdata[i].w = -1; 
	  cdata[j].w = 0;
	}
	else {
	  cdata[i].w += cdata[j].w; //join softs.
	  cdata[j].w = 0;
	}
      }
    }
    //finished processing all clauses that match with vi.
  }

  auto byIndex = [](const ClsData& a, const ClsData &b)
    { return a.index < b.index; };
  sort(cdata.begin(), cdata.end(), byIndex);

  for(size_t i=0; i < cdata.size(); i++) {
    auto i_index = cdata[i].index;
    auto ohard = cdata[i].origHard;
    auto vi = ohard ? hard_cls[i_index] : soft_cls[i_index];

    if(cdata[i].w < 0) {
      tmpH.addVec(vi.getVec());
      //cout << "i = " << i << " Added hard " << vi.getVec() << "\n\n";
    }
    else if(cdata[i].w > 0) {
      tmpS.addVec(vi.getVec());
      tmp_wts.push_back(cdata[i].w);
      //cout << "i = " << i << " Added soft " << vi.getVec() << " weight = " << cdata[i].w << "\n\n";
    }
  }

  size_t ph = hard_cls.size();
  size_t ps = soft_cls.size();

  hard_cls = std::move(tmpH);
  soft_cls = std::move(tmpS);
  soft_clswts = std::move(tmp_wts);
  total_cls_wt = 0;
  for(auto wt : soft_clswts)
    total_cls_wt += wt;

  if(params.verbosity > 0)
    cout << "c WCNF found " << ph - hard_cls.size()
	 << " redundant hards and " << ps -soft_cls.size()
	 << " duplicate or subsumed softs\n";
}

bool Wcnf::eqVecs(const ClsData& a, const ClsData& b) {
  //auxilary function for rmDupCls
  //relies on all clauses being sorted on input.
  //Should fix this!
  size_t sa = (a.w < 0) ? hardSize(a.index) : softSize(a.index);
  size_t sb = (b.w < 0) ? hardSize(b.index) : softSize(b.index);
  if(sa != sb)
    return false;
  
  auto va = (a.w < 0) ? getHard(a.index) : getSoft(a.index);
  auto vb = (b.w < 0) ? getHard(b.index) : getSoft(b.index);
  for(size_t i=0; i < va.size(); i++)
    if(va[i] != vb[i])
      return false;
  return true;
} 

void Wcnf::initClsData(vector<ClsData>& cdata) {
  //auxilary function for rmDupcls.
  //units are hashed as variables not as lits.
  for(size_t i = 0; i < nHards(); i++) 
    if(hardSize(i) == 1) {
      vector<Var> unit { var(hard_cls[i][0]) };
      cdata.emplace_back(static_cast<uint32_t>(i), 
			 hashCode(unit.begin(), unit.end()), -1, true);
    }
    else 
      cdata.emplace_back(static_cast<uint32_t>(i), 
			 hashCode(hard_cls[i].begin(), hard_cls[i].end()),-1, true);

  for(size_t i = 0; i < nSofts(); i++)
    if(softSize(i) == 1) {
      vector<Var> unit { var(soft_cls[i][0]) };
      cdata.emplace_back(static_cast<uint32_t>(i),
			 hashCode(unit.begin(), unit.end()), getWt(i), false);
    }
    else
      cdata.emplace_back(static_cast<uint32_t>(i), 
			 hashCode(soft_cls[i].begin(), soft_cls[i].end()), getWt(i), false);

  if(params.verbosity > 1) {
    vector<uint32_t> hcodes;
    for(auto &item : cdata) 
      hcodes.push_back(item.hash);
    sort(hcodes.begin(), hcodes.end());
    auto it = std::unique(hcodes.begin(), hcodes.end());
    hcodes.resize(std::distance(hcodes.begin(), it));
    cout << "c Hashed " << cdata.size() << " clauses with " 
	 << it-hcodes.begin() << " (" << hcodes.size() << ") different hash codes\n";
  }
}

void Wcnf::mxBvars() {
  //modify the WCNF by finding at most one constraints among the bvars
  //and replacing all of these vars by one bvar.
  int newbvars {0};
  for(size_t i=0; i<nSofts(); i++)
    if(softSize(i) > 1)
      ++newbvars;

  Bvars bvars {this};
  if(params.verbosity > 3) {
    cout << "BEFORE mxbvars\n";
    printFormula(bvars);
  }
  processMxs(mxFinder(bvars), bvars);
  if(params.verbosity > 3) {
    cout << "AFTER mxbvars\n";
    printFormula(bvars);
  }
  
  //syntatic_mx_bvars();
}
  
void Wcnf::processMxs(vector<vector<Lit>> mxs, Bvars& bvars) {
  //mxs should be disjoint collection of mx sets. Each set should be a
  //non empty set of blits all of which have the same weight and are
  //either cores or non-cores. Modify the WCNF to account for this mx
  //set.
  if(unsat)
    return;
  
  /*cout << "Before processmx\n";
    printFormula(bvars);*/

  vector<char> delMarks (nSofts(), 0);
  Var newVar = maxOrigVar() + 1;     //Wcnf has no b-vars (only sat solver does)
                                     //So we can start new ones from here
  for(auto& v : mxs) {

    //debug
    /*cout << "Processing " << (bvars.isCore(v[0]) ? "Core Mx: [ " : "NonCore Mx: [ ");
    for(auto l : v)
      cout << l << "(ci = " << bvars.clsIndex(l) << "), ";
    cout << "]\n";
    if(v.size() < 2)
      cout << "ERROR: Got mutual exclusion with less than 2 vars" << v << "\n";
    bool dc = bvars.isCore(v[0]);
    for(auto l : v) {
      if(dc && !bvars.isCore(l) || !dc && bvars.isCore(l)) 
	cout << "ERROR mx with mixed core/non-cores" << v << "\n";
      if(bvars.wt(var(l)) != bvars.wt(var(v[0])))
	cout << "ERROR mx with different wts" << v << "\n";
	}*/
    //debug

    int ci {0};
    vector<Lit> blits {};
    for(auto l :v) {
      ci = bvars.clsIndex(l);
      auto sftcls = getSoft(ci);
      if(sftcls.size() == 0) {
	cout << "c ERROR WCNF processMxs encountered zero length soft clause\n";
	continue;
      }
      if(sftcls.size() == 1) {
	blits.push_back(~sftcls[0]);
      }
      else { //must make new blit and modify clause.
	auto blit = mkLit(newVar++);
	blits.push_back(blit);
	sftcls.push_back(blit);
	delMarks[ci] = 1;
	addHardClause(sftcls);
	addSoftClause(~blit, getWt(ci));
      }
    }
    //auto dvar = newVar++;
    //auto dlit = mkLit(dvar);

    if(bvars.isNonCore(v[0])) { //non core mx
      for(size_t i = 0; i < blits.size(); i++) 
	blits[i] = ~blits[i];
      //dlit = ~dlit;
    }

    /*vector<Lit> binCls (2);
    binCls[1] = dlit;
    for(auto b : blits) {
      binCls[0] = ~b;
      addHardClause(binCls);
      }*/
    
    //blits.push_back(~dlit);
    //addHardClause(blits);
    //addSoftClauseZeroWt(mkLit(dvar,true));
    //blits.pop_back(); //get rid of dvar
    mutexes.push_back(std::move(blits)); 
    //mutexDvars.push_back(dvar);
  }

  //now rewite the softs
  Packed_vecs<Lit> tmp;
  size_t j {0};
  for(size_t i = 0; i < nSofts(); i++) 
    if(i >= delMarks.size() || !delMarks[i]) { 
      //delmarks don't extend to newly added softs
      tmp.addVec(getSoft(i));
      soft_clswts[j++] = soft_clswts[i];
    }
  soft_clswts.resize(j);
  soft_clswts.shrink_to_fit();
  soft_cls = std::move(tmp);

  total_cls_wt = 0;
  for(auto wt : soft_clswts)
    total_cls_wt += wt;
  //computeStats();
  
  /*cout << "Process mx\n";
  cout << "mutexes\n";
  for(auto& v : mutexes)
    cout << v << "\n";
    printFormula();*/
}

class MXFinder {
  //helper class for finding mutually exclusive bvars
 public:
  MXFinder(Wcnf* f, Bvars& b) : 
    nImpCalls {0},
    bvars {b},
    theWcnf {f},
    blitMarks (2*(bvars.maxvar()+1), 0)
  {}
  ~MXFinder() {
    for(auto p : blitMXes) 
      if(p) delete p;
  }
  bool findMxs(vector<vector<Lit>>&);
  int nImpCalls;
 private:
  miniSolver solver;
  Bvars bvars;
  Wcnf* theWcnf;
  vector<uint8_t> blitMarks;
  const uint8_t inmx {1};
  const uint8_t in2s {2};
  bool fbeq();
  size_t getMXLitSize(Lit);
  const vector<Lit>* getMXLits(Lit);
  vector<vector<Lit>*> blitMXes;
  void getMXRecomputeSizes(const vector<Lit>&);
  vector<Lit> growMx(Lit start);
  //debug
  void MXprintLit(Lit l) {
    cout << l << " (mkr=" << (int) blitMarks[toInt(l)] << (bvars.isCore(l) ? " C " : " NC ")
	 << " wt = " << bvars.wt(var(l)) << ") ";
  }
};

vector<vector<Lit>> Wcnf::mxFinder(Bvars& bvars) {
  //Return collection of mutally exclusive bvars. Where each set of
  //Bvars are cores or are non-cores and each is associated with a
  //soft clause of identical weight; finder does all the work: we use
  //a function wrapper to ensure MXFinder is deallocated after it has
  //done its work.
  MXFinder finder {this, bvars};
  vector<vector<Lit>> mxs;
  if(!finder.findMxs(mxs))
    unsat = true;
  if(params.verbosity>0)
    cout << "c WCNF mx finder used " << finder.nImpCalls << " calls to UP engine\n";
  return mxs;
}

bool MXFinder::findMxs(vector<vector<Lit>>& mxs) {
  //Top level findMxs method of MXFinder class. 
  //find mx collections of bvars and store in mxs. Return false if
  //we found a contradiction.

  bool timedOut {false};
  double start_time = Minisat::cpuTime();
  
  //1. Initialize solver with fbeq
  if(!fbeq()) {
    if(params.verbosity>0)
      cout << "c WCNF detected input to be unsat during preprocessing\n";
    return false;
  }

  //Two stage. Note that absorbing a blit into a mutex block it and
  //its negation from being in any other mutex. So try to grow big
  //mutexes we delay the processing of mutexes of size 2. E.g., it
  //could be that (b1,b2) are mutex but so is (b2, b3, b4, b5) so we
  //don't want to absorbe b2 into (b1, b2). 

  vector<Lit> toProcess;
  vector<Lit> twos;      //blits that might generate 2s. Process later.

  //toProcess will be used as a stack. 
  //Non core mx bump the base cost so process those first.
  for(size_t i = 0; i < theWcnf->nSofts(); ++i) {
    toProcess.push_back(bvars.litOfCls(i));
  }
  for(size_t i = 0; i < theWcnf->nSofts(); ++i) {
    toProcess.push_back(~bvars.litOfCls(i));
  }
  
  int loops {0};
  while(!toProcess.empty()) {
    //in this loop toProcess.back() is either selected, or blits that
    //are mx with it are processed. Thus the size of
    //toProcess.back()'s mx lit set is decreased. So eventually toProcess
    //will become empty.
    ++loops;
    if(params.wcnf_mx_cpu_lim > 0 && loops%500 == 0)
      if((Minisat::cpuTime() - start_time) > params.wcnf_mx_cpu_lim) {
	timedOut=true;
	break;
      }
    
    Lit blit = toProcess.back();
    if(blitMarks[toInt(blit)]) {  
      //in an mx or in twos
      toProcess.pop_back();
      continue;
    }
    auto mx = getMXLits(blit);
    
    //Debug
    /*cout << "findmxs first loop unmarked processing ";
    MXprintLit(blit);
    cout << " mx = [";
    for(auto p : *mx) {
      MXprintLit(p);
      cout << " (" << getMXLitSize(p) << "), ";
    }
    cout << "]\n";*/

    if(mx->size() <= 1) { 
      if(mx->size() == 1) {
	blitMarks[toInt(blit)] = in2s;
	twos.push_back(blit);
	//cout << "Pushed into twos\n";
      }
      //cout << "Got rit of\n";
      toProcess.pop_back();
      continue;
    }
    
    //Potential mx of size > 2 (but not guaranteed!)
    //cout << "Growing from start ";

    Lit start = blit;
    size_t size {mx->size()};
    
    //Find start.
    for(auto l : *mx) {
      size_t sz = getMXLitSize(l);
      if(sz > size) {
	size = sz;
	start = l;
      }
    }

    //cout << start << "\n";
    //grow from start
    auto tmp = growMx(start);

    //tmp might be small and it might not contain blit
    if(tmp.size() <= 2) {

      //cout << "too small\n";

      //no easy way to get rid of start from toProcess
      //so mark as being in twos
      blitMarks[toInt(blit)] = in2s;
      if(tmp.size() == 2) {
	//but only put there if it has potential
	twos.push_back(start);	
	//cout << "put in twos\n";
      }
    }

    else { //legit mx for this stage
      for(auto b : tmp) {
	//cout << "adding mx\n";

	blitMarks[toInt(b)] = inmx;
	blitMarks[toInt(~b)] = inmx;
      }
      mxs.push_back(std::move(tmp));
    }
  }

  if(!timedOut)
    while(!twos.empty()) {
      Lit blit = twos.back();
      
      //cout << "Processing twos " << blit << "\n";
      
      twos.pop_back(); 
      if(blitMarks[toInt(blit)] == inmx) {
	//cout << "Already marked\n";
	continue;
      }
      
      auto tmp = growMx(blit);
      if(tmp.size() > 1) {
	if(tmp.size() > 2)
	  cout << "c WARNING. WCNF large mx got into twos\n";
	for(auto b : tmp) {
	  blitMarks[toInt(b)] = inmx;
	  blitMarks[toInt(~b)] = inmx;
	}
	mxs.push_back(std::move(tmp));
      }
    }
  
  if(params.verbosity > 0) {
    cout << "c WCNF found " << mxs.size() << " mutexes";
    if(mxs.size() > 0) {
      double ave {0};
      for(auto& mx : mxs)
	ave += mx.size();
      cout << " average size = " << ave/mxs.size() << "\n";
    }
    else
      cout << "\n";
    
  }

  return true;
}

vector<Lit> MXFinder::growMx(Lit start) {
  //Starting with blit start, grow a mx constraint (at most one)
  //The algorithm is as follows. 
  //We have a set mx that is initially start, and a set of candidates
  //initially the negations of the appropriate implications of start
  //(returned by getMXLits)
  //Appropriate means that these negations are cores if start is a core
  //and they are non-cores if start is a non-core. Furthermore, none
  //of them is marked (as used in another mx constraint), and they all
  //correspond to soft clauses with identical weight as start's soft clause.
  //These restrictions are maintained by the subroutine getMXLits

  //The algorithm's invariant is that 
  //(a) the lits in mx form an mx constraint
  //(b) every single lit in candidates is mx with each lit in mx
  //    Thus mx can be grown by any member of candidates.

  //1. All l in candidates are MX (mutually exclusive) with all c in
  //   mx. So when we move l from candidates to mx (i.e., we select l)
  //   we must remove from candiates all l' that are not MX with l.
  //   Here we sort candidates by |mxset(l)\cap candidates|. So that
  //   if l is selected we can retain as many members of candidates as
  //   is possible. We only sort at the start. A greedy method would 
  //   always recompute the size of this intersection since candidates
  //   is shrinking after every l is selected. But we don't do that
  //   to avoid this cost.

  vector<Lit> origCandidates(*getMXLits(start)); //need copy
  std::set<Lit> candidates(origCandidates.begin(), origCandidates.end());

  //compute |mxset(l) \cap candidates| or all l\in candidates
  vector<int> interSize;
  for(auto l : origCandidates) {
    int count {0};
    int ci {bvars.clsIndex(l)};
    for(auto l1 : *getMXLits(l))
      if(candidates.find(l1) != candidates.end())
	++count;
    if(static_cast<size_t>(ci) >= interSize.size())
      interSize.resize(ci + 1, 0);
    interSize[ci] = count;
  }

  auto mxSize = [this, &interSize](Lit l1, Lit l2) {
    return interSize[bvars.clsIndex(l1)] > interSize[bvars.clsIndex(l2)];
  };
  sort(origCandidates.begin(), origCandidates.end(), mxSize); 

  //debug*****
  /*cout << "growMX on " << start << "\n";
  cout << start << " mx = " << *getMXLits(start) << "\n";
  cout << "candidiates\n";
  for(size_t i = 0; i < origCandidates.size(); i++) {
    auto l = origCandidates[i];
    auto ci = bvars.clsIndex(l);
    cout << l << " mx = "
	 << *getMXLits(l) << " [" << interSize[ci] << "]\n";
	 }*/
  //debug*****

  vector<Lit> mx {start};
  size_t cani {0};
  while(!candidates.empty()) {

    /*cout << "Loop #" << cani << " candidiates [";
    for(auto l : candidates)
      cout << l << ", ";
      cout << "]\n";*/

    auto l = origCandidates[cani++]; //select according to computed order
    //cout << " growing " << cani << " lit = " << l;
    auto it = candidates.find(l);
    if(it == candidates.end()) {
      //cout << " Not found\n";
      continue;
    }
    //cout << " Found\n";
    mx.push_back(l);
    candidates.erase(it);
    //remove from candidates all elements not mx with the newly selected l
    auto l_mx = getMXLits(l);
    std::set<Lit> newLitMx(l_mx->begin(), l_mx->end());
    for(auto p = candidates.begin(); p != candidates.end(); ) {
      //cout << "checking active candiate " << *p;
      if(newLitMx.find(*p) == newLitMx.end())  {
	//this candidate not mx with newly added lit---not a candidate anymore;
	//cout << " Pruning\n";
	candidates.erase(p++); //sets! Erase invalidates p, so pass copy and increment here.
      }
      else {
	++p;
	//cout << " Keeping\n";
      }
    }
  }

  //debug
  //cout << "Grow found mx " << mx << "\n";
  /*for(size_t i=0; i<mx.size(); i++) 
    for(size_t j=i+1; j < mx.size(); j++) 
      if(!solver.isMX(mx[i], mx[j])) {
	cout << "ERROR MX faulty (" << mx[i] << ", " << mx[j] << ")\n";
	break;
      }
  for(size_t i=0; i< mx.size(); i++) 
    if(    (bvars.isCore(mx[0]) && bvars.isNonCore(mx[i]))
	|| (bvars.isNonCore(mx[0]) && bvars.isCore(mx[i]))
        || (bvars.wt(var(mx[0])) != bvars.wt(var(mx[0])))   ) {
      cout << "ERROR MX faulty (" << mx[0] << ", " << mx[i] << ")\n";
      break;
    }*/

  return mx;
}

bool MXFinder::fbeq() {
  //Add fbeq to solver.
  for(size_t i = 0; i < theWcnf->nHards(); i++) 
    if(!solver.addClause(theWcnf->getHard(i)))  
      return false; 

  for(size_t i = 0; i < theWcnf->nSofts(); i++) {
    Lit blit = bvars.litOfCls(i);
    if(theWcnf->softSize(i) > 1) {
      vector<Lit> sftCls {theWcnf->getSoft(i)};
      sftCls.push_back(blit);
      if(!solver.addClause(sftCls))
	return false;
    
      vector<Lit> eqcls(2, lit_Undef);
      eqcls[1] = ~blit;
      for(auto l : theWcnf->softs()[i]) {
	eqcls[0] = ~l;
	if(!solver.addClause(eqcls)) 
	  return false;
      }
    }
  }    

  for(size_t i = 0; i < theWcnf->nSofts(); i++) {
    Var v {bvars.varOfCls(i)};
    if(solver.activeVar(v))
      solver.freezeVar(v);
  }

  double start {cpuTime()};
  solver.eliminate(true);
  if(params.verbosity>0)
    cout << "c WCNF minisat preprocess eliminated " << solver.nEliminated() << " variables. Took "
	 << cpuTime() - start << "sec.\n";
  return true;
}
 
const vector<Lit>* MXFinder::getMXLits(Lit l) {
  //return *unmarked* literals of same type (same wt and same core status) that
  //are mutually exclusive with l.
  //This is accomplished by asking the sat solver to find the implications
  //of l that have the same weight and the opposite core status.
  //If l --> l1, then l and ~l1 are mutually exclusive.
  //To make this more efficient we remember the compute sets in blitMXex.
  //
  //Since literals are marked at various stages, we must prune these cached 
  //sets to remove newly marked literals (??do we need to do this??)

  Weight lWT {0}; //rather than set up a class of template, we capture this local var in our lambda.
  auto coreMX = [this, &lWT] (Lit l1) {
    return blitMarks[toInt(l1)]!=inmx && bvars.isNonCore(l1) && bvars.wt(var(l1)) == lWT;
  };
  auto nonCoreMX = [this, &lWT] (Lit l1) {
    return blitMarks[toInt(l1)]!=inmx && bvars.isCore(l1) && bvars.wt(var(l1)) == lWT;
  };

  if(blitMXes.size() <= static_cast<size_t>(toInt(l))) 
    blitMXes.resize(toInt(l)+1, nullptr);

  vector<Lit> imps;
  if(!blitMXes[toInt(l)]) { //not cached compute
    lWT = bvars.wt(var(l));
    ++nImpCalls;
    if(bvars.isCore(l))
      solver.findImplicationsIf(l, imps, coreMX);
    else
      solver.findImplicationsIf(l, imps, nonCoreMX);

    //debug
    /*vector<Lit> t;
    t.push_back(l);
    vector<Lit> o;
    vector<Lit> pruned;
    solver.findImplications(t, o);
    t.clear();
    for(size_t i=0; i < o.size(); ++i) {
      if(blitMarks[toInt(o[i])] != inmx &&
	 ((bvars.isCore(l) && bvars.isNonCore(o[i]))
	  || (bvars.isNonCore(l) && bvars.isCore(o[i])))
	 && (bvars.wt(var(l)) == bvars.wt(var(o[i]))))
	pruned.push_back(o[i]);
    }

    std::sort(pruned.begin(), pruned.end());
    std::sort(imps.begin(), imps.end());
    if(pruned.size() != imps.size()) {
      cout << "ERROR regular interface returned different set of imps for ";
      cout << l << " (marks = " << (int) blitMarks[toInt(l)] << (bvars.isCore(l) ? " Core " : " nonCore ");
      cout << " wt = " << bvars.wt(var(l)) << ")\n";
      
      cout << " imps = [ ";
      for(auto x : imps) 
	cout << x << " (marks = " << (int) blitMarks[toInt(x)] << (bvars.isCore(x) ? " Core " : " nonCore ")
	     << " wt = " << bvars.wt(var(x)) << "), ";
      cout << "] (" << imps.size() << ")\n";

      cout << " pruned = [ "; 
      for(auto x : pruned) 
	cout << x << " (marks = " << (int) blitMarks[toInt(x)] << (bvars.isCore(x) ? " Core " : " nonCore ")
	     << " wt = " << bvars.wt(var(x)) << "), ";
      cout << "] (" << pruned.size() << ")\n";
    }

    else {
      for(size_t i =0; i < pruned.size(); i++)
	if(pruned[i] != imps[i]) {
	  cout << "ERROR regular interface returned different set of imps\n";

	  cout << l << " (marks = " << (int) blitMarks[toInt(l)] << (bvars.isCore(l) ? " Core " : " nonCore ");
	  cout << " wt = " << bvars.wt(var(l)) << ")\n";
	  
	  cout << " imps = [ ";
	  for(auto x : imps) 
	    cout << x << " (marks = " << (int) blitMarks[toInt(x)] << (bvars.isCore(x) ? " Core " : " nonCore ")
		 << " wt = " << bvars.wt(var(x)) << "), ";
	  cout << "] (" << imps.size() << ")\n";
	  
	  cout << " pruned = [ "; 
	  for(auto x : pruned) 
	    cout << x << " (marks = " << (int) blitMarks[toInt(x)] << (bvars.isCore(x) ? " Core " : " nonCore ")
		 << " wt = " << bvars.wt(var(x)) << "), ";
	  cout << "] (" << pruned.size() << ")\n";

	  break;
	}
    }*/
    //debug	

    for(size_t i=0; i < imps.size(); ++i)
      imps[i] = ~imps[i]; //convert from implication to MX
    blitMXes[toInt(l)] = new vector<Lit>(std::move(imps));
    return blitMXes[toInt(l)];
  }

  //otherwise prune for marks
  auto v = blitMXes[toInt(l)];
  size_t j {0};
  for(size_t i=0; i < v->size(); ++i)
    if(blitMarks[toInt((*v)[i])] != inmx) 
      (*v)[j++] = (*v)[i];

  v->resize(j);
  return v;
}
       
size_t MXFinder::getMXLitSize(Lit l) {
  //potentially we could aproximate this by returning
  //the size without pruning for marks and using getMXrecomputeSizes
  //on each found mx to get most of the sizes right.
  return getMXLits(l)->size();
}

void MXFinder::getMXRecomputeSizes(const vector<Lit>& newlyMarked) {
  auto nic = nImpCalls;
  for(auto l : newlyMarked) { //note we don't need to update vectors of marked lits
    auto v = getMXLits(l);    //this is automatic from getMXLits. v is set of lits that need update
    for(auto x : *v) {
      auto vx = blitMXes[toInt(x)];
      if(!vx) continue;
      size_t j {0};
      for(size_t i = 0; i < vx->size(); ++i)
	if(blitMarks[toInt((*vx)[i])] == inmx)
	  (*vx)[j++] = (*vx)[i];
      vx->resize(j);
    }
  }
  if(nImpCalls > nic && params.verbosity>0) 
    cout << "c WARNING getMXRecomputeSizes used some implication calls!\n";
}

//INPUT PROBLEM/INTERNAL PROBLEM interface
//Take model found by solver and rewrite it into model of original formula
void Wcnf::rewriteModelToInput(vector<lbool>& ubmodel) {
  //add forced and equivalent variables settings to model---indexed by variable.
  ubmodel.resize(nOrigVars(), l_Undef);
  for(size_t i = 0; i < nOrigVars(); i++) {
    auto eqLit = eqRoot(mkLit(i));
    auto eqVar = var(eqLit);
    if(static_cast<size_t>(eqVar) != i && tvals[i] != l_Undef)
      cout << "c WCNF ERROR. An equivalence reduced variable was set by the maxsat solver\n";

    if(tvals[eqVar] != l_Undef) //eqvar has forced value in WCNF
      ubmodel[i] = sign(eqLit) ? tvals[eqVar].neg() : tvals[eqVar]; //if i = -v, must flip tval
    else
      ubmodel[i] = sign(eqLit) ? ubmodel[eqVar].neg() : ubmodel[eqVar];
  }
}

//verify model against original formula.
Weight Wcnf::checkModel(vector<lbool>& ubmodel, int& nfalseSofts, bool final) {
  if(final) {
    hard_cls.clear();
    soft_cls.clear();
  }
  nfalseSofts = 0;
  Wcnf newCopy;
  newCopy.inputDimacs(fileName(), true); //don't process input problem
  for(auto hc : newCopy.hards()) {
    bool isSat = false;
    for(auto lt : hc)
      if(lbool(!sign(lt)) == ubmodel[var(lt)]) { //ubmodel[var(lt)] = l_True or l_False, not = l_Undef
	isSat = true;
	break;
      }
    if(!isSat) {
      cout << "c ERROR! WCNF. Model does not satisfy the hards\n";
      return -1;
    }
  }
  Weight w {0};
  int i=0;
  for(auto sc : newCopy.softs()) {
    bool isSat = false;
    for(auto lt : sc)
      if(lbool(!sign(lt)) == ubmodel[var(lt)]) {
	isSat = true;
	break;
      }
    if(!isSat) {
      w += newCopy.getWt(i);
      ++nfalseSofts;
    }
    ++i;
  }
  return w;
}

//Stats and output
void Wcnf::computeStats() {
  wt_min = wt_max = 0;
  vector<Weight> wts(soft_clswts);
  std::sort(wts.begin(), wts.end());
	     
  if (wts.size() > 0) {
    wt_min = wts.front();
    wt_max = wts.back();
  }

  wt_mean = wt_var = 0;
  for(auto x : wts) 
    wt_mean += x;

  wt_mean /= wts.size();
  for(auto x : wts)
    wt_var += (x-wt_mean)*(x-wt_mean);
  wt_var /= wts.size()-1;

  auto nend = std::unique(wts.begin(), wts.end());
  wts.resize(std::distance(wts.begin(), nend));
  diffWts = wts;

  if(hard_cls.size() > 0) {
    if(diffWts.size() > 1)
      ms_type = MStype::wpms;
    else
      ms_type = MStype::pms;
  }
  else {
    if(diffWts.size() > 1)
      ms_type = MStype::wms;
    else
      ms_type = MStype::ms;
  }
}

void Wcnf::printFormulaStats() {
  computeStats();
  cout << "c Instance: " << instance_file_name << "\n";
  cout << "c Dimacs Vars: " << dimacs_nvars << "\n";
  cout << "c Dimacs Clauses: " << dimacs_nclauses << "\n";
  cout << "c HARD: #Clauses = " << hard_cls.size()
       << ", Total Lits = " << hard_cls.total_size() 
       << ", Ave Len = " << ((hard_cls.size() > 0) ? (1.0*hard_cls.total_size())/hard_cls.size() : 0.0) << "\n";
  cout << "c SOFT: #Clauses = " << soft_cls.size()
       << ", Total Lits = " << soft_cls.total_size() 
       << ", Ave Len = " << (1.0*soft_cls.total_size())/soft_cls.size() << "\n";
  cout << "c Total Soft Clause Weight (+ basecost): " << totalClsWt() << " (+ "
       << baseCost() << "), Dimacs Top = " << dimacs_top << "\n";
  cout << "c SOFT%: " << (100.0*soft_cls.size())/(soft_cls.size()+hard_cls.size()) << "%\n";
  cout << "c #distinct weights: " << nDiffWts() << ", mean = " << aveSftWt()
       << ", std. dev = " << std::sqrt(varSftWt()) << ", min = " << minSftWt() << ", max = " << maxSftWt() << "\n";
  cout << "c Total Clauses: " << hard_cls.size() + soft_cls.size() << "\n";
  cout << "c Parse time: " << parsing_time << "\n";
  cout << "c Wcnf Space Required: " << ((hard_cls.total_size()+soft_cls.total_size())*sizeof(Lit) + soft_clswts.size()*sizeof(Weight))/1000000.0 << "MB\n";
  if(unsat)
    cout << "c Wcnf is UNSAT (hards are contradictory)\n";
  cout << "c ================================" << "\n";
}

void Wcnf::printFormula(std::ostream& out) const {
  //TODO modify to optionally output new DIMACS file.
  out << "c Wcnf---Print Formula\n";
  out << "c Dimacs (Vars, Clauses, TOP) = (" << dimacs_nvars
      << " ," << dimacs_nclauses
      << " ," << dimacs_top << ")";
  out << " maxvar = " << maxvar+1 << "\n";
  if(unsat)
    out << " formula is UNSAT\n";
  out << "c Hard Clauses # = " << hard_cls.size()+nhard_units << "\n";
  for(size_t i = 0; i < nOrigVars(); i++)
    if(tvals[i] != l_Undef)
      out << " " << (tvals[i] == l_True ? "" : "-") << i+1 << " 0 \n";
  out << hard_cls;

  out << "c Soft Clauses, # = " << soft_cls.size() << "\n";
  out << "c Base cost = " << base_cost << "\n";
  for(size_t i = 0; i < soft_cls.size(); i++) {
    out << soft_clswts[i] << " ";
    for(auto& item : soft_cls[i])
      out << item << " ";
    out << "0 \n";
  }
}

void Wcnf::printFormula(Bvars& bvars, std::ostream& out) const {
  //TODO modify to optionally output new DIMACS file.
  out << "c Wcnf---Print Formula\n";
  out << "c Dimacs (Vars, Clauses, TOP) = (" << dimacs_nvars
      << " ," << dimacs_nclauses
      << " ," << dimacs_top << ")";
  out << " maxvar = " << maxvar+1 << "\n";
  out << "c totalClsWt = " << totalClsWt() << "\n";
  if(unsat)
    out << " formula is UNSAT\n";
  out << "c Hard Clauses # = " << hard_cls.size()+nhard_units << "\n";
  int nh {0};
  for(size_t i = 0; i < nOrigVars(); i++)
    if(tvals[i] != l_Undef)
      out << "h#" << nh++ << ": [ " << (tvals[i] == l_True ? "" : "-") << i+1 << "]\n";
  for(size_t i = 0; i < nHards(); i++)
    out << "h#" << nh++ << ": " << getHard(i) << "\n";

  out << "c Soft Clauses, # = " << soft_cls.size() << "\n";
  out << "c Base cost = " << base_cost << "\n";

  int ns {0};
  for(size_t i = 0; i < nSofts(); i++)
    out << "c#" << ns++ << " blit = " << bvars.litOfCls(i) 
	<< " wt = " << getWt(i) << " : " << getSoft(i) << "\n";
}
