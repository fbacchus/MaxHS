/***********[greedySatSolver.cc]
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

/* Interface to minisat.
*/

#include <vector>
#include <algorithm>
#include <ostream>

#include "maxhs/ifaces/GreedySolver.h"
#include "maxhs/utils/io.h"
#include "minisat/core/SolverTypes.h"
#include "minisat/utils/System.h"
#include "minisat/mtl/Heap.h"

using namespace MaxHS_Iface;
using namespace Minisat;

GreedySolver::GreedySolver(Bvars& b) : bvars (b), nsatCores {0}, solves {0},
  totalTime {0}, prevTotalTime {0}, stime{-1} {}

GreedySolver::~GreedySolver() { }

void GreedySolver::ensureSC(int clsi) {
  //make sure all data structures are initialized for soft clause clsi
  if(clsi >= static_cast<int>(clsVal.size()))
    clsVal.resize(clsi+1, l_Undef);
  if(clsi >= static_cast<int>(init_sc.size()))
    init_sc.resize(clsi+1, 0);
  if(clsi >= static_cast<int>(occurList.size())) 
    occurList.resize(clsi+1,{});
}

void GreedySolver::ensureCore(int corei) {
  //make sure all data structures are initialized for core corei
  if(corei >= static_cast<int>(cores.size()))
    cores.resize(corei+1);
  if(corei >= static_cast<int>(coreIsSat.size()))
    coreIsSat.resize(corei+1, 0);
}

bool GreedySolver::addClause(const vector<Lit>& lts) {
  /* Internally the greedy solver stores cores and does it processing with soft clause indicies 
     This is a more compact range than the b-vars */
  //cout << "Adding " << lts << " to greedy solver\n";

  for(auto l: lts) 
    if((lts.size() > 1 && !bvars.isCore(l))
	|| (lts.size() == 1 && !bvars.isBvar(l))) {
      cout << "c ERROR added non-unit non-core or unit non-bvar constraint to greedy solver\n";
      cout << lts << "\n";
      return false;
    }

  if(lts.size() == 1) 
    return inputUnit(lts[0]);

  vector<int> c;
  for(auto l: lts) {
    auto clsi = bvars.clsIndex(l);
    ensureSC(clsi);
    if(clsVal[clsi] == l_True) {
      cout << "c WARNING added already satisfied constraint to greedy solver\n";
      cout << lts << " soft cls " << l << "\n";
      return true; //ignore this core.
    }
    if(clsVal[clsi] != l_False) //falsified soft clauses cannot be used to satisfy other cores
      c.push_back(clsi);
  }
  
  if(c.size() == 0) {
    cout << "c ERROR added unsatisfiable core to greedy solver\n";
    cout << lts << "\n";
    return false;
  }
    
  auto corei = cores.size();
  ensureCore(corei);
  for(auto clsi : c) {
    occurList[clsi].push_back(corei);
    init_sc[clsi] += 1;
  }
  cores[corei] = std::move(c);
  return true;
}

bool GreedySolver::inputUnit(Lit  lt) {
  /* Special function to deal with input of unit bvars that have been 
     discovered to have a forced value by the user of GreedySolver.
     
     (a) lt is core --- it satisfies some of the already known cores.
         Remove those cores and update the initial sat count of each 
	 literal in the removed core. Remove the cores from the literal
	 occur lists. DO NOT renumber the remaining cores.
	 
     (b) lt is a non-core --- it strengthens some of the already known
         cores---potentially making them unit!
         Remove ~lt from each of the cores containing it. 
         If a core becomes unit (x) then we have to process x which
	 is a core literal--case a--fortunately this will not cause any
	 further propagation.
      In both cases the sftcls index corresponding to lt gets its value marked
      so that future input cores can be simplified on input, and the occurs list
      for that soft clause is emptied.
  */
  int clsi = bvars.clsIndex(lt);
  ensureSC(clsi);
  lbool val = bvars.isCore(lt) ? l_True : l_False;
  if(clsVal[clsi] == val)
    return true;  //redundant unit;
  if(clsVal[clsi] != l_Undef) {
    cout << "c ERROR adding unit whose opposite has already been added to or inferred by greedy solver \n";
    cout << lt << "\n";
    return false;
  }
  clsVal[clsi] = val;
  if(val == l_True) 
    processTrueB(clsi);
  else
    processFalseB(clsi);
  return true;
}
  
void GreedySolver::processTrueB(int clsi) { 
  //soft clause clsi has become relaxed. This satisfies some cores.
  for(auto corei : occurList[clsi]) {
    if(coreIsSat[corei])
      continue;
    for(auto ci : cores[corei]) 
      if(ci != clsi) {
	init_sc[ci] -= 1; //decrement sat count
	size_t j {0};
	auto& olist = occurList[ci];
	for(size_t i=0; i < olist.size(); i++) 
	  if(olist[i] != corei)
	    olist[j++] = olist[i];
	olist.resize(j);
      }
    coreIsSat[corei] = 1;
    ++nsatCores;
  }
  vector<int> tmp;
  std::swap(occurList[clsi], tmp); //soft clause clsi now has a sat count of zero.
  init_sc[clsi] = 0;
}

void GreedySolver::processFalseB(int clsi) {
  //soft clause clsi has become hard. This reduces some cores.
  vector<int> newUnits;

  for(auto corei: occurList[clsi]) {
    if(coreIsSat[corei])
       continue;
    size_t j {0};
    auto& core = cores[corei];
    for(size_t i = 0; i < core.size(); i++)
      if(core[i] != clsi)
	core[j++] = core[i];
    core.resize(j);
    if(core.size() == 1) {//new positive unit. 
      //cout << "Found new unit core " << bvars.litOfCls(core[0]) << "\n";
      newUnits.push_back(core[0]);
    }
  }
  vector<int> tmp;
  std::swap(occurList[clsi], tmp); //soft clause clsi now has a sat count of zero.
  init_sc[clsi] = 0;
  
  for(auto sci: newUnits) {
    clsVal[sci] = l_True;
    processTrueB(sci);        //This cannot generate any new units
  }
}  

vector<Lit> GreedySolver::solve_() {
  //Compute greedy solution. 
  vector<int> satCount {init_sc};
  vector<int> soln;
  vector<char> dyn_coreIsSat {coreIsSat};
  int dyn_nSatCores = nsatCores;

  struct ClsOrderLt {
    //minisat heap is a min-heap. Want the "minimum" soft clause to 
    //satisfies the most cores for the least wt. I.e., 
    //x < y if satcount(x)/wt(x) > satcount(x)/wt(y)
    //assume that weights are non-zero.
    bool operator() (int x, int y) const {
      double diff = sc[x]*1.0/bvars.wtNcls(x) - sc[y]*1.0/bvars.wtNcls(y);
      if(diff > 0)
	return true;
      if(diff < 0)
	return false;
      return x < y;
    }
    Bvars& bvars;
    vector<int>& sc;
    ClsOrderLt(Bvars& b, vector<int>& c) : bvars (b), sc (c) {}
  };

  Heap<int,ClsOrderLt> sftcls_heap {ClsOrderLt {bvars,satCount}}; 

  for(size_t i = 0; i < satCount.size(); i++)
    if(satCount[i] > 0) 
      sftcls_heap.insert(i);

  while(dyn_nSatCores < static_cast<int>(cores.size()) && !sftcls_heap.empty()) {
    auto next = sftcls_heap.removeMin();
    //cout << "Processing blit " << bvars.litOfCls(next) << "\n";
    //cout << "dyn_nSatCores = " << dyn_nSatCores << "\n";
    soln.push_back(next);
    //update heap
    for(auto corei : occurList[next])
      if(dyn_coreIsSat[corei]==0) {
	  dyn_coreIsSat[corei] = 1;
	  ++dyn_nSatCores;
	  auto core = cores[corei];
	  for(auto clsi: core)  //update soft clauses of core.
	    if(sftcls_heap.inHeap(clsi)) {
	      satCount[clsi] -= 1;
	      sftcls_heap.increase(clsi);
	    }
      }
  }
  /*cout << "Greedy solver soln: [";
  for(auto clsi : soln)
    cout << bvars.litOfCls(clsi) << ", ";
  cout << "]\n";*/
 
  vector<Lit> tmp;
  for(size_t i = 0; i < static_cast<size_t>(bvars.n()); i++) 
    if(i >= clsVal.size() || clsVal[i] != l_True)
      tmp.push_back(~bvars.litOfCls(i)); //harden soft is default;
    else 
      tmp.push_back(bvars.litOfCls(i));

  for(auto clsi : soln) 
    tmp[clsi] = bvars.litOfCls(clsi);
   
  return tmp;
}

void GreedySolver::printDS() {
  cout << "GreedySolver Data Structures:\n";
  for(size_t i=0; i < cores.size(); ++i) {
    cout << "Core #" << i << ": [";
    for(auto sc: cores[i])
      cout << bvars.litOfCls(sc) << ", ";
    cout << "] (" << cores[i].size() << ") ";
    cout << " core is sat = " << ((coreIsSat[i] == 1) ? 1 : 0) << "\n";
  }
  cout << "Number of satisfied cores = " << nsatCores << "\n";

  for(size_t i=0; i < occurList.size(); ++i) {
    cout << "Lit " << bvars.litOfCls(i) << ": [";
    for(auto ci: occurList[i])
      cout << ci << ", ";
    cout << "] (" << occurList[i].size() << ") ";
    cout << " initial sat count = " << init_sc[i];
    cout << " initial value = " << clsVal[i];
    cout << "\n";
  }
}
