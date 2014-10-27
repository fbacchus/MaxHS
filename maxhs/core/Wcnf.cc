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
#include "maxhs/core/Wcnf.h"
#include "minisat/utils/System.h"
#include "maxhs/utils/io.h"
#include "maxhs/core/Dimacs.h"
#include "minisat/core/SolverTypes.h"

bool Wcnf::inputDimacs(std::string filename) 
{
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

  vector<Weight> wts(soft_clswts);
  std::sort(wts.begin(), wts.end());
  if (wts.size() > 0) {
    wt_min = wts.front();
    wt_max = wts.back();
  }
  Weight old{-1}; //soft clause weights should be >=0!
  for(auto x : wts) {
    wt_mean += x;
    if(x != old) {
      wt_n_diff++;
      old = x;
    }
  }
  wt_mean /= wts.size();
  for(auto x : wts)
    wt_var += (x-wt_mean)*(x-wt_mean);
  wt_var /= wts.size()-1;

  if(hard_cls.size() > 0) {
    if(wt_n_diff > 1)
      ms_type = MStype::wpms;
    else
      ms_type = MStype::pms;
  }
  else {
    if(wt_n_diff > 1)
      ms_type = MStype::wms;
    else
      ms_type = MStype::ms;
  }
  parsing_time = Minisat::cpuTime() - start_time;
  return true;
}

void Wcnf::addDimacsClause(vector<Lit> &lits, Weight w) {
  //This routine needs to know dimacs_top (so set_dimacs_params should
  //have been called first) to determine if the clause is soft or hard
  if(lits.size() > 1) {
    std::sort(lits.begin(), lits.end());
    size_t cur_size, examine;
    for(cur_size = examine = 1; examine < lits.size(); examine++) {
      if(lits[cur_size-1] == ~lits[examine]) {
	return; //Tautologies can be excluded.
      }
      if(lits[cur_size-1] != lits[examine])
	lits[cur_size++] = lits[examine];
    }
    lits.resize(cur_size);
  }
  
  if(maxvar < Minisat::var(lits.back()))
     maxvar = Minisat::var(lits.back());

  if (w >= dimacs_top) 
    addHardClause(lits);
  else
    addSoftClause(lits, w);
}

void Wcnf::printFormulaStats() {
  cout << "c Instance: " << instance_file_name << "\n";
  cout << "c Dimacs Vars: " << dimacs_nvars << "\n";
  cout << "c Dimacs Clauses: " << dimacs_nclauses << "\n";
  cout << "c HARD: #Clauses = " << hard_cls.size()
       << ", Total Lits = " << hard_cls.total_size() 
       << ", Ave Len = " << ((hard_cls.size() > 0) ? (1.0*hard_cls.total_size())/hard_cls.size() : 0.0) << "\n";
  cout << "c SOFT: #Clauses = " << soft_cls.size()
       << ", Total Lits = " << soft_cls.total_size() 
       << ", Ave Len = " << (1.0*soft_cls.total_size())/soft_cls.size() << "\n";
  cout << "c Total Soft Clause Weight: " << total_wt << ", Dimacs Top = " << dimacs_top << "\n";
  cout << "c SOFT%: " << (100.0*soft_cls.size())/(soft_cls.size()+hard_cls.size()) << "%\n";
  cout << "c #distinct weights: " << wt_n_diff << ", mean = " << wt_mean
       << ", std. dev = " << std::sqrt(wt_var) << ", min = " << wt_min << ", max = " << wt_max << "\n";
  cout << "c Total Clauses: " << hard_cls.size() + soft_cls.size() << "\n";
  cout << "c Parse time: " << parsing_time << "\n";
  cout << "c Wcnf Space Required: " << ((hard_cls.total_size()+soft_cls.total_size())*sizeof(Lit) + soft_clswts.size()*sizeof(Weight))/1000000.0 << "MB\n";
  cout << "c ================================" << std::endl;
}


void Wcnf::printFormula(std::ostream& out) const {
  out << "c Wcnf---Print Formula\n";
  out << "c Dimacs (Vars, Clauses, TOP) = (" << dimacs_nvars
      << " ," << dimacs_nclauses
      << " ," << dimacs_top << ")";
  out << " maxvar =" << maxvar << "\n";
  out << "c Hard Clauses (" << hard_cls.size() << ")";
  int nzeros {0};
  for(const auto& v : hard_cls)
    if (v.size() == 0) nzeros++;
  if (nzeros)
    out << " (" << nzeros << " zero length clauses)";
  out << "\n";
  out << hard_cls;
  
  out << "c Soft Clauses, # = " << soft_cls.size();
  nzeros = 0;
  for(const auto& v : soft_cls)
    if (v.size() == 0) nzeros++;
  if (nzeros)
    out << " (" << nzeros << " zero length clauses)";
  out << "\n";
  for(size_t i = 0; i < soft_cls.size(); i++) {
    out << soft_clswts[i] << " ";
    for(auto& item : soft_cls[i])
      out << item << " ";
    out << "0 \n";
  }
}

