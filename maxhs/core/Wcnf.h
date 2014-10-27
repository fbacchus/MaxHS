/***********[Wcnf.h]
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

#ifndef WCNF_H
#define WCNF_H

#include <string>
#include <vector>
#include <limits>
#include <iostream>
#include "maxhs/ds/Packed.h"
#include "maxhs/core/MaxSolverTypes.h"
#include "minisat/core/SolverTypes.h"

using std::cout;
using Minisat::Lit;

/* Store a weighted CNF formula */
enum class MStype { undef, ms, pms, wms, wpms };

class Wcnf
{
public:
  //Parsing
  bool inputDimacs(std::string filename);
  void set_dimacs_params(int nvars, int nclauses, Weight top = std::numeric_limits<Weight>::max());
  void addDimacsClause(vector<Lit> &lits, Weight w); //Changes input vector lits
  double parseTime() const { return parsing_time; }

  //print info
  void printFormulaStats();
  void printFormula(std::ostream& out = std::cout) const;

  //api-support for adding hard or soft clauses
  void addHardClause(vector<Lit> &lits) {
    hard_cls.addVec(lits);
  }
  
  void addSoftClause(vector<Lit> &lits, Weight w) {
    if (w < 0) 
      cout << "c ERROR: soft clause cannot have negative weight: " << w << "\n";
    else if (w > 0) { //zero weigh softs are tautological
      soft_cls.addVec(lits);
      soft_clswts.push_back(w);
      total_wt += w;
    }
  }

  //data setters and getters
  const Packed_vecs<Lit>& hards() const { return hard_cls; }
  const Packed_vecs<Lit>& softs() const { return soft_cls; }
  const vector<Weight>& softWts() const { return soft_clswts; }
  vector<Lit> getSoft(int i) const { return soft_cls.getVec(i); }
  vector<Lit> getHard(int i) const { return hard_cls.getVec(i); }
  Weight getWt(int i) const { return soft_clswts[i]; }

  Weight dimacsTop() const { return dimacs_top; }
  Weight totalWt() const { return total_wt; }
  Weight minSftWt() const { return wt_min; }
  Weight maxSftWt() const { return wt_max; }
  int nDiffWts() const { return wt_n_diff; }
  Weight aveSftWt() const { return wt_mean; }
  Weight varSftWt() const { return wt_var; }
  size_t nHards() const { return hard_cls.size(); }
  size_t nSofts() const { return soft_cls.size(); }
  int nOrigVars() const { return maxvar+1; }
  MStype mstype() const { return ms_type; }
  const std::string& fileName() const { return instance_file_name; }
  Wcnf();  

private:
  int maxvar;
  int dimacs_nvars;
  int dimacs_nclauses;
  int wt_n_diff;
  MStype ms_type;
  double parsing_time;
  Weight total_wt;
  Weight dimacs_top;  //weight of a hard clause...typically sum of soft clause weights + 1
  Weight wt_var, wt_mean, wt_min, wt_max;
  std::string instance_file_name;
  Packed_vecs<Lit> hard_cls;
  Packed_vecs<Lit> soft_cls;
  vector<Weight> soft_clswts;
};

inline  Wcnf::Wcnf() :
  maxvar{0},
  dimacs_nvars{0},
  dimacs_nclauses{0},
  wt_n_diff{0},
  ms_type{MStype::undef},
  parsing_time{0},
  total_wt{0},
  dimacs_top{std::numeric_limits<Weight>::max()},
  wt_var {0},
  wt_mean {0}
{}
    
inline void Wcnf::set_dimacs_params(int nvars, int nclauses, Weight top)
{
    dimacs_nvars = nvars;
    dimacs_nclauses = nclauses;
    dimacs_top = top;
}

#endif
