/***********[Bvars.cc]
Copyright (c) 2012-2015 Jessica Davies, Fahiem Bacchus

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

#include "maxhs/core/Bvars.h"
#include <algorithm>
#include <ostream>

Bvars::Bvars(const Wcnf* f)
    : theWcnf{f},
      nBvars{theWcnf->nSofts()},
      nOvars{theWcnf->nVars()},
      clsBlit{theWcnf->nSofts(), Minisat::lit_Undef},
      var_types(theWcnf->nVars()),
      mxNum(theWcnf->nVars(), -1) {

  for (auto& cls : theWcnf->hards())
    for (auto l : cls) var_types[var(l)].original = true;
  for (auto& cls : theWcnf->softs())
    for (auto l : cls) var_types[var(l)].original = true;

  int maxbvar = -1;
  for (size_t i = 0; i < theWcnf->nSofts(); i++) {
    auto scls = theWcnf->softs()[i];
    if (scls.size() == 1)
      clsBlit[i] = ~scls[0];  // blit false means clause must be satisfied
    else
      clsBlit[i] = mkLit(make_newVar());
    maxbvar = std::max(maxbvar, var(clsBlit[i]));
  }

  bvarCls.resize(maxbvar + 1, -1);
  for (size_t i = 0; i < theWcnf->nSofts(); i++) {
    auto blit = clsBlit[i];
    bvarCls[var(clsBlit[i])] = i;
    var_types[var(blit)].bvar = true;
    if(!sign(blit)) var_types[var(blit)].core_is_pos = true;
  }

  // process mutexes
  mxNum.resize(n_vars(), -1);
  for (size_t i = 0; i < theWcnf->get_SCMxs().size(); i++) {
    auto& mx = theWcnf->get_SCMxs()[i];
    if (mx.encoding_lit() != Minisat::lit_Undef) {
      var_types[var(mx.encoding_lit())].Var_type::dvar = true;
      mxNum[var(mx.encoding_lit())] = i;
    }
    for (auto l : mx.soft_clause_lits()) {
      var_types[var(l)].in_mutex = true;
      if (!sign(l)) var_types[var(l)].orig_core_is_pos = true;
      mxNum[var(l)] = i;
    }
  }
}

void Bvars::printVars() {
  for (size_t i = 0; i < n_vars(); i++) {
    cout << "Var #" << i + 1 << "." << var_types[i] << "\n";
    cout << "is bvar: " << isBvar(i) << "\n";
    if (isBvar(i)) {
      auto clsi = clsIndex(i);
      Lit blit = litOfCls(clsi);
      cout << "Clause " << clsi << ". blit = " << blit << " "
           << theWcnf->getSoft(clsi) << "\n";
      cout << "coreIsPos(" << blit << ") = " << coreIsPos(blit);
      cout << " sign(" << blit << ") = " << sign(blit);
      cout << " isCore(" << blit << ") = " << isCore(blit) << " isNonCore("
           << blit << ") = " << isNonCore(blit) << "\n";
    }
    if (inMutex(i)) {
      cout << "In mutex " << getMxNum(i) << " "
           << theWcnf->get_SCMxs()[getMxNum(i)] << "\n";
      cout << "orig_IsCore(" << mkLit(i) << ") = " << orig_IsCore(mkLit(i))
           << " orig_IsNonCore(" << mkLit(i)
           << ") = " << orig_IsNonCore(mkLit(i)) << "\n";
    }
    cout << "\n";
  }
}

void Bvars::print_var_types() {
  for (size_t i = 0; i < var_types.size(); i++)
    cout << "Var " << i + 1 << " type = " << var_types[i] << "\n";
}

std::ostream& operator<<(std::ostream& os, const Var_type& x) {
  if (x.original) os << "original ";
  if (x.bvar) os << "bvar ";
  if (x.core_is_pos) os << "core_is_pos ";
  if (x.in_mutex) os << "in_mutex ";
  if (x.orig_core_is_pos)
    os << "orig_core_is_pos ";
  if (x.dvar) os << "dvar ";
  if (x.summation) os << "summation ";
  if (!x.original && !x.bvar && !x.core_is_pos
      && !x.in_mutex && !x.orig_core_is_pos &&
      !x.dvar && !x.summation) os << "not_in_theory ";

  return os;
}
