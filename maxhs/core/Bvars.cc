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

#include <ostream>
#include <algorithm>
#include "maxhs/core/Bvars.h"

Bvars::Bvars(const Wcnf* f) :
  theWcnf {f}, 
  maxbvar {0},
  clsBlit {theWcnf->nSofts(), Minisat::lit_Undef},
  bvarCls  {},
  var_types (theWcnf->nVars(), Var_type::not_in_theory),
  mxNum (theWcnf->nVars(), -1)
{
  Var nxtbvar {theWcnf->nVars()};

  for(auto& cls : theWcnf->hards())
    for(auto l : cls)
      var_types[var(l)] = Var_type::original;
  for(auto& cls : theWcnf->softs())
    for(auto l : cls)
      var_types[var(l)] = Var_type::original;

  for(size_t i = 0; i < theWcnf->nSofts(); i++) {
    auto scls = theWcnf->softs()[i];
    if(scls.size() == 1) 
      clsBlit[i] = ~scls[0]; //blit false means clause must be satisfied
    else
      clsBlit[i] = mkLit(nxtbvar++);
    maxbvar = std::max(maxbvar, var(clsBlit[i]));
  }

  bvarCls.resize(maxbvar+1, -1);
  for(size_t i = 0; i < theWcnf->nSofts(); i++) 
    bvarCls[var(clsBlit[i])] = i;
  
  if(static_cast<size_t>(maxvar()) >= var_types.size())
    var_types.resize(maxvar()+1, Var_type::not_in_theory);

  for(size_t i = 0; i < theWcnf->nSofts(); i++) {
    auto blit = clsBlit[i];
    var_types[var(blit)] = var_types[var(blit)] | Var_type::bvar;
    if(!sign(blit)) var_types[var(blit)] = var_types[var(blit)] | Var_type::core_is_pos;
  }
  
  //process mutexes
  mxNum.resize(maxvar()+1, -1);
  for(size_t i =0; i < theWcnf->get_SCMxs().size(); i++) {
    auto& mx = theWcnf->get_SCMxs()[i];
    if(mx.encoding_lit() != Minisat::lit_Undef) {
      var_types[var(mx.encoding_lit())] = var_types[var(mx.encoding_lit())] | Var_type::dvar;
      mxNum[var(mx.encoding_lit())] = i;
    }
    for(auto l : mx.soft_clause_lits()) {
      var_types[var(l)] = var_types[var(l)] | Var_type::in_mutex;
      if(!sign(l))
        var_types[var(l)] = var_types[var(l)] | Var_type::orig_core_is_pos;
      mxNum[var(l)] = i;
    }
  }
}

void Bvars::printVars() {
  for(int i = 0; i <= maxvar(); i++) {
    cout << "Var #" << i+1 << "." << var_types[i] << "\n";
    if(isBvar(i)) {
      auto clsi = clsIndex(i);
      Lit blit = litOfCls(clsi);
      cout << "Clause " << clsi << ". blit = " << blit << " " << theWcnf->getSoft(clsi) << "\n";
      cout << "coreIsPos(" << blit << ") = " << coreIsPos(blit);
      cout << " sign(" << blit << ") = " << sign(blit);
      cout << " isCore(" << blit << ") = " << isCore(blit)
           << " isNonCore(" << blit << ") = " << isNonCore(blit) << "\n";
    }
    if(inMutex(i)) {
      cout << "In mutex " << getMxNum(i) << " " << theWcnf->get_SCMxs()[getMxNum(i)] << "\n";
      cout << "orig_IsCore(" << mkLit(i) << ") = " << orig_IsCore(mkLit(i))
           << " orig_IsNonCore(" << mkLit(i) << ") = " << orig_IsNonCore(mkLit(i)) << "\n";
    }
    cout << "\n";
  }
}

void Bvars::print_var_types() {
  for(size_t i=0; i < var_types.size(); i++)
    cout << "Var " << i+1 << " type = " << var_types[i] << "\n";
}

ostream& operator<<(ostream& os, const Var_type& x) {
  if(x == Var_type::not_in_theory)
    os << "not_in_theory, ";
  if(to_bool(x & Var_type::original))
    os << "original, ";
  if(to_bool(x & Var_type::bvar))
    os << "blocking var, ";
  if(to_bool(x & Var_type::core_is_pos))
    os << "positive is core, ";
  if(to_bool(x & Var_type::in_mutex))
    os << "in mutex, ";
  if(to_bool(x & Var_type::orig_core_is_pos))
    os << "positive is original core, ";
  if(to_bool(x & Var_type::dvar))
    os << "defined var, ";
  return os;
}
