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
#include "maxhs/core/Bvars.h"

Bvars::Bvars(const Wcnf* f) :
  theWcnf {f}, 
  maxbvar {0},
  clsBlit {theWcnf->nSofts(), Minisat::lit_Undef},
  bvarCls {}
  {
    Var nxtbvar {theWcnf->nVars()};
    for(size_t i = 0; i < theWcnf->nSofts(); i++) {
      auto scls = theWcnf->softs()[i];
      if(scls.size() == 1) 
	clsBlit[i] = ~scls[0]; //blit false means clause must be satisfied
      else
	clsBlit[i] = mkLit(nxtbvar++);
      maxbvar = maxbvar < var(clsBlit[i]) ? var(clsBlit[i]) : maxbvar;
    }
    bvarCls.resize(maxbvar+1, -1);
    for(size_t i = 0; i < theWcnf->nSofts(); i++) 
      bvarCls[var(clsBlit[i])] = i;
  }
