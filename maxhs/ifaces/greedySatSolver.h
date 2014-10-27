/***********[greedySatSolver.h]
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

/* greedysat interface
*/

#ifndef GREEDYSATSOLVER_H
#define GREEDYSATSOLVER_H

#include "maxhs/core/MaxSolverTypes.h"
#include "maxhs/core/Bvars.h"
#include "maxhs/ifaces/miniSatSolver.h"

namespace MaxHS_Iface {
  class GreedySolver : public miniSolver {
  public:
    GreedySolver(Bvars b);
    virtual ~GreedySolver();
    bool addClause(const vector<Lit>& lts);
    
  protected:
    Lit pickBranchLit();
    void syncTrails();
    int satCount(Lit l);
    vector<Lit> myTrail;
    vector<vector<int>> occurList;
    Bvars bvars;
    int nclauses;
    int nsatClauses;
    vector<Lit> clsIsSat;

    Weight litWt(Lit l) {
      //get weight of internal literal map to external and use bvars.
      return bvars.wt(in2ex(l));
    }

    bool better(int sc1, Weight wt1, int sc2, Weight wt2) {
      //return true if the metric (sc1, w1) (satcount, litwt)
      //represents a better choice than (sc2, w2).
      if(wt1 == 0 && wt2 == 0)
	return sc1 > sc2;
      else if(wt1 == 0 && wt2 > 0)
	return (sc1 > 0 || sc2 == 0);
      else if(wt1 > 0 && wt2 == 0)
	return (sc1 > 0 && sc2 == 0);
      else //(wt1 > 0 && wt2 > 0)
	return sc1/wt1 > sc2/wt2;
    }

    lbool solve_(const vector<Lit>& assumps, vector<Lit>& conflict,
		 int64_t confBudget, int64_t propBudget);
  };

  
} //end namespace

#endif 
