/***********[SortNet.h]
Copyright (c) 2019, Fahiem Bacchus

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

Some code and ideas from

  Open-WBO, Copyright (c) 2013-2017, Ruben Martins, Vasco Manquinho, Ines Lynce

have been used;
  Open-WBO is subject to the following LICENSE
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
***********/

#ifndef SortNet_h
#define SortNet_h

#include <iostream>
#include <vector>

#include "maxhs/core/MaxSolverTypes.h"
#include "maxhs/core/SumAuxStruct.h"
#include "maxhs/utils/io.h"

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

using Minisat::Lit;
using Minisat::Var;
using std::vector;

class SortNet {
  friend class SumManager;

 public:
  // use only these static makeSortNet routines to make sorting networks.
  // due to internal storage of all SortNet.

  // 1. Build the a sort net over inputLits.
  static SRef makeSortNet(SumManager& tm, const vector<Lit>& inputLits,
                          Weight w);

  // 2. Build sort net by joining two previous sortnet referred to rightSRef
  // and leftSRef
  static SRef makeSortNet(SumManager& tm, SRef rS, SRef lS);

  static SortNet& getSortNet(SRef idx) {
    assert(0 <= idx && idx < static_cast<int>(all_sortNets.size()));
    return all_sortNets[int(idx)];
  }

  static size_t getNbSortNets() { return all_sortNets.size(); }
  const vector<Lit>& getOutputs() const { return output_lits; }
  vector<Lit> getInputs() const { return input_lits; }
  size_t getSize() const { return input_lits.size(); };
  int getOutTrue() const { return nOutTrue; }
  int getOutFalse() const { return nOutFalse; }
  void setNOutTrue(int t) { nOutTrue = t; }
  void setNOutFalse(int t) { nOutFalse = t; }
  Weight getWeight() const { return weight; }
  bool isTopLevel() const { return toplevel; }
  bool isExhausted() const { return exhausted; }
  void setTopLevel() { toplevel = true; }
  void unsetTopLevel() { toplevel = false; }
  void setExhausted() { exhausted = true; }
  void unsetExhausted() { exhausted = false; }
  SRef getRight() const { return rightS; }
  SRef getLeft() const { return leftS; }

  SortNet(SumManager& sm, const vector<Lit>& inputLits, Weight w);
  SortNet(SumManager& sm, SRef rS, SRef lS);
  friend std::ostream& operator<<(std::ostream& os, const SortNet& tot);

 private:
  vector<Lit> output_lits;
  vector<Lit> input_lits;
  int nOutTrue{0}, nOutFalse{0};
  Weight weight;
  SRef leftS{}, rightS{};
  bool toplevel{false}, exhausted{false};

  static vector<SortNet> all_sortNets;
  vector<Lit> odd_even_sort(SumManager& tm, const vector<Lit>& inputLits);
  vector<Lit> odd_even_merge(SumManager& tm, SRef lS, SRef rS);
  void oe_merge(SumManager& tm, vector<Lit>& in, int begin, int end);
  void cmp2(SumManager& tm, vector<Lit>& in, int begin);
  void oe_separate(vector<Lit>& v);
  void oe_join(vector<Lit>& v);

  vector<Lit> direct_merge(SumManager& tm, const vector<Lit>& lits1,
                           const vector<Lit>& lits2);
  // projected number of clauses of different encodings
  // recursive merge
  int MR_size(int a, int b);
  // direct merge
  int MD_size(int a, int b);
  // recursive sort
  int SR_size(int n);
  // direct sort
  int SD_size(int n);
  vector<Lit> direct_sort(SumManager& tm, const vector<Lit>& inputLits, int s,
                          int e);
};

// Interface with SortNet class
inline SortNet* SRef::operator->() const { return &SortNet::getSortNet(idx); }

inline std::ostream& operator<<(std::ostream& os, const SortNet& snet) {
  os << "SortNet: weight = " << wt_fmt(snet.weight)
     << " trueOuts = " << snet.nOutTrue << " falseOuts = " << snet.nOutFalse
     << "\n"
     << " outputs = " << snet.output_lits << "\n"
     << " inputs = " << snet.getInputs() << "\n";
  return os;
}

#endif
