/***********[Totalizers.cc]
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

#include "Totalizer.h"
#include <algorithm>
#include <initializer_list>
#include <iostream>
#include <memory>
#include "TotalizerManager.h"

using std::vector;

vector<Totalizer> Totalizer::all_totalizers{};

TRef Totalizer::makeTotalizer(TotalizerManager& tm,
                              const vector<Lit>& inputLits, Weight wt) {
  assert(!inputLits.empty());
  Totalizer t0{tm, inputLits, wt};
  Totalizer::all_totalizers.push_back(t0);
  return TRef{Totalizer::all_totalizers.size() - 1};
}

TRef Totalizer::makeTotalizer(TotalizerManager& tm,
                              const vector<Lit>& inputLits, size_t start,
                              size_t end, Weight wt) {
  assert(!inputLits.empty());
  Totalizer t0{tm, inputLits, start, end, wt};
  Totalizer::all_totalizers.push_back(t0);
  return TRef{Totalizer::all_totalizers.size() - 1};
}

TRef Totalizer::makeTotalizer(TotalizerManager& tm, TRef rT, TRef lT) {
  Totalizer::all_totalizers.emplace_back(tm, rT, lT);
  return TRef{Totalizer::all_totalizers.size() - 1};
}

Totalizer& Totalizer::getTotalizer(TRef idx) {
  assert(0 <= idx && idx < static_cast<int>(all_totalizers.size()));
  return all_totalizers[idx];
}

Totalizer::Totalizer(TotalizerManager& tm, const vector<Lit>& inputLits,
                     Weight wt)
    : Totalizer{tm, inputLits, 0, inputLits.size(), wt} {}

Totalizer::Totalizer(TotalizerManager& tm, const vector<Lit>& inputLits,
                     size_t start, size_t end, Weight wt)
    : weight{wt} {
  assert(end <= inputLits.size());
  assert(start < inputLits.size());
  nb_inputs = static_cast<int>(end - start);
  assert(nb_inputs != 0);
  _maxFalse = 0;
  _maxTrue = 0;

  if (nb_inputs == 1) {
    rightT = NullTRef;
    leftT = NullTRef;
    output_lits.push_back(
        inputLits[start]);  // no needed to connect output and input lits.
    _maxFalse = 1;
    _maxTrue = 1;
  } else {
    size_t mid = start + nb_inputs / 2;
    leftT = makeTotalizer(tm, inputLits, start, mid, wt);
    rightT = makeTotalizer(tm, inputLits, mid, end, wt);
    for (int i = 0; i < nb_inputs; i++)
      output_lits.push_back(tm.getNewOutputLit());
  }
}

Totalizer::Totalizer(TotalizerManager& tm, TRef lT, TRef rT) {
  assert(rT != NullTRef && lT != NullTRef);
  rightT = rT;
  leftT = lT;
  nb_inputs = (*rightT).nb_inputs + (*leftT).nb_inputs;
  weight = (*rightT).weight;
  _maxFalse = 0;
  _maxTrue = 0;
  for (int i = 0; i < nb_inputs; i++)
    output_lits.push_back(tm.getNewOutputLit());
}

void Totalizer::increaseMaxFalse(int maxFalse, vector<vector<Lit>>& clauses) {
  // maxFalse is max number of outputs that must constraint inputs when false.
  // We must ensure that nOutTrue for the right and the left totalizer childen
  // have been properly set! Note that maxFalse means that the totalizer must
  // sum up maxFalse true inputs (so that when we set the maxFalse output to
  // false we allow < maxFalse inputs to be true)

  if (rightT == NullTRef && leftT == NullTRef) return;
  assert(rightT != NullTRef && leftT != NullTRef);
  maxFalse = std::min(maxFalse, nb_inputs);
  // we already know that nOutTrue outs are true...so _maxFalse can't
  // be smaller than this
  _maxFalse = std::max(_maxFalse, nOutTrue);
  if (maxFalse <= _maxFalse) return;

  // give children a chance to update in case they have a lower
  // current _maxFalse. Given that left contributes k true inputs
  // right only has to sum its true inputs up to maxFalse-k (if it
  // sums that many true inputs this will be sufficent to sum the
  // parent to maxFalse.

  (*rightT).increaseMaxFalse(maxFalse - (*leftT).nOutTrue, clauses);
  (*leftT).increaseMaxFalse(maxFalse - (*rightT).nOutTrue, clauses);
  getAtLeastCNF(clauses, _maxFalse + 1, maxFalse);
  _maxFalse = maxFalse;
}

void Totalizer::increaseMaxTrue(int maxTrue, vector<vector<Lit>>& clauses) {
  // TODO account for know false outputs.
  // maxTrue is max number of outputs that must constrain input when true
  if (rightT == NullTRef && leftT == NullTRef) return;
  assert(rightT != NullTRef && leftT != NullTRef);
  maxTrue = std::min(maxTrue, nb_inputs);
  if (maxTrue <= _maxTrue) return;

  // give children a chance to update their UB in case they have a lower
  // current UB than this parent
  (*rightT).increaseMaxTrue(maxTrue, clauses);
  (*leftT).increaseMaxTrue(maxTrue, clauses);

  // Now update ours and generate our new clauses
  getAtMostCNF(clauses, _maxTrue + 1, maxTrue);
  _maxTrue = maxTrue;
}

void Totalizer::getCNF(vector<vector<Lit>>& clauses) const {
  if (rightT == NullTRef && leftT == NullTRef) return;

  assert(rightT != NullTRef && leftT != NullTRef);

  (*rightT).getCNF(clauses);  // encode right outputs
  (*leftT).getCNF(clauses);   // encode left ouputs

  getAtLeastCNF(clauses, 1, _maxFalse);  // encode this totalizers outputs.
  getAtMostCNF(clauses, 1, _maxTrue);
}

void Totalizer::getAtLeastCNF(vector<vector<Lit>>& clauses, int low,
                              int high) const {
  // Return clauses capturing if j inputs are true then the j-th
  // output must be true (i.e. output_lits[j-1]=l_true), for values of
  // j in range [low, high] inclusive. By the contrapositive
  // -output_lits[j-1] for j in [low, high] implies that less
  // than j inputs are true. These clauses capture that the
  // output is as least as large as the number of true inputs.
  assert(low > 0);
  assert(high <= static_cast<int>(output_lits.size()));
  if (low > high) return;

  Totalizer& right = *rightT;
  Totalizer& left = *leftT;
  auto& r_outs = right.output_lits;
  auto& l_outs = left.output_lits;
  int r_max = r_outs.size();
  int l_max = l_outs.size();

  // A) if right (left) has j true outputs then the j-th output is true.
  for (int r = low; r <= r_max && r <= high; r++)
    clauses.emplace_back(
        std::initializer_list<Lit>{~r_outs[r - 1], output_lits[r - 1]});

  for (int l = low; l <= l_max && l <= high; l++)
    clauses.emplace_back(
        std::initializer_list<Lit>{~l_outs[l - 1], output_lits[l - 1]});

  // B) output m (m >= low, m <=high) is true if right has j>=1 true
  // outputs and left has k>=1 true outputs where j+k = m. (right or
  // left with 0 true outputs are handled by case A)
  for (int m = low; m <= high; m++)
    for (int r = 1; r <= r_max && r < m; r++) {
      int l = m - r;
      if (l <= l_max)
        clauses.emplace_back(std::initializer_list<Lit>{
            ~l_outs[l - 1], ~r_outs[r - 1], output_lits[m - 1]});
    }
}

void Totalizer::getAtMostCNF(vector<vector<Lit>>& clauses, int low,
                             int high) const {
  // Return clauses capturing if < j inputs are true then output_lit[j-1]
  // must be false for j in range [low, high] inclusive. These
  // clauses capture that the output is at most large as the number of
  // true inputs. By the contrapositive output_lits[j-1] for j in [low,high]
  // 1-based implies that >= j inputs are true.
  assert(low > 0);
  assert(high <= static_cast<int>(output_lits.size()));
  if (low > high) return;

  Totalizer& right = *rightT;
  Totalizer& left = *leftT;
  auto& r_outs = right.output_lits;
  auto& l_outs = left.output_lits;
  int r_max = r_outs.size();
  int l_max = l_outs.size();

  // A) At most left.nb_inputs can be true from the left. Therefore
  //    if the r-th right output is false, then for this totalizer
  //    at most (r-1)+left.nb_inputs can be true over both children
  //    So the m-th output with m = r+left.nb_inputs must be false.
  //    Similar reasoning applies wrt to the l-th output of the left child.

  for (int m = low; m <= high; m++) {
    int r = m - left.nb_inputs;
    if (r >= 1 && r <= r_max)
      clauses.emplace_back(
          std::initializer_list<Lit>{r_outs[r - 1], ~output_lits[m - 1]});
    int l = m - right.nb_inputs;
    if (l >= 1 && l <= l_max)
      clauses.emplace_back(
          std::initializer_list<Lit>{l_outs[l - 1], ~output_lits[m - 1]});
  }

  // B) output m-1 (m-1 >= low, m-1 <=high) is false if right has
  //   < r true inputs and left has < l true inputs where r+l =
  //   m. In particular, at most r-1 + l-1 = r+l-2 inputs can be
  //   true, so at most r+l-2 ouputs can be true. Therefore output
  //   r+l-1 = m-1 must be false.
  for (int m = low + 1; m <= high + 1; m++)
    for (int r = 1; r <= r_max && r < m; r++) {
      int l = m - r;
      if (l <= l_max && m >= 2)
        clauses.emplace_back(std::initializer_list<Lit>{
            l_outs[l - 1], r_outs[r - 1], ~output_lits[m - 2]});
    }
}

void Totalizer::getInputs(vector<Lit>& inputs) const {
  if (rightT == NullTRef && leftT == NullTRef) {
    for (auto l : output_lits) inputs.push_back(l);
  } else {
    assert(rightT != NullTRef && leftT != NullTRef);
    (*rightT).getInputs(inputs);
    (*leftT).getInputs(inputs);
  }
}
