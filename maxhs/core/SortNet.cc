/***********[SortNet.cc]
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
***********/

#include "maxhs/core/SortNet.h"
#include <algorithm>
#include <initializer_list>
#include <iostream>
#include <memory>
#include "maxhs/core/SumManager.h"

using std::vector;

vector<SortNet> SortNet::all_sortNets{};

SRef SortNet::makeSortNet(SumManager& sm,
                              const vector<Lit>& inputLits, Weight wt) {
  assert(!inputLits.empty());
  SortNet t0{sm, inputLits, wt};
  SortNet::all_sortNets.push_back(t0);
  return SRef{SortNet::all_sortNets.size() - 1};
}

SRef SortNet::makeSortNet(SumManager& sm, SRef rS, SRef lS) {
  SortNet::all_sortNets.emplace_back(sm, rS, lS);
  return SRef{SortNet::all_sortNets.size() - 1};
}

SortNet::SortNet(SumManager& sm, const vector<Lit>& inputLits,
                     Weight wt)
    : input_lits{inputLits}, weight{wt} {
  assert(!input_lits.empty() != 0);
  output_lits = odd_even_sort(sm, input_lits);
}

SortNet::SortNet(SumManager& sm, SRef lS, SRef rS)
    : nOutTrue{lS->nOutTrue + rS->nOutTrue},
      nOutFalse{lS->nOutFalse + rS->nOutFalse},
      weight{lS->weight},
      leftS{lS},
      rightS{rS} {
  input_lits = lS->input_lits;
  input_lits.insert(input_lits.end(), rS->input_lits.begin(),
                    rS->input_lits.end());
  output_lits = odd_even_merge(sm, lS, rS);
}

// Sorting networks. Based on the elegant implementation of Ens and
// Sorresson used in their minisat+ system.
// TODO later try direct merges and direct sort for short enough inputs.

// Top level interface.
vector<Lit> SortNet::odd_even_sort(SumManager& sm,
                                     const vector<Lit>& in) {
  vector<Lit> out{in};
  int orig_sz = out.size();
  if (orig_sz <= 1) return out;
  if (orig_sz == 2) {
    cmp2(sm, out, 0);
    return out;
  }
  // pad to power of two (size 4 or larger)
  int sz;
  for (sz = 1; sz < static_cast<int>(out.size()); sz *= 2)
    ;
  out.resize(sz, lit_Undef);  // pad with falses

  for (int i{1}; i < static_cast<int>(out.size()); i *= 2)
    // in blocks of increasing powers of 2 size
    for (int j{}; j < static_cast<int>(out.size()); j += 2 * i)
      // for j at the start of each block of size 2i
      // build a merger over the lits in this range of out.
      // replace this range with the ouputs of the merge
      oe_merge(sm, out, j, j + 2 * i);

  // remove padding
  out.resize(orig_sz);  // remove padding
  return out;
}

vector<Lit> SortNet::odd_even_merge(SumManager& sm, SRef lS, SRef rS) {
  // one and two are sorted outputs.
  auto one{lS->output_lits};
  auto two{rS->output_lits};
  if (one.empty()) return two;
  if (two.empty()) return one;

  sm.setValuedOuts(lS);
  sm.setValuedOuts(rS);

  int orig_sz = one.size() + two.size();
  if (orig_sz == 2) {
    vector<Lit> out{one.front(), two.front()};
    cmp2(sm, out, 0);
    return out;
  }
  // Pad both to make equal size and power of two then call lower level
  // merge

  int max_sz = one.size() > two.size() ? one.size() : two.size();
  int sz;
  for (sz = 1; sz < max_sz; sz *= 2)
    ;
  vector<Lit> out{one};
  out.resize(sz, lit_Undef);  // pad with false lits
  out.insert(out.end(), two.begin(), two.end());
  out.resize(sz * 2, lit_Undef);

  oe_merge(sm, out, 0, out.size());
  out.resize(orig_sz);  // remove padding
  return out;
}

void SortNet::oe_merge(SumManager& sm, vector<Lit>& in, int begin,
                         int end) {
  assert(end - begin > 1);  // a range of at least two
  if (end - begin == 2)
    cmp2(sm, in, begin);
  else {
    int mid = (end - begin) / 2;
    vector<Lit> tmp(in.begin() + begin, in.begin() + end);
    oe_separate(tmp);
    oe_merge(sm, tmp, 0, mid);
    oe_merge(sm, tmp, mid, tmp.size());
    oe_join(tmp);
    for (int i = 1; i < static_cast<int>(tmp.size()) - 1; i += 2)
      cmp2(sm, tmp, i);
    std::copy(tmp.begin(), tmp.end(), in.begin() + begin);
  }
}

void SortNet::cmp2(SumManager& sm, vector<Lit>& in, int begin) {
  // put lowest value lit at highest output (ones come first then
  // zeros) when one or more inputs are constants (false lits or
  // forced lits) no clauses need to be generated
  if (in[begin] == lit_Undef ||
      sm.satsolver->fixedValue(in[begin]) == l_False ||
      sm.satsolver->fixedValue(in[begin + 1]) == l_True) {
    std::swap(in[begin], in[begin + 1]);
    return;
  }
  if (in[begin + 1] == lit_Undef ||
      sm.satsolver->fixedValue(in[begin + 1]) == l_False ||
      sm.satsolver->fixedValue(in[begin]) == l_True)
    return;

  Lit a = in[begin];
  Lit b = in[begin + 1];
  in[begin] = sm.getNewOutputLit();
  in[begin + 1] = sm.getNewOutputLit();
  sm.addClausesToSolvers(
      {{~a, in[begin]}, {~b, in[begin]}, {~a, ~b, in[begin + 1]}});
  return;
}

void SortNet::oe_separate(vector<Lit>& v) {
  vector<Lit> tmp{v};
  for (int i{}; i < static_cast<int>(v.size() / 2); ++i) {
    v[i] = tmp[i * 2];
    v[i + v.size() / 2] = tmp[i * 2 + 1];
  }
}

void SortNet::oe_join(vector<Lit>& v) {
  vector<Lit> tmp{v};
  for (int i{}; i < static_cast<int>(v.size() / 2); ++i) {
    v[i * 2] = tmp[i];
    v[i * 2 + 1] = tmp[i + v.size() / 2];
  }
}

int SortNet::MR_size(int a, int b) {
  if (a == 0 || b == 0) return 0;
  if (a == 1 && b == 1) return 3;
  return MR_size(a / 2, b / 2) + MR_size(a - a / 2, b - b / 2) +
         3 * ((a + b - 1) / 2);
}

int SortNet::MD_size(int a, int b) { return a * b + a + b; }

int SortNet::SR_size(int n) {
  if (n <= 1) return 0;
  if (n == 2) return 3;
  return SR_size(n / 2) + SR_size(n - n / 2) + MR_size(n / 2, n - n / 2);
}

int SortNet::SD_size(int n) { return (1 << n) - 1; }

vector<Lit> SortNet::direct_sort(SumManager& sm, const vector<Lit>& in,
                                   int s, int e) {
  const auto sz{e - s};
  assert(sz > 1 && sz <= 4);
  vector<Lit> out(sz);
  for (int i{}; i < sz; ++i) out[i] = sm.getNewOutputLit();

  if (sz >= 2)
    sm.addClausesToSolvers(
        {{~in[s], out[0]}, {~in[s + 1], out[0]}, {~in[s], ~in[s + 1], out[1]}});
  if (sz >= 3) {
    sm.addClausesToSolvers({{~in[s + 2], out[0]},
                            {~in[s], ~in[s + 2], out[1]},
                            {~in[s + 1], ~in[s + 2], out[1]},
                            {~in[s], ~in[s + 1], ~in[s + 2], out[2]}});
  }
  if (sz == 4) {
    sm.addClausesToSolvers(
        {{~in[s + 3], out[0]},
         {~in[s], ~in[s + 3], out[1]},
         {~in[s + 1], ~in[s + 3], out[1]},
         {~in[s + 2], ~in[s + 3], out[1]},
         {~in[s], ~in[s + 1], ~in[s + 3], out[2]},
         {~in[s], ~in[s + 2], ~in[s + 3], out[2]},
         {~in[s + 1], ~in[s + 2], ~in[s + 3], out[2]},
         {~in[s], ~in[s + 1], ~in[s + 2], ~in[s + 3], out[3]}});
  }
  return out;
}

vector<Lit> SortNet::direct_merge(SumManager& sm, const vector<Lit>& f,
                                    const vector<Lit>& s) {
  assert(!f.empty() && !s.empty());
  const int sz{static_cast<int>(f.size() + s.size())};
  assert(sz > 2);
  vector<Lit> out(sz);
  for (int i{}; i < sz; ++i) out[i] = sm.getNewOutputLit();

  for (int i{}; i < static_cast<int>(f.size()); ++i)
    sm.addClausesToSolvers({{~f[i], out[i]}});
  for (int i{}; i < static_cast<int>(s.size()); ++i)
    sm.addClausesToSolvers({{~s[i], out[i]}});

  for (int i{}; i < static_cast<int>(f.size()); ++i)
    for (int j{}; j < static_cast<int>(s.size()); ++j)
      sm.addClausesToSolvers({{~f[i], ~s[i], out[i + j]}});
  return out;
}
