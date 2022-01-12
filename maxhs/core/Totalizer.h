/***********[Totalizers.h]
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

#ifndef Totalizer_h
#define Totalizer_h

#include <iostream>
#include <vector>

#include "maxhs/core/MaxSolverTypes.h"
#include "maxhs/core/TotalizerAuxStruct.h"
#include "maxhs/utils/io.h"

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

using Minisat::Lit;
using Minisat::Var;
using std::vector;

class Totalizer {
 public:
  // use only these static makeTotalizer routines to make totalizers.
  // due to internal storage of all totalizers.

  // 1. Build the totalizer over inputLits.
  static TRef makeTotalizer(TotalizerManager& tm, const vector<Lit>& inputLits,
                            Weight w);

  // 2. Build totalizer by joining two previous totalizers referred to rightTRef
  // and leftTRef
  static TRef makeTotalizer(TotalizerManager& tm, TRef rT, TRef lT);

  static TRef makeTotalizer(TotalizerManager& tm, const vector<Lit>& inputLits,
                            size_t start, size_t end, Weight w);

  static Totalizer& getTotalizer(TRef idx);
  static size_t getNbTotalizers() { return all_totalizers.size(); }

  // Update maxTrue/maxFalse to a higher value and return new clauses
  // generated clauses to allow the additional outputs to constrain the inputs
  vector<vector<Lit>> increaseMaxFalse(int maxFalse) {
    vector<vector<Lit>> clauses{};
    increaseMaxFalse(maxFalse, clauses);
    return clauses;
  }

  vector<vector<Lit>> increaseMaxTrue(int maxTrue) {
    vector<vector<Lit>> clauses{};
    increaseMaxTrue(maxTrue, clauses);
    return clauses;
  }

  // get full CNF representation of totalizer current state of totalizer.
  // Usually called after constructing totalizer with specific inputLits
  // as that constructor does not return the CNF encoding.
  vector<vector<Lit>> getCNF() const {
    vector<vector<Lit>> clauses;
    getCNF(clauses);
    return clauses;
  }

  const vector<Lit>& getOutputs() const { return output_lits; }

  vector<Lit> getInputs() const {
    vector<Lit> inputs;
    getInputs(inputs);
    return inputs;
  }

  void getInputs(vector<Lit>& inputs) const;
  int getSize() const { return nb_inputs; };
  int getMaxFalse() const { return _maxFalse; }
  int getMaxTrue() const { return _maxTrue; }
  int getOutTrue() const { return nOutTrue; }
  int getOutFalse() const { return nOutFalse; }
  void setNOutTrue(int t) { nOutTrue = t; }
  void setNOutFalse(int t) { nOutFalse = t; }
  Weight getWeight() const { return weight; }
  bool isTopLevel() const { return toplevel; }
  void setTopLevel() { toplevel = true; }
  void unsetTopLevel() { toplevel = false; }

  bool isLeaf() const {
    assert((rightT != NullTRef && leftT != NullTRef) ||
           (rightT == NullTRef && leftT == NullTRef));
    return (rightT == NullTRef && leftT == NullTRef);
  }
  TRef getRight() const { return rightT; }
  TRef getLeft() const { return leftT; }

  Totalizer(TotalizerManager& tm, const vector<Lit>& inputLits, Weight w);
  Totalizer(TotalizerManager& tm, TRef rT, TRef lT);
  Totalizer(TotalizerManager& tm, const vector<Lit>& inputLits, size_t start,
            size_t end, Weight w);

  friend std::ostream& operator<<(std::ostream& os, const Totalizer& tot);

 private:
  // return incremental clauses required to ensure setting
  // output[maxFalse-1] = False or output[maxTrue-1] = True properly
  // constrains the inputs. maxFalse, maxTrue are COUNTS of the number
  // of false/true outputs
  void increaseMaxFalse(int maxFalse, vector<vector<Lit>>& clauses);
  void increaseMaxTrue(int maxTrue, vector<vector<Lit>>& clauses);

  void getCNF(vector<vector<Lit>>& clauses) const;
  void getAtLeastCNF(vector<vector<Lit>>& clauses, int low, int high) const;
  void getAtMostCNF(vector<vector<Lit>>& clauses, int low, int high) const;
  TRef rightT;
  TRef leftT;
  bool toplevel{false};
  vector<Lit> output_lits;
  int _maxFalse{0}, _maxTrue{0}, nOutTrue{0}, nOutFalse{0};
  int nb_inputs{0};
  Weight weight;
  static vector<Totalizer> all_totalizers;
};

// Interface with Totalizer class
inline Totalizer& operator*(TRef t) { return Totalizer::getTotalizer(t); }

inline std::ostream& operator<<(std::ostream& os, const Totalizer& tot) {
  std::cout << "Totalizer: weight = " << tot.weight
            << " _maxFalse=" << tot._maxFalse << " _maxTrue=" << tot._maxTrue
            << " trueOuts = " << tot.nOutTrue
            << " falseOuts = " << tot.nOutFalse << "\n"
            << " outputs = " << tot.output_lits << "\n"
            << " inputs = " << tot.getInputs() << "\n"
            << " leftT = " << tot.leftT << "\n"
            << " rightT = " << tot.rightT << "\n";
  /*if (tot.leftT == NullTRef)
    std::cout << "LEFT: NullTRef\n";
  else
    std::cout << "LEFT:" << (*tot.leftT) << "\n";
  if (tot.rightT == NullTRef)
    std::cout << "RIGHT: NullTRef\n";
  else
  std::cout << "RIGHT:" << (*tot.rightT);*/
  return os;
}

#endif
