/***********[Packed.h]
Copyright (c) 2013, Fahiem Bacchus

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


#ifndef PACKED_VEC_H
#define PACKED_VEC_H

#include <vector>
#include <ostream>
#include <utility>
#include <algorithm>

using std::vector;
using std::cout;

/* pack a set of vectors into a single vector.
   This implemenation only works for concrete types of classes.
   There is no support for erasing elements (either packed
   vectors or elements of the packed vector) */
template<typename T>
class Packed_vecs {
public:
  class ivec;         //Accessor for an internal vector
  class const_ivec;
  class iterator;     //iterator over internal vectors
  class const_iterator;

  Packed_vecs() {};
  Packed_vecs(vector<vector<T>> init_vecs);
  Packed_vecs(std::initializer_list<vector<T>> ilist); 

  //keep default move constructors and assignments. 
  Packed_vecs(Packed_vecs &&) = default;
  Packed_vecs& operator=(Packed_vecs &&) = default;
  
  size_t size() const;        //# of internal vecs (including zero sized vecs)
  bool empty() const { return !size(); }

  const ivec operator[](size_t);  //accessor for i'th internal vec
  const const_ivec operator[](size_t) const;  
  iterator begin();           //iterator over internal vecs
  iterator end();
  const_iterator begin() const;
  const_iterator end() const;

  /* internal vectors <--> standard vectors */
  void addVec(const vector<T> &); //will add and get zero sized vecs.
  vector<T> getVec (size_t i) const;
  size_t ithSize(size_t i) const; //Return size of i-th internal vector

  void compress(); //remove spaces; Retain zero length vectors
  void rm_empty_vecs();  //remove zero length vectors...don't do this
			 //to save space as they don't occupy much
			 //space
  void clear() { //release allVec's memory
    vector<T> tmp;
    std::swap(allVecs, tmp);
    offsets.clear();
    sizes.clear(); }
  
  size_t capacity() const { return allVecs.capacity(); }
  void reserve(size_t n) { allVecs.reserve(n); }
  size_t total_size() const { return allVecs.size(); }

  class ivec {
    /* accessor class to an internal vec. Can be subscripted [] or
       elements of internal vec can be iterated over (begin, end)
       begin, end are standard vector iterators so various
       <algorithms> (e.g., sort) can be run on the internal vector (a
       subsequence of a std::vector) */
  public:
    ivec(Packed_vecs<T> * pv, size_t index): i(index),  p(pv) {}
    size_t size() const { return p->sizes[i]; }
    bool empty() const { return !size(); }

    typename vector<T>::iterator begin() const { return p->allVecs.begin()+p->offsets[i]; }
    typename vector<T>::iterator end() const { return begin()+p->sizes[i]; }
    T& operator[](size_t j) const { return p->allVecs[p->offsets[i]+j]; }
    void shrink(size_t n) const { p->sizes[i] -= n; }
    vector<T> getVec() const { return p->getVec(i); }
  private:
    size_t i;
    Packed_vecs<T> *p;
  };
  
  class const_ivec {
  public:
    const_ivec(const Packed_vecs<T> *pv, size_t index): i (index), p (pv) {}
    const_ivec(ivec iv): p (iv.p), i (iv.i) {}
    size_t size() const { return p->sizes[i]; }
    bool empty() const { return !size(); }
    typename vector<T>::const_iterator begin() const {
      return p->allVecs.cbegin()+p->offsets[i]; }
    typename vector<T>::const_iterator end() const {
      return begin()+p->sizes[i]; }
    const T& operator[](size_t j) const { return p->allVecs[p->offsets[i]+j]; }
    const vector<T> getVec() const { return p->getVec(i); }
  private:
    size_t i;
    const Packed_vecs<T> * p;
  };

  class iterator {
  public:
    iterator(Packed_vecs<T> *pv, size_t pos) : _pos(pos), _pv(pv) {}
    bool operator!=(iterator &other) const { 
      return (_pv != other._pv || _pos != other._pos); 
    }
    iterator& operator++() { _pos++; return *this; }
    const ivec operator*() { return ivec(_pv, _pos); }
  private:
    size_t _pos;
    Packed_vecs<T> * _pv;
  };

  class const_iterator {
  public:
    const_iterator(const Packed_vecs<T> *pv, size_t pos) : _pos(pos), _pv(pv) {}
    const_iterator(iterator i) : _pos(i._pos), _pv(i._pv) {}
    bool operator!=(const_iterator &other) const {
      return (_pv != other._pv || _pos != other._pos); 
    }
    const_iterator& operator++() { _pos++; return *this; }
    const const_ivec operator*() { return const_ivec(_pv, _pos); }
  private:
    size_t _pos;
    const Packed_vecs<T> * _pv;
  };

private:
  vector<size_t> offsets;
  vector<T> allVecs;
  vector<size_t> sizes;
};

template <class T>
inline size_t Packed_vecs<T>::size() const { return offsets.size(); }

template <class T>
inline const typename Packed_vecs<T>::ivec Packed_vecs<T>::operator[](size_t i) 
{
  return ivec(this, i);
}

template <class T>
inline const typename Packed_vecs<T>::const_ivec Packed_vecs<T>::operator[](size_t i) const
{
  return const_ivec(this, i); 
}

template <class T>
inline typename Packed_vecs<T>::iterator Packed_vecs<T>::begin() { return iterator(this, 0); }

template <class T>
inline typename Packed_vecs<T>::iterator Packed_vecs<T>::end() {
  return iterator(this, offsets.size()); 
}

template <class T>
inline typename Packed_vecs<T>::const_iterator Packed_vecs<T>::begin() const {
  return const_iterator(this, 0); 
}

template <class T>
inline typename Packed_vecs<T>::const_iterator Packed_vecs<T>::end() const { 
  return const_iterator(this, offsets.size()); 
}

template <class T>
inline void Packed_vecs<T>::addVec(const vector<T> &v) 
{
  offsets.push_back(allVecs.size());
  sizes.push_back(v.size());
  for(size_t i = 0; i < v.size(); i++)
    allVecs.push_back(v[i]);
}

template <class T>
inline vector<T> Packed_vecs<T>::getVec(size_t i) const
{
  vector<T> v;
  for(size_t j = offsets[i]; j < offsets[i] + sizes[i]; j++)
    v.push_back(allVecs[j]);
  return v;
}

template <class T>
inline size_t Packed_vecs<T>::ithSize(size_t i) const
{
  return sizes[i];
}

template <class T>
inline void Packed_vecs<T>::compress()
{
  size_t to = 0;
  size_t cur_vec;
  /* skip compressed prefix */
  for(cur_vec = 0; cur_vec < offsets.size(); cur_vec++) {
    if (offsets[cur_vec] != to)
      break;
    to += sizes[cur_vec];
  }
  for( ; cur_vec < offsets.size(); cur_vec++) {
    size_t start = offsets[cur_vec];
    offsets[cur_vec] = to;
    for(size_t j = 0; j < sizes[cur_vec]; j++)
      allVecs[to++] = allVecs[start+j];
  }
  allVecs.resize(offsets.back() + sizes.back());
}

template <class T>
inline void Packed_vecs<T>::rm_empty_vecs()
{
  size_t from;
  size_t to;
  for(to = from = 0;  from < offsets.size(); from++) 
    if(sizes[from] > 0) {
      offsets[to] = offsets[from];
      sizes[to] = sizes[from];
      to++;
    }
  offsets.resize(to);
  sizes.resize(to);
}

template <class T>
inline Packed_vecs<T>::Packed_vecs(vector<vector <T>> init_vecs)
{
  for(auto& item : init_vecs) 
    addVec(item);
}

template <class T>
inline Packed_vecs<T>::Packed_vecs(std::initializer_list<vector<T>> ilist)
{
  for(auto& item: ilist)
    addVec(item);
}


/* 
//Example Usage. 
#include <iostream>
#include <vector>

int main (int argc, char * const argv[]) 
{
  Packed_vecs<int> pv;
  vector<int> v1 {1, 2, 3, 4};
  vector<int> v2 {11, 12, 13, 14, 15, 16};
  vector<int> v3 {6, 7, 8};
  pv.addVec(v1);
  pv.addVec(v2);
  pv.addVec(v3);

  Packed_vecs<int> pv1 {v1, v2, v3};
  vector<vector<int>> vall {v1, v2, v3};
  const Packed_vecs<int> pv2(vall);

  //Following should work for pv, pv1, or pv2.

  pv1[0][0] = 999;
  
  auto v = pv1[0];
  cout << "pv1[0].size() = " << v.size() << "\n";
  //Flagged as error by compiler:  pv1[0] = pv1[1];

  cout << "T1: Packed Vec Size: " << pv2.size() << "\n";
  for(size_t i = 0; i < pv2.size(); i++) {
    cout << "Vec " << i << "\n" << "[";
    for(size_t j = 0; j < pv2[i].size() - 1; j++)
      cout << pv2[i][j] << ", ";
    cout << pv2[i][pv2[i].size()-1] << "]\n";
  }
  cout << "T2 getVec access\n";
  for(size_t i = 0; i < pv2.size(); i++) {
    vector<int> tmp;
    cout << "Vec " << i << "\n" << "[";
    tmp = pv2.getVec(i);
    for(size_t j = 0; j < tmp.size()-1; j++)
      cout << tmp[j] << ", ";
    cout << tmp.back() << "]\n";
  }
  cout << "T3 range-for access\n";
  for(size_t i = 0; i < pv2.size(); i++) {
    cout << "Vec " << i << "\n" << "[";
    for(auto& item : pv2[i])
      cout << item << ", ";
    cout << "]\n";
  }
  cout << "T4 range-for Packed_vecs access\n";
  for(auto v : pv2) {
    cout << "Vec:" << "\n" << "[";
    for(auto& item : v) 
      cout << item << ", ";
    cout << "]\n";
  }
} */

#endif
