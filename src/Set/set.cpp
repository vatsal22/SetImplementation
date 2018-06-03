#include "tuple.h"
#include "set.h"
#include "invariant.h"
#include <iostream>
#include <limits.h>   // needed for INT_MIN

// Set up an error set to be returned as necessary
const Set emptySet(0,(int*)0);
const Set errorSet(-1,(int*)0);

bool Set::isEmpty() const {
  return true;
}

bool Set::isError() const {
  return false;
}
  
int Set::cardinality() const {
  return 0;
}

Set Set::union_(const Set& s) const {
  return emptySet;
}

Set Set::intersection(const Set& s) const {
  return emptySet;
}

Set Set::difference(const Set& s) const {
  return emptySet;
}

Set Set::select(predicate* p) const {
  return emptySet;
}

Set Set::project(const int numItems, const int items[]) const {
  return emptySet;
}

Set Set::cartesian(const Set& s) const {
  return emptySet;
}

Set Set::operator()(const int item) const {
  return emptySet;
}

void Set::operator=(const Set& s) {
}

Set::Set() {
  _numElements = 0;
}

Set::Set(const Set& s) {
  _numElements = s._numElements;
  _tupleArraySize = s._tupleArraySize;
  
  _pTuples = new Tuples[_numElements];

  for (int i=0;i<_numElements;++i){
    _pTuples[i] = s._pTuples[i];
  }

}

Set::Set(const int numElements, const int data[]) {
  //TODO finish the constructors, finish operator<<, ???, profit

}

Set::Set(const int numElements, const Tuple tuples[]) {
}

Set::~Set() {
}

std::ostream& operator<<(std::ostream& os, const Set& s) {
}
