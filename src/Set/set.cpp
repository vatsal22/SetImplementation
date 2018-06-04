#include "tuple.h"
#include "set.h"
#include "invariant.h"
#include <iostream>
#include <limits.h>   // needed for INT_MIN

#define SET_INVARIANT(LOC) INVARIANT_TEST(_numElements < -1, LOC)

// Set up an error set to be returned as necessary
const Set emptySet(0,(int*)0);
const Set errorSet(-1,(int*)0);

bool Set::isEmpty() const {
  SET_INVARIANT("Set::isEmpty()");
  return _numElements==0;
}

bool Set::isError() const {
  SET_INVARIANT("Set::isError()");
  return _numElements==-1;
}
  
int Set::cardinality() const {
  SET_INVARIANT("Set::cardinality()");
  return 0;
}

Set Set::union_(const Set& s) const {
  SET_INVARIANT("Set::union_()");
  return emptySet;
}

Set Set::intersection(const Set& s) const {
  SET_INVARIANT("Set::intersection()");
  return emptySet;
}

Set Set::difference(const Set& s) const {
  SET_INVARIANT("Set::difference()");
  return emptySet;
}

Set Set::select(predicate* p) const {
  SET_INVARIANT("Set::select()");
  return emptySet;
}

Set Set::project(const int numItems, const int items[]) const {
  SET_INVARIANT("Set::project()");
  return emptySet;
}

Set Set::cartesian(const Set& s) const {
  SET_INVARIANT("Set::cartesian()");
  return emptySet;
}

Set Set::operator()(const int item) const {
  SET_INVARIANT("Set::operator()()");
  return emptySet;
}

void Set::operator=(const Set& s) {
  SET_INVARIANT("Set::operator=()");
}

Set::Set() {
  _numElements = 0;
  _pTuples = NULL;
}

Set::Set(const Set& s) : Set(s._numElements, s._pTuples){}

Set::Set(const int numElements, const int data[]) {

  _numElements = numElements;

  if (_numElements<=0){
    _pTuples=NULL;
    return;
  } 

  _pTuples = new Tuple[_numElements];

  for (int i=0;i<_numElements;++i){
    _pTuples[i] = Tuple(data[i]);
  } 

}

Set::Set(const int numElements, const Tuple tuples[]) {

  _numElements = numElements;

  if (_numElements<=0){
    _pTuples=NULL;
    return;
  } 

  _pTuples = new Tuple[_numElements];

  for (int i=0;i<numElements;++i){
    _pTuples[i] = Tuple(tuples[i]);
  } 

}

Set::~Set() {
  delete [] _pTuples;
  _numElements = -2; //Deleted set indication

}

std::ostream& operator<<(std::ostream& os, const Set& s) {

  if (s._numElements==-2){
    std::cerr << "Error: Attempted to output deleted set; exiting";
    exit(-1);
  }

  if (s.isEmpty()){
    os<<"()";
    return os;
  }

  if (s.isError()){
    os<<"(Error Set)";
    return os;
  }
  
  os<<"("<<s._pTuples[0];

  for (int i=1;i<s._numElements;i++){
    os<<", "<<s._pTuples[i];
  }

  os<<")";

  return os;

}
