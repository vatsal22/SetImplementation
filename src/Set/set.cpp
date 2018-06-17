#include "tuple.h"
#include "set.h"
#include "invariant.h"
#include <iostream>
#include <limits.h> // needed for INT_MIN

#define SET_INVARIANT(LOC) INVARIANT_TEST(_numElements < -1, LOC)

//TODO: Add if(s._numElements<0 || _numElements<0) return (Set)errorSet;

// Set up an error set to be returned as necessary
const Set emptySet(0, (int *)0);
const Set errorSet(-1, (int *)0);

bool Set::isEmpty() const
{
  SET_INVARIANT("Set::isEmpty()");
  return _numElements == 0;
}

bool Set::isError() const
{
  SET_INVARIANT("Set::isError()");
  return _numElements == -1;
}

int Set::cardinality() const
{
  SET_INVARIANT("Set::cardinality()");
  return _numElements;
}

Set Set::union_(const Set &s) const
{
  SET_INVARIANT("Set::union_()");

  if (_numElements == 0 && s._numElements == 0)
  {
    return emptySet;
  }
  else if (_numElements == 0)
  {
    return Set(s);
  }
  else if (s._numElements == 0)
  {
    return Set(*this);
  }

  int newNumElements = _numElements + s._numElements;

  Tuple newTuples[newNumElements];

  for (int i = 0; i < _numElements; ++i)
  {
    newTuples[i] = _pTuples[i];
  }
  for (int i = 0; i < s._numElements; i++)
  {
    newTuples[i + _numElements] = s._pTuples[i];
  }

  int removeList[newNumElements - 1] = {0};
  int numOfRejects = 0;
  for (int x = 0; x < newNumElements - 1; x++)
  {

    for (int y = x + 1; y < newNumElements; y++)
    {

      if (newTuples[x] == newTuples[y])
      {
        removeList[numOfRejects] = y;
        numOfRejects++;
      }
    }
  }

  Tuple uniqueTuples[newNumElements - numOfRejects];
  int uniqueTuplesIndex = 0;

  for (int i = 0; i < newNumElements; i++)
  {
    bool isReject = false;
    for (int z = 0; z < numOfRejects; z++)
    {
      if (removeList[z] == i)
      {
        isReject = true;
        break;
      }
    }
    if (!isReject)
    {
      uniqueTuples[uniqueTuplesIndex] = newTuples[i];
      uniqueTuplesIndex++;
    }
  }

  return Set(uniqueTuplesIndex, uniqueTuples);

  //Remove duplicates

  //
}

Set Set::intersection(const Set &s) const
{
  SET_INVARIANT("Set::intersection()");
  if (_numElements == 0 || s._numElements == 0)
  {
    return emptySet;
  }

  int numOfMatches = 0;

  for (int x = 0; x < _numElements; x++)
  {
    for (int y = 0; y < s._numElements; y++)
    {
      if (_pTuples[x] == s._pTuples[y])
        numOfMatches++;
    }
  }

  Tuple newTuples[numOfMatches];
  int newTuplesIndex = 0;

  for (int x = 0; x < _numElements; x++)
  {
    for (int y = 0; y < s._numElements; y++)
    {
      if (_pTuples[x] == s._pTuples[y])
      {
        newTuples[newTuplesIndex] = _pTuples[x];
        newTuplesIndex++;
      }
    }
  }

  return Set(newTuplesIndex, newTuples);
}

Set Set::difference(const Set &s) const
{
  SET_INVARIANT("Set::difference()");
  if (s._numElements == 0)
  {
    return Set(*this);
  }
  if (_numElements == 0)
  {
    return emptySet;
  }

  //int rejects[_numElements] = {0}; //Store index of elements to remove in here
  int numOfRejects = 0;
  for (int x = 0; x < _numElements; x++)
  {
    for (int y = 0; y < s._numElements; y++)
    {
      if (_pTuples[x] == s._pTuples[y])
      {
        //      rejects[numOfRejects] = x;
        numOfRejects++;
      }
    }
  }

  if (numOfRejects == 0)
  {
    return Set(*this);
  }

  Tuple newTuples[_numElements - numOfRejects];
  int newTuplesIndex = 0;
  for (int x = 0; x < _numElements; x++)
  {
    bool matchFound = false;
    for (int y = 0; y < s._numElements; y++)
    {
      if (_pTuples[x] == s._pTuples[y])
      {
        matchFound = true;
      }
    }
    if (!matchFound)
    {
      newTuples[newTuplesIndex] = _pTuples[x];
      newTuplesIndex++;
    }
  }
  return Set(newTuplesIndex, newTuples);
}

Set Set::select(predicate *p) const
{
  SET_INVARIANT("Set::select()");
  Tuple goodTuples[_numElements];
  int goodTuplesIndex = 0;
  for (int i = 0; i < _numElements; i++)
  {
    if (p(_pTuples[i]))
    {
      goodTuples[goodTuplesIndex] = _pTuples[i];
      goodTuplesIndex++;
    }
  }

  return Set(goodTuplesIndex, goodTuples);
}

Set Set::project(const int numItems, const int items[]) const
{
  SET_INVARIANT("Set::project()");

  if (numItems < 0)
  {
    return (Set)errorSet;
  }
  Tuple modifiedTuples[_numElements];

  for (int i = 0; i < _numElements; i++)
  {
    modifiedTuples[i] = _pTuples[i].project(numItems, items);
  }

  return Set(_numElements, modifiedTuples);
}

Set Set::cartesian(const Set &s) const
{
  SET_INVARIANT("Set::cartesian()");

  if (_numElements == 0 || s._numElements == 0)
  {
    return emptySet;
  }

  Tuple resultTuples[_numElements * s._numElements];

  for (int x = 0; x < _numElements; x++)
  {
    for (int y = 0; y < s._numElements; y++)
    {
      resultTuples[s._numElements * x + y + 1] = _pTuples[x] + s._pTuples[y];
    }
  }
  return Set(_numElements * s._numElements, resultTuples);
}

Set Set::operator()(const int item) const
{
  SET_INVARIANT("Set::operator()()");
  if (item < 1 || item > _numElements)
  {
    return (Set)errorSet;
  }

  return Set(1, _pTuples + item - 1);
}

void Set::operator=(const Set &s)
{
  SET_INVARIANT("Set::operator=()");
}

Set::Set()
{
  _numElements = 0;
  _pTuples = NULL;
}

Set::Set(const Set &s) : Set(s._numElements, s._pTuples) {}

Set::Set(const int numElements, const int data[])
{

  _numElements = numElements;

  if (_numElements <= 0)
  {
    _pTuples = NULL;
    return;
  }

  _pTuples = new Tuple[_numElements];

  for (int i = 0; i < _numElements; ++i)
  {
    _pTuples[i] = Tuple(data[i]);
  }

  //
  if (_numElements > 1)
  {
    int removeList[_numElements - 1] = {0};
    int numOfRejects = 0;
    for (int x = 0; x < _numElements - 1; x++)
    {

      for (int y = x + 1; y < _numElements; y++)
      {

        if (_pTuples[x] == _pTuples[y])
        {
          removeList[numOfRejects] = y;
          numOfRejects++;
        }
      }
    }

    Tuple uniqueTuples[_numElements - numOfRejects];
    int uniqueTuplesIndex = 0;

    for (int i = 0; i < _numElements; i++)
    {
      bool isReject = false;
      for (int z = 0; z < numOfRejects; z++)
      {
        if (removeList[z] == i)
        {
          isReject = true;
          break;
        }
      }
      if (!isReject)
      {
        uniqueTuples[uniqueTuplesIndex] = _pTuples[i];
        uniqueTuplesIndex++;
      }
    }
    _numElements = uniqueTuplesIndex;
    delete[] _pTuples;
    _pTuples = new Tuple[_numElements];
    for (int i = 0; i < _numElements; i++)
    {
      _pTuples[i] = uniqueTuples[i];
    }
  }
}

Set::Set(const int numElements, const Tuple tuples[])
{

  _numElements = numElements;

  if (_numElements <= 0)
  {
    _pTuples = NULL;
    return;
  }

  _pTuples = new Tuple[_numElements];

  for (int i = 0; i < numElements; ++i)
  {
    _pTuples[i] = Tuple(tuples[i]);
  }
  if (_numElements > 1)
  {
    int removeList[_numElements - 1] = {0};
    int numOfRejects = 0;
    for (int x = 0; x < _numElements - 1; x++)
    {

      for (int y = x + 1; y < _numElements; y++)
      {

        if (_pTuples[x] == _pTuples[y])
        {
          removeList[numOfRejects] = y;
          numOfRejects++;
        }
      }
    }

    Tuple uniqueTuples[_numElements - numOfRejects];
    int uniqueTuplesIndex = 0;

    for (int i = 0; i < _numElements; i++)
    {
      bool isReject = false;
      for (int z = 0; z < numOfRejects; z++)
      {
        if (removeList[z] == i)
        {
          isReject = true;
          break;
        }
      }
      if (!isReject)
      {
        uniqueTuples[uniqueTuplesIndex] = _pTuples[i];
        uniqueTuplesIndex++;
      }
    }
    _numElements = uniqueTuplesIndex;
    delete[] _pTuples;
    _pTuples = new Tuple[_numElements];
    for (int i = 0; i < _numElements; i++)
    {
      _pTuples[i] = uniqueTuples[i];
    }
  }
}

Set::~Set()
{
  delete[] _pTuples;
  _numElements = -2; //Deleted set indication
}

std::ostream &operator<<(std::ostream &os, const Set &s)
{

  if (s._numElements == -2)
  {
    std::cerr << "Error: Attempted to output deleted set; exiting";
    exit(-1);
  }

  if (s.isEmpty())
  {
    os << "{}";
    return os;
  }

  if (s.isError())
  {
    os << "{Error Set}";
    return os;
  }

  os << "{" << s._pTuples[0];

  for (int i = 1; i < s._numElements; i++)
  {
    os << ", " << s._pTuples[i];
  }

  os << "}";

  return os;
}
