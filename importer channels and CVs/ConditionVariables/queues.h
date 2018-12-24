/*
  Queues
*/

#include "levels_with_importers.h"

#ifndef QUEUES_H
#define QUEUES_H

struct queue;

/*@
predicate queue<T>(struct queue *q; list<T> elems, predicate(T x) M, fixpoint(T x, list<void*>) M');
predicate create_queue_ghost_args<T>(list<real> Mr, predicate(T x) M, fixpoint(T x, list<void*>) M') = true;  
@*/

struct queue* create_queue<T>();
    //@ requires create_queue_ghost_args<T>(?Mr,?M,?M');
    //@ ensures queue<T>(result,nil,M,M') &*& Mr(result) == Mr;

int size_of<T>(struct queue *q);
    //@ requires queue<T>(q,?elems,?M,?M');
    //@ ensures queue<T>(q,elems,M,M') &*& result == length(elems);

void enqueue<T>(struct queue *q, T x);
    //@ requires obs(?O,?R) &*& queue<T>(q,?elems,?M,?M') &*& M(x) &*& (Mr(q) == nil ? true : trandit((void*)q)) &*& forall(map(level_of, M'(x)),(mem')(Mr(q))) == true;
    //@ ensures obs(minus(O,M'(x)), R) &*& queue<T>(q,cons(x,elems),M,M');
  
T dequeue<T>(struct queue *q);
    //@ requires obs(?O,?R) &*& queue<T>(q,?elems,?M,?M') &*& length(elems) >= 1;
    //@ ensures obs(append(O,M'(result)), remove(q,R)) &*& queue<T>(q,take(length(elems)-1,elems),M,M') &*& M(result);
#endif