/*
  Queues
*/

#include "levels_with_importers.h"

#ifndef QUEUES_H
#define QUEUES_H

struct queue;

/*@
predicate queue<T>(struct queue *q; int s, predicate(T x) M, fixpoint(T x, list<void*>) M');
predicate create_queue_ghost_args<T>(list<real> Mr, predicate(T x) M, fixpoint(T x, list<void*>) M') = true;  
@*/

struct queue* create_queue<T>();
    //@ requires create_queue_ghost_args<T>(?Mr,?M,?M');
    //@ ensures queue<T>(result,0,M,M') &*& Mr(result) == Mr;

int size_of<T>(struct queue *q);
    //@ requires queue<T>(q,?s,?M,?M');
    //@ ensures queue<T>(q,s,M,M') &*& result == s;

void enqueue<T>(struct queue *q, T x);
    //@ requires obs(?O,?R) &*& queue<T>(q,?s,?M,?M') &*& M(x) &*& (Mr(q) == nil ? true : trandit((void*)q)) &*& forall(map(level_of, M'(x)),(mem')(Mr(q))) == true;
    //@ ensures obs(minus(O,M'(x)), R) &*& queue<T>(q,s+1,M,M');
  
T dequeue<T>(struct queue *q);
    //@ requires obs(?O,?R) &*& queue<T>(q,?s,?M,?M') &*& s >= 1;
    //@ ensures obs(append(O,M'(result)), remove(q,R)) &*& queue<T>(q,s-1,M,M') &*& M(result);

  /* @ requires obs(?O, ?R) &*& [?f]channel<T>(ch,?Mch,?M'ch) &*& (S(ch) ? true : credit(ch)) &*& object_lt_objects(ch,O) == true &*& 
        object_lt_Mrs(ch,O) == true &*& S(ch) ? O==nil && count(R,(id)(ch)) == length(R) : true; @*/
  ///@ ensures obs(append(O,M'ch(result)), remove(ch,R)) &*& [f]channel(ch,Mch,M'ch) &*& Mch(result);

    
/* @
predicate queue<T>(struct queue *q; list<T> items);
@*/
/*
struct queue* create_queue<T>();
    //@ requires true;
    //@ ensures queue<T>(result,nil);

void dispose_queue(struct queue* queue);
    //@ requires queue(queue,_);
    //@ ensures true;

int size_of<T>(struct queue *q);
    //@ requires queue<T>(q,?s);
    //@ ensures queue<T>(q,s) &*& result == length(s);

T dequeue<T>(struct queue *q);
    //@ requires queue<T>(q,?s) &*& length(s) >= 1;
    //@ ensures queue<T>(q,take(length(s)-1,s));

void enqueue<T>(struct queue *q, T x);
    //@ requires queue<T>(q,?s);
    //@ ensures queue<T>(q,cons(x,s));
*/

#endif