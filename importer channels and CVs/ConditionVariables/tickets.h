/*
  tickets
*/

#include "levels_with_importers.h"

#ifndef TICKETS_H
#define TICKETS_H

struct ticket;

/*@
predicate ticket(struct ticket *t; int active, int next, predicate() M, list<void*> M');
predicate create_queue_ghost_args(list<real> Mr, predicate() M, list<void*> M') = true;  
@*/

struct ticket* create_ticket();
    //@ requires create_queue_ghost_args(?Mr,?M,?M');
    //@ ensures ticket(result,0,0,M,M') &*& Mr(result) == Mr;

int get_ticket(struct ticket *t);
    //@ requires ticket(t,?active,?next,?M,?M');
    //@ ensures ticket(t,active,next+1,M,M') &*& result == next;

bool is_my_turn(struct ticket *t, int my_turn);
    //@ requires ticket(t,?active,?next,?M,?M');
    //@ ensures ticket(t,active,next+1,M,M') &*& result == (my_turn == active);

bool has_next_one(struct ticket *t);
    //@ requires ticket(t,?active,?next,?M,?M');
    //@ ensures ticket(t,active,next,M,M') &*& result == (active < next);

void next_one(struct ticket *t);
    //@ requires obs(?O,?R) &*& ticket(t,?active,?next,?M,?M') &*& active < next &*& (Mr(t) == nil ? true : trandit((void*)t));
    //@ ensures obs(minus(O,M'), R) &*& ticket(t,active+1,next,M,M');

#endif