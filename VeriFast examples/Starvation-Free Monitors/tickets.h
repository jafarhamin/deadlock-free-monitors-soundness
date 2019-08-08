#ifndef TICKETS_H
#define TICKETS_H

#include "levels_with_importers.h"
//@ #include "ghost_counters.gh"

struct tvm;

/*@
predicate tvm(struct tvm* t; void* v, int g);
@*/

struct tvm *new_tvm();
  //@ requires exists<real>(?v_wlevel);
  //@ ensures tvm(result,?v,?g) &*& level_of(v) == v_wlevel;

void enter_tvm(struct tvm* t);
  //@ requires [_]tvm(t,?v,?g) &*& obs(?O) &*& object_lt_objects(v,O)== true;
  //@ ensures [_]tvm(t,v,g) &*& obs(cons(v,O)) &*& tic(g);

void exit_tvm(struct tvm* t);
  //@ requires [_]tvm(t,?v,?g) &*& obs(cons(v,?O)) &*& tic(g) &*&  object_lt_objects(v,O)== true;
  //@ ensures [_]tvm(t,v,g) &*& obs(O);
