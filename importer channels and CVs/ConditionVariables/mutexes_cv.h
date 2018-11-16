#ifndef MUTEXESCV_H
#define MUTEXESCV_H

#include "levels.h"

struct exclusive;

/*@
predicate exclusive(struct exclusive *ex; void* v);

predicate create_exclusive_ghost_args(pair<list<void*>, real> v_wlevel) = true;
@*/

struct exclusive *new_exclusive();
  //@ requires exists< pair<list<void*>, real> >(?v_wlevel) &*& wait_level_lt(pair({(new_exclusive)}, 0r), v_wlevel) == true;
  //@ ensures exclusive(result,?v) &*& wait_level_of(v) == v_wlevel;

void enter_cs(struct exclusive *ex);
  //@ requires [_]exclusive(ex,?v) &*& obs(?O) &*& w_level_below_all(v,O)== true &*& wait_level_below_obs(pair({(enter_cs)}, 0r), O) == true;
  //@ ensures [_]exclusive(ex,v) &*& obs(cons(v,O));

void exit_cs(struct exclusive *ex);
  //@ requires [_]exclusive(ex,?v) &*& obs(cons(v,?O)) &*& wait_level_below_obs(pair({(exit_cs)}, 0r), cons(v,O)) == true;
  //@ ensures [_]exclusive(ex,v) &*& obs(O);
  
#endif
