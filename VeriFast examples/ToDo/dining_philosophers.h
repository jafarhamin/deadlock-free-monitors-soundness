#ifndef DINING_PHILOSOPHERS_H
#define DINING_PHILOSOPHERS_H

#include "levels.h"

struct dining_philosophers;

typedef struct dining_philosophers *dining_philosophers;

/*@
predicate create_dphs_ghost_args(list< pair<list<void*>, real> > wlevels) = true;
  
predicate dphs(dining_philosophers dph, list<void*> cvs);
fixpoint bool map_wlevels(list<void*> l, list< pair<list<void*>, real> > l'){
  switch (l){
    case nil: return true;
    case cons(x,xs): return
      switch (l'){
        case nil: return false;
        case cons(x',xs'): return wait_level_of(x) == x' && map_wlevels(xs,xs');
      };
  }  
}
fixpoint bool X_none(void* x){
  return X(x) == none;
}
lemma void forall_nth<t>(list<t> l, fixpoint(t, bool) fp, int i);
  requires forall(l,fp) == true &*& 0 <= i &*& i < length(l);
  ensures fp(nth(i,l)) == true;
lemma void wlevel_nth(list<void*> l, list< pair<list<void*>, real> > l', int i);
  requires map_wlevels(l,l') == true &*& 0 <= i &*& i < length(l);
  ensures wait_level_of(nth(i,l)) == nth(i,l');
lemma void mod_plus(int x, int y);
  requires 0 < x &*& 0 <= y &*& y < x;
  ensures y == (y+x)%x;
lemma void mod_plus_le(int x, int y);
  requires 0 < x &*& 0 <= y &*& y < x;
  ensures y == y%x;
lemma void mod_minus(int x, int y);
  requires 0 < x &*& 0 <= y &*& y <= x;
  ensures (x-y)%x == x-y;
@*/

dining_philosophers new_dining_philosophers(int size);
  //@ requires create_dphs_ghost_args(?wlevels) &*& forall(wlevels,(wait_level_lt)(pair({new_dining_philosophers}, 0r))) == true &*& length(wlevels) == size &*& 2 < size;
  //@ ensures dphs(result, ?cvs) &*& map_wlevels(cvs,wlevels) == true &*& forall(cvs,X_none) == true &*& length(cvs) == size;

void pickup(dining_philosophers dph, int i);
  //@ requires obs(?O) &*& [?f]dphs(dph,?cvs) &*& no_cycle(nth(i,cvs),O) == true &*& 0 <= i &*& i < length(cvs) &*& wait_level_below_obs(pair({(pickup)}, 0r), O) == true;
  //@ ensures obs(cons((void*)nth((i+length(cvs)-1)%length(cvs),cvs),cons((void*)nth((i+1)%length(cvs),cvs),O))) &*& [f]dphs(dph, cvs);

void putdown(dining_philosophers dph, int i);
  //@ requires obs(?O) &*& [?f]dphs(dph,?cvs) &*& 0 <= i &*& i < length(cvs) &*& wait_level_below_obs(pair({(putdown)}, 0r), O) == true;
  //@ ensures obs(remove((void*)nth((i-1+length(cvs))%length(cvs),cvs),remove((void*)nth((i+1)%length(cvs),cvs),O))) &*& [f]dphs(dph, cvs);

#endif