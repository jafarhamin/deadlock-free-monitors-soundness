#ifndef RELAXED_LEVELS_H
#define RELAXED_LEVELS_H

#include "levels.h"
           

/*@
fixpoint option< pair<list<void*>, real> > level'(void* x);
fixpoint bool P(void* x);
@*/

/*@
fixpoint bool one_obs(void* condvar, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot){ 
  return Wt(condvar) < 1 || Ot(condvar) > 0;
}

fixpoint bool spr_obs(void* condvar, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot){ 
  return Wt(condvar) < 1 || Wt(condvar) < Ot(condvar);
}

fixpoint bool own_obs(void* condvar, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot){ 
  return Wt(condvar) <= Ot(condvar);
}

fixpoint bool safe_obs(void* condvar, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot){ 
  return one_obs(condvar,Wt,Ot) && (!P(condvar) || spr_obs(condvar,Wt,Ot)) && (level'(condvar) == none || own_obs(condvar,Wt,Ot));
}
@*/

/*@
fixpoint bool w_level_below_all(void* o, list<void*> O) {
  return forall(O, (wait_level_below_object)(level(o)));
}

fixpoint pair<list<void*>, real> max_wlevel(pair<list<void*>, real> w1, pair<list<void*>, real> w2){
  return wait_level_lt(w1,w2) ? w2 : w1;
}

fixpoint bool wl_xle_max(void* o, pair<list<void*>, real> xo, void* x){
  return !wait_level_lt(max_wlevel(level(o), xo),level(x));
}

fixpoint bool wait_level_lt_o(option< pair<list<void*>, real> > ow, pair<list<void*>, real> w){
  switch (ow){
    case none: return true;
    case some(sw): return wait_level_lt(sw, w);
  }
}

fixpoint bool wl_ltle(void* o, pair<list<void*>, real> xo, void* x){
  return wait_level_lt(max_wlevel(level(o), xo),level(x)) || !wait_level_lt_o(level'(x), max_wlevel(level(o), xo));
}

fixpoint bool no_cycle_some(void* o, pair<list<void*>, real> xo, list<void*> O){
  return (count(O,(wl_xle_max)(o,xo)) <= 1) && forall(O, (wl_ltle)(o,xo)) && (w_level_below_all(o, O) || P(o));
}

fixpoint bool no_cycle_x(void* o, option< pair<list<void*>, real> > xo, list<void*> O){
  switch (xo){
    case none: return w_level_below_all(o, O);
    case some(so): return no_cycle_some(o, so, O);
  }
}

// ==============================
// The Relaxed Precedece Relation
// ==============================

fixpoint bool no_cycle(void* o, list<void*> O){
  return no_cycle_x(o, level'(o), O);
}
@*/

/*@
lemma void below_count(void* v, list<void*> O)
    requires wait_level_below_obs(level(v),O) == true;
    ensures count(O,(wl_xle_max)(v,level(v))) == 0;
{
  switch (O){
    case nil:
    case cons(o,Os):
        assert wait_level_lt(level(v), level(o)) == true;
        if (level(v) == level(o)){ remove_all_all(fst(level(v))); }
        else{below_count(v,Os);}
  } 
}

lemma void count_same(void* v, list<void*> O)
    requires count(O,(wl_xle_max)(v,level(v))) == 0;
    ensures forall(O, (wl_ltle)(v,level(v))) == true;
{
  switch (O){
    case nil:
    case cons(o,Os): count_nonnegative(Os,(wl_xle_max)(v,level(v))); count_same(v,Os);
  } 
}
@*/           

#endif    
