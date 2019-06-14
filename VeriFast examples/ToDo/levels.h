/*
  - Relaxed Precedence Relation
  - Safe Obligations
*/

#ifndef LEVELS_H
#define LEVELS_H

//@ #include "nat.gh"
//@ #include "listex.gh"

/*@
fixpoint option< pair<list<void*>, real> > X(void* x);
fixpoint bool P(void* x);
@*/

/*@
predicate obs(list<void*> O);
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
  return one_obs(condvar,Wt,Ot) &&
         (!P(condvar) || spr_obs(condvar,Wt,Ot))
          && (X(condvar) == none || own_obs(condvar,Wt,Ot));
}
@*/

/*@
fixpoint bool lt_some<t>(fixpoint(t, t, bool) lt, list<t> ys, t x) {
    return exists(ys, (lt)(x));
}
fixpoint bool all_lt_some<t>(fixpoint(t, t, bool) lt, list<t> xs, list<t> ys) {
    return forall(xs, (lt_some)(lt, ys));
}
fixpoint bool bag_le<t>(fixpoint(t, t, bool) lt, list<t> xs, list<t> ys) {
    return ys == xs || all_lt_some(lt, remove_all(ys, xs), remove_all(xs, ys)) == true;
}
fixpoint bool bag_lt<t>(fixpoint(t, t, bool) lt, list<t> xs, list<t> ys) {
    return bag_le(lt, xs, ys) && remove_all(xs, ys) != nil;
}
fixpoint bool level_lt(list<void*> level1, list<void*> level2) { return bag_lt(func_lt, level1, level2); }
fixpoint bool level_le(list<void*> level1, list<void*> level2) { return bag_le(func_lt, level1, level2); }
fixpoint bool wait_level_lt(pair<list<void*>, real> w1, pair<list<void*>, real> w2)
{ return level_lt(fst(w1), fst(w2)) || level_le(fst(w1), fst(w2)) && snd(w1) < snd(w2); }
fixpoint bool wait_level_le(pair<list<void*>, real> w1, pair<list<void*>, real> w2)
{ return wait_level_lt(w1,w2) || w1 == w2;}
fixpoint bool wait_level_below_object(pair<list<void*>, real> w, void* o) { return wait_level_lt(w, wait_level_of(o)); }
fixpoint bool wait_level_below_obs(pair<list<void*>, real> w, list<void*> O) { return forall(O, (wait_level_below_object)(w)); }
fixpoint bool w_level_below_all(void* o, list<void*> O) {
  return forall(O, (wait_level_below_object)(wait_level_of(o)));
}
fixpoint pair<list<void*>, real> max_wlevel (pair<list<void*>, real> w1, pair<list<void*>, real> w2){
  return wait_level_lt(w1,w2) ? w2 : w1;
}
fixpoint bool wl_xle_max(void* o, pair<list<void*>, real> xo, void* x){
  return !wait_level_lt(max_wlevel(wait_level_of(o), xo),wait_level_of(x));
}
fixpoint bool wait_level_lt_o(option< pair<list<void*>, real> > ow, pair<list<void*>, real> w){
  switch (ow){
    case none: return true;
    case some(sw): return wait_level_lt(sw, w);
  }
}
fixpoint bool wl_ltle(void* o, pair<list<void*>, real> xo, void* x){
  return wait_level_lt(max_wlevel(wait_level_of(o), xo),wait_level_of(x)) || !wait_level_lt_o(X(x), max_wlevel(wait_level_of(o), xo));
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
  return no_cycle_x(o, X(o), O);
}
@*/

/*@
fixpoint list<T> minus<T> (list<T> O1, list<T> O2){
    switch (O1){
        case nil: return nil;
        case cons(o,Os): return mem(o,O2)==true ? minus(Os,remove(o,O2)) : cons(o, minus(Os,O2));
    }
}
fixpoint list<T> ntimes_list<T>(nat n, T e, list<T> tail){
  switch (n){
    case zero: return tail;
    case succ(n0): return cons(e,ntimes_list(n0,e,tail));
  }
}
lemma void minus_ntimes(nat n, void* v)
  requires true;
  ensures minus(ntimes_list(succ(n),v,nil), cons(v,nil)) == ntimes_list(n,v,nil);
{
  switch (n){
    case zero:
    case succ(n0): minus_ntimes(n0,v);
  }
}
lemma void minus_nil<T>(list<T> O)
  requires true;
  ensures minus(O,nil) == O;
{
  switch (O){
    case nil:
    case cons(o,Os): minus_nil(Os);
  }
}
lemma void minus_self<T>(list<T> O, T x)
  requires true;
  ensures minus(cons(x,O),cons(x,nil)) == O;
{
  switch (O){
    case nil:
    case cons(o,Os): minus_self(Os,x);
  }  
}
fixpoint list<T> cons_bool<T>(bool b, list<T> O, T t){
  return b ? cons(t,O) : O;
}
@*/

/*@
fixpoint pair<list<void*>, real> wait_level_of(void* waitableObject);
lemma void wait_level_lt_trans(pair<list<void*>, real> w1, pair<list<void*>, real> w2, pair<list<void*>, real> w3);
    requires wait_level_lt(w1, w2) && wait_level_lt(w2, w3);
    ensures wait_level_lt(w1, w3) == true;
lemma void wait_level_lt_below_obs(pair<list<void*>, real> w1, pair<list<void*>, real> w2, list<void*> O);
    requires wait_level_lt(w1, w2) && wait_level_below_obs(w2, O);
    ensures wait_level_below_obs(w1, O) == true;
lemma void remove_all_all<t>(list<t> xs)
  requires true;
  ensures remove_all(xs,xs) == nil;
{
  switch (xs){
    case nil:
    case cons(x,xs0): remove_all_all(xs0); remove_remove_all(x,xs0,cons(x,xs0));    
  } 
}
lemma void w_level_lt_neq(void *v1, void* v2)
  requires wait_level_lt(wait_level_of(v1), wait_level_of(v2)) == true;
  ensures wait_level_of(v1) != wait_level_of(v2);
{
  remove_all_all(fst(wait_level_of(v1)));
}
lemma void below_count(void* v, list<void*> O)
    requires wait_level_below_obs(wait_level_of(v),O) == true;
    ensures count(O,(wl_xle_max)(v,wait_level_of(v))) == 0;
{
  switch (O){
    case nil:
    case cons(o,Os):
        assert wait_level_lt(wait_level_of(v), wait_level_of(o)) == true;
        if (wait_level_of(v) == wait_level_of(o)){ remove_all_all(fst(wait_level_of(v))); }
        else{below_count(v,Os);}
  } 
}
lemma void count_same(void* v, list<void*> O)
    requires count(O,(wl_xle_max)(v,wait_level_of(v))) == 0;
    ensures forall(O, (wl_ltle)(v,wait_level_of(v))) == true;
{
  switch (O){
    case nil:
    case cons(o,Os): count_nonnegative(Os,(wl_xle_max)(v,wait_level_of(v))); count_same(v,Os);
  } 
}
lemma void wait_level_between(pair<list<void*>, real> w0, pair<list<void*>, real> w2);
    requires wait_level_lt(w0,w2) == true;
    ensures exists(?w1) &*& wait_level_lt(w0, w1) == true &*& wait_level_lt(w1, w2) == true;
lemma void wait_level_betweens(pair<list<void*>, real> w1, list<void*> O);
    requires wait_level_below_obs(w1, O) == true;
    ensures exists(?w2) &*& wait_level_lt(w1, w2) == true &*& wait_level_below_obs(w2, O) == true;
        
//lemma void pich_wait_level_lt(pair<list<void*>, real> w);
//    requires true;
//    ensures exists(?w1) &*& wait_level_lt(w1, w) == true;    
@*/
           
#endif