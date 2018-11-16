/*
  - Relaxed Precedence Relation
  - Safe Obligations
*/

#ifndef LEVELS_H
#define LEVELS_H

//@ #include "nat.gh"
//@ #include "listex.gh"

/*@
predicate obs(list<void*> O);
@*/

/*@
fixpoint bool enfo(void* condvar, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot){ 
  return Wt(condvar) <= 0 || Ot(condvar) > 0;
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

fixpoint bool wait_level_below_object(pair<list<void*>, real> w, void* o) { return wait_level_lt(w, wait_level_of(o)); }

fixpoint bool wait_level_below_obs(pair<list<void*>, real> w, list<void*> O) { return forall(O, (wait_level_below_object)(w)); }

fixpoint bool w_level_below_all(void* o, list<void*> O) {
  return forall(O, (wait_level_below_object)(wait_level_of(o)));
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

@*/

/*@
fixpoint pair<list<void*>, real> wait_level_of(void* waitableObject);

lemma void wait_level_lt_below_obs(pair<list<void*>, real> w1, pair<list<void*>, real> w2, list<void*> O);
    requires wait_level_lt(w1, w2) && wait_level_below_obs(w2, O);
    ensures wait_level_below_obs(w1, O) == true;
@*/
           
#endif    
