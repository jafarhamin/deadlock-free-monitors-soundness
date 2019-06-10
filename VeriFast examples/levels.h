#ifndef LEVELS_H
#define LEVELS_H

//@ #include "listex.gh"

/*@
fixpoint pair<list<void*>, real> level(void* waitableObject);
@*/

/*@
fixpoint bool lt_some<t>(fixpoint(t, t, bool) lt, list<t> ys, t x){
    return exists(ys, (lt)(x));
}

fixpoint bool all_lt_some<t>(fixpoint(t, t, bool) lt, list<t> xs, list<t> ys){
    return forall(xs, (lt_some)(lt, ys));
}

fixpoint bool bag_le<t>(fixpoint(t, t, bool) lt, list<t> xs, list<t> ys){
    return ys == xs || all_lt_some(lt, remove_all(ys, xs), remove_all(xs, ys)) == true;
}

fixpoint bool bag_lt<t>(fixpoint(t, t, bool) lt, list<t> xs, list<t> ys){
    return bag_le(lt, xs, ys) && remove_all(xs, ys) != nil;
}

fixpoint bool level_lt(list<void*> level1, list<void*> level2){
  return bag_lt(func_lt, level1, level2);
}

fixpoint bool level_le(list<void*> level1, list<void*> level2){
  return bag_le(func_lt, level1, level2);
}

fixpoint bool wait_level_lt(pair<list<void*>, real> w1, pair<list<void*>, real> w2){
  return level_lt(fst(w1), fst(w2)) || level_le(fst(w1), fst(w2)) && snd(w1) < snd(w2);
}

fixpoint bool wait_level_le(pair<list<void*>, real> w1, pair<list<void*>, real> w2){
  return wait_level_lt(w1,w2) || w1 == w2;
}

fixpoint bool wait_level_below_object(pair<list<void*>, real> w, void* o){
  return wait_level_lt(w, level(o));
}

fixpoint bool wait_level_below_obs(pair<list<void*>, real> w, list<void*> O){
  return forall(O, (wait_level_below_object)(w));
}
@*/

/*@
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
  requires wait_level_lt(level(v1), level(v2)) == true;
  ensures level(v1) != level(v2);
{
  remove_all_all(fst(level(v1)));
}

lemma void wait_level_between(pair<list<void*>, real> w0, pair<list<void*>, real> w2);
    requires wait_level_lt(w0,w2) == true;
    ensures exists(?w1) &*& wait_level_lt(w0, w1) == true &*& wait_level_lt(w1, w2) == true;

lemma void wait_level_betweens(pair<list<void*>, real> w1, list<void*> O);
    requires wait_level_below_obs(w1, O) == true;
    ensures exists(?w2) &*& wait_level_lt(w1, w2) == true &*& wait_level_below_obs(w2, O) == true;
@*/
     
#endif    
