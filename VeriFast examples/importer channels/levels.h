#ifndef LEVELS_H
#define LEVELS_H

//@ #include "nat.gh"
//@ #include "listex.gh"

/*@
predicate obs(list<void*> O, list<void*> R);
@*/

/*@
fixpoint real level_of(void* waitableObject);
@*/

/*@
fixpoint bool level_lt_level(real w1, real w2){
  return w1 < w2;
}

fixpoint bool level_lt_object(real w, void* o){
  return level_lt_level(w, level_of(o));
}

fixpoint bool object_lt_objects(void* o, list<void*> O) {
  return forall(O, (level_lt_object)(level_of(o)));
}

fixpoint bool level_lt_levels(real r, list<real> R) {
  return forall(R, (level_lt_level)(r));
}

fixpoint bool level_lt_objects(real r, list<void*> O) {
  return forall(O, (level_lt_object)(r));
}

lemma void object_lt_remove(void* o, void* o', list<void*> O)
  requires object_lt_objects(o,O) == true;  
  ensures object_lt_objects(o,remove(o',O)) == true;
{
  switch (O){
    case nil:
    case cons(o1,O1): object_lt_remove(o,o',O1);
  }  
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
           
#endif