#ifndef OBLIGATIONS_H
#define OBLIGATIONS_H

//@ #include "nat.gh"
//@ #include "levels.h"
//@ #include "relaxed_levels.h"

/*@
predicate obs(list<void*> O);
@*/

/*@
fixpoint list<T> minus<T> (list<T> O1, list<T> O2){
    switch (O1){
        case nil: return nil;
        case cons(o,Os): return mem(o,O2)==true ? minus(Os,remove(o,O2)) : cons(o, minus(Os,O2));
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
predicate nothing() = true;

predicate n_times(int n, predicate() p) =
  n <= 0 ? true : p() &*& n_times(n-1,p);

lemma void n_times_no_transfer(int n);
  requires true;
  ensures n_times(n,nothing);  
  
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
@*/
#endif
