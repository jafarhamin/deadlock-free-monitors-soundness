#ifndef CHANNELS_H
#define CAHNNELS_H
#include "levels.h"

struct channel;

typedef struct channel *channel;

/*@
fixpoint list<void*> N(void* o);
fixpoint list<real> Mr(void* o);
fixpoint predicate(T message) M<T>(void* o);
fixpoint fixpoint(T message, list<void*>) M'<T>(void* o);
fixpoint bool S(void* o);

predicate MP<T>(void* o, predicate(T message) Mo) = M(o) == Mo;
predicate M'P<T>(void* o, fixpoint(T message, list<void*>) M'o) = M'(o) == M'o;

predicate create_channel_ghost_args<T>(real gamma_wlevel, list<void*> Nch, list<real> Mr, predicate(T message) Mch, fixpoint(T message, list<void*>) M'ch, bool server) = true;  

predicate credit(struct channel *ch);
predicate trandit(struct channel *ch);

lemma void g_credit(struct channel *ch);
  requires obs(?O, ?R);
  ensures obs(cons(ch,O), R) &*& credit(ch);

lemma void g_trandit(struct channel *ch);
  requires obs(?O, ?R);
  ensures obs(O, Mr(ch) == nil ? R : cons(ch,R)) &*& trandit(ch);

lemma void g_trandit'(struct channel *ch);
  requires obs(?O, ?R) &*& trandit(ch);
  ensures obs(O, remove(ch,R));

 
fixpoint bool memMr<T>(real r, void* o){
  return mem(r, Mr(o));
}

fixpoint bool level_lt_Mr(real r, void* o){
  return level_lt_levels(r, Mr(o));
}

fixpoint bool level_lt_Mrs(real r, list<void*> O) {
  return forall(O, (level_lt_Mr)(r));
}

fixpoint bool object_lt_Mrs(void* o, list<void*> O) {
  return level_lt_Mrs(level_of(o), O);
}

fixpoint bool id<T>(T x, T y){
  return x == y;
}

fixpoint bool can_transfer<T>(T message, void* ch, void* ch'){
  return count((M')(ch)(message), (id)(ch')) == count(N(ch'), (id)(ch));
}

fixpoint bool mem'<t>(list<t> xs, t x){
  return mem(x,xs);
}
@*/

struct channel *create_channel<T>();
  //@ requires create_channel_ghost_args<T>(?level, ?Nch, ?Mrch, ?Mch, ?M'ch, ?server) &*& forall(Nch, (memMr)(level)) == true;
  //@ ensures level_of(result) == level &*& N(result) == Nch &*& M'(result) == M'ch &*& Mr(result) == Mrch &*& S(result) == server;// &*& M(result) == Mch;

void send<T>(struct channel *ch, T message);
  /*@ requires obs(?O, ?R) &*& MP<T>(ch,?Mch) &*& Mch(message) &*& trandit(ch) &*&
        forall(map(level_of, (M')(ch)(message)),(mem')(Mr(ch))) == true &*& 
        forall((M')(ch)(message), (can_transfer)(message, ch)) == true; @*/
  //@ ensures obs(remove(ch,minus(O,(M')(ch)(message))), R);        

T receive<T>(struct channel *ch);
  /*@ requires obs(?O, ?R) &*& (S(ch) ? true : credit(ch)) &*& object_lt_objects(ch,O) == true &*& 
        object_lt_Mrs(ch,O) == true &*& MP<T>(ch,?Mch) &*& S(ch) ? O==nil && count(R,(id)(ch)) == length(R) : true; @*/
  //@ ensures obs(append(O,(M')(ch)(result)), remove(ch,R)) &*& Mch(result);

#endif  
