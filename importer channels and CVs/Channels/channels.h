#ifndef CHANNELS_H
#define CAHNNELS_H
#include "levels.h"

struct channel;

typedef struct channel *channel;

/*@
fixpoint list<real> Mr(void* o);
fixpoint bool Ser<T>(void* o);


predicate create_channel_ghost_args<T>(real gamma_wlevel, list<real> Mr, bool server) = true;  
predicate init_channel_ghost_args<T>(predicate(T message) M, fixpoint(T message, list<void*>) M') = true;  
predicate uchannel(struct channel *ch);
predicate channel<T>(struct channel *ch, predicate(T message) M, fixpoint(T message, list<void*>) M');
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

fixpoint bool level_lt_Mr_or_eq(void* o1, void* o){
  return level_lt_levels(level_of(o1), Mr(o)) || o1 == o;
}

fixpoint bool level_lt_Mrs(real r, list<void*> O) {
  return forall(O, (level_lt_Mr)(r));
}

fixpoint bool object_lt_Mrs(void* o, list<void*> O) {
  return forall(O, (level_lt_Mr_or_eq)(o));
}

fixpoint bool id<T>(T x, T y){
  return x == y;
}

fixpoint bool mem'<t>(list<t> xs, t x){
  return mem(x,xs);
}
@*/

/*@
lemma void init_channel<T>(channel ch);
  requires init_channel_ghost_args<T>(?Mch, ?M'ch) &*& uchannel(ch);
  ensures channel(ch, Mch, M'ch);
@*/


struct channel *create_channel<T>();
  //@ requires create_channel_ghost_args<T>(?level, ?Mrch, ?server);
  //@ ensures uchannel(result) &*& level_of(result) == level &*& Mr(result) == Mrch &*& Ser(result) == server;

void send<T>(struct channel *ch, T message);
  /*@ requires obs(?O, ?R) &*& [?f]channel(ch,?Mch,?M'ch) &*& Mch(message) &*& (Mr(ch) == nil ? true : trandit(ch)) &*&
        forall(map(level_of, M'ch(message)),(mem')(Mr(ch))) == true; @*/
  //@ ensures obs(remove(ch,minus(O,M'ch(message))), R) &*& [f]channel(ch,Mch,M'ch);        

T receive<T>(struct channel *ch);
  /*@ requires obs(?O, ?R) &*& [?f]channel<T>(ch,?Mch,?M'ch) &*& (Ser(ch) ? true : credit(ch)) &*& object_lt_objects(ch,O) == true &*& 
        object_lt_Mrs(ch,R) == true &*& Ser(ch) ? O == nil && count(R,(id)(ch)) == length(R) : true; @*/
  //@ ensures obs(append(O,M'ch(result)), remove(ch,R)) &*& [f]channel(ch,Mch,M'ch) &*& Mch(result);

#endif  
