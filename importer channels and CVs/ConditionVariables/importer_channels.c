#include "stdlib.h"
#include "monitors_with_importers.h"
#include "queues.h"
//@ #include "ghost_counters.gh"

struct channel {
   struct queue *q;
   struct mutex *m;
   struct condvar *v;
   //@ int gid;
};

/*@
predicate create_channel_ghost_args<T>(real gamma_wlevel, list<real> Mr, predicate(pair<int,struct channel*> message) M, fixpoint(T message, list<void*>) M') = true;  
predicate init_channel_ghost_args<T>(predicate(T message) Mch) = true;  

fixpoint bool level_lt_Mr(real r, void* o){
  return level_lt_levels(r, Mr(o));
}

fixpoint bool level_lt_Mrs(real r, list<void*> O) {
  return forall(O, (level_lt_Mr)(r));
}

fixpoint bool object_lt_Mrs(void* o, list<void*> O) {
  return level_lt_Mrs(level_of(o), O);
}

predicate uchannel(struct channel *ch, void* gamma, void* betta, predicate(pair<int,struct channel*> message) M, fixpoint(pair<int,struct channel*> message, list<void*>) M') =
  [_]ch->v |-> gamma &*& 
  [_]ch->q |-> betta &*&   
  [_]ch->m |-> ?m &*& 
  [_]ch->gid |-> ?gid &*&    
  [_]mutex(m) &*&  
  [_]cond(gamma,vtrn(gid),nil) &*&
  gamma != m &*&
  mutex_of(gamma) == m &*&
  inv(m) == channel_inv(ch,gamma,M,M');

predicate channel(struct channel *ch, void* gamma, void* betta, predicate(pair<int,struct channel*> message) M, fixpoint(pair<int,struct channel*> message, list<void*>) M') =
  [_]ch->v |-> gamma &*& 
  [_]ch->q |-> betta &*&     
  [_]ch->m |-> ?m &*& 
  [_]ch->gid |-> ?gid &*&      
  [_]mutex(m) &*&  
  [_]cond(gamma,vtrn(gid),nil) &*&
  gamma != m &*&  
  mutex_of(gamma) == m &*&
  inv(m) == channel_inv(ch,gamma, M, M');

predicate credit(struct channel *ch) = [_]ch->gid |-> ?gid  &*& tic(gid);

predicate_ctor creditor(struct channel *ch)() = credit(ch);

lemma void load(struct channel *ch)
  requires [?f]channel(ch,?v,?q,?M,?M') &*& obs(?O,?R);
  ensures [f]channel(ch,v,q,M,M') &*& obs(cons(v,O), R) &*& credit(ch);
{
  open [f]channel(ch,v,q,M,M');
  assert [_]ch->m |-> ?m;
  close mutex_inv(m,channel_inv(ch,v,M,M'));
  produce_lemma_function_pointer_chunk invariant_preserved(m, channel_inv(ch,v,M,M'), O, cons(v,O), R, creditor(ch))() {
    open channel_inv(ch,v,M,M')(?Wt2,?Ot2);
    assert [_]ch->gid |-> ?gid2;
    inc_ctr(gid2);
    g_chrgl(v);
    close channel_inv(ch,v,M,M')(Wt2,finc(Ot2,v));
    close credit(ch);
    close creditor(ch)();
  }{
  run_in_cs(m);
  };
  close [f]channel(ch,v,q,M,M');
  open creditor(ch)();
}
@*/

/*@
predicate_ctor vtrn(int gid)() = tic(gid);

predicate_ctor channel_inv(struct channel *b, struct condvar *v, predicate(pair<int,struct channel*> message) M, fixpoint(pair<int,struct channel*> message, list<void*>) M')(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) =
  [_]b->q |-> ?q &*& 
  [_]b->v |-> v &*& 
  [_]b->m |-> ?m &*&   
  [_]b->gid |-> ?gid &*&  
  queue< pair<int,struct channel*> >(q,?s,M,M') &*& 
  ctr(gid,?Ct) &*&  
  0 <= s &*&
  (void*)v != m &*&
  Wt(v) + Ct <= Ot(v) + s &&
  Wt(v) <= Ot(v);
@*/

struct channel *create_channel<T>()
  //@ requires create_channel_ghost_args< pair<int,struct channel*> >(?level, ?Mr, ?M, ?M');
  //@ ensures uchannel(result, ?gamma, ?betta, M, M') &*& level_of(gamma) == level &*& Mr(betta) == Mr;
{
  //@ leak create_channel_ghost_args(_,_,_,_);
  //@ close create_queue_ghost_args(Mr,M,M');
  struct queue *q = create_queue();
  //@ close create_mutex_ghost_args(0r);
  struct mutex *m = create_mutex();
    
  //@ int gid = new_ctr();
  //@ close create_condvar_ghost_args(level);
  struct condvar *v = create_condvar();
  //@ close init_condvar_ghost_args(m,vtrn(gid),nil);
  //@ init_condvar(v);
  
  struct channel *ch = malloc(sizeof(struct channel));
  if (ch==0)
    abort(); 
  ch->q = q;
  ch->m = m;
  ch->v = v;
  //@ ch->gid = gid;
  //@ leak [_]ch->v |-> _;
  //@ leak [_]ch->m |-> _;
  //@ leak [_]ch->gid |-> _;
  //@ leak [_]ch->q |-> _;
  //@ leak [_]malloc_block_channel(_);
  //@ leak [_]cond(v,_,_);

  //@ close init_mutex_ghost_args(channel_inv(ch,v,M,M'));
  //@ neq_cond_mutex(v,m);
  //@ close channel_inv(ch,v,M,M')(empb,empb);
  //@ init_mutex(m);
  //@ leak [_]mutex(m);  
  //@ close uchannel(ch, v, q,M,M');
  return ch;
}

void send(struct channel *ch, pair<int, struct channel*> message)
  /*@ requires obs(?O, ?R) &*& [?f]channel(ch,?gamma,?betta,?M,?M') &*& M(message) &*& (Mr(betta) == nil ? true : trandit(betta)) &*&
        forall(map(level_of, M'(message)),(mem')(Mr(betta))) == true; @*/
  //@ ensures obs(remove(gamma,minus(O,M'(message))), R) &*& [f]channel(ch,gamma,betta,M,M');        
{
  //@ open channel(ch,gamma,betta,M,M');
  //@ assert [_]ch->m |-> ?m &*& [_]ch->v |-> ?v;
  //@ close mutex_inv(m,channel_inv(ch,v,M,M'));
  //@ assume(object_lt_objects(ch->m,O)); 
  //@ assume (!mem(m,M'(message)));  
  // This assumption can be avoided using the notion of termination levels.
  // See Jacobs, Bart, Dragan Bosnacki, and Ruurd Kuiper. "Modular termination verification of single-threaded and multithreaded programs." 
  // ACM Transactions on Programming Languages and Systems (TOPLAS) 40.3 (2018): 12.)
  mutex_acquire(ch->m);
  //@ open channel_inv(ch,v,M,M')(?Wt,_);
  //@ assert [_]ch->gid |-> ?gid;    
  /*@ if (Wt(gamma)>0){
        inc_ctr(gid);
        close vtrn(gid)();
      }
  @*/
  condvar_signal(ch->v);
  enqueue(ch->q, message);
  //@ g_dischl(gamma);
  //@ assert mutex_held(m,_,?Wt1,?Ot1);
  //@ close channel_inv(ch,v,M,M')(Wt1,Ot1);
  //@ close mutex_inv(m,channel_inv(ch,v,M,M'));
  mutex_release(ch->m);
  //@ close [f]channel(ch,gamma,betta,M,M');
}

pair<int, struct channel*> receive(struct channel *ch)
  //@ requires obs(?O, ?R) &*& [?f]channel(ch,?gamma,?betta,?M,?M') &*& credit(ch) &*& object_lt_objects(gamma,O) == true &*& object_lt_Mrs(gamma,O) == true;
  //@ ensures obs(append(O,M'(result)), remove(betta,R)) &*& [f]channel(ch,gamma,betta,M,M') &*& M(result);
{
  //@ open channel(ch,gamma,betta,M,M');
  //@ assert [_]ch->m |-> ?m &*& [_]ch->v |-> ?v &*& [_]ch->q |-> ?q;
  //@ close mutex_inv(m,channel_inv(ch,v,M,M'));
  //@ assume(object_lt_objects(ch->m,O));
  mutex_acquire(ch->m);
  //@ open channel_inv(ch,v,M,M')(?Wt1,?Ot1);
  //@ assert [_]ch->gid |-> ?gid;  
  //@ open credit(ch);
  while (size_of(ch->q)==0)
  /*@ invariant [_]ch->m |-> m &*& 
                [_]ch->v |-> v &*& 
                [_]ch->gid |-> gid &*&                 
		[_]cond(v,vtrn(gid),nil) &*&                
                [_]ch->q |-> q &*&
                queue< pair<int, struct channel*> >(q,?s,M,M') &*& 
                ctr(gid,?Ct) &*&                
                s >= 0 &*& 
                mutex_held(m, _, ?Wt, ?Ot) &*& 
                Wt(v) + Ct <= Ot(v) + s &*&
                Wt(v) <= Ot(v) &*&
                obs(cons(m,O),R) &*&
                tic(gid); @*/
  {
    //@ dec_ctr(gid);
    //@ close channel_inv(ch,v,M,M')(finc(Wt,v),Ot);
    //@ close mutex_inv(m,channel_inv(ch,v,M,M'));
    condvar_wait(ch->v, ch->m);
    //@ open channel_inv(ch,v,M,M')(_,_);
    //@ open vtrn(gid)();
  }
  pair<int, struct channel*> msg = dequeue< pair<int, struct channel*> >(ch->q);
  //@ dec_ctr(gid);
  //@ close channel_inv(ch,v,M,M')(Wt, Ot);
  //@ close mutex_inv(m,channel_inv(ch,v,M,M'));
  mutex_release(ch->m);
  //@ leak [_]mutex(m);
  //@ close [f]channel(ch,gamma,betta,M,M');
  return msg;
}

