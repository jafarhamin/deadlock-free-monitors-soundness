#include "stdlib.h"
#include "levels.h"
#include "monitors.h"
#include "queues.h"
#include "channels.h"
//@ #include "ghost_counters.gh"

struct channel {
   struct queue *q;
   mutex m;
   cvar v;
   //@ int gid;
};

/*@
predicate channel(struct channel *ch; void* gamma) =
  [_]ch->v |-> gamma &*& 
  [_]ch->m |-> ?m &*& 
  [_]mutex(m) &*&  
  [_]cond(gamma,creditor(ch),nil) &*&
  mutex_of(gamma) == m &*&
  inv(m) == channel_inv(ch,gamma) &*&
  level'(m) == none &*&
  level(m) == pair({create_channel}, 0r);

predicate credit(struct channel *ch) = [_]ch->gid |-> ?gid  &*& tic(gid);

predicate_ctor creditor(struct channel *ch)() = credit(ch);

lemma void load(struct channel *ch)
  requires [?f]channel(ch,?v) &*& obs(?O);
  ensures [f]channel(ch,v) &*& obs(cons(v,O)) &*& credit(ch);
{
  open [f]channel(ch,v);
  assert [_]ch->m |-> ?m;
  close mutex_inv(m,channel_inv(ch,v));
  produce_lemma_function_pointer_chunk invariant_preserved(m, channel_inv(ch,v), O, cons(v,O), creditor(ch))() {
    open channel_inv(ch,v)(?Wt2,?Ot2);
    assert [_]ch->gid |-> ?gid2;
    inc_ctr(gid2);
    g_chrgl(v);
    close channel_inv(ch,v)(Wt2,finc(Ot2,v));
    close credit(ch);
    close creditor(ch)();
  }{
  run_in_cs(m);
  };
  close [f]channel(ch,v);
  open creditor(ch)();
}
@*/

/*@
predicate_ctor vtrn(int gid)() = tic(gid);

predicate_ctor channel_inv(channel ch, cvar v)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) =
  ch->q |-> ?q &*& 
  [_]ch->v |-> v &*& 
  queue(q,?s) &*& 
  s >= 0 &*& 
  [_]ch->gid |-> ?gid &*&  
  ctr(gid,?Ct) &*&  
  (P(v) == false || (Wt(v) + Ct < Ot(v) + s && (Wt(v) == 0 || Wt(v) < Ot(v)))) &&
  Wt(v) + Ct <= Ot(v) + s &&
  Wt(v) <= Ot(v);
@*/

struct channel *create_channel()
  //@ requires create_channel_ghost_args(?gamma_wlevel, ?gamma_X, ?gamma_P) &*& obs(?O);
  /*@ ensures channel(result,?gamma) &*& level(gamma) == gamma_wlevel &*& level'(gamma) == gamma_X &*& P(gamma) == gamma_P &*& 
        obs(?O') &*&((gamma_P && O' == cons(gamma,O)) || (!gamma_P && O' == O));@*/
{
  //@ leak create_channel_ghost_args(_,_,_);
  struct queue *q = create_queue();
  //@ close create_mutex_ghost_args(pair({create_channel}, 0r));
  struct mutex *m = create_mutex();
    
  //@ int gid = new_ctr();
  //@ close create_cvar_ghost_args(gamma_wlevel,gamma_P,gamma_X);
  cvar v = create_cvar();
  
  struct channel *ch = malloc(sizeof(struct channel));
  if (ch==0) abort(); 
  
  //@ close init_cvar_ghost_args(m,creditor(ch),nil);
  //@ init_cvar(v);
  
  ch->q = q;
  ch->m = m;
  ch->v = v;
  //@ ch->gid = gid;
  //@ leak [_]ch->v |-> _;
  //@ leak [_]ch->m |-> _;
  //@ leak [_]ch->gid |-> _;
  //@ leak [_]malloc_block_channel(_);
  //@ leak [_]cond(v,_,_);

  //@ close init_mutex_ghost_args(channel_inv(ch,v));
  /*@ if (!gamma_P)
        close channel_inv(ch,v)(empb,empb);
      else{
        g_chrgu(v);
        close channel_inv(ch,v)(empb,finc(empb,v));
      }
  @*/
  //@ init_mutex(m);
  //@ leak [_]mutex(m);  
  return ch;
}

int receive(struct channel *ch)
  //@ requires [?f]channel(ch,?gamma) &*& obs(?O) &*& credit(ch) &*& no_cycle(gamma,O) == true &*& wait_level_below_obs(pair({receive}, 0r), O) == true;
  //@ ensures  [f]channel(ch,gamma) &*& obs(O);
{
  //@ open channel(ch,gamma);
  //@ assert [_]ch->m |-> ?m &*& [_]ch->v |-> ?v;
  //@ close mutex_inv(m,channel_inv(ch,v));
  //@ wait_level_lt_below_obs(level(m), pair({receive}, 0r), O);
  mutex_acquire(ch->m);
  //@ open channel_inv(ch,v)(?Wt1,?Ot1);
  //@ assert [_]ch->gid |-> ?gid;  
  while (size_of(ch->q)==0)
  /*@ invariant [_]ch->m |-> m &*& 
                [_]ch->v |-> v &*& 
                [_]ch->gid |-> gid &*&                 
		[_]cond(v,creditor(ch),nil) &*&                
                ch->q |-> ?q &*&
                queue(q,?s) &*& 
                s >= 0 &*& 
                mutex_held(m, _, ?Wt, ?Ot) &*& 
                ctr(gid,?Ct) &*&
                (P(v) == false || (Wt(v) + Ct < Ot(v) + s && (Wt(v) == 0 || Wt(v) < Ot(v)))) &&
                Wt(v) + Ct <= Ot(v) + s &*&
                Wt(v) <= Ot(v) &*&
                obs(cons(m,O)) &*&
                credit(ch); @*/
  {
    //@ open credit(ch);  
    //@ dec_ctr(gid);
    //@ close channel_inv(ch,v)(finc(Wt,v),Ot);
    //@ close mutex_inv(m,channel_inv(ch,v));
    /*@ produce_lemma_function_pointer_chunk spurious(channel_inv(ch,v), creditor(ch), v)() {
       open channel_inv(ch,v)(?Wt2,?Ot2);
       assert [_]ch->gid |-> ?gid2;
       inc_ctr(gid2);
       close channel_inv(ch,v)(fdec(Wt2,v),Ot2);
       close credit(ch);
       close creditor(ch)();
      }; @*/    
    cvar_spwk_wait(ch->v, ch->m);
    //@ open channel_inv(ch,v)(_,_);
    //@ open creditor(ch)();    
  }
  int d = dequeue(ch->q);
  //@ open credit(ch);  
  //@ dec_ctr(gid);
  //@ close channel_inv(ch,v)(Wt, Ot);
  //@ close mutex_inv(m,channel_inv(ch,v));
  mutex_release(ch->m);
  //@ leak [_]mutex(m);
  //@ close [f]channel(ch,gamma);
  return d;
}

void send(struct channel *ch, int data)
  //@ requires [?f]channel(ch,?gamma) &*& obs(?O) &*& wait_level_below_obs(pair({send}, 0r), O) == true;
  //@ ensures [f]channel(ch,gamma) &*& obs(remove(gamma,O));
{
  //@ open channel(ch,gamma);
  //@ assert [_]ch->m |-> ?m &*& [_]ch->v |-> ?v;
  //@ close mutex_inv(m,channel_inv(ch,v));
  //@ wait_level_lt_below_obs(level(m), pair({send}, 0r), O);
  mutex_acquire(ch->m);
  //@ open channel_inv(ch,v)(?Wt,_);
  //@ assert [_]ch->gid |-> ?gid;    
  /*@ if (Wt(gamma)>0){
        inc_ctr(gid);
        close credit(ch);
        close creditor(ch)();
      } @*/
  cvar_signal(ch->v);
  //@ minus_nil(cons(gamma,O));
  enqueue(ch->q,data);
  //@ assert mutex_held(m,_,?Wt0,?Ot0);
  //@ g_dischl(gamma);
  //@ assert mutex_held(m,_,?Wt1,?Ot1);
  //@ close channel_inv(ch,v)(Wt1,Ot1);
  //@ close mutex_inv(m,channel_inv(ch,v));
  mutex_release(ch->m);
  //@ close [f]channel(ch,gamma);
}
