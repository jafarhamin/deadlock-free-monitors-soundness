#include "stdlib.h"
#include "monitors.h"
#include "barriers.h"

struct barrier {
   struct mutex *m;
   struct cvar *v;
   int r;
};

/*@
predicate_ctor barrier_inv(struct barrier *b, struct cvar *v)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) = 
  b->r |-> ?r &*& 
  [_]b->v |-> v &*& 
  [_]b->m |-> ?m &*& 
  [_]cond(v, nothing, nil) &*&
  r >= 0 &*& 
  mutex_of(v)==m &*& 
  P(v)==false &*&
  Wt(v) <= 0 || 0 < r &*& 
  r <= Ot(v);
  
predicate barrier(struct barrier *b; void* gamma) = 
  [_]b->m |-> ?m &*&
  [_]b->v |-> gamma &*& 
  [_]mutex(m) &*& 
  inv(m) == barrier_inv(b,gamma) &*&
  level'(gamma) == none &*&
  level(m) == pair({create_barrier}, 0r) &*&
  level'(m) == none;
@*/

struct barrier *create_barrier(int r)
  //@ requires obs(nil) &*& create_barrier_ghost_args(?v_level) &*& r >= 0;
  //@ ensures barrier(result, ?v) &*& obs(ntimes_list(nat_of_int(r),v,nil)) &*& level(v) == v_level;
{
  //@ leak create_barrier_ghost_args(v_level);
  //@ close create_mutex_ghost_args(pair({create_barrier}, 0r));
  mutex m = create_mutex();
  //@ close create_cvar_ghost_args(v_level, false, none);
  cvar v = create_cvar();
  //@ close init_cvar_ghost_args(m,nothing,nil);
  //@ init_cvar(v);
    
  struct barrier *b = malloc(sizeof(struct barrier));
  
  if (b==0)
    abort();      
  b->r = r;
  b->m = m;
  b->v = v;
  //@ leak [_]barrier_m(_,_);
  //@ leak [_]barrier_v(_,_);
  //@ leak [_]malloc_block_barrier(_);
  //@ leak [_]cond(v, nothing, nil);
  //@ close init_mutex_ghost_args(barrier_inv(b,v));
  //@ close barrier_inv(b,v)(empb,finc'(r,empb,v));  
  //@ g_chrgu'(r,v); 
  //@ init_mutex(m);
  //@ leak [_]mutex(m);
  return b;
}

void wait_barrier(struct barrier *b)
  //@ requires [_]barrier(b,?v) &*& obs(cons(v,?O)) &*& w_level_below_all(v,O) == true &*& wait_level_below_obs(pair({(wait_barrier)}, 0r), cons(v,O)) == true;
  //@ ensures [_]barrier(b,v) &*& obs(O);
{
  //@ open [_]barrier(b,v);
  //@ assert [_]b->m |-> ?m;
  //@ close mutex_inv(m,barrier_inv(b,v));
  //@ wait_level_lt_below_obs(level(m), pair({(wait_barrier)}, 0r), cons(v,O));
  mutex_acquire(b->m);
  //@ open barrier_inv(b,v)(?Wt1,?Ot1);
  if (b->r <= 0)
    abort();
  b->r = b->r - 1;
  if (b->r==0){
    //@ n_times_no_transfer(Wt1(v));
    cvar_broadcast(b->v);
    //@ g_dischl(v);
  }
  else {
    //@ g_dischl(v);
    while (b->r > 0)
      /*@ invariant [_]b->m |-> m &*& 
                    [_]b->v |-> v &*& 
                    [_]cond(v, nothing, nil) &*&
                    b->r |-> ?r &*& 
                    r>=0 &*& 
                    mutex_held(m, _, ?Wt, ?Ot) &*&
                    obs(cons(m,O)) &*&
                    Wt(v) <= 0 || 0 < r &*&
                    r <= Ot(v); @*/
    {
      //@ close barrier_inv(b,v)(finc(Wt,v),Ot);
      //@ close mutex_inv(m,barrier_inv(b,v));
      /*@ produce_lemma_function_pointer_chunk spurious(barrier_inv(b,v), nothing, v)() {
            open barrier_inv(b,v)(?Wt2,?Ot2);
            close barrier_inv(b,v)(fdec(Wt2,v),Ot2);
            close nothing();}; @*/
      cvar_spwk_wait(b->v, b->m);
      //@ open barrier_inv(b,v)(_,_); 
      //@ open nothing();   
    }
}
  //@ assert mutex_held(m,_,?Wte,?Ote);
  //@ close barrier_inv(b,v)(Wte,Ote);
  //@ close mutex_inv(m,barrier_inv(b,v));  
  mutex_release(b->m);
  //@ leak [_]mutex(m);
}
