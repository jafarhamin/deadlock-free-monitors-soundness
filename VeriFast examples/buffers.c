#include "stdlib.h"
#include "levels.h"
#include "monitors.h"
#include "buffers.h"

/*@
predicate buffer(struct buffer *b; void* gamma) =
  [_]b->v |-> gamma &*& 
  [_]b->m |-> ?m &*& 
  [_]mutex(m) &*&  
  [_]cond(gamma,nothing,nil) &*&
  mutex_of(gamma) == m &*&
  inv(m) == buffer_inv(b,gamma) &*&
  level'(m) == none &*&
  level(m) == pair({create_buffer}, 0r);

predicate_ctor buffer_inv(struct buffer *b, cvar v)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) =
  b->value |-> ?val &*& 
  b->ready |-> ?ready &*& 
  [_]b->v |-> v &*& 
  P(v) == false &*&
  level'(v) == none &*&
  ready ? true : 0 < Ot(v);
@*/

struct buffer{
   int value;
   bool ready;
   struct mutex *m;
   cvar v;
};

struct buffer* create_buffer()
  //@ requires create_buffer_ghost_args(?wlevel) &*& obs(?O);
  /*@ ensures buffer(result,?v) &*& obs(cons(v,O)) &*& level(v) == wlevel; @*/
{
  //@ leak create_buffer_ghost_args(_);
  //@ close create_mutex_ghost_args(pair({create_buffer}, 0r));
  mutex m = create_mutex();
  //@ close create_cvar_ghost_args(wlevel,false,none);
  cvar v = create_cvar();
  //@ close init_cvar_ghost_args(m,nothing,nil);
  //@ init_cvar(v);
  
  struct buffer *b = malloc(sizeof(struct buffer));
  if (b==0) abort(); 
  b->ready=false;
  b->m = m;
  b->v = v;
  //@ leak [_]b->v |-> _;
  //@ leak [_]b->m |-> _;
  //@ leak [_]malloc_block_buffer(_);
  //@ leak [_]cond(v,_,_);

  //@ close init_mutex_ghost_args(buffer_inv(b,v));
  //@ close buffer_inv(b,v)(empb, finc(empb,v));
  //@ g_chrgu(v);
  //@ init_mutex(m);
  //@ leak [_]mutex(m);  
  return b;
}

int get(struct buffer* b)
  //@ requires [_]buffer(b,?v) &*& obs(?O) &*& wait_level_below_obs(pair({get}, 0r), O) == true;
  //@ ensures [_]buffer(b,v) &*& obs(O);
{
  //@ assert [_]b->m |-> ?m; 
  //@ wait_level_lt_below_obs(level(m), pair({get}, 0r), O);        
  mutex_acquire(b->m);
  //@ open buffer_inv(b,v)(?Wt0,?Ot0);
  int result = b->value;  
  //@ close buffer_inv(b,v)(Wt0,Ot0);
  mutex_release(b->m);
  return result;
}

int get_when_ready(struct buffer* b)
  //@ requires [_]buffer(b,?v) &*& obs(?O) &*& w_level_below_all(v,O)==true &*& wait_level_below_obs(pair({get_when_ready}, 0r), O) == true;
  //@ ensures [_]buffer(b,v) &*& obs(O);
{
  //@ assert [_]b->m |-> ?m;
  //@ wait_level_lt_below_obs(level(m), pair({get_when_ready}, 0r), O);    
  mutex_acquire(b->m);
  //@ open buffer_inv(b,v)(?Wt,?Ot); 
  //@ assert mutex_held(m,?f,Wt,Ot); 
  while (!b->ready)
  /*@ invariant obs(cons(m,O)) &*& b->ready |-> ?ready &*& [_]b->v |-> v &*& [_]b->m |-> m &*& [_]cond(v,nothing,nil) &*& mutex_held(m,f,?Wt',?Ot') &*& b->value |-> ?val &*& ready ? true : 0 < Ot'(v); @*/
  { 
    //@ close buffer_inv(b,v)(finc(Wt',v),Ot');
    /*@ produce_lemma_function_pointer_chunk spurious(buffer_inv(b, v), nothing, v)() {
       open buffer_inv(b, v)(?Wt2,?Ot2);
       close buffer_inv(b, v)(fdec(Wt2,v),Ot2);
       close nothing();
      }; @*/    
    cvar_spwk_wait(b->v, b->m);
    //@ open buffer_inv(b,v)(_,_);  
    //@ open nothing();
  }
  int result = b->value;
  //@ close buffer_inv(b,v)(Wt',Ot');  
  mutex_release(b->m);
  return result;
}

void set_and_notify(struct buffer* b, int value)
  //@ requires [_]buffer(b,?v) &*& obs(?O) &*& wait_level_below_obs(pair({set_and_notify}, 0r), O) == true;
  //@ ensures [_]buffer(b,v) &*& obs(remove(v,O));
{
  //@ assert [_]b->m |-> ?m; 
  //@ wait_level_lt_below_obs(level(m), pair({set_and_notify}, 0r), O);        
  mutex_acquire(b->m);
  //@ open buffer_inv(b,v)(_,_);    
  b->value = value;
  b->ready = true;
  //@ assert mutex_held(m, _, ?Wt0, ?Ot0); 
  //@ n_times_no_transfer(Wt0(v));
  cvar_broadcast(b->v); 
  //@ minus_nil(O);  
  //@ g_dischl(v);  
  //@ assert mutex_held(m, _, ?Wt, ?Ot); 
  //@ close buffer_inv(b,v)(Wt,Ot);
  mutex_release(b->m);  
}
