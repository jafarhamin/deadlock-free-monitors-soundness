#include "stdlib.h"
#include "monitors.h"
#include "mutexes_cv.h"
//@ #include "ghost_counters.gh"

struct exclusive{
   struct mutex *m;
   struct condvar *v;
   bool b;
   int w;
};

/*@
predicate exclusive(struct exclusive *ex; void* v) =
  [_]ex->v |-> v &*& 
  [_]ex->m |-> ?m &*& 
  [_]mutex(m) &*&  
  mutex_of(v) == m &*&
  inv(m) == exclusive_inv(ex, v) &*&
  wait_level_of(m) == pair({new_exclusive}, 0r) &*&
  wait_level_lt(wait_level_of(m), wait_level_of(v)) == true &*&  
  M'(v) == cons(v,nil);
@*/

/*@
predicate_ctor exclusive_inv(struct exclusive *e, struct condvar *v)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) = 
  [_]e->m |-> ?m &*& 
  e->b |-> ?b &*& 
  e->w |-> Wt(v) &*&   
  [_]e->v |-> v &*& 
  [_]cond(v) &*&
  mutex_of(v)==m &*& 
  M(v) == no_transfer &*&
  0 <= Ot(v) &*&  
  (b ? 0 < Ot(v) : Wt(v) <= 0);
  
predicate_ctor vtrn(int i)() = tic(i);
@*/

struct exclusive *new_exclusive()
  //@ requires exists(?v_wlevel) &*& wait_level_lt(pair({(new_exclusive)}, 0r), v_wlevel) == true;
  //@ ensures exclusive(result,?v) &*& wait_level_of(v) == v_wlevel;
{
    //@ close create_mutex_ghost_args(pair({new_exclusive}, 0r));
    struct mutex *m = create_mutex();
    
    //@ open exists(v_wlevel);
    //@ close create_condvar_ghost_args(v_wlevel);
    struct condvar *v = create_condvar();
    //@ close init_condvar_ghost_args(m,no_transfer,cons(v,nil));
    //@ init_condvar(v);
        
    struct exclusive *ex = malloc(sizeof(struct exclusive));
    if (ex==0)
      abort();
    ex->m = m;
    ex->w = 0;    
    ex->v = v;
    ex->b = false;
    //@ leak [_]ex->v |-> _;
    //@ leak [_]ex->m |-> _;    
    //@ leak [_]malloc_block_exclusive(_);
    //@ leak [_]cond(v);
    //@ close init_mutex_ghost_args(exclusive_inv(ex, v));
    //@ close exclusive_inv(ex,v)(empb,empb);  
    //@ init_mutex(m);
    //@ leak [_]mutex(m);    
    return ex;
}

void enter_cs(struct exclusive *ex)
  //@ requires [_]exclusive(ex,?v) &*& obs(?O) &*& w_level_below_all(v,O)== true;
  //@ ensures [_]exclusive(ex,v) &*& obs(cons(v,O));
{
  //@ open exclusive(ex,v);
  //@ assert [_]ex->m |-> ?m;
  //@ close mutex_inv(m,exclusive_inv(ex, v));
  //@ wait_level_lt_below_obs(wait_level_of(m), wait_level_of(v), O);  
  mutex_acquire(ex->m);
  //@ open exclusive_inv(ex, v)(_,_);
  //@ assert mutex_held(m,_,?Wt,?Ot);
  if (ex->b){
    ex->w++;
    //@ close exclusive_inv(ex,v)(finc(Wt,v),Ot);
    //@ close mutex_inv(m,exclusive_inv(ex, v));
    //@ close MP(v,no_transfer);
    //@ close M'P(v,cons(v,nil));    
    condvar_wait(ex->v, ex->m);
    //@ open exclusive_inv(ex,v)(_,_);   
    //@ open no_transfer();
  }  
  else{
    ex->b = true;  
    //@ g_chrgl(v);
  }
  //@ close mutex_inv(m,exclusive_inv(ex, v)); 
  //@ assert mutex_held(m,_,?Wte,?Ote);
  //@ close exclusive_inv(ex, v)(Wte,Ote);
  mutex_release(ex->m);
  //@ leak [_]mutex(m);    
}

void exit_cs(struct exclusive *ex)
  //@ requires [_]exclusive(ex,?v) &*& obs(cons(v,?O)) &*& wait_level_below_obs(pair({(exit_cs)}, 0r), cons(v,O)) == true;
  //@ ensures [_]exclusive(ex,v) &*& obs(O);
{
  //@ open exclusive(ex,v);
  //@ assert [_]ex->m |-> ?m;
  //@ close mutex_inv(m,exclusive_inv(ex, v));
  //@ wait_level_lt_below_obs(wait_level_of(m), pair({(exit_cs)}, 0r), O);
  mutex_acquire(ex->m);
  //@ open exclusive_inv(ex, v)(?Wt,?Ot); 
  ex->b = false;  
  if (ex->w > 0){
  //@ close MP(v,no_transfer); 
  //@ close M'P(v,cons(v,nil));   
  /*@ if (Wt(v)>0){
        close no_transfer();
      }
  @*/
  condvar_signal(ex->v);
  //@ minus_nil(cons(v,O));  
  ex->w --;
  ex->b = true;
  }
  else{
    //@ g_dischl(v);
  }
  //@ assert mutex_held(m,_,?Wte,?Ote);
  //@ close mutex_inv(m,exclusive_inv(ex, v)); 
  //@ close exclusive_inv(ex,v)(Wte,Ote);
  mutex_release(ex->m);
  //@ leak [_]mutex(m);
}
