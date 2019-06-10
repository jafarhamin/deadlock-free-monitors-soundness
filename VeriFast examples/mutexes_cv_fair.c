#include "stdlib.h"
#include "monitors.h"
#include "mutexes_cv.h"
//@ #include "ghost_counters.gh"

struct exclusive{
   mutex m;
   cvar v;
   int n;
   int w;
};

/*@
predicate exclusive(struct exclusive *ex; void* v) =
  [_]ex->v |-> v &*& 
  [_]ex->m |-> ?m &*& 
  [_]mutex(m) &*&  
  mutex_of(v) == m &*&
  inv(m) == exclusive_inv(ex, v) &*&
  level'(m) == none &*&
  level(m) == pair({new_exclusive}, 0r) &*&
  wait_level_lt(level(m), level(v)) == true &*&  
  P(v) == false &*&
  level'(v) == none;
@*/

/*@
predicate_ctor exclusive_inv(struct exclusive *b, cvar v)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) = 
  [_]b->m |-> ?m &*& 
  b->n |-> ?n &*& 
  b->w |-> Wt(v) &*&   
  [_]b->v |-> v &*& 
  [_]cond(v,nothing,cons(v,nil)) &*&
  n >= 0 &*& 
  Wt(v) >= 0 &*&   
  mutex_of(v)==m &*& 
  0 <= Ot(v) &*&  
  n <= Ot(v) &*&
  (Wt(v) <= 0 ? true : 0 < n);
  
predicate_ctor vtrn(int i)() = tic(i);
@*/

struct exclusive *new_exclusive()
  //@ requires exists(?v_wlevel) &*& wait_level_lt(pair({(new_exclusive)}, 0r), v_wlevel) == true;
  //@ ensures exclusive(result,?v) &*& level(v) == v_wlevel;
{
    //@ close create_mutex_ghost_args(pair({new_exclusive}, 0r));
    struct mutex *m = create_mutex();
    
    //@ open exists(v_wlevel);
    //@ close create_cvar_ghost_args(v_wlevel,false,none);
    cvar v = create_cvar();
    //@ close init_cvar_ghost_args(m,nothing,cons(v,nil));
    //@ init_cvar(v);
        
    struct exclusive *ex = malloc(sizeof(struct exclusive));
    if (ex==0)
      abort();
    ex->m = m;
    ex->w = 0;    
    ex->v = v;
    ex->n = 0;
    //@ leak [_]ex->v |-> _;
    //@ leak [_]ex->m |-> _;    
    //@ leak [_]malloc_block_exclusive(_);
    //@ leak [_]cond(v,_,_);
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
  //@ wait_level_lt_below_obs(level(m), level(v), O);  
  mutex_acquire(ex->m);
  //@ open exclusive_inv(ex, v)(_,_);
  //@ assert mutex_held(m,_,?Wt,?Ot);
  if (0 < ex->n){
    ex->w++;
    //@ close exclusive_inv(ex,v)(finc(Wt,v),Ot);
    //@ close mutex_inv(m,exclusive_inv(ex, v));
    cvar_wait(ex->v, ex->m);
    //@ open exclusive_inv(ex,v)(_,_);   
    //@ open nothing();
  }  
  else{
    ex->n ++;  
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
  //@ wait_level_lt_below_obs(level(m), pair({(exit_cs)}, 0r), O);
  mutex_acquire(ex->m);
  //@ open exclusive_inv(ex, v)(?Wt,?Ot); 
  if (ex->n <= 0) abort(); 
  ex->n --;  
  if (ex->w > 0){
  /*@ if (Wt(v)>0){
        close nothing();
      } @*/
  cvar_signal(ex->v);
  //@ minus_nil(cons(v,O));  
  ex->w --;
  ex->n ++;
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
