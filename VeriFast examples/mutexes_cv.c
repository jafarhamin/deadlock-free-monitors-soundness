#include "stdlib.h"
#include "monitors.h"
#include "mutexes_cv.h"
//@ #include "ghost_counters.gh"

struct exclusive{
   mutex m;
   cvar v;
   int n;
   //@ int gv;
};

/*@
predicate exclusive(struct exclusive *ex; void* v) =
  [_]ex->v |-> v &*& 
  [_]ex->m |-> ?m &*& 
  [_]mutex(m) &*&  
  [_]ex->gv |-> _ &*&
  mutex_of(v) == m &*&
  inv(m) == exclusive_inv(ex, v) &*&
  level'(m) == none &*&
  level(m) == pair({new_exclusive}, 0r) &*&
  wait_level_lt(level(m), level(v)) == true &*&  
  P(v)==true &*&
  level'(v) == some(level(v));
@*/

/*@
predicate_ctor creditor(struct exclusive *b)() = [_]b->gv |-> ?gv &*& tic(gv);

predicate_ctor exclusive_inv(struct exclusive *b, cvar v)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) = 
  [_]b->m |-> ?m &*& 
  b->n |-> ?n &*& 
  [_]b->v |-> v &*& 
  [_]b->gv |-> ?gv &*& 
  [_]cond(v,creditor(b),nil) &*&
  n >= 0 &*& 
  mutex_of(v)==m &*& 
  ctr(gv,?Cv) &*& 
  0 <= Ot(v) &*&  
  Wt(v) + Cv + n <= Ot(v) &*&
  (Wt(v) < 1 ? true : Wt(v) < Ot(v));
@*/

struct exclusive *new_exclusive()
  //@ requires exists(?v_wlevel) &*& wait_level_lt(pair({(new_exclusive)}, 0r), v_wlevel) == true;
  //@ ensures exclusive(result,?v) &*& level(v) == v_wlevel;
{
    //@ close create_mutex_ghost_args(pair({new_exclusive}, 0r));
    mutex m = create_mutex();
    
    //@ int gv = new_ctr();
    //@ close create_cvar_ghost_args(v_wlevel,true,some(v_wlevel));
    cvar v = create_cvar();
        
    struct exclusive *ex = malloc(sizeof(struct exclusive));
    if (ex==0) abort();

    //@ close init_cvar_ghost_args(m,creditor(ex),nil);
    //@ init_cvar(v);
        
    ex->m = m;
    ex->v = v;
    ex->n = 0;
    //@ ex->gv = gv;
    //@ leak [_]ex->v |-> _;
    //@ leak [_]ex->m |-> _;    
    //@ leak [_]ex->gv |-> _;
    //@ leak [_]malloc_block_exclusive(_);
    //@ leak [_]cond(v,_,_);
    //@ close init_mutex_ghost_args(exclusive_inv(ex, v));
    //@ close exclusive_inv(ex,v)(empb,empb);  
    //@ init_mutex(m);
    //@ leak [_]mutex(m);    
    //@ close exclusive(ex,v);
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
  //@ assert [_]ex->gv |-> ?gv;    
  //@ g_chrgl(v);
  //@ inc_ctr(gv);
  while (0 < ex->n)
  /*@ invariant [_]ex->m |-> m &*& 
                ex->n |-> ?n0 &*& 
                [_]ex->v |-> v &*& 
                [_]ex->gv |-> gv &*& 
                [_]cond(v,creditor(ex),nil) &*&
                n0 >= 0 &*& 
                mutex_held(m, _, ?Wt, ?Ot) &*&
                ctr(gv,?Cv) &*&
		0 <= Ot(v) &*&                
                Wt(v) + Cv + n0 <= Ot(v) &*&
                (Wt(v) < 1 || Wt(v) < Ot(v)) &*&
                obs(cons((void*)v,cons(m,O))) &*& tic(gv); @*/
  {
    //@ dec_ctr(gv);
    //@ close exclusive_inv(ex,v)(finc(Wt,v),Ot);
    //@ close mutex_inv(m,exclusive_inv(ex, v));
    /*@ produce_lemma_function_pointer_chunk spurious(exclusive_inv(ex,v), creditor(ex), v)() {
       open exclusive_inv(ex,v)(?Wt2,?Ot2);
       assert [_]ex->gv |-> ?g2;
       inc_ctr(g2);
       close exclusive_inv(ex,v)(fdec(Wt2,v),Ot2);
       close creditor(ex)();}; @*/
    //@ below_count(v,O);
    //@ count_same(v,O); 
    cvar_spwk_wait(ex->v, ex->m);
    //@ open exclusive_inv(ex,v)(_,_);   
    //@ open creditor(ex)();
  }  
  ex->n ++;
  //@ close mutex_inv(m,exclusive_inv(ex, v)); 
  //@ dec_ctr(gv);
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
  //@ assert [_]ex->gv |-> ?gv;      
  /*@ if (Wt(v)>0){
        inc_ctr(gv);
        close creditor(ex)();
      } @*/
  cvar_signal(ex->v);
  //@ minus_nil(cons(v,O));  
  //@ g_dischl(v);
  //@ close mutex_inv(m,exclusive_inv(ex, v)); 
  //@ assert mutex_held(m,_,?Wte,?Ote);
  //@ close exclusive_inv(ex,v)(Wte,Ote);
  mutex_release(ex->m);
  //@ leak [_]mutex(m);
}
