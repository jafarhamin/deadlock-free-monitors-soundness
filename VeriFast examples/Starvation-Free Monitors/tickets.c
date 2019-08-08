#include "tickets.h"
#include "stdlib.h"
#include "monitors.h"
//@ #include "ghost_counters.gh"

struct tvm{
   struct mutex *m;
   struct condvar *v;
   int active;
   int next;
   //@ int g;
   //@ int gp;   
};

/*@
predicate tvm(struct tvm* t; void* v, int g) =
  [_]t->v |-> v &*& 
  [_]t->m |-> ?m &*& 
  [_]mutex(m) &*&  
  [_]t->g |-> g &*&
  mutex_of(v) == m &*&
  inv(m) == tvm_inv(t, v) &*&
  level_of(m) < level_of(v);
@*/

/*@
predicate_ctor tvm_inv(struct tvm *t, struct condvar *v)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot, list< pair<void*,int> >It) = 
  t->active |-> ?active &*&
  t->next |-> ?next &*&
  [_]t->m |-> ?m &*& 
  [_]t->v |-> v &*& 
  [_]t->g |-> ?g &*& 
  [_]t->gp |-> ?gp &*&   
  [_]cond(v, ptictor(gp,0,1), cons(v,nil)) &*&
  mutex_of(v)==m &*& 
  ctr(g,?Tr) &*& 
  pctr(gp,active) &*&   
  0 <= Tr &*&
  0 <= Ot(v) &*&  
  active <= next &*&
  list_perm(It,waitings(nat_of_int(next-active-2), v, active+1)) == true &*&
  (active < next ? 0 < Ot(v) : true) &*&
  (next <= active + 1 ? Wt(v) <= 0 : true) &*&
  (active + 1 < next ? next - active - 1 <= Tr : true);

fixpoint bool list_perm<A>(list<A> l1, list<A> l2){
  return subset(l1,l2) && subset(l2,l1);
}

fixpoint list< pair<void*, int> > waitings(nat n, void* v, int start){
  switch (n){
    case zero: return nil;
    case succ(n'): return cons(pair(v,start),waitings(n', v, start+1));
  }
}
  
predicate_ctor ptictor(int gp, int u, int p)() = ptic(gp, u, p);

lemma void pticpublishable(int gp, int u, int p);
  requires true;
  ensures publishable(ptictor(gp,u,p), ptictor(gp,0,u));    
@*/

struct tvm *new_tvm()
  //@ requires exists<real>(?v_wlevel);
  //@ ensures tvm(result,?v,?g) &*& level_of(v) == v_wlevel;
{
    //@ close create_mutex_ghost_args(v_wlevel-1);
    struct mutex *m = create_mutex();
    
    //@ int g = new_ctr();
    //@ int gp = new_pctr();        
    //@ close create_condvar_ghost_args(v_wlevel);
    struct condvar *v = create_condvar();
    //@ close init_condvar_ghost_args(m,ptictor(gp,0,1),cons(v,nil));
    //@ init_condvar(v);
        
    struct tvm *t = malloc(sizeof(struct tvm));
    if (t==0)
      abort();
    t->active = 0;
    t->next = 0;
    t->m = m;
    t->v = v;
    //@ t->g = g;
    //@ t->gp = gp;
    //@ leak [_]t->v |-> _;
    //@ leak [_]t->m |-> _;    
    //@ leak [_]t->g |-> _;
    //@ leak [_]t->gp |-> _;    
    //@ leak [_]malloc_block_tvm(_);
    //@ leak [_]cond(v,_,_);
    //@ close init_mutex_ghost_args(tvm_inv(t, v));
    //@ assume (nat_of_int(-2) == zero);
    //@ close tvm_inv(t,v)(empb,empb,nil);  
    //@ init_mutex(m);
    //@ leak [_]mutex(m);    
    //@ close tvm(t,v,g);
    return t;
}

void enter_tvm(struct tvm* t)
  //@ requires [_]tvm(t,?v,?g) &*& obs(?O) &*& object_lt_objects(v,O)== true;
  //@ ensures [_]tvm(t,v,g) &*& obs(cons(v,O)) &*& tic(g);
{
  //@ open tvm(t,v,g);
  //@ assert [_]t->m |-> ?m;
  //@ close mutex_inv(m,tvm_inv(t, v));
  //@ wait_level_lt_below_obs(level_of(m), level_of(v), O);  
  mutex_acquire(t->m);
  //@ open tvm_inv(t, v)(?Wt0, ?Ot0, ?It0);
  
  int mine = t->next ++;
  //@ inc_ctr(g);
  //@ if (t->next == t->active + 1) g_chrgl(v);
  //@ assert [_]t->gp |-> ?gp;
  //@ inc_pctr(gp);
  //@ dec_pctr(gp);
  //@ assume (nat_of_int(-1) == zero);
  while (t->active < mine)  
  /*@ invariant t->active |-> ?active &*&
		t->next |-> ?next &*&
		[_]t->m |-> m &*& 
                [_]t->v |-> v &*& 
                [_]t->g |-> g &*& 
                [_]t->gp |-> gp &*&                 
                [_]cond(v,ptictor(gp,0,1),cons(v,nil)) &*&
                mutex_held(m, _, ?Wt, ?Ot, ?It) &*&
                ctr(g,?Tr) &*&
                pctr(gp,active) &*&                
		0 <= Tr &*&
		0 <= Ot(v) &*&  
		active <= next &*&  
                list_perm (It, append(waitings(nat_of_int(mine-active-2), v, active+1), waitings(nat_of_int(next-mine-2), v, mine+1))) == true &*&
		mine < next &*&
		ptic(gp,0,?minactive) &*&	
		(active < next ? 0 < Ot(v) : true) &*&		
		(next <= active + 1 ? Wt(v) <= 0 : true) &*&
		(active + 1 < next ? next - active - 1 <= Tr : true) &*&				
		active >= mine ? obs(cons(v,cons(m,O))) : obs(cons(m,O)) ;
  @*/
  //@ decreases mine - minactive;
  {
    //@ assume (subset(cons(pair(v,mine),It), waitings(nat_of_int(next-active-2), v, active+1)));    
    //@ assume (subset(waitings(nat_of_int(next-active-2), v, active+1), cons(pair(v,mine),It)));
    /* Proof
    //@ assert list_perm (It, append(waitings(nat_of_int(mine-active-2), v, active+1), waitings(nat_of_int(next-mine-2), v, mine+1))) == true; */
    
    //@ min_pctr(gp);
    
    //@ close tvm_inv(t,v)(finc(Wt,v),Ot,cons(pair(v,mine),It));
    //@ close mutex_inv(m,tvm_inv(t, v));
    //@ close Id(mine);
    condvar_wait(t->v, t->m);
    //@ open tvm_inv(t,v)(?Wt',?Ot',?It');       
    //@ assert mutex_held(m, _, Wt', Ot', ?It'');
    //@ open ptictor(gp,0,1)();
    //@ assert t->active |-> ?active1;
    //@ assert t->next |-> ?next1;    
    
    //@ assume(next <= next1);
    // Proof: with the help of a ghost monotonic counter

    //@ assume (list_perm(It'', append(waitings(nat_of_int(mine-active1-2), v, active1+1), waitings(nat_of_int(next1-mine-2), v, mine+1))));
    /* Proof:
    //@ assert It'' == remove(pair(v,mine),It') || (It'' == It' && mem(pair(v,mine), It'') == false);
    //@ assume (list_perm(It'', remove(pair(v,mine),It')));
    //@ assert list_perm(It',waitings(nat_of_int(next1-active1-2), v, active1+1)) == true;
    /*@ assume (list_perm(remove(pair(v,mine),waitings(nat_of_int(next1-active1-2), v, active1+1)), 
                append(waitings(nat_of_int(mine-active1-2), v, active1+1), waitings(nat_of_int(next1-mine-2), v, mine+1)))); @*/
                
    //@ assume (mine <= active1 ? mem(pair(v,mine), It') == false : mem(pair(v,mine), It') == true);
    /* Proof: 
    //@ assert list_perm(It',waitings(nat_of_int(next1-active1-2), v, active1+1)) == true;
    //@ assert mine < next1; */
    
    //@ merge_ptic(gp,0,minactive,0,1);
  }  
  //@ close mutex_inv(m,tvm_inv(t, v)); 
  //@ assert mutex_held(m,_,?Wte,?Ote,?Ite);

  //@ assume (list_perm(Ite, waitings(nat_of_int(next-active-2), v, active+1)));  
  /* Proof:
  //@ assert list_perm (Ite, append(waitings(nat_of_int(mine-active-2), v, active+1), waitings(nat_of_int(next-mine-2), v, mine+1))) == true;
  //@ assume (list_perm(append(waitings(nat_of_int(mine-active-2), v, active+1), waitings(nat_of_int(next-mine-2), v, mine+1)), waitings(nat_of_int(next-active-2), v, active+1)));  
  */

  //@ close tvm_inv(t, v)(Wte,Ote,Ite);
  mutex_release(t->m);
  //@ leak [_]mutex(m);   
  //@ leak ptic(gp,_,_);
}

void exit_tvm(struct tvm* t)
  //@ requires [_]tvm(t,?v,?g) &*& obs(cons(v,?O)) &*& tic(g) &*& object_lt_objects(v,O)== true;
  //@ ensures [_]tvm(t,v,g) &*& obs(O);
{
  //@ open tvm(t,v,g);
  //@ assert [_]t->m |-> ?m;
  //@ close mutex_inv(m,tvm_inv(t, v));
  //@ wait_level_lt_below_obs(level_of(m), level_of(v), O);    
  mutex_acquire(t->m);
  //@ open tvm_inv(t, v)(?Wt,?Ot,?It); 
  //@ assert [_]t->gp |-> ?gp;  
  //@ assert [_]t->active |-> ?active;  

 if (t->active >= t->next) abort();
  
  //@ assert list_perm(It, waitings(nat_of_int(t->next - active - 2), v, active + 1)) == true;  
  t->active ++;
  //
  /*@
    if (t->next == t->active){
      g_dischl(v);
      assume (mem(pair(v,t->active),It) == false);      
    }
    else{
      assert t->active < t->next;
      assume (mem(pair(v,t->active),It));      
    }
  @*/
  
  //@ close Id(t->active);
  //@ pticpublishable(gp, 1, 0);
  //@ inc_pctr(gp);
  //@ close ptictor(gp,1,0)();
  condvar_broadcast(t->v);
  //@ minus_nil(cons(v,O));
  //@ dec_ctr(g);
  //@ close mutex_inv(m,tvm_inv(t, v)); 
  //@ assert mutex_held(m,_,?Wte,?Ote,?Ite);
  
  //@ assume (list_perm(remove(pair(v,t->active),It), waitings(nat_of_int(t->next - t->active - 2), v, t->active + 1)));
  /* Proof:
  //@ assert list_perm(It, waitings(nat_of_int(t->next - active - 2), v, active + 1)) == true;    
  //@ assert active == t->active - 1;
  //@ assume (list_perm(It, waitings(nat_of_int(t->next - t->active - 3), v, t->active)))*/
  
  //@ close tvm_inv(t,v)(Wte,Ote,Ite);
  mutex_release(t->m);
  //@ leak [_]mutex(m);
}
