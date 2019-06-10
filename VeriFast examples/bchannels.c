#include "stdlib.h"
#include "monitors.h"
#include "queues.h"
#include "bchannels.h"
//@ #include "ghost_counters.gh"

struct channel{
   struct queue *q;
   struct mutex *m;
   cvar ve;
   cvar vf;
   int max;
   //@ int ge;
   //@ int gf;
};

/*@
predicate channel(struct channel *ch; void* ve, void* vf) =
  [_]ch->ve |-> ve &*& 
  [_]ch->vf |-> vf &*& 
  [_]ch->m |-> ?m &*& 
  [_]mutex(m) &*&  
  [_]ch->ge |-> _ &*&
  [_]ch->gf |-> _ &*&
  mutex_of(ve) == m &*&
  mutex_of(vf) == m &*&
  inv(m) == channel_inv(ch, ve, vf) &*&
  level'(m) == none &*&
  level(m) == pair({create_channel}, 0r) &*&
  ve != vf &*&
  P(vf)==true &*&
  wait_level_lt(level(ve), level(vf)) == true;
  
predicate credite(channel ch) = [_]ch->ge |-> ?ge  &*& tic(ge);
predicate creditf(channel ch) = [_]ch->gf |-> ?gf  &*& tic(gf);
predicate_ctor creditore(channel ch)() = credite(ch);
predicate_ctor creditorf(channel ch)() = creditf(ch);
predicate_ctor vtrn(int gid)() = tic(gid);
 
lemma void loade(struct channel *ch)
  requires [?f]channel(ch,?ve,?vf) &*& obs(?O);
  ensures [f]channel(ch,ve,vf) &*& obs(cons(ve,O)) &*& credite(ch);  
{
  assume(false);
}
   
lemma void loadf(struct channel *ch)
  requires [?f]channel(ch,?ve,?vf) &*& obs(?O);
  ensures [f]channel(ch,ve,vf) &*& obs(cons(vf,O)) &*& creditf(ch);  
{
  assume(false);
}
@*/

/*@
predicate_ctor channel_inv(channel ch, cvar ve, cvar vf)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) = 
  ch->q |-> ?q &*& 
  [_]ch->max |-> ?max &*& 
  [_]ch->ve |-> ve &*& 
  [_]ch->vf |-> vf &*& 
  [_]ch->ge |-> ?ge &*& 
  [_]ch->gf |-> ?gf &*& 
  [_]cond(ve,creditore(ch),nil) &*&
  [_]cond(vf,creditorf(ch),nil) &*&
  queue(q,?s) &*& 
  s >= 0 &*& 
  [_]ch->m |-> ?m &*& 
  mutex_of(ve)==m &*& 
  mutex_of(vf)==m &*&
  ctr(ge,?Ce) &*& 
  ctr(gf,?Cf) &*&
  (P(ve) == false || (Wt(ve) + Ce < Ot(ve) + s && (Wt(ve) == 0 || Wt(ve) < Ot(ve)))) &&                  
  Wt(ve) + Ce <= Ot(ve) + s &*&
  Wt(ve) <= Ot(ve) &*&
  Wt(vf) + Cf + s < Ot(vf) + max &*&
  (Wt(vf) == 0 ? true : Wt(vf) < Ot(vf));
  
lemma void inc_ctr'(nat m, int id)
  requires ctr(id,?n);
  ensures ctr(id,n+int_of_nat(m)) &*& n_times(int_of_nat(m),vtrn(id));
{
  switch (m){
    case zero: close n_times(int_of_nat(m),vtrn(id));
    case succ(m0): inc_ctr(id); inc_ctr'(m0, id); close vtrn(id)(); close n_times(int_of_nat(m),vtrn(id));
  }
}

lemma void tics_creditors(nat n, struct channel *ch)
  requires [_]ch->gf |-> ?gf &*& n_times(int_of_nat(n),vtrn(gf));// &*& [_]cond(?v,gid);
  ensures [_]ch->gf |-> gf &*& n_times(int_of_nat(n),creditorf(ch));
{
  switch (n) {
    case zero: open n_times(int_of_nat(n),vtrn(gf)); close n_times(int_of_nat(n),creditorf(ch));
    case succ(n0): open n_times(int_of_nat(n),vtrn(gf)); tics_creditors(n0,ch); open vtrn(gf)(); close creditf(ch); close creditorf(ch)(); close n_times(int_of_nat(n),creditorf(ch));
  }  
}

lemma void creditor_credits(nat n, struct channel *ch)
  requires n_times(int_of_nat(n),creditorf(ch));
  ensures creditsf(int_of_nat(n),ch);
{
  open n_times(int_of_nat(n),creditorf(ch));
  switch (n) {
    case zero:
    case succ(n0): creditor_credits(n0,ch); open creditorf(ch)(); //close creditf(ch); //open credits(int_of_nat(n0),v);
  }  
  close creditsf(int_of_nat(n),ch);
}

lemma void tics_credits(nat n, struct channel *ch)
  requires [_]ch->gf |-> ?gf &*& n_times(int_of_nat(n),vtrn(gf));
  ensures creditsf(int_of_nat(n),ch);
{
  tics_creditors(n,ch);
  creditor_credits(n,ch);
}  
@*/

struct channel *create_channel(int max)
    /*@ requires obs(nil) &*& create_channel_ghost_args(?ve_wlevel, ?ve_X, ?ve_P, ?vf_wlevel, ?vf_X) &*&
          wait_level_lt(ve_wlevel, vf_wlevel) == true &*& 0 < max; @*/
    /*@ ensures channel(result,?ve,?vf) &*& obs(cons_bool(ve_P,nil,ve)) &*& creditsf(max-1,result) &*& 
          level(ve) == ve_wlevel &*& level'(ve) == some(ve_X) &*& P(ve) == ve_P &*&
          level(vf) == vf_wlevel &*& level'(vf) == some(vf_X) &*& P(vf) == true; @*/
{
    //@ leak create_channel_ghost_args(ve_wlevel, ve_X, ve_P, vf_wlevel, vf_X);
    struct queue *q = create_queue();
    
    //@ close create_mutex_ghost_args(pair({create_channel}, 0r));
    struct mutex *m = create_mutex();
    
    //@ int ge = new_ctr();
    //@ close create_cvar_ghost_args(ve_wlevel,ve_P,some(ve_X));
    cvar ve = create_cvar();
        
    //@ int gf = new_ctr();
    //@ close create_cvar_ghost_args(vf_wlevel,true,some(vf_X));
    cvar vf = create_cvar();
        
    struct channel *ch = malloc(sizeof(struct channel));
    if (ch==0) abort();
    
    //@ close init_cvar_ghost_args(m,creditore(ch),nil);
    //@ init_cvar(ve);
    //@ close init_cvar_ghost_args(m,creditorf(ch),nil);
    //@ init_cvar(vf);
    
    //@ if (ve == vf) cond_frac(ve);
    
    ch->q = q;
    ch->m = m;
    ch->ve = ve;
    ch->vf = vf;
    ch->max = max;
    //@ ch->ge = ge;
    //@ ch->gf = gf;
    //@ leak [_]ch->ve |-> _;
    //@ leak [_]ch->vf |-> _;     
    //@ leak [_]ch->m |-> _;    
    //@ leak [_]ch->max |-> _;
    //@ leak [_]ch->ge |-> _;
    //@ leak [_]ch->gf |-> _;    
    //@ leak [_]malloc_block_channel(_);
    //@ leak [_]cond(ve,creditore(ch),nil);
    //@ leak [_]cond(vf,creditorf(ch),nil);
    
    //@ inc_ctr'(nat_of_int(max-1),gf);        
    //@ tics_credits(nat_of_int(max-1),ch);
    //@ if (ve_P) g_chrgu(ve);    
    //@ close init_mutex_ghost_args(channel_inv(ch, ve, vf));
    //@ close channel_inv(ch, ve, vf)(empb,finc_bool(ve_P,empb,ve));  
    //@ init_mutex(m);
    //@ leak [_]mutex(m);
    //@ close channel(ch,ve,vf);
    return ch;
}

void receive(struct channel *ch)
  //@ requires [_]channel(ch,?ve,?vf) &*& obs(?O) &*& credite(ch) &*& no_cycle(ve,O) == true &*& wait_level_below_obs(pair({(receive)}, 0r), O) == true;
  //@ ensures [_]channel(ch,ve,vf) &*& obs(remove(vf,O));
{
  //@ open channel(ch,ve,vf);
  //@ assert [_]ch->m |-> ?m;
  //@ close mutex_inv(m,channel_inv(ch, ve, vf));
  //@ wait_level_lt_below_obs(level(m), pair({(receive)}, 0r), O);
  mutex_acquire(ch->m);
  //@ open channel_inv(ch, ve, vf)(_,_);
  //@ assert [_]ch->ge |-> ?ge &*& [_]ch->gf |-> ?gf;
  while (size_of(ch->q)==0)
  /*@ invariant [_]ch->m |-> m &*& 
                [_]ch->max |-> ?max &*& 
                [_]ch->ve |-> ve &*& 
                [_]ch->vf |-> vf &*&  
		[_]ch->ge |-> ge &*&
		[_]ch->gf |-> gf &*&               
		[_]cond(ve,creditore(ch),nil) &*&
		[_]cond(vf,creditorf(ch),nil) &*&		
                ch->q |-> ?q &*& 
                queue(q,?s) &*& 
                s>=0 &*& 
                mutex_held(m, _, ?Wt, ?Ot) &*& 
                ctr(gf,?Cf) &*& 
                ctr(ge,?Ce) &*&
                Wt(ve) + Ce <= Ot(ve) + s &*&
                Wt(ve) <= Ot(ve) &*&
                (P(ve) == false || (Wt(ve) + Ce < Ot(ve) + s && (Wt(ve) == 0 || Wt(ve) < Ot(ve)))) &&                
                Wt(vf) + Cf + s < Ot(vf) + max &*&
                (Wt(vf) == 0 ? true : Wt(vf) < Ot(vf)) &*&
                obs(cons(m,O)) &*& 
                credite(ch); @*/
  {
    //@ open credite(ch);  
    //@ dec_ctr(ge);
    //@ close channel_inv(ch, ve, vf)(finc(Wt,ve),Ot);
    //@ close mutex_inv(m,channel_inv(ch, ve, vf));  
    /*@ produce_lemma_function_pointer_chunk spurious(channel_inv(ch,ve,vf), creditore(ch), ve)() {
          open channel_inv(ch,ve,vf)(?Wt2,?Ot2);
          assert [_]ch->ge |-> ?ge2;
          inc_ctr(ge2);
          close channel_inv(ch,ve,vf)(fdec(Wt2,ve),Ot2);
          close credite(ch);
          close creditore(ch)();}; @*/
    cvar_spwk_wait(ch->ve, ch->m);
    //@ open channel_inv(ch, ve, vf)(_,_);  
    //@ open creditore(ch)();
  }
  dequeue(ch->q);
  /*@ if (Wt(vf)>0){
        inc_ctr(gf);
        close creditf(ch);
        close creditorf(ch)();
      }
  @*/
  cvar_signal(ch->vf); 
  //@ minus_nil(cons(vf,O));
  //@ g_Ot_isbag(m,vf);
  //@ g_dischl(vf); 
  //@ open credite(ch);     
  //@ dec_ctr(ge); 
  //@ assert mutex_held(m,_,?Wte,?Ote);
  //@ close channel_inv(ch, ve, vf)(Wte,Ote);
  //@ close mutex_inv(m,channel_inv(ch, ve, vf));
  mutex_release(ch->m);
  //@ leak [_]mutex(m);
}

void send(struct channel *ch)
  //@ requires [_]channel(ch,?ve,?vf) &*& obs(?O) &*& creditf(ch) &*& no_cycle(vf,O)== true &*& wait_level_below_obs(pair({(send)}, 0r), cons(ve,O)) == true;
  //@ ensures [_]channel(ch,ve,vf) &*& obs(remove(ve,O));
{
  //@ open channel(ch,ve,vf);
  //@ assert [_]ch->m |-> ?m;
  //@ close mutex_inv(m,channel_inv(ch, ve, vf));
  //@ wait_level_lt_below_obs(level(m), pair({(send)}, 0r), cons(ve,O));
  mutex_acquire(ch->m);
  //@ open channel_inv(ch, ve, vf)(_,_);
  int maximum = ch->max;
  //@ assert [_]ch->ge |-> ?ge &*& [_]ch->gf |-> ?gf;    
  while (size_of(ch->q) == maximum)
  /*@ invariant [_]ch->m |-> m &*& 
                [_]ch->max |-> ?max &*& 
                maximum == max &*& 
                [_]ch->ve |-> ve &*& 
                [_]ch->vf |-> vf &*& 
                [_]ch->ge |-> ge &*& 
                [_]ch->gf |-> gf &*& 
		[_]cond(ve,creditore(ch),nil) &*&
		[_]cond(vf,creditorf(ch),nil) &*&		
                ch->q |-> ?q &*& 
                queue(q,?s) &*& 
                s>=0 &*& 
                mutex_held(m, _, ?Wt, ?Ot) &*&
                ctr(gf,?Cf) &*& ctr(ge,?Ce) &*&
                (P(ve) == false || (P(ve) == true && (Wt(ve) + Ce < Ot(ve) + s && (Wt(ve) == 0 || Wt(ve) < Ot(ve))))) &&                                
                Wt(ve) + Ce <= Ot(ve) + s &*&
                Wt(ve) <= Ot(ve) &*&
                Wt(vf) + Cf + s < Ot(vf) + max &*&
                (max == s || Wt(vf) == 0 ? true : Wt(vf) < Ot(vf)) &*&
                obs(cons(m,O)) &*& creditf(ch); @*/
  {
    //@ open creditf(ch);  
    //@ dec_ctr(gf);
    //@ close channel_inv(ch,ve,vf)(finc(Wt,vf),Ot);
    //@ close mutex_inv(m,channel_inv(ch, ve, vf));
    
    /*@ produce_lemma_function_pointer_chunk spurious(channel_inv(ch,ve,vf), creditorf(ch), vf)() {
          open channel_inv(ch,ve,vf)(?Wt2,?Ot2);
          assert [_]ch->gf |-> ?gf2;
          inc_ctr(gf2);
          close channel_inv(ch,ve,vf)(fdec(Wt2,vf),Ot2);
          close creditf(ch);
          close creditorf(ch)();}; @*/
    cvar_spwk_wait(ch->vf, ch->m);
    //@ open channel_inv(ch,ve,vf)(_,_);   
    //@ assert mutex_held(m,_,?Wt11,?Ot11);
    //@ open creditorf(ch)();
  }  
  //@ assert mutex_held(m,_,?Wt1,?Ot1);
  enqueue(ch->q,12);
  /*@ if (Wt(ve)>0){
        inc_ctr(ge);
        close credite(ch);
        close creditore(ch)();} @*/
  cvar_signal(ch->ve);
  //@ minus_nil(cons(ve,O));
  //@ g_dischl(ve);
  //@ close mutex_inv(m,channel_inv(ch, ve, vf)); 
  //@ open creditf(ch);    
  //@ dec_ctr(gf);
  //@ assert mutex_held(m,_,?Wte,?Ote);
  //@ close channel_inv(ch, ve, vf)(Wte,Ote);
  mutex_release(ch->m);
  //@ leak [_]mutex(m);    
}
