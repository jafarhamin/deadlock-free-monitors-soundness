#include "stdlib.h"
#include "monitors.h"
#include "barbershops.h"

//@ #include "ghost_counters.gh"

struct barbershop {
   int barber;
   int chair;
   int door;
   struct mutex *m;
   cvar cbarber;
   cvar cchair;
   cvar cdoor;
   cvar ccustomer;
   //@ int gba;
   //@ int gch;
   //@ int gdo;
   //@ int gcu;
};

/*@
predicate barber(struct barbershop *b, void *cbarber, void *cchair, void *cdoor, void *ccustomer) =
  [_]b->cbarber |-> cbarber &*& [_]b->cchair |-> cchair &*& [_]b->cdoor |-> cdoor &*& [_]b->ccustomer |-> ccustomer &*& [_]b->m |-> ?m  &*& [_]mutex(m) &*& 
  inv(m) == barbershop(b, cbarber, cchair, cdoor, ccustomer) &*& mutex_of(cbarber) == m &*& mutex_of(cchair) == m &*& mutex_of(cdoor) == m &*& mutex_of(ccustomer) == m &*&
  wait_level_lt(level(m), level(cbarber)) == true &*&
  wait_level_lt(level(cbarber), level(cchair)) == true &*&    
  wait_level_lt(level(cdoor), level(ccustomer)) == true &*&  
  level(cchair) == level(ccustomer) &*&    
  level(cbarber) == level(cdoor) &*&      
  level'(m) == none;

predicate creditba(struct barbershop *b) = [_]b->gba |-> ?gba  &*& tic(gba);
predicate creditch(struct barbershop *b) = [_]b->gch |-> ?gch  &*& tic(gch);
predicate creditdo(struct barbershop *b) = [_]b->gdo |-> ?gdo  &*& tic(gdo);
predicate creditcu(struct barbershop *b) = [_]b->gcu |-> ?gcu  &*& tic(gcu);

predicate_ctor creditorba(struct barbershop *b)() = [_]b->gba |-> ?gba  &*& tic(gba);
predicate_ctor creditorch(struct barbershop *b)() = [_]b->gch |-> ?gch  &*& tic(gch);
predicate_ctor creditordo(struct barbershop *b)() = [_]b->gdo |-> ?gdo  &*& tic(gdo);
predicate_ctor creditorcu(struct barbershop *b)() = [_]b->gcu |-> ?gcu  &*& tic(gcu);
@*/

/*@

predicate protected_permissions(struct barbershop *b; int barber, int chair, int door, cvar cbarber, cvar cchair, cvar cdoor, cvar ccustomer, struct mutex *m) =
  b->barber |-> barber &*& b->chair |-> chair &*& b->door |-> door
  &*& [_]b->cbarber |-> cbarber &*& [_]b->cchair |-> cchair &*& [_]b->cdoor |-> cdoor &*& [_]b->ccustomer |-> ccustomer &*& [_]b->m |-> m
  &*& mutex_of(cbarber) == m &*& mutex_of(cchair) == m &*& mutex_of(cdoor) == m &*& mutex_of(ccustomer) == m  
  &*& cbarber != cchair &*& cbarber != cdoor &*& cbarber != ccustomer &*& cchair != cdoor &*& cchair != ccustomer &*& cdoor != ccustomer
  &*& barber >= 0 &*& chair >= 0 &*& door >= 0;

predicate_ctor barbershop(struct barbershop *b, cvar cbarber, cvar cchair, cvar cdoor, cvar ccustomer)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) = 
  protected_permissions(b,?barber,?chair,?door,cbarber,cchair,cdoor,ccustomer,?m) 
  &*& [_]b->gba |-> ?gba &*& [_]b->gch |-> ?gch &*& [_]b->gdo |-> ?gdo &*& [_]b->gcu |-> ?gcu  
  &*& [_]cond(cbarber, creditorba(b), nil) &*& [_]cond(cchair, creditorch(b), nil) &*& [_]cond(cdoor, creditordo(b), nil) &*& [_]cond(ccustomer, creditorcu(b), nil) 
  &*& ctr(gba,?Cba) &*& ctr(gch,?Cch) &*& ctr(gdo,?Cdo) &*& ctr(gcu,?Ccu)
  &*& P(cbarber) == false && P(cchair) == false && P(cdoor) == false && P(ccustomer) == false
  &*& level'(cbarber) == none && level'(cchair) == none && level'(cdoor) == none && level'(ccustomer) == none  
  && Wt(cbarber) + Cba <= Ot(cbarber) + barber
  && Wt(cbarber) <= Ot(cbarber)
  && Wt(cdoor) + Cdo <= Ot(cdoor) + door
  && Wt(cdoor) <= Ot(cdoor)
  && Wt(cchair) + Cch <= Ot(cchair) + chair
  && Wt(cchair) <= Ot(cchair)
  && Wt(ccustomer) + Ccu + door <= Ot(ccustomer) + 1
  && Wt(ccustomer) <= Ot(ccustomer);
@*/

struct barbershop *create_barber()
  //@ requires create_barber_ghost_args(?start, ?end) &*& wait_level_lt(start,end) == true;
  /*@ ensures barber(result, ?cbarber, ?cchair, ?cdoor, ?ccustomer) &*& creditcu(result) &*& 
        wait_level_le(start, level(cbarber)) == true &*& wait_level_le(start, level(cdoor)) == true &*& 
        wait_level_le(start, level(cchair)) == true &*& wait_level_le(start, level(ccustomer)) == true &*& 
        wait_level_le(level(cbarber), end) == true &*& wait_level_le(level(cdoor), end) == true &*&         
        wait_level_le(level(cchair), end) == true &*& wait_level_le(level(ccustomer), end) == true; @*/
{
    //@ leak create_barber_ghost_args(_,_);
    //@ close create_mutex_ghost_args(start);
    struct mutex *m = create_mutex();
   
    //@ int gba = new_ctr();
    //@ wait_level_between(start,end);
    //@ leak exists(?ba_level);
    //@ close create_cvar_ghost_args(ba_level,false,none);
    cvar cbarber = create_cvar();
    
    //@ int gch = new_ctr();
    //@ close create_cvar_ghost_args(end,false,none);
    cvar cchair = create_cvar();
    //@ int gdo = new_ctr();
    //@ close create_cvar_ghost_args(ba_level,false,none);
    cvar cdoor = create_cvar();
    //@ int gcu = new_ctr();
    //@ close create_cvar_ghost_args(end,false,none);
    cvar ccustomer = create_cvar();
    
    struct barbershop *b = malloc(sizeof(struct barbershop));    
    if (b==0)  abort();
    
    //@ close init_cvar_ghost_args(m,creditorba(b),nil);
    //@ init_cvar(cbarber);
    //@ close init_cvar_ghost_args(m,creditorch(b),nil);
    //@ init_cvar(cchair);
    //@ close init_cvar_ghost_args(m,creditordo(b),nil);
    //@ init_cvar(cdoor);
    //@ close init_cvar_ghost_args(m,creditorcu(b),nil);
    //@ init_cvar(ccustomer);
      
    //@ if (cbarber == cchair || cbarber == cdoor || cbarber == ccustomer) cond_frac(cbarber);
    //@ if (cchair == cdoor || cchair == ccustomer) cond_frac(cchair);
    //@ if (cdoor == ccustomer) cond_frac(cdoor);
      
    b->m = m;
    b->barber = 0;
    b->chair = 0;
    b->door = 0;
    b->cbarber = cbarber;
    b->cchair = cchair;
    b->cdoor = cdoor;
    b->ccustomer = ccustomer;
    //@ b->gba = gba;
    //@ b->gch = gch;
    //@ b->gdo = gdo;
    //@ b->gcu = gcu;

    //@ leak [_]b->cbarber |-> _;
    //@ leak [_]b->cchair |-> _;
    //@ leak [_]b->cdoor |-> _;
    //@ leak [_]b->ccustomer |-> _;            
    //@ leak [_]b->m |-> _;  
    //@ leak [_]b->gba |-> _;               
    //@ leak [_]b->gch |-> _;               
    //@ leak [_]b->gdo |-> _;               
    //@ leak [_]b->gcu |-> _;  
    //@ leak [_]cond(cbarber,_,_);
    //@ leak [_]cond(cchair,_,_);
    //@ leak [_]cond(cdoor,_,_);
    //@ leak [_]cond(ccustomer,_,_);
    //@ leak [_]malloc_block_barbershop(_);
    
    //@ inc_ctr(gcu);
    //@ close barbershop(b, cbarber, cchair, cdoor, ccustomer)(empb,empb);
    //@ close init_mutex_ghost_args(barbershop(b, cbarber, cchair, cdoor, ccustomer));    
    //@ init_mutex(m);
    //@ leak [_]mutex(m);
    //@ close barber(b,_,_,_,_);
    //@ close creditcu(b);
    return b;
}

void get_haircut(struct barbershop *b)
  //@ requires [_]barber(b, ?cbarber, ?cchair, ?cdoor, ?ccustomer) &*& obs(cons(cchair,cons(ccustomer,?O))) &*& creditba(b) &*& creditdo(b) &*& wait_level_below_obs(level(cbarber), O) == true;
  //@ ensures [_]barber(b, cbarber, cchair, cdoor, ccustomer) &*& obs(O);
{
  //@ open barber(_,_,_,_,_);
  //@ assert [_]b->m |-> ?m;
  //@ close mutex_inv(m, barbershop(b, cbarber, cchair, cdoor, ccustomer));
  //@ wait_level_lt_below_obs(level(m), level(cbarber), O);  
  //@ wait_level_lt_trans(level(m), level(cbarber), level(cchair));      
  mutex_acquire(b->m);
  //@ open barbershop(b, cbarber, cchair, cdoor, ccustomer)(_,_);
  //@ assert [_]b->gba |-> ?gba &*& [_]b->gch |-> ?gch &*& [_]b->gdo |-> ?gdo &*& [_]b->gcu |-> ?gcu;
  //@ open creditba(b);
  //@ open creditdo(b);
  while (b->barber==0)
    /*@ invariant [_]b->cbarber |-> cbarber &*& [_]b->cchair |-> cchair &*& [_]b->cdoor |-> cdoor &*& [_]b->ccustomer |-> ccustomer
          &*& [_]b->m |-> m &*& b->barber |-> ?barber &*& b->chair |-> ?chair &*& b->door |-> ?door
          &*& barber >= 0 &*& chair >= 0 &*& door >= 0 &*& mutex_held(m, _, ?Wt, ?Ot)
          &*& [_]b->gba |-> gba &*& [_]b->gch |-> gch &*& [_]b->gdo |-> gdo &*& [_]b->gcu |-> gcu
	  &*& [_]cond(cbarber, creditorba(b), nil) &*& [_]cond(cchair, creditorch(b), nil) &*& [_]cond(cdoor, creditordo(b), nil) &*& [_]cond(ccustomer, creditorcu(b), nil) 
          &*& ctr(gba,?Cba) &*& ctr(gch,?Cch) &*& ctr(gdo,?Cdo) &*& ctr(gcu,?Ccu)
          &*& (P(cbarber) == false || (P(cbarber) == true && Wt(cbarber) + Cba < Ot(cbarber) + barber && (Wt(cbarber) == 0 || Wt(cbarber) < Ot(cbarber))))
          && (P(cchair) == false || (P(cchair) == true && Wt(cchair) + Cch < Ot(cchair) + chair && (Wt(cchair) == 0 || Wt(cchair) < Ot(cchair))))
          && (P(cdoor) == false || (P(cdoor) == true && Wt(cdoor) + Cdo < Ot(cdoor) + door && (Wt(cdoor) == 0 || Wt(cdoor) < Ot(cdoor))))
          && (P(ccustomer) == false || (P(ccustomer) == true && Wt(ccustomer) + Ccu + door < Ot(ccustomer) + 1 && (Wt(ccustomer) == 0 || Wt(ccustomer) < Ot(ccustomer))))
          && Wt(cbarber) + Cba <= Ot(cbarber) + barber
          && Wt(cbarber) <= Ot(cbarber)
          && Wt(cdoor) + Cdo <= Ot(cdoor) + door
          && Wt(cdoor) <= Ot(cdoor)
          && Wt(cchair) + Cch <= Ot(cchair) + chair
          && Wt(cchair) <= Ot(cchair)
          && Wt(ccustomer) + Ccu + door <= Ot(ccustomer) + 1
          && Wt(ccustomer) <= Ot(ccustomer)
          &*& obs(cons(m,cons((void*)cchair,cons(ccustomer,O)))) &*& tic(gba) &*& tic(gdo);
    @*/
  {
    //@ dec_ctr(gba);
    //@ close barbershop(b, cbarber, cchair, cdoor, ccustomer)(finc(Wt,cbarber),Ot);
    //@ close mutex_inv(m,barbershop(b, cbarber, cchair, cdoor, ccustomer));
    /*@ produce_lemma_function_pointer_chunk spurious(barbershop(b, cbarber, cchair, cdoor, ccustomer), creditorba(b), cbarber)() {
          open barbershop(b, cbarber, cchair, cdoor, ccustomer)(?Wt2,?Ot2);
          assert [_]b->gba |-> ?gba2;
          inc_ctr(gba2);
          close barbershop(b, cbarber, cchair, cdoor, ccustomer)(fdec(Wt2,cbarber),Ot2);
          close creditorba(b)();}; @*/
    cvar_spwk_wait(b->cbarber, b->m);
    //@ open barbershop(b, cbarber, cchair, cdoor, ccustomer)(_,_); 
    //@ open creditorba(b)();  
  }
  b->barber = b->barber - 1;
  b->chair = b->chair + 1;
  /*@ if (Wt(cchair)>0){
        inc_ctr(gch);
        close creditorch(b)();} @*/
  cvar_signal(b->cchair);
  //@ minus_nil(cons(cchair,cons(ccustomer,O)));
  //@ g_dischl(cchair);
  //@ dec_ctr(gba);
  
  //@ assert mutex_held(m,_,?Wte,?Ote);  
  //@ close barbershop(b, cbarber, cchair, cdoor, ccustomer)(Wte,Ote);
  //@ close mutex_inv(m, barbershop(b, cbarber, cchair, cdoor, ccustomer));
  mutex_release(b->m);
  //@ leak [_]mutex(m);
  get_haircut2(b);
  //@ leak [_]mutex(m);
}

void get_haircut2(struct barbershop *b)
  //@ requires [_]barber(b, ?cbarber, ?cchair, ?cdoor, ?ccustomer) &*& obs(cons(ccustomer,?O)) &*& [_]b->gdo |-> ?gdo &*& tic(gdo) &*& wait_level_below_obs(level(cbarber), O) == true;
  //@ ensures [_]barber(b, cbarber, cchair, cdoor, ccustomer) &*& obs(O);
{
  //@ open barber(_,_,_,_,_);
  //@ assert [_]b->m |-> ?m;  
  //@ close mutex_inv(m, barbershop(b, cbarber, cchair, cdoor, ccustomer));
  //@ wait_level_lt_trans(level(m), level(cbarber), level(ccustomer)); 
  //@ wait_level_lt_below_obs(level(m), level(cbarber), O);
  mutex_acquire(b->m);
  //@ open barbershop(b, cbarber, cchair, cdoor, ccustomer)(_,_);  
  //@ assert [_]b->gba |-> ?gba &*& [_]b->gch |-> ?gch &*& [_]b->gdo |-> gdo &*& [_]b->gcu |-> ?gcu; 
  
  while (b->door==0)
    /*@ invariant [_]b->cbarber |-> cbarber &*& [_]b->cchair |-> cchair &*& [_]b->cdoor |-> cdoor &*& [_]b->ccustomer |-> ccustomer
          &*& [_]b->m |-> m &*& b->barber |-> ?barber &*& b->chair |-> ?chair &*& b->door |-> ?door
          &*& barber >= 0 &*& chair >= 0 &*& door >= 0 &*& mutex_held(m, _, ?Wt, ?Ot)
          &*& [_]b->gba |-> gba &*& [_]b->gch |-> gch &*& [_]b->gdo |-> gdo &*& [_]b->gcu |-> gcu
	  &*& [_]cond(cbarber, creditorba(b), nil) &*& [_]cond(cchair, creditorch(b), nil) &*& [_]cond(cdoor, creditordo(b), nil) &*& [_]cond(ccustomer, creditorcu(b), nil) 
          &*& ctr(gba,?Cba) &*& ctr(gch,?Cch) &*& ctr(gdo,?Cdo) &*& ctr(gcu,?Ccu)
          &*& (P(cbarber) == false || (P(cbarber) == true && Wt(cbarber) + Cba < Ot(cbarber) + barber && (Wt(cbarber) == 0 || Wt(cbarber) < Ot(cbarber))))
          && (P(cchair) == false || (P(cchair) == true && Wt(cchair) + Cch < Ot(cchair) + chair && (Wt(cchair) == 0 || Wt(cchair) < Ot(cchair))))
          && (P(cdoor) == false || (P(cdoor) == true && Wt(cdoor) + Cdo < Ot(cdoor) + door && (Wt(cdoor) == 0 || Wt(cdoor) < Ot(cdoor))))
          && (P(ccustomer) == false || (P(ccustomer) == true && Wt(ccustomer) + Ccu + door < Ot(ccustomer) + 1 && (Wt(ccustomer) == 0 || Wt(ccustomer) < Ot(ccustomer))))
          && Wt(cbarber) + Cba <= Ot(cbarber) + barber
          && Wt(cbarber) <= Ot(cbarber)
          && Wt(cdoor) + Cdo <= Ot(cdoor) + door
          && Wt(cdoor) <= Ot(cdoor)
          && Wt(cchair) + Cch <= Ot(cchair) + chair
          && Wt(cchair) <= Ot(cchair)
          && Wt(ccustomer) + Ccu + door <= Ot(ccustomer) + 1
          && Wt(ccustomer) <= Ot(ccustomer)
          &*& obs(cons(m,cons((void*)ccustomer,O))) &*& tic(gdo);
    @*/
  {
    //@ dec_ctr(gdo);
    
    //@ close barbershop(b, cbarber, cchair, cdoor, ccustomer)(finc(Wt,cdoor),Ot);
    //@ close mutex_inv(m,barbershop(b, cbarber, cchair, cdoor, ccustomer));
    /*@ produce_lemma_function_pointer_chunk spurious(barbershop(b, cbarber, cchair, cdoor, ccustomer), creditordo(b), cdoor)() {
          open barbershop(b, cbarber, cchair, cdoor, ccustomer)(?Wt2,?Ot2);
          assert [_]b->gdo |-> ?gdo2;
          inc_ctr(gdo2);
          close barbershop(b, cbarber, cchair, cdoor, ccustomer)(fdec(Wt2,cdoor),Ot2);
          close creditordo(b)();}; @*/
          
    cvar_spwk_wait(b->cdoor, b->m);
    //@ open barbershop(b, cbarber, cchair, cdoor, ccustomer)(_,_);  
    //@ open creditordo(b)();
  }
  b->door = b->door - 1;
  /*@ if (Wt(ccustomer)>0){
        inc_ctr(gcu);
        close creditorcu(b)();} @*/
        
  cvar_signal(b->ccustomer);
  //@ minus_nil(cons(ccustomer,O));
  //@ g_dischl(ccustomer);
  //@ dec_ctr(gdo);
  //@ assert mutex_held(m,_,?Wte,?Ote);
  //@ close barbershop(b, cbarber, cchair, cdoor, ccustomer)(Wte,Ote);
  //@ close mutex_inv(m, barbershop(b, cbarber, cchair, cdoor, ccustomer));
  mutex_release(b->m);
  //@ leak [_]mutex(m);
}  

void get_next_customer(struct barbershop *b)
  //@ requires [_]barber(b, ?cbarber, ?cchair, ?cdoor, ?ccustomer) &*& obs(cons(cbarber,?O)) &*& creditch(b) &*& wait_level_below_obs(level(cchair), O) == true;
  //@ ensures [_]barber(b, cbarber, cchair, cdoor, ccustomer) &*& obs(O);
{
  //@ open barber(_,_,_,_,_);
  //@ assert [_]b->m |-> ?m;  
  //@ close mutex_inv(m, barbershop(b, cbarber, cchair, cdoor, ccustomer));
  //@ wait_level_lt_trans(level(m), level(cbarber), level(cchair)); 
  //@ wait_level_lt_below_obs(level(m), level(cchair), O);
  mutex_acquire(b->m);
  //@ open barbershop(b, cbarber, cchair, cdoor, ccustomer)(?Wt0,?Ot0);
  //@ assert [_]b->gba |-> ?gba &*& [_]b->gch |-> ?gch &*& [_]b->gdo |-> ?gdo &*& [_]b->gcu |-> ?gcu;
  if (b->barber <= 0)
    abort();
  b->barber = b->barber + 1;
  /*@ if (Wt0(cbarber)>0){
        inc_ctr(gba);
        close creditorba(b)();} @*/
  cvar_signal(b->cbarber);   
  //@ minus_nil(cons(cbarber,O));
  //@ g_dischl(cbarber);
  //@ open creditch(b);
  while (b->chair==0)
    /*@ invariant [_]b->cbarber |-> cbarber &*& [_]b->cchair |-> cchair &*& [_]b->cdoor |-> cdoor &*& [_]b->ccustomer |-> ccustomer
          &*& [_]b->m |-> m &*& b->barber |-> ?barber &*& b->chair |-> ?chair &*& b->door |-> ?door
          &*& barber >= 0 &*& chair >= 0 &*& door >= 0 &*& mutex_held(m, _, ?Wt, ?Ot)
          &*& [_]b->gba |-> gba &*& [_]b->gch |-> gch &*& [_]b->gdo |-> gdo &*& [_]b->gcu |-> gcu
	  &*& [_]cond(cbarber, creditorba(b), nil) &*& [_]cond(cchair, creditorch(b), nil) &*& [_]cond(cdoor, creditordo(b), nil) &*& [_]cond(ccustomer, creditorcu(b), nil) 
          &*& ctr(gba,?Cba) &*& ctr(gch,?Cch) &*& ctr(gdo,?Cdo) &*& ctr(gcu,?Ccu)
          &*& (P(cbarber) == false || (P(cbarber) == true && Wt(cbarber) + Cba < Ot(cbarber) + barber && (Wt(cbarber) == 0 || Wt(cbarber) < Ot(cbarber))))
          && (P(cchair) == false || (P(cchair) == true && Wt(cchair) + Cch < Ot(cchair) + chair && (Wt(cchair) == 0 || Wt(cchair) < Ot(cchair))))
          && (P(cdoor) == false || (P(cdoor) == true && Wt(cdoor) + Cdo < Ot(cdoor) + door && (Wt(cdoor) == 0 || Wt(cdoor) < Ot(cdoor))))
          && (P(ccustomer) == false || (P(ccustomer) == true && Wt(ccustomer) + Ccu + door < Ot(ccustomer) + 1 && (Wt(ccustomer) == 0 || Wt(ccustomer) < Ot(ccustomer))))        
          && Wt(cbarber) + Cba <= Ot(cbarber) + barber
          && Wt(cbarber) <= Ot(cbarber)
          && Wt(cdoor) + Cdo <= Ot(cdoor) + door
          && Wt(cdoor) <= Ot(cdoor)
          && Wt(cchair) + Cch <= Ot(cchair) + chair
          && Wt(cchair) <= Ot(cchair)
          && Wt(ccustomer) + Ccu + door <= Ot(ccustomer) + 1
          && Wt(ccustomer) <= Ot(ccustomer)
          &*& obs(cons(m,O)) &*& tic(gch);
    @*/
  {
    //@ dec_ctr(gch);
    //@ close barbershop(b, cbarber, cchair, cdoor, ccustomer)(finc(Wt,cchair),Ot);
    //@ close mutex_inv(m,barbershop(b, cbarber, cchair, cdoor, ccustomer));
    /*@ produce_lemma_function_pointer_chunk spurious(barbershop(b, cbarber, cchair, cdoor, ccustomer), creditorch(b), cchair)() {
          open barbershop(b, cbarber, cchair, cdoor, ccustomer)(?Wt2,?Ot2);
          assert [_]b->gch |-> ?gch2;
          inc_ctr(gch2);
          close barbershop(b, cbarber, cchair, cdoor, ccustomer)(fdec(Wt2,cchair),Ot2);
          close creditorch(b)();}; @*/
    cvar_spwk_wait(b->cchair, b->m);
    //@ open barbershop(b, cbarber, cchair, cdoor, ccustomer)(_,_);  
    //@ open creditorch(b)();
  }    
  b->chair = b->chair - 1;
  //@ dec_ctr(gch);
  //@ close barbershop(b, cbarber, cchair, cdoor, ccustomer)(Wt,Ot);
  //@ close mutex_inv(m, barbershop(b, cbarber, cchair, cdoor, ccustomer));
  mutex_release(b->m);
  //@ leak [_]mutex(m);  
}

void finished_cut_customer(struct barbershop *b)
  //@ requires [_]barber(b, ?cbarber, ?cchair, ?cdoor, ?ccustomer) &*& obs(cons(cdoor,?O)) &*& wait_level_below_obs(level(ccustomer), O) == true &*& creditcu(b) &*& creditcu(b);
  //@ ensures [_]barber(b, cbarber, cchair, cdoor, ccustomer) &*& obs(O) &*& creditcu(b);
{
  //@ open barber(_,_,_,_,_);
  //@ assert [_]b->m |-> ?m;  
  //@ close mutex_inv(m, barbershop(b, cbarber, cchair, cdoor, ccustomer));
  //@ wait_level_lt_trans(level(m), level(cbarber), level(ccustomer));  
  //@ wait_level_lt_below_obs(level(m), level(ccustomer), O);  
  mutex_acquire(b->m);
  //@ open barbershop(b, cbarber, cchair, cdoor, ccustomer)(?Wt0,?Ot0);
  //@ assert [_]b->gba |-> ?gba &*& [_]b->gch |-> ?gch &*& [_]b->gdo |-> ?gdo &*& [_]b->gcu |-> ?gcu;  
  b->door = b->door + 1;
  /*@ if (Wt0(cdoor)>0){
        inc_ctr(gdo);
        close creditordo(b)();} @*/
  cvar_signal(b->cdoor);
  //@ minus_nil(cons(cdoor,O));
  //@ open creditcu(b);  
  //@ g_dischl(cdoor);
  //@ dec_ctr(gcu);
  //@ open creditcu(b);
  while (b->door>0)
    /*@ invariant [_]b->cbarber |-> cbarber &*& [_]b->cchair |-> cchair &*& [_]b->cdoor |-> cdoor &*& [_]b->ccustomer |-> ccustomer
          &*& [_]b->m |-> m &*& b->barber |-> ?barber &*& b->chair |-> ?chair &*& b->door |-> ?door
          &*& barber >= 0 &*& chair >= 0 &*& door >= 0 &*& mutex_held(m, _, ?Wt, ?Ot)
          &*& [_]b->gba |-> gba &*& [_]b->gch |-> gch &*& [_]b->gdo |-> gdo &*& [_]b->gcu |-> gcu
	  &*& [_]cond(cbarber, creditorba(b), nil) &*& [_]cond(cchair, creditorch(b), nil) &*& [_]cond(cdoor, creditordo(b), nil) &*& [_]cond(ccustomer, creditorcu(b), nil) 
          &*& ctr(gba,?Cba) &*& ctr(gch,?Cch) &*& ctr(gdo,?Cdo) &*& ctr(gcu,?Ccu)
          &*& (P(cbarber) == false || (P(cbarber) == true && Wt(cbarber) + Cba < Ot(cbarber) + barber && (Wt(cbarber) == 0 || Wt(cbarber) < Ot(cbarber))))
          && (P(cchair) == false || (P(cchair) == true && Wt(cchair) + Cch < Ot(cchair) + chair && (Wt(cchair) == 0 || Wt(cchair) < Ot(cchair))))
          && (P(cdoor) == false || (P(cdoor) == true && Wt(cdoor) + Cdo < Ot(cdoor) + door && (Wt(cdoor) == 0 || Wt(cdoor) < Ot(cdoor))))
          && (P(ccustomer) == false || (P(ccustomer) == true && Wt(ccustomer) + Ccu + door < Ot(ccustomer) + 1 && (Wt(ccustomer) == 0 || Wt(ccustomer) < Ot(ccustomer))))
          && Wt(cbarber) + Cba <= Ot(cbarber) + barber
          && Wt(cbarber) <= Ot(cbarber)
          && Wt(cdoor) + Cdo <= Ot(cdoor) + door
          && Wt(cdoor) <= Ot(cdoor)
          && Wt(cchair) + Cch <= Ot(cchair) + chair
          && Wt(cchair) <= Ot(cchair)
          && Wt(ccustomer) + Ccu + door <= Ot(ccustomer) + 1
          && Wt(ccustomer) <= Ot(ccustomer)
          &*& obs(cons(m,O)) &*& tic(gcu);
    @*/
  {
    //@ dec_ctr(gcu);   
    //@ close barbershop(b, cbarber, cchair, cdoor, ccustomer)(finc(Wt,ccustomer),Ot);    
    //@ close mutex_inv(m,barbershop(b, cbarber, cchair, cdoor, ccustomer));
    /*@ produce_lemma_function_pointer_chunk spurious(barbershop(b, cbarber, cchair, cdoor, ccustomer), creditorcu(b), ccustomer)() {
       open barbershop(b, cbarber, cchair, cdoor, ccustomer)(?Wt2,?Ot2);
       assert [_]b->gcu |-> ?gcu2;
       inc_ctr(gcu2);
       close barbershop(b, cbarber, cchair, cdoor, ccustomer)(fdec(Wt2,ccustomer),Ot2);
       close creditorcu(b)();}; @*/
    cvar_spwk_wait(b->ccustomer, b->m);
    //@ open barbershop(b, cbarber, cchair, cdoor, ccustomer)(_,_); 
    //@ open creditorcu(b)(); 
  }
  //@ close barbershop(b, cbarber, cchair, cdoor, ccustomer)(Wt,Ot);
  //@ close mutex_inv(m, barbershop(b, cbarber, cchair, cdoor, ccustomer));
  mutex_release(b->m);
  //@ close creditcu(b);
  //@ leak [_]mutex(m);
}
