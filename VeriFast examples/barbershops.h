#include "stdlib.h"
#include "obligations.h"

struct barbershop;

/*@
predicate create_barber_ghost_args(pair<list<void*>, real> begin, pair<list<void*>, real> end) = true; 

predicate barber(struct barbershop* b, void *cbarber, void* cchair, void* cdoor, void* ccustomer);

predicate creditba(struct barbershop *b);
predicate creditch(struct barbershop *b);
predicate creditdo(struct barbershop *b);
predicate creditcu(struct barbershop *b);

lemma void loadba(struct barbershop *b);
  requires [?f]barber(b,?ba,?ch,?d,?cu) &*& obs(?O);
  ensures [f]barber(b,ba,ch,d,cu) &*& obs(cons(ba,O)) &*& creditba(b);

lemma void loadch(struct barbershop *b);
  requires [?f]barber(b,?ba,?ch,?d,?cu) &*& obs(?O);
  ensures [f]barber(b,ba,ch,d,cu) &*& obs(cons(ch,O)) &*& creditch(b);

lemma void loaddo(struct barbershop *b);
  requires [?f]barber(b,?ba,?ch,?d,?cu) &*& obs(?O);
  ensures [f]barber(b,ba,ch,d,cu) &*& obs(cons(d,O)) &*& creditdo(b);

lemma void loadcu(struct barbershop *b);
  requires [?f]barber(b,?ba,?ch,?d,?cu) &*& obs(?O);
  ensures [f]barber(b,ba,ch,d,cu) &*& obs(cons(cu,O)) &*& creditcu(b);
@*/

struct barbershop *create_barber();
  //@ requires create_barber_ghost_args(?start, ?end) &*& wait_level_lt(start,end) == true;
  /*@ ensures barber(result, ?cbarber, ?cchair, ?cdoor, ?ccustomer) &*& creditcu(result) &*& 
        wait_level_le(start, level(cbarber)) == true &*& wait_level_le(start, level(cdoor)) == true &*& 
        wait_level_le(start, level(cchair)) == true &*& wait_level_le(start, level(ccustomer)) == true &*& 
        wait_level_le(level(cbarber), end) == true &*& wait_level_le(level(cdoor), end) == true &*&         
        wait_level_le(level(cchair), end) == true &*& wait_level_le(level(ccustomer), end) == true; @*/

void get_haircut(struct barbershop *b);
  //@ requires [_]barber(b, ?cbarber, ?cchair, ?cdoor, ?ccustomer) &*& obs(cons(cchair,cons(ccustomer,?O))) &*& creditba(b) &*& creditdo(b) &*& wait_level_below_obs(level(cbarber), O) == true; 
  //@ ensures [_]barber(b, cbarber, cchair, cdoor, ccustomer) &*& obs(O);
  
void get_next_customer(struct barbershop *b);
  //@ requires [_]barber(b, ?cbarber, ?cchair, ?cdoor, ?ccustomer) &*& obs(cons(cbarber,?O)) &*& creditch(b) &*& wait_level_below_obs(level(cchair), O) == true;
  //@ ensures [_]barber(b, cbarber, cchair, cdoor, ccustomer) &*& obs(O);

void finished_cut_customer(struct barbershop *b);
  //@ requires [_]barber(b, ?cbarber, ?cchair, ?cdoor, ?ccustomer) &*& obs(cons(cdoor,?O)) &*& wait_level_below_obs(level(ccustomer), O) == true &*& creditcu(b) &*& creditcu(b);
  //@ ensures [_]barber(b, cbarber, cchair, cdoor, ccustomer) &*& obs(O) &*& creditcu(b);
