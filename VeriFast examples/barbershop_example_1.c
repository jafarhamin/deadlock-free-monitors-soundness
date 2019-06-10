#include "stdlib.h"
#include "threads.h"
#include "barbershops.h"
  
/*@
predicate_family_instance thread_run_data(get_haircut_thread)(list<void*> tobs, struct barbershop *b) =
  [_]barber(b,?cbarber,?cchair,?cdoor,?ccustomer) &*& tobs == cons(cchair,cons(ccustomer,nil)) &*& creditba(b) &*& creditdo(b);
  
predicate_family_instance thread_run_data(finished_cut_customer_thread)(list<void*> tobs, struct barbershop *b) =
  [_]barber(b,?cbarber,?cchair,?cdoor,?ccustomer) &*& tobs == cons(cdoor,nil) &*& creditcu(b) &*& creditcu(b);

predicate_family_instance thread_run_data(get_next_customer_thread)(list<void*> tobs, struct barbershop *b) =
  [_]barber(b,?cbarber,?cchair,?cdoor,?ccustomer) &*& tobs == cons(cbarber,nil) &*& creditch(b);
@*/

void get_haircut_thread(struct barbershop *b)  //@ : thread_run
    //@ requires thread_run_data(get_haircut_thread)(?tobs,b) &*& obs(tobs);
    //@ ensures obs(nil);
{
  //@ open thread_run_data(get_haircut_thread)(_,_);
  get_haircut(b);
}

void finished_cut_customer_thread(struct barbershop *b)  //@ : thread_run
    //@ requires thread_run_data(finished_cut_customer_thread)(?tobs,b) &*& obs(tobs);
    //@ ensures obs(nil);
{
  //@ open thread_run_data(finished_cut_customer_thread)(_,_);
  finished_cut_customer(b);
  //@ leak creditcu(b);
}

void get_next_customer_thread(struct barbershop *b)  //@ : thread_run
    //@ requires thread_run_data(get_next_customer_thread)(?tobs,b) &*& obs(tobs);
    //@ ensures obs(nil);
{
  //@ open thread_run_data(get_next_customer_thread)(_,_);
  get_next_customer(b);
}

void main()
    //@ requires obs(nil);
    //@ ensures obs(nil);
{
    //@ close create_barber_ghost_args(pair({(main)}, 1r), pair({main}, 2r));
    struct barbershop *b = create_barber();   
    //@ leak barber(b, ?cbarber, ?cchair, ?cdoor, ?ccustomer);

    //@ loadcu(b);
    //@ loaddo(b);
    //@ loadch(b);
    //@ loadba(b);

    //@ close thread_run_data(get_haircut_thread)(cons(cchair,(cons(ccustomer,nil))),b);
    thread_start(get_haircut_thread, b);
    
    //@ close thread_run_data(get_next_customer_thread)(cons(cbarber,nil),b);
    thread_start(get_next_customer_thread, b);

    //@ close thread_run_data(finished_cut_customer_thread)(cons(cdoor,nil),b);
    thread_start(finished_cut_customer_thread, b);
}
