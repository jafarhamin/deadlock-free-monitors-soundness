#include "stdlib.h"
#include "threads.h"
#include "barriers.h"

/*@  
predicate_family_instance thread_run_data(wait_barrier_thread)(list<void*> tobs, struct barrier *b) =
   [_]barrier(b,?v) &*&
   wait_level_below_obs(pair({(wait_barrier_thread)}, 0r), cons(v,nil)) == true &*&
   tobs == cons(v,nil);
@*/

void wait_barrier_thread(struct barrier *b)  //@ : thread_run
  //@ requires thread_run_data(wait_barrier_thread)(?tobs,b) &*& obs(tobs);
  //@ ensures obs(nil);
{
  //@ open thread_run_data(wait_barrier_thread)(_,_);
  //@ assume(func_lt(wait_barrier,wait_barrier_thread));
  //@ wait_level_lt_below_obs(pair({(wait_barrier)}, 0r), pair({(wait_barrier_thread)}, 0r), tobs);
  wait_barrier(b);
}

void main()
  /*@ requires obs(nil) &*& wait_level_lt(pair({(wait_barrier)}, 0r), pair({(main)}, 0r)) == true; @*/
  //@ ensures obs(nil);
{
  int r = 3;
  //@ close create_barrier_ghost_args(pair({(main)}, 1r));
  struct barrier *b = create_barrier(r);
  //@ leak [_]barrier(b,?v);  

  //@ assert obs(ntimes_list(nat_of_int(r),v,nil));  
  
  //@ close thread_run_data(wait_barrier_thread)(cons(v,nil),b);   
  thread_start(wait_barrier_thread, b);
  //@ minus_ntimes(nat_of_int(2),v);  

  //@ close thread_run_data(wait_barrier_thread)(cons(v,nil),b);
  thread_start(wait_barrier_thread, b);
  //@ minus_ntimes(nat_of_int(1),v);    

  //@ close thread_run_data(wait_barrier_thread)(cons(v,nil),b);
  thread_start(wait_barrier_thread, b);
  //@ minus_ntimes(nat_of_int(0),v);
}
