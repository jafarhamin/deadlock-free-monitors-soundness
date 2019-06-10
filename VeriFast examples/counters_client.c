#include "counters.h"
#include "threads.h"

/*@
predicate_family_instance thread_run_data(inc_thread)(list<void*> tobs, struct counter *c) =
   [_]counter(c,?gamma) &*&
   tobs == nil;
@*/

void inc_thread(struct counter *c)  //@ : thread_run
  //@ requires thread_run_data(inc_thread)(?tobs,c) &*& obs(tobs);
  //@ ensures obs(nil);
{
  //@ open thread_run_data(inc_thread)(_,_);
  inc_counter(c);
}

struct counter* client_1()
  //@ requires obs(?O) &*& wait_level_below_obs(pair({(client_1)}, 0r), O) == true;
  //@ ensures obs(O) &*& [_]counter(result, ?gamma);
{
  //@ assume(func_lt(new_counter,client_1));  
  //@ wait_level_lt_below_obs(pair({(new_counter)}, 0r), pair({(client_1)}, 0r), O);
  //@ close exists(pair({(client_1)}, 0r));
  struct counter *c = new_counter(0);
  //@ leak [_]counter(c,?gamma);
  //@ close thread_run_data(inc_thread)(nil,c);
  thread_start(inc_thread, c);
  //@ close thread_run_data(inc_thread)(nil,c);
  thread_start(inc_thread, c);
  //@ minus_nil(O);
  return c;
}
