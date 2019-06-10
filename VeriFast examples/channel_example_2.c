#include "stdlib.h"
#include "channels.h"
#include "threads.h"

/*@
predicate_family_instance thread_run_data(inc_thread)(list<void*> tobs, struct channel *ch) =
  [_]channel(ch,?gamma) &*&
  no_cycle(gamma,cons(gamma,nil)) == true &*& 
  wait_level_lt(pair({inc}, 0r), level(gamma)) == true &*&
  wait_level_lt(pair({inc}, 0r), level(gamma)) == true &*&
  tobs == nil;
@*/

void inc(struct channel *ch)
/*@ requires [_]channel(ch,?gamma) &*& obs(?O) &*& no_cycle(gamma,cons(gamma,O)) == true &*& wait_level_below_obs(pair({(inc)}, 0r), O) == true &*&
      wait_level_lt(pair({inc}, 0r), level(gamma)) == true; @*/
//@ ensures [_]channel(ch,gamma) &*& obs(O);
{
  //@ load(ch);
  //@ assume(func_lt(receive,inc));
  //@ assume(func_lt(send,inc));  
  //@ wait_level_lt_below_obs(pair({(receive)}, 0r), pair({(inc)}, 0r), cons(gamma,O));
  //@ wait_level_lt_below_obs(pair({(send)}, 0r), pair({(inc)}, 0r), cons(gamma,O));  
  receive(ch);
  send(ch,12);
}

void inc_thread(struct channel *ch)  //@ : thread_run
  //@ requires thread_run_data(inc_thread)(?tobs,ch) &*& obs(tobs);
  //@ ensures obs(nil);
{
  //@ open thread_run_data(inc_thread)(_,_);
  inc(ch);
}

void main()
  //@ requires obs(nil);
  //@ ensures obs(nil);
{
  //@ close create_channel_ghost_args(pair({(main)}, 1r),some(pair({(main)}, 1r)),true);
  struct channel *ch = create_channel();
  //@ leak [_]channel(ch,?gamma);
  
  //@ close thread_run_data(inc_thread)(nil,ch);
  thread_start(inc_thread, ch);

  //@ close thread_run_data(inc_thread)(nil,ch);
  thread_start(inc_thread, ch);
  
  send(ch,12);  
}
