#include "stdlib.h"
#include "channels.h"
#include "threads.h"

/*@
predicate_family_instance thread_run_data(receive_thread)(list<void*> tobs, struct channel *ch) =
   [_]channel(ch,?gamma) &*& no_cycle(gamma,tobs) == true &*&
   credit(ch) &*& 
   tobs == nil;

predicate_family_instance thread_run_data(send_thread)(list<void*> tobs, struct channel *ch) =
  [_]channel(ch,?gamma) &*&
  wait_level_below_obs(pair({(send_thread)}, 0r), cons(gamma,nil)) == true &*&
  tobs == cons(gamma,nil);
@*/

void receive_thread(struct channel *b)  //@ : thread_run
  //@ requires thread_run_data(receive_thread)(?tobs,b) &*& obs(tobs);
  //@ ensures obs(nil);
{
  //@ open thread_run_data(receive_thread)(_,_);
  receive(b);
}

void send_thread(struct channel *ch)  //@ : thread_run
  //@ requires thread_run_data(send_thread)(?tobs,ch) &*& obs(tobs);
  //@ ensures obs(nil);
{
  //@ open thread_run_data(send_thread)(_,_);
  //@ assume(func_lt(send,send_thread));
  //@ wait_level_lt_below_obs(pair({(send)}, 0r), pair({(send_thread)}, 0r), tobs);
  send(ch,12);
}

void example_1()
  //@ requires obs(?O) &*& wait_level_below_obs(pair({(example_1)}, 0r), O) == true;
  //@ ensures obs(O);
{
  //@ close create_channel_ghost_args(pair({(example_1)}, 1r),none,false);
  struct channel *ch = create_channel();
  //@ leak [_]channel(ch,?gamma);

  //@ load(ch);
  
  //@ close thread_run_data(receive_thread)(nil,ch);
  thread_start(receive_thread, ch);
  //@ minus_nil(cons(gamma,O));
  
  //@ close thread_run_data(send_thread)(cons(gamma,nil),ch);
  thread_start(send_thread, ch);  
}

void example_2()
  //@ requires obs(?O) &*& wait_level_below_obs(pair({(example_2)}, 0r), O) == true;
  //@ ensures obs(O);
{
  //@ close create_channel_ghost_args(pair({(example_2)}, 1r),none,false);
  struct channel *ch = create_channel();
  //@ leak [_]channel(ch,?gamma);

  //@ load(ch);
  
  //@ close thread_run_data(receive_thread)(nil,ch);
  thread_start(receive_thread, ch);
  //@ minus_nil(cons(gamma,O));
  
  //@ assume(func_lt(send,example_2));
  //@ wait_level_lt_below_obs(pair({(send)}, 0r), pair({(example_2)}, 0r), cons(gamma,O));
  send(ch,12);
}


