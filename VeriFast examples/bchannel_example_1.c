#include "stdlib.h"
#include "threads.h"
#include "bchannels.h"

/*@
predicate_family_instance thread_run_data(receive_thread)(list<void*> tobs, struct channel *ch) =
   [_]channel(ch,?ve,?vf) &*&
   no_cycle(ve,cons(vf,nil)) == true &*&
   wait_level_below_obs(pair({(receive_thread)}, 0r), cons(vf,nil)) == true &*&
   credite(ch) &*& 
   tobs == cons(vf,nil);

predicate_family_instance thread_run_data(send_thread)(list<void*> tobs, struct channel *ch) =
   [_]channel(ch,?ve,?vf) &*&
   no_cycle(vf,cons(ve,nil)) == true &*& 
   wait_level_below_obs(pair({(send_thread)}, 0r), cons(ve,nil)) == true &*&
   tobs == cons(ve,nil) &*& 
   creditf(ch);
@*/

void receive_thread(struct channel *b)  //@ : thread_run
    //@ requires thread_run_data(receive_thread)(?tobs,b) &*& obs(tobs);
    //@ ensures obs(nil);
{
  //@ open thread_run_data(receive_thread)(_,_);
  //@ assume(func_lt(receive,receive_thread));
  //@ wait_level_lt_below_obs(pair({(receive)}, 0r), pair({(receive_thread)}, 0r), tobs);
  receive(b);
}

void send_thread(struct channel *b)  //@ : thread_run
    //@ requires thread_run_data(send_thread)(?tobs,b) &*& obs(tobs);
    //@ ensures obs(nil);
{
  //@ open thread_run_data(send_thread)(_,_);
  //@ assume(func_lt(send,send_thread));
  //@ wait_level_lt_below_obs(pair({(send)}, 0r), pair({(send_thread)}, 0r), tobs);
  send(b,12);
}

void main()
    //@ requires obs(nil);
    //@ ensures obs(nil);
{
    int max = 1;
    //@ close create_channel_ghost_args(pair({(main)}, 1r), pair({(main)}, 2r), false, pair({(main)}, 2r), pair({(main)}, 2r));
    struct channel *ch = create_channel(max);
    //@ leak creditsf(max-1,ch);
    
    //@ leak [_]channel(ch,?ve,?vf);
    
    //@ loadf(ch);
    //@ loade(ch);    
    
    //@ close thread_run_data(send_thread)(cons(ve,nil),ch);
    thread_start(send_thread, ch);
    
    //@ close thread_run_data(receive_thread)(cons(vf,nil),ch);
    thread_start(receive_thread, ch);   
}
