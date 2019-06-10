#include "stdlib.h"
#include "channels.h"
#include "fibonacci.h"
#include "threads.h"

struct intermediator{
  struct channel* source;
  struct channel* destination;
};

/*@
predicate intermediator(struct intermediator* c, void* src, void* dst) =
  [_]c->source |-> ?source &*&
  [_]c->destination |-> ?destination &*&
  [_]channel(source,src) &*&
  [_]channel(destination,dst) &*&  
  wait_level_lt(pair({intermediate}, 0r), level(dst)) == true &*&
  no_cycle(src,cons(dst,nil)) == true &*&
  credit(source);
@*/

/*@
predicate_family_instance thread_run_data(im_thread)(list<void*> tobs, struct intermediator* im) =
    intermediator(im, ?src, ?dst) &*& tobs == cons(dst,nil);
@*/

void intermediate(struct channel* source, struct channel* destination)
  //@ requires obs(?O) &*& [_]channel(source,?src) &*& [_]channel(destination,?dst) &*& wait_level_below_obs(pair({(intermediate)}, 0r), O) == true &*& credit(source) &*& no_cycle(src,O) == true;
  //@ ensures obs(remove(dst,O)) &*& [_]channel(source,src) &*& [_]channel(destination,dst);
{
  //@ assume(func_lt(receive,intermediate));  
  //@ wait_level_lt_below_obs(pair({(receive)}, 0r), pair({(intermediate)}, 0r), O);
  int x = receive(source);
  
  //@ assume(func_lt(send,intermediate));    
  //@ wait_level_lt_below_obs(pair({(send)}, 0r), pair({(intermediate)}, 0r), O);
  send(destination,x);
}

void intermediator_client()
  //@ requires obs(?O) &*& wait_level_below_obs(pair({(intermediator_client)}, 0r), O) == true;
  //@ ensures obs(O);
{
  //@ close create_channel_ghost_args(pair({(intermediator_client)}, 1r),some(pair({(intermediator_client)}, 2r)),false);
  struct channel* source = create_channel();
  //@ leak [_]channel(source,?src);
  
  //@ close create_channel_ghost_args(pair({(intermediator_client)}, 2r),some(pair({(intermediator_client)}, 2r)),true);
  struct channel* destination = create_channel();
  //@ leak [_]channel(destination,?dst);

  //@ no_cycle(src,cons(dst,nil)) && no_cycle(dst,cons(src,nil));
  
  //@ assume(func_lt(send,intermediator_client));
  //@ wait_level_lt_below_obs(pair({(send)}, 0r), pair({(intermediator_client)}, 0r), O);
  send(destination,1);

  struct intermediator* im = malloc(sizeof(struct intermediator));
  if (im==0)
    abort();
  im->source = source;
  im->destination = destination;
  //@ leak [_]im->source |-> source;
  //@ leak [_]im->destination |-> destination;
  //@ leak [_]malloc_block_intermediator(im);
    
  //@ load(source);
  //@ load(destination);

  //@ close intermediator(im, src, dst);
  //@ close thread_run_data(im_thread)(cons(dst,nil),im);
  thread_start(im_thread, im);
  //@ minus_nil(cons(src,O));
  
  struct intermediator* im' = malloc(sizeof(struct intermediator));
  if (im'==0)
    abort();
  im'->source = destination;
  im'->destination = source;
  //@ leak [_]im'->source |-> destination;
  //@ leak [_]im'->destination |-> source;
  //@ leak [_]malloc_block_intermediator(im');

  //@ close intermediator(im', dst, src);
  //@ close thread_run_data(im_thread)(cons(src,nil),im');
  thread_start(im_thread, im');
    
}

void im_thread(struct intermediator *im)  //@ : thread_run
  //@ requires thread_run_data(im_thread)(?tobs,im) &*& obs(tobs);
  //@ ensures obs(nil);
{
  //@ open thread_run_data(im_thread)(_,_);
  //@ open intermediator(im, ?src, ?dst);
  intermediate(im->source, im->destination);
}
