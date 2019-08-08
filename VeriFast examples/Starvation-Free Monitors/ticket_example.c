#include "tickets.h"
#include "stdlib.h"
#include "monitors.h"
#include "threads.h"

/*@
predicate_family_instance thread_run_data(customer_thread)(list<void*> tobs, struct tvm *tvm) =
   [_]tvm(tvm,?v,?g) &*& tobs == nil;
@*/

void customer_thread(struct tvm *tvm)  //@ : thread_run
  //@ requires thread_run_data(customer_thread)(?tobs,tvm) &*& obs(tobs);
  //@ ensures obs(nil);
{
  //@ open thread_run_data(customer_thread)(_,_);
  enter_tvm(tvm);
  exit_tvm(tvm);
}

int main()
  //@ requires obs(nil);
  //@ ensures obs(nil);
{
  //@ close exists(level_of(main));
  struct tvm *tvm = new_tvm();
  //@ leak tvm(tvm, ?v, ?g);
  
  while(true)
  //@ invariant obs(nil) &*& [_]tvm(tvm, v, g);
  {
  //@ close thread_run_data(customer_thread)(nil,tvm);
  thread_start(customer_thread, tvm);
  }
  
  enter_tvm(tvm);
  exit_tvm(tvm);  
  return 0;
}
