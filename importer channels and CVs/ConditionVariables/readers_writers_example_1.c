#include "stdlib.h"
#include "threads.h"
#include "readers_writers.h"

/*@
predicate_family_instance thread_run_data(reader_thread)(list<void*> tobs, struct read_write *b) =
   [_]reader_writer(b,?grd,?gwr, ?ardrs, ?awrtrs) &*& wait_level_below_obs(pair({reader_thread}, 0r), cons(gwr,nil)) == true &*& tobs == nil;

predicate_family_instance thread_run_data(writer_thread)(list<void*> tobs, struct read_write *b) =
   [_]reader_writer(b,?grd,?gwr, ?ardrs, ?awrtrs) &*& wait_level_below_obs(pair({writer_thread}, 0r), cons(gwr,cons(grd,nil))) == true &*& tobs == nil;
@*/

void reader_thread(struct read_write *b)  //@ : thread_run
    //@ requires thread_run_data(reader_thread)(?tobs,b) &*& obs(tobs);
    //@ ensures obs(nil);
{
  //@ open thread_run_data(reader_thread)(_,_);
  //@ assert [_]reader_writer(b, ?grd, ?gwr, ?ardrs, ?awrtrs);
  reader_enter(b);
  // Reading ...
  
  //@ assume(func_lt(reader_exit,reader_thread));
  //@ wait_level_lt_below_obs(pair({(reader_exit)}, 0r), pair({(reader_thread)}, 0r), cons(gwr,tobs));
  reader_exit(b);
}

void writer_thread(struct read_write *b)  //@ : thread_run
    //@ requires thread_run_data(writer_thread)(?tobs,b) &*& obs(tobs);
    //@ ensures obs(nil);
{
  //@ open thread_run_data(writer_thread)(_,_);
  //@ assert [_]reader_writer(b, ?grd, ?gwr, ?ardrs, ?awrtrs);
    
  writer_enter(b);
  // Writing ...
  
  //@ assume(func_lt(writer_exit,writer_thread));
  //@ wait_level_lt_below_obs(pair({(writer_exit)}, 0r), pair({(writer_thread)}, 0r), cons(gwr,cons(grd,tobs)));
  writer_exit(b);
}

void main()
    //@ requires obs(nil); 
    //@ ensures obs(nil);
{
    //@ close create_rw_ghost_args(pair({main}, 1r), pair({main}, 2r));
    struct read_write *b = create_readers_writers();
    if (b==0)
      abort();
    //@ leak [_]reader_writer(b,?grd,?gwr, ?ardrs, ?awrtrs);

    //@ close thread_run_data(reader_thread)(nil,b);
    thread_start(reader_thread, b);

    //@ close thread_run_data(reader_thread)(nil,b);
    thread_start(reader_thread, b);
    
    //@ close thread_run_data(writer_thread)(nil,b);    
    while (true)
    /*@ invariant obs(nil) &*& thread_run_data(writer_thread)(nil,b) &*& [_]reader_writer(b,grd,gwr, ardrs, awrtrs);
    @*/
    {
      thread_start(writer_thread, b);
      //@ close thread_run_data(writer_thread)(nil,b);    
    }
}

