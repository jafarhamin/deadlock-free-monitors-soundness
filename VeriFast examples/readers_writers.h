#ifndef READERS_WRITERS_H
#define READERS_WRITERS_H

#include "stdlib.h"
#include "obligations.h"
//@ #include "ghost_counters.gh"

struct read_write;

/*@
predicate create_rw_ghost_args(pair<list<void*>, real> gwr_wlevel, pair<list<void*>, real> grw_wlevel) = true;  
   
predicate reader_writer(struct read_write *b; void* grd, void* gwr, int ardrs, int awrtrs);
@*/

struct read_write *create_readers_writers();
    /*@ requires create_rw_ghost_args(?wr_wlevel, ?rd_wlevel) &*& wait_level_lt(wr_wlevel, rd_wlevel) == true &*&
          wait_level_lt(pair({(create_readers_writers)}, 0r), wr_wlevel) == true &*&
          wait_level_lt(pair({(create_readers_writers)}, 0r), rd_wlevel) == true; @*/
    //@ ensures reader_writer(result, ?rd, ?wr, ?ardrs, ?awrtrs) &*& level(wr) == wr_wlevel &*& level(rd) == rd_wlevel;

void reader_enter(struct read_write *b);
  //@ requires [_]reader_writer(b, ?rd, ?wr, ?ardrs, ?awrtrs) &*& obs(?O) &*& w_level_below_all(rd,O) == true &*& wait_level_below_obs(pair({reader_enter}, 0r), O) == true;
  //@ ensures [_]reader_writer(b, rd, wr, ardrs, awrtrs) &*& obs(cons(wr,O)) &*& tic(ardrs);

void reader_exit(struct read_write *b);
  //@ requires [_]reader_writer(b, ?rd, ?wr, ?ardrs, ?awrtrs) &*& obs(cons(wr,?O)) &*& tic(ardrs) &*& w_level_below_all(rd, O) == true  &*& wait_level_below_obs(pair({reader_exit}, 0r), cons(wr,O)) == true;
  //@ ensures [_]reader_writer(b, rd, wr, ardrs, awrtrs) &*& obs(O);

void writer_enter(struct read_write *b);
  //@ requires [_]reader_writer(b, ?rd, ?wr, ?ardrs, ?awrtrs) &*& obs(?O) &*& w_level_below_all(rd,O) == true &*& wait_level_below_obs(pair({writer_enter}, 0r), O) == true;
  //@ ensures [_]reader_writer(b, rd, wr, ardrs, awrtrs) &*& obs(cons(wr,cons(rd,O))) &*& tic(awrtrs);

void writer_exit(struct read_write *b);
  //@ requires [_]reader_writer(b, ?rd, ?wr, ?ardrs, ?awrtrs) &*& obs(cons(wr,cons(rd,?O))) &*& tic(awrtrs) &*& w_level_below_all(rd,O) == true &*& wait_level_below_obs(pair({writer_exit}, 0r), cons(wr,cons(rd,O))) == true;
  //@ ensures [_]reader_writer(b, rd, wr, ardrs, awrtrs) &*& obs(O);

#endif
