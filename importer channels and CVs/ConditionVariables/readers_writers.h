#ifndef READERS_WRITERS_H
#define READERS_WRITERS_H

#include "stdlib.h"
#include "levels.h"
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
    //@ ensures reader_writer(result, ?rd, ?wr, ?ardrs, ?awrtrs) &*& wait_level_of(wr) == wr_wlevel &*& wait_level_of(rd) == rd_wlevel;

void reader_enter(struct read_write *b);
  //@ requires [_]reader_writer(b, ?grd, ?gwr, ?ardrs, ?awrtrs) &*& obs(?O) &*& w_level_below_all(grd,O) == true &*& wait_level_below_obs(pair({reader_enter}, 0r), O) == true;
  //@ ensures [_]reader_writer(b, grd, gwr, ardrs, awrtrs) &*& obs(cons(gwr,O)) &*& tic(ardrs);

void reader_exit(struct read_write *b);
  //@ requires [_]reader_writer(b, ?grd, ?gwr, ?ardrs, ?awrtrs) &*& obs(cons(gwr,?O)) &*& tic(ardrs) &*& wait_level_below_obs(pair({reader_exit}, 0r), cons(gwr,O)) == true;
  //@ ensures [_]reader_writer(b, grd, gwr, ardrs, awrtrs) &*& obs(O);

void writer_enter(struct read_write *b);
  //@ requires [_]reader_writer(b, ?grd, ?gwr, ?ardrs, ?awrtrs) &*& obs(?O) &*& w_level_below_all(grd,O) == true &*& wait_level_below_obs(pair({writer_enter}, 0r), O) == true;
  //@ ensures [_]reader_writer(b, grd, gwr, ardrs, awrtrs) &*& obs(cons(gwr,cons(grd,O))) &*& tic(awrtrs);

void writer_exit(struct read_write *b);
  //@ requires [_]reader_writer(b, ?grd, ?gwr, ?ardrs, ?awrtrs) &*& obs(cons(gwr,cons(grd,?O))) &*& tic(awrtrs) &*& wait_level_below_obs(pair({writer_exit}, 0r), cons(gwr,cons(grd,O))) == true;
  //@ ensures [_]reader_writer(b, grd, gwr, ardrs, awrtrs) &*& obs(O);

#endif
