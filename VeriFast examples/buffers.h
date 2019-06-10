#ifndef BUFFERS_H
#define BUFFERS_H

#include "obligations.h"

/*@
predicate create_buffer_ghost_args(pair<list<void*>, real> wlevel) = true;

predicate buffer(struct buffer *b; void* gamma);
@*/

struct buffer;

struct buffer* create_buffer();
  //@ requires create_buffer_ghost_args(?wlevel) &*& obs(?O);
  //@ ensures buffer(result,?v) &*& obs(cons(v,O)) &*& level(v) == wlevel;

int get(struct buffer* b);
  //@ requires [_]buffer(b,?v) &*& obs(?O) &*& wait_level_below_obs(pair({get}, 0r), O) == true;
  //@ ensures [_]buffer(b,v) &*& obs(O);

int get_when_ready(struct buffer* b);
  //@ requires [_]buffer(b,?v) &*& obs(?O) &*& w_level_below_all(v,O)==true &*& wait_level_below_obs(pair({get_when_ready}, 0r), O) == true;
  //@ ensures [_]buffer(b,v) &*& obs(O);

void set_and_notify(struct buffer* b, int value);
  //@ requires [_]buffer(b,?v) &*& obs(?O) &*& wait_level_below_obs(pair({set_and_notify}, 0r), O) == true;
  //@ ensures [_]buffer(b,v) &*& obs(remove(v,O));

#endif    
