#ifndef COUNTERS_H
#define COUNTERS_H
#include "obligations.h"

struct counter;

/*@
predicate counter(struct counter* c; void* gamma);
@*/

struct counter* new_counter(int value);
  //@ requires obs(?O) &*& wait_level_below_obs(pair({(new_counter)}, 0r), O) == true &*& exists< pair<list<void*>, real> >(?w_level) &*& wait_level_lt(pair({new_counter}, 0r), w_level) == true;
  //@ ensures obs(O) &*& counter(result, ?gamma) &*& level(gamma) == w_level;

void inc_counter(struct counter* c);
  //@ requires obs(?O) &*& [_]counter(c,?gamma) &*& w_level_below_all(gamma,O) == true &*& wait_level_below_obs(pair({(inc_counter)}, 0r), O) == true;
  //@ ensures obs(O) &*& [_]counter(c,gamma);

int read_counter(struct counter* c);
  //@ requires obs(?O) &*& [_]counter(c,?gamma) &*& w_level_below_all(gamma,O) == true &*& wait_level_below_obs(pair({(read_counter)}, 0r), O) == true;
  //@ ensures obs(O) &*& [_]counter(c,gamma);

#endif