#ifndef FIBONACCI_H
#define FIBONACCI_H
#include "obligations.h"

struct fibonacci;

/*@
predicate fibonacci(struct fibonacci* f; void* gamma);
@*/

struct fibonacci* new_fibonacci();
  //@ requires obs(?O) &*& wait_level_below_obs(pair({(new_fibonacci)}, 0r), O) == true;
  //@ ensures obs(O) &*& fibonacci(result, ?gamma);

void next_fibonacci(struct fibonacci* f);
  //@ requires obs(?O) &*& [_]fibonacci(f, ?gamma) &*& w_level_below_all(gamma,O) == true &*& wait_level_below_obs(pair({(next_fibonacci)}, 0r), O) == true;
  //@ ensures obs(O) &*& [_]fibonacci(f, gamma);

void read_fibonacci(struct fibonacci* f);
  //@ requires obs(?O) &*& [_]fibonacci(f, ?gamma) &*& w_level_below_all(gamma,O) == true &*& wait_level_below_obs(pair({(read_fibonacci)}, 0r), O) == true;
  //@ ensures obs(O) &*& [_]fibonacci(f, gamma);

#endif  