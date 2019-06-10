#include "stdlib.h"
#include "channels.h"
#include "fibonacci.h"

struct fibonacci{
  struct channel* ch1;
  struct channel* ch2;  
};

/*@
predicate fibonacci(struct fibonacci* f; void* gamma)=
  [_]f->ch1 |-> ?ch1 &*&
  [_]f->ch2 |-> ?ch2 &*&  
  [_]channel(ch1,?gamma1) &*&
  [_]channel(ch2,gamma) &*&
  wait_level_lt(pair({receive}, 0r), level(gamma)) == true &*&
  wait_level_lt(pair({send}, 0r), level(gamma)) == true &*&  
  wait_level_lt(pair({receive}, 0r), level(gamma1)) == true &*&
  wait_level_lt(pair({send}, 0r), level(gamma1)) == true &*&  
  P(gamma1) == true &*&
  level'(gamma1) == some(level(gamma1)) &*&
  P(gamma) == true &*&
  level'(gamma) == some(level(gamma)) &*&
  wait_level_lt(level(gamma1), level(gamma)) == true;
@*/

struct fibonacci* new_fibonacci()
  //@ requires obs(?O) &*& wait_level_below_obs(pair({(new_fibonacci)}, 0r), O) == true;
  //@ ensures obs(O) &*& fibonacci(result, ?gamma);
{
  //@ close create_channel_ghost_args(pair({(new_fibonacci)}, 0r),some(pair({(new_fibonacci)}, 0r)),true);
  struct channel* ch1 = create_channel();
  //@ leak [_]channel(ch1,?gamma1);
  
  //@ close create_channel_ghost_args(pair({(new_fibonacci)}, 1r),some(pair({(new_fibonacci)}, 1r)),true);
  struct channel* ch2 = create_channel();
  //@ leak [_]channel(ch2,?gamma);
  
  //@ assume(func_lt(send,new_fibonacci));
  //@ assume(func_lt(receive,new_fibonacci));  
  //@ wait_level_lt_below_obs(pair({(send)}, 0r), pair({(new_fibonacci)}, 0r), O);
  send(ch1,1);
  send(ch2,1);
  
  struct fibonacci* f = malloc(sizeof(struct fibonacci));
  if (f==0)
    abort();
  f->ch1 = ch1;
  f->ch2 = ch2;
  //@ leak [_]f->ch1 |-> _;
  //@ leak [_]f->ch2 |-> _;
  //@ leak [_]malloc_block_fibonacci(f);  
  //@ close fibonacci(f,gamma);
  return f;
}

void next_fibonacci(struct fibonacci* f)
  //@ requires obs(?O) &*& [_]fibonacci(f, ?gamma) &*& w_level_below_all(gamma,O) == true &*& wait_level_below_obs(pair({(next_fibonacci)}, 0r), O) == true;
  //@ ensures obs(O) &*& [_]fibonacci(f, gamma);
{
  //@ load(f->ch2);
  //@ below_count(gamma,O);
  //@ count_same(gamma,O);
  //@ assume(func_lt(receive,next_fibonacci));  
  //@ wait_level_lt_below_obs(pair({(receive)}, 0r), pair({(next_fibonacci)}, 0r), O);
  int x2 = receive(f->ch2);
  
  //@ load(f->ch1);
  //@ assert [_]f->ch1 |-> ?ch1;
  //@ assert [_]channel(ch1,?gamma1);
  //@ wait_level_lt_below_obs(level(gamma1),level(gamma),O);
  //@ below_count(gamma1,O);
  //@ count_same(gamma1,O);
  int x1 = receive(f->ch1);

  //@ assume(func_lt(send,next_fibonacci));    
  //@ wait_level_lt_below_obs(pair({(send)}, 0r), pair({(next_fibonacci)}, 0r), O);
  send(f->ch1, x2);  
  send(f->ch2, x1 + x2);
}  

void read_fibonacci(struct fibonacci* f)
  //@ requires obs(?O) &*& [_]fibonacci(f, ?gamma) &*& w_level_below_all(gamma,O) == true &*& wait_level_below_obs(pair({(read_fibonacci)}, 0r), O) == true;
  //@ ensures obs(O) &*& [_]fibonacci(f, gamma);
{
  //@ load(f->ch2);
  //@ below_count(gamma,O);
  //@ count_same(gamma,O);
  //@ assume(func_lt(receive,read_fibonacci));  
  //@ wait_level_lt_below_obs(pair({(receive)}, 0r), pair({(read_fibonacci)}, 0r), O);
  int x = receive(f->ch2);
  //@ assume(func_lt(send,read_fibonacci));    
  //@ wait_level_lt_below_obs(pair({(send)}, 0r), pair({(read_fibonacci)}, 0r), O);
  send(f->ch2, x);
}
