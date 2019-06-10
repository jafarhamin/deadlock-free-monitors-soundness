#include "stdlib.h"
#include "channels.h"
#include "counters.h"

struct counter{
  struct channel *ch;
};

/*@
predicate counter(struct counter* c; void* gamma)=
  [_]c->ch |-> ?ch &*&
  [_]channel(ch,gamma) &*&
  wait_level_lt(pair({receive}, 0r), level(gamma)) == true &*&
  wait_level_lt(pair({send}, 0r), level(gamma)) == true &*&  
  P(gamma) == true &*&
  level'(gamma) == some(level(gamma));
@*/

struct counter* new_counter(int value)
  //@ requires obs(?O) &*& wait_level_below_obs(pair({(new_counter)}, 0r), O) == true &*& exists< pair<list<void*>, real> >(?w_level) &*& wait_level_lt(pair({new_counter}, 0r), w_level) == true;
  //@ ensures obs(O) &*& counter(result, ?gamma) &*& level(gamma) == w_level;
{
  //@ close create_channel_ghost_args(w_level,some(w_level),true);  
  struct channel* ch = create_channel();
  //@ leak [_]channel(ch,?gamma);
  //@ assume(func_lt(send,new_counter));
  //@ assume(func_lt(receive,new_counter));  
  //@ wait_level_lt_below_obs(pair({(send)}, 0r), pair({(new_counter)}, 0r), O);
  //@ wait_level_lt_trans(pair({send}, 0r), pair({new_counter}, 0r), w_level);
  //@ wait_level_lt_trans(pair({receive}, 0r), pair({new_counter}, 0r), w_level);  
  send(ch,value);
  struct counter* c = malloc(sizeof(struct counter));
  if (c==0)
    abort();
  c->ch = ch;
  //@ leak [_]c->ch |-> _;
  //@ leak [_]malloc_block_counter(c);  
  //@ close counter(c,gamma);
  return c;
}

void inc_counter(struct counter* c)
  //@ requires obs(?O) &*& [_]counter(c,?gamma) &*& w_level_below_all(gamma,O) == true &*& wait_level_below_obs(pair({(inc_counter)}, 0r), O) == true;
  //@ ensures obs(O) &*& [_]counter(c,gamma);
{
  //@ load(c->ch);
  //@ below_count(gamma,O);
  //@ count_same(gamma,O);
  //@ assume(func_lt(receive,inc_counter));  
  //@ wait_level_lt_below_obs(pair({(receive)}, 0r), pair({(inc_counter)}, 0r), O);
  int x = receive(c->ch);
  //@ assume(func_lt(send,inc_counter));    
  //@ wait_level_lt_below_obs(pair({(send)}, 0r), pair({(inc_counter)}, 0r), O);
  send(c->ch, x+1);
}

int read_counter(struct counter* c)
  //@ requires obs(?O) &*& [_]counter(c,?gamma) &*& w_level_below_all(gamma,O) == true &*& wait_level_below_obs(pair({(read_counter)}, 0r), O) == true;
  //@ ensures obs(O) &*& [_]counter(c,gamma);
{
  //@ load(c->ch);
  //@ below_count(gamma,O);
  //@ count_same(gamma,O);
  //@ assume(func_lt(receive,read_counter));  
  //@ wait_level_lt_below_obs(pair({(receive)}, 0r), pair({(read_counter)}, 0r), O);
  int x = receive(c->ch);
  //@ assume(func_lt(send,read_counter));    
  //@ wait_level_lt_below_obs(pair({(send)}, 0r), pair({(read_counter)}, 0r), O);
  send(c->ch, x);
  return x;
}