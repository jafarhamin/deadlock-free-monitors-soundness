#ifndef CHANNELS_H
#define CAHNNELS_H
#include "obligations.h"

struct channel;

typedef struct channel *channel;

/*@
predicate channel(struct channel *ch; void* gamma);

predicate create_channel_ghost_args(pair<list<void*>, real> gamma_wlevel, option< pair<list<void*>, real> > gamma_X, bool gamma_P) = true;  

predicate credit(struct channel *ch);

lemma void load(struct channel *ch);
  requires [?f]channel(ch,?v) &*& obs(?O);
  ensures [f]channel(ch,v) &*& obs(cons(v,O)) &*& credit(ch);

lemma void channel_frac'(channel ch);
  requires [?f]channel(ch,?v);
  ensures [f]channel(ch,v) &*& 0 < f &*& f <= 1;        
@*/

struct channel *create_channel();
  //@ requires create_channel_ghost_args(?gamma_wlevel, ?gamma_X, ?gamma_P) &*& obs(?O);
  /*@ ensures channel(result,?gamma) &*& level(gamma) == gamma_wlevel &*& level'(gamma) == gamma_X &*& P(gamma) == gamma_P &*& 
        obs(?O') &*&((gamma_P && O' == cons(gamma,O)) || (!gamma_P && O' == O)); @*/

                
int receive(struct channel *ch);
  //@ requires [?f]channel(ch,?gamma) &*& obs(?O) &*& credit(ch) &*& no_cycle(gamma,O) == true &*& wait_level_below_obs(pair({receive}, 0r), O) == true;
  //@ ensures  [f]channel(ch,gamma) &*& obs(O);

void send(struct channel *ch, int data);
  //@ requires [?f]channel(ch,?gamma) &*& obs(?O) &*& wait_level_below_obs(pair({send}, 0r), O) == true;
  //@ ensures [f]channel(ch,gamma) &*& obs(remove(gamma,O));

#endif  
