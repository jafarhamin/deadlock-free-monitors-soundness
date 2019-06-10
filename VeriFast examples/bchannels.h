#include "stdlib.h"
#include "obligations.h"

struct channel;
typedef struct channel *channel;

/*@
predicate channel(struct channel *ch; void* ve, void* vf);

predicate create_channel_ghost_args(pair<list<void*>, real> ve_wlevel, pair<list<void*>, real> ve_X, bool vef_P, pair<list<void*>, real> vf_wlevel , pair<list<void*>, real> vf_X) = true;

predicate credite(struct channel *ch);

predicate creditf(struct channel *ch);

lemma void loadf(struct channel *ch);
  requires [?f]channel(ch,?ve,?vf) &*& obs(?O);
  ensures [f]channel(ch,ve,vf) &*& obs(cons(vf,O)) &*& creditf(ch);  

lemma void loade(struct channel *ch);
  requires [?f]channel(ch,?ve,?vf) &*& obs(?O);
  ensures [f]channel(ch,ve,vf) &*& obs(cons(ve,O)) &*& credite(ch);  
  
predicate creditsf(int n, struct channel *ch) =
  n == 0 ? true :
  creditf(ch) &*& creditsf(n-1, ch);
  
fixpoint list<T> cons_bool<T>(bool b, list<T> O, T t){
  return b ? cons(t,O) : O;
}  
@*/

struct channel *create_channel(int max);
    /*@ requires obs(nil) &*& create_channel_ghost_args(?ve_wlevel, ?ve_X, ?ve_P, ?vf_wlevel, ?vf_X) &*&
          wait_level_lt(ve_wlevel, vf_wlevel) == true &*& !wait_level_lt(ve_X, vf_X) &*& 0 < max; @*/
    /*@ ensures channel(result,?ve,?vf) &*& obs(cons_bool(ve_P,nil,ve)) &*& creditsf(max-1,result) &*& 
          level(ve) == ve_wlevel &*& level'(ve) == some(ve_X) &*& P(ve) == ve_P &*&
          level(vf) == vf_wlevel &*& level'(vf) == some(vf_X) &*& P(vf) == true; @*/

void receive(struct channel *ch);
  //@ requires [_]channel(ch,?ve,?vf) &*& obs(?O) &*& credite(ch) &*& no_cycle(ve,O) == true &*& wait_level_below_obs(pair({(receive)}, 0r), O) == true;
  //@ ensures [_]channel(ch,ve,vf) &*& obs(remove(vf,O));

void send(struct channel *ch, int x);
  //@ requires [_]channel(ch,?ve,?vf) &*& obs(?O) &*& creditf(ch) &*& no_cycle(vf,O)== true &*& wait_level_below_obs(pair({(send)}, 0r), cons(ve,O)) == true;
  //@ ensures [_]channel(ch,ve,vf) &*& obs(remove(ve,O));
