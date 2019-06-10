#include "stdlib.h"
#include "channels.h"
#include "counters.h"
#include "mutexes_cv.h"
#include "registration.h"

struct course{
  struct channel* request;
  struct counter* numbers;  
};

/*@
predicate course(struct course* c; void* req, void* num)=
  [_]c->request |-> ?request &*&
  [_]c->numbers |-> ?numbers &*&  
  [_]channel(request,req) &*&
  [_]counter(numbers,num) &*&
  wait_level_lt(pair({register_course}, 0r), level(req)) == true &*&  
  wait_level_lt(pair({register_course}, 0r), level(num)) == true &*&
  P(req) == true &*&
  level'(req) == some(level(req)) &*&
  wait_level_lt(level(num), level(req)) == true;
@*/

struct course* new_course()
  /*@ requires obs(?O) &*& wait_level_below_obs(pair({(new_course)}, 0r), O) == true &*& 
        create_course_ghost_args(?req_wlevel, ?num_wlevel) &*& 
        wait_level_lt(pair({register_course}, 0r), num_wlevel) == true &*&
        wait_level_lt(pair({register_course}, 0r), req_wlevel) == true &*&
        wait_level_lt(num_wlevel, req_wlevel) == true; @*/
  //@ ensures obs(cons(?req,O)) &*& course(result, req, ?num);
{
  //@ open create_course_ghost_args(req_wlevel, num_wlevel);
  //@ close create_channel_ghost_args(req_wlevel,some(req_wlevel),true);
  struct channel* request = create_channel();
  //@ leak [_]channel(request,?req);

  //@ assume(func_lt(new_counter,new_course));
  //@ assume(func_lt(receive,new_course));
  //@ assume(func_lt(send,new_course));    
  //@ close exists< pair<list<void*>, real> >(num_wlevel); 
  //@ wait_level_lt_below_obs(pair({(new_counter)}, 0r), pair({(new_course)}, 0r), O);
  //@ wait_level_lt_trans(pair({new_counter}, 0r), pair({register_course}, 0r), req_wlevel);   
  //@ wait_level_lt_trans(pair({new_counter}, 0r), pair({register_course}, 0r), num_wlevel);   
  struct counter* numbers = new_counter(0);
  //@ leak [_]counter(numbers,?num);
    
  struct course* c = malloc(sizeof(struct course));
  if (c==0)
    abort();
  c->request = request;
  c->numbers = numbers;  
  
  //@ leak [_]c->request |-> request;
  //@ leak [_]c->numbers |-> numbers;

  //@ leak [_]malloc_block_course(c);  
  //@ close course(c,req,num);
  return c;
}

void register_course(struct course* c)
  //@ requires obs(?O) &*& course(c, ?req, ?num) &*& w_level_below_all(req,O) == true &*& wait_level_below_obs(pair({(register_course)}, 0r), O) == true;
  //@ ensures obs(O) &*& course(c, req, num);
{
  //@ load(c->request);
  //@ below_count(req,O);
  //@ count_same(req,O);
  //@ assume(func_lt(receive,register_course));  
  //@ assume(func_lt(inc_counter,register_course));    
  //@ assume(func_lt(read_counter,register_course));      
  //@ wait_level_lt_below_obs(pair({(receive)}, 0r), pair({(register_course)}, 0r), O);
  //@ wait_level_lt_trans(pair({receive}, 0r), pair({register_course}, 0r), level(req));     
  receive(c->request);

  //@ wait_level_lt_below_obs(level(num), level(req), O);
  //@ wait_level_lt_below_obs(pair({(inc_counter)}, 0r), pair({(register_course)}, 0r), O);  
  //@ wait_level_lt_trans(pair({(inc_counter)}, 0r), pair({register_course}, 0r), level(req));         
  inc_counter(c->numbers);    
  
  //@ assume(func_lt(send,register_course));    
  //@ wait_level_lt_below_obs(pair({(send)}, 0r), pair({(register_course)}, 0r), O);
  //@ wait_level_lt_trans(pair({send}, 0r), pair({register_course}, 0r), level(req));       
  send(c->request, 1);
}

void register_course'(struct course* c)
  //@ requires obs(?O) &*& course(c, ?req, ?num) &*& w_level_below_all(req,O) == true &*& wait_level_below_obs(pair({(register_course)}, 0r), O) == true;
  //@ ensures obs(O) &*& course(c, req, num);
{
  //@ load(c->request);
  //@ below_count(req,O);
  //@ count_same(req,O);
  //@ assume(func_lt(receive,register_course));  
  //@ assume(func_lt(inc_counter,register_course));    
  //@ assume(func_lt(read_counter,register_course));      
  //@ wait_level_lt_below_obs(pair({(receive)}, 0r), pair({(register_course)}, 0r), O);
  //@ wait_level_lt_trans(pair({receive}, 0r), pair({register_course}, 0r), level(req));     
  receive(c->request);

  //@ wait_level_lt_below_obs(level(num), level(req), O);
  //@ wait_level_lt_below_obs(pair({(inc_counter)}, 0r), pair({(register_course)}, 0r), O);  
  //@ wait_level_lt_trans(pair({(inc_counter)}, 0r), pair({register_course}, 0r), level(req));         
  inc_counter(c->numbers);    
  
  //@ wait_level_lt_below_obs(pair({(read_counter)}, 0r), pair({(register_course)}, 0r), O);  
  //@ wait_level_lt_trans(pair({(read_counter)}, 0r), pair({register_course}, 0r), level(req));         
  int numbers = read_counter(c->numbers);      
  
  //@ assume(func_lt(send,register_course));    
  //@ wait_level_lt_below_obs(pair({(send)}, 0r), pair({(register_course)}, 0r), O);
  //@ wait_level_lt_trans(pair({send}, 0r), pair({register_course}, 0r), level(req));       
  send(c->request, numbers);
}
