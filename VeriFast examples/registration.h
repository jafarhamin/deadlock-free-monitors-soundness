#ifndef REGISTRATION_H
#define REGISTRATION_H
#include "obligations.h"

struct course;

/*@
predicate create_course_ghost_args(pair<list<void*>, real> req_wlevel, pair<list<void*>, real> num_wlevel) = true;  

predicate course(struct course* c; void* req, void* num);
@*/

struct course* new_course();
  /*@ requires obs(?O) &*& wait_level_below_obs(pair({(new_course)}, 0r), O) == true &*& 
        create_course_ghost_args(?req_wlevel, ?num_wlevel) &*& 
        wait_level_lt(pair({register_course}, 0r), num_wlevel) == true &*&
        wait_level_lt(pair({register_course}, 0r), req_wlevel) == true &*&
        wait_level_lt(num_wlevel, req_wlevel) == true; @*/
  //@ ensures obs(cons(?req,O)) &*& course(result, req, ?num);

void register_course(struct course* c);
  //@ requires obs(?O) &*& course(c, ?req, ?num) &*& w_level_below_all(req,O) == true &*& wait_level_below_obs(pair({(register_course)}, 0r), O) == true;
  //@ ensures obs(O) &*& course(c, req, num);

void register_course'(struct course* c);
  //@ requires obs(?O) &*& course(c, ?req, ?num) &*& w_level_below_all(req,O) == true &*& wait_level_below_obs(pair({(register_course)}, 0r), O) == true;
  //@ ensures obs(O) &*& course(c, req, num);
