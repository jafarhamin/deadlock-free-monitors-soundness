#include "dining_philosophers.h"

void ex1()
  //@ requires obs(nil);
  //@ ensures obs(nil);
{
  //@ close create_dphs_ghost_args(cons(pair({(ex1)}, 1r),cons(pair({(ex1)}, 2r),cons(pair({(ex1)}, 3r),cons(pair({(ex1)}, 4r),cons(pair({(ex1)}, 5r),nil))))));
  dining_philosophers dp = new_dining_philosophers(5);
  //@ leak [_]dphs(dp,?cvs);
  
  //@ forall_nth(cvs,X_none,0);  
  //@ forall_nth(cvs,X_none,1);    
  //@ wlevel_nth(cvs,cons(pair({(ex1)}, 1r),cons(pair({(ex1)}, 2r),cons(pair({(ex1)}, 3r),cons(pair({(ex1)}, 4r),cons(pair({(ex1)}, 5r),nil))))),length(cvs)-1);  
  //@ wlevel_nth(cvs,cons(pair({(ex1)}, 1r),cons(pair({(ex1)}, 2r),cons(pair({(ex1)}, 3r),cons(pair({(ex1)}, 4r),cons(pair({(ex1)}, 5r),nil))))),1);  
  //@ wlevel_nth(cvs,cons(pair({(ex1)}, 1r),cons(pair({(ex1)}, 2r),cons(pair({(ex1)}, 3r),cons(pair({(ex1)}, 4r),cons(pair({(ex1)}, 5r),nil))))),0);  
  //@ wlevel_nth(cvs,cons(pair({(ex1)}, 1r),cons(pair({(ex1)}, 2r),cons(pair({(ex1)}, 3r),cons(pair({(ex1)}, 4r),cons(pair({(ex1)}, 5r),nil))))),2);  
  //@ mod_plus_le(length(cvs), length(cvs)-1);
  //@ mod_plus_le(length(cvs), 1);
  //@ mod_plus(length(cvs), 0);
  //@ mod_plus_le(length(cvs), 2);
  
  pickup(dp,0);
  putdown(dp,0);
  pickup(dp,1);
  putdown(dp,1);
}

void ex2()
  //@ requires obs(nil);
  //@ ensures obs(nil);
{
  //@ close create_dphs_ghost_args(cons(pair({(ex2)}, 4r),cons(pair({(ex2)}, 5r),cons(pair({(ex2)}, 1r),cons(pair({(ex2)}, 2r),cons(pair({(ex2)}, 3r),nil))))));
  dining_philosophers dp = new_dining_philosophers(5);
  //@ leak [_]dphs(dp,?cvs);

  //@ forall_nth(cvs,X_none,0);  
  //@ forall_nth(cvs,X_none,2);  
  //@ wlevel_nth(cvs,cons(pair({(ex2)}, 4r),cons(pair({(ex2)}, 5r),cons(pair({(ex2)}, 1r),cons(pair({(ex2)}, 2r),cons(pair({(ex2)}, 3r),nil))))),1);  
  //@ wlevel_nth(cvs,cons(pair({(ex2)}, 4r),cons(pair({(ex2)}, 5r),cons(pair({(ex2)}, 1r),cons(pair({(ex2)}, 2r),cons(pair({(ex2)}, 3r),nil))))),length(cvs)-1);  
  //@ wlevel_nth(cvs,cons(pair({(ex2)}, 4r),cons(pair({(ex2)}, 5r),cons(pair({(ex2)}, 1r),cons(pair({(ex2)}, 2r),cons(pair({(ex2)}, 3r),nil))))),2);  
  //@ wlevel_nth(cvs,cons(pair({(ex2)}, 4r),cons(pair({(ex2)}, 5r),cons(pair({(ex2)}, 1r),cons(pair({(ex2)}, 2r),cons(pair({(ex2)}, 3r),nil))))),3);  
  //@ mod_plus_le(length(cvs), length(cvs)-1);
  //@ mod_plus_le(length(cvs), 1);
  //@ mod_plus(length(cvs), 1);
  //@ mod_plus_le(length(cvs), 3);
  
  pickup(dp,0);
  pickup(dp,2);
  putdown(dp,0);
  putdown(dp,2);
}