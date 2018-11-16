/*
  Threads
*/

#ifndef THREADS_H
#define THREADS_H

#include "levels.h"

/*@
predicate_family thread_run_data(void* thread_run)(list<void*> O, list<void*> R, void *data);
@*/

typedef void thread_run(void* data);
    //@ requires thread_run_data(this)(?O, ?R, data) &*& obs(O, R);
    //@ ensures obs(nil, nil);

void thread_start(void* run, void* data);
    //@ requires is_thread_run(run) == true &*& thread_run_data(run)(?tobs, ?tims, data) &*& obs(?obs, ?ims);
    //@ ensures obs(minus(obs,tobs), minus(ims,tims));
            
#endif    
