#ifndef THREADS_H
#define THREADS_H

#include "obligations.h"

/*@
predicate_family thread_run_data(void* thread_run)(list<void*> O, void *data);
@*/

typedef void thread_run(void* data);
    //@ requires thread_run_data(this)(?O, data) &*& obs(O);
    //@ ensures obs(nil);

void thread_start(void* run, void* data);
    //@ requires is_thread_run(run) == true &*& thread_run_data(run)(?tobs, data) &*& obs(?obs);
    //@ ensures obs(minus(obs,tobs));
            
#endif    
