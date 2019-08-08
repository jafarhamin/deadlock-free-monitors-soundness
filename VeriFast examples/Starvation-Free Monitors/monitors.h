#ifndef MONITORS_H
#define MONITORS_H

#include "levels_with_importers.h"
//@#include "ghost_cells.gh"


struct mutex;
struct condvar;

typedef struct mutex *mutex;
typedef struct condvar *condvar;

/*@
fixpoint mutex mutex_of(void* condvar);
fixpoint predicate(fixpoint(void*, unsigned int), fixpoint(void*, unsigned int), list< pair<void*, int> > It) inv(struct mutex* mutex);
@*/

/*@
predicate umutex(mutex mutex; fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot, list< pair<void*, int> > It);

predicate mutex(mutex mutex;);

predicate mutex_held(mutex mutex; real frac, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot, list< pair<void*, int> > It);

predicate ucond(condvar condvar;);

predicate cond(condvar condvar; predicate() M, list<void*> M');

predicate create_mutex_ghost_args(real wlevel) = true;

predicate init_mutex_ghost_args(predicate(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot, list< pair<void*, int> > It) lockinv) = true;

predicate create_condvar_ghost_args(real wlevel) = true;

predicate init_condvar_ghost_args(mutex mutex, predicate() M, list<void*> M') = true;

predicate mutex_inv(mutex mutex; predicate(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot, list< pair<void*, int> > It) lockinv) = lockinv == inv(mutex);

predicate Id(int id) = true;
@*/

/*@
predicate no_transfer() = true;
@*/

/*@
fixpoint int inc(fixpoint(void*, int) f, void* x, void* y){
    return x==y ? f(x)+1 : f(y);
}

fixpoint fixpoint(void*, unsigned int) finc(fixpoint(void*, unsigned int) f, void* x){
    return (inc)(f)(x);
}

fixpoint int inc'(int i, fixpoint(void*, int) f, void* x, void* y){
    return x==y ? f(x) + i : f(y);
}

fixpoint fixpoint(void*, unsigned int) finc'(int i, fixpoint(void*, unsigned int) f, void* x){
    return (inc')(i,f)(x);
}

fixpoint int dec1(int x){
  return x > 0 ? x-1 : x;
}

fixpoint int dec(fixpoint(void*, unsigned int) f, void* x, void* y){
    return x==y ? dec1(f(x)) : f(y);
}

fixpoint fixpoint(void*, int) fdec(fixpoint(void*, unsigned int) f, void* x){
    return (dec)(f)(x);
}

fixpoint int empb(void* x){
    return 0;
}

fixpoint int rma(fixpoint(void*, unsigned int) f, void* x, void* y){
    return x==y ? 0 : f(y);
}

fixpoint fixpoint(void*, int) removeAll<t>(fixpoint(void*, unsigned int) f, void* x) {
    return (rma)(f)(x); 
}

fixpoint fixpoint(void*, int) finc_bool(bool b, fixpoint(void*, int) Ot, void* v){
  return b ? finc(Ot,v) : Ot;
}
@*/

/*@
lemma void init_mutex(mutex mutex);
    requires umutex(mutex, ?Wt, ?Ot, ?It) &*& init_mutex_ghost_args(?p) &*& p(Wt,Ot,It);
    ensures mutex(mutex) &*& inv(mutex)==p;

lemma void init_condvar(condvar condvar);
    requires ucond(condvar) &*& init_condvar_ghost_args(?mutex,?M,?M'); 
    ensures cond(condvar, M, M') &*& mutex_of(condvar) == mutex;

lemma void g_chrgu(condvar condvar);
    requires umutex(mutex_of(condvar), ?Wt, ?Ot, ?It) &*& obs(?O);
    ensures umutex(mutex_of(condvar), Wt, finc(Ot,condvar), It) &*& obs(cons(condvar,O));

lemma void g_chrgu'(int n, condvar condvar);
    requires umutex(mutex_of(condvar), ?Wt, ?Ot, ?It) &*& obs(?O) &*& n >= 0;
    ensures umutex(mutex_of(condvar), Wt, finc'(n,Ot,condvar), It) &*& obs(ntimes_list(nat_of_int(n),condvar,O));

lemma void g_chrgl(condvar condvar);
    requires mutex_held(mutex_of(condvar), ?f, ?Wt, ?Ot, ?It) &*& obs(?O);
    ensures mutex_held(mutex_of(condvar), f, Wt, finc(Ot,condvar), It) &*& obs(cons(condvar,O));

lemma void g_dischu(condvar condvar);
    requires umutex(mutex_of(condvar), ?Wt, ?Ot, ?It) &*& obs(?O) &*& enfo(condvar,Wt,fdec(Ot,condvar)) == true;
    ensures umutex(mutex_of(condvar), Wt, fdec(Ot,condvar), It) &*& obs(remove(condvar,O));

lemma void g_dischl(condvar condvar);
    requires mutex_held(mutex_of(condvar), ?f, ?Wt, ?Ot, ?It) &*& obs(?O) &*& enfo(condvar,Wt,fdec(Ot,condvar)) == true;
    ensures mutex_held(mutex_of(condvar), f, Wt, fdec(Ot,condvar), It) &*& obs(remove(condvar,O));
    
lemma void g_Ot_isbag(mutex mutex, condvar condvar);
    requires mutex_held(mutex, ?f, ?Wt, ?Ot, ?It);
    ensures mutex_held(mutex, f, Wt, Ot, It) &*& Ot(condvar) >= 0;

predicate publishable(predicate() p1, predicate() p2);
@*/

mutex create_mutex();
    //@ requires create_mutex_ghost_args(?wlevel);
    //@ ensures result != 0 &*& umutex(result, empb ,empb, nil) &*& mutex_of(result)==result &*& level_of(result) == wlevel;
    
void mutex_acquire(mutex mutex);
    //@ requires [?f]mutex(mutex) &*& obs(?O) &*& mutex_inv(mutex, ?p) &*& object_lt_objects(mutex,O) == true;
    //@ ensures mutex_held(mutex, f, ?Wt, ?Ot, ?It) &*& p(Wt,Ot,It) &*& obs(cons(mutex,O)) &*& true;

void mutex_release(mutex mutex);
    //@ requires mutex_held(mutex, ?f, ?Wt, ?Ot, ?It) &*& mutex_inv(mutex,?p) &*& p(Wt, Ot, It) &*& obs(?O);
    //@ ensures [f]mutex(mutex) &*& obs(remove(mutex,O));

condvar create_condvar();
    //@ requires create_condvar_ghost_args(?wlevel); 
    //@ ensures ucond(result) &*& level_of(result) == wlevel;

void condvar_wait(condvar condvar, mutex mutex);
    /*@ requires [?fc]cond(condvar,?M,?M') &*& mutex_held(mutex, ?f, ?Wt, ?Ot, ?It) &*& mutex_inv(mutex,?inv) &*& Id(?id) &*& inv(finc(Wt,condvar), Ot, cons(pair(condvar,id),It)) &*& obs(?O) &*&
                 object_lt_objects(condvar,remove(mutex,O))==true &*& object_lt_objects(mutex,append(M',remove(mutex,O))) == true &*& enfo(condvar,finc(Wt,condvar),Ot)==true;@*/
    /*@ ensures [fc]cond(condvar,M,M') &*& M() &*& inv(?Wt', ?Ot', ?It') &*&
        mem(pair(condvar,id), It') ? mutex_held(mutex, f, Wt', Ot', remove(pair(condvar,id),It')) &*& obs(O) : 
        mutex_held(mutex, f, Wt', Ot', It') &*& obs(append(M',O)); @*/

void condvar_signal(condvar condvar);
    //@ requires obs(?O) &*& [?fc]cond(condvar,?M,?M') &*& mutex_held(?mutex, ?f, ?Wt, ?Ot, ?It) &*& (Wt(condvar) <= 0 ? true : M()) &*& (0 < Wt(condvar) || M' == nil);
    //@ ensures obs(minus(O,M')) &*& [fc]cond(condvar,M,M') &*& mutex_held(mutex, f, fdec(Wt,condvar), Ot, It);

void condvar_broadcast(condvar condvar);
    //@ requires obs(?O) &*& [?fc]cond(condvar,?M,?M') &*& mutex_held(?mutex, ?f, ?Wt, ?Ot, ?It) &*& Id(?id) &*& publishable(?P,M) &*& P();
    //@ ensures obs(minus(O, mem(pair(condvar,id), It) ? M' : nil)) &*& [fc]cond(condvar,M,M') &*& mutex_held(mutex, f, removeAll(Wt,condvar), Ot, remove(pair(condvar,id),It));

#endif    
