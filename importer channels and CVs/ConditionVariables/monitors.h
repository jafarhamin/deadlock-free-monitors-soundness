/*
  Monitors
*/

#ifndef MONITORS_H
#define MONITORS_H

#include "levels.h"
//@#include "ghost_cells.gh"

struct mutex;
struct condvar;

typedef struct mutex *mutex;
typedef struct condvar *condvar;

/*@
fixpoint mutex mutex_of(void* condvar);
fixpoint predicate() M(condvar condvar);
fixpoint list<void*> M'(condvar condvar);
fixpoint predicate(fixpoint(void*, unsigned int), fixpoint(void*, unsigned int)) inv(struct mutex* mutex);
@*/

/*@
predicate umutex(mutex mutex; fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot);

predicate mutex(mutex mutex;);

predicate mutex_held(mutex mutex; real frac, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot);

predicate ucond(condvar condvar;);

predicate cond(condvar condvar;);

predicate create_mutex_ghost_args(pair<list<void*>, real> wlevel) = true;

predicate init_mutex_ghost_args(predicate(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) lockinv) = true;

predicate create_condvar_ghost_args(pair<list<void*>, real> wlevel) = true;

predicate init_condvar_ghost_args(mutex mutex, predicate() Mv, list<void*> M'v) = true;

predicate mutex_inv(mutex mutex; predicate(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) lockinv) = lockinv == inv(mutex);

predicate MP(condvar condvar, predicate() condvarp) = M(condvar) == condvarp;
predicate M'P(condvar condvar, list<void*> O) = M'(condvar) == O;
@*/

/*@
predicate no_transfer() = true;

predicate n_times(int n, predicate() p) =
  n <= 0 ? true : p() &*& n_times(n-1,p);

lemma void n_times_no_transfer(int n);
  requires true;
  ensures n_times(n,no_transfer);  
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
    requires umutex(mutex, ?Wt, ?Ot) &*& init_mutex_ghost_args(?p) &*& p(Wt,Ot);
    ensures mutex(mutex) &*& inv(mutex)==p;

lemma void init_condvar(condvar condvar);
    requires ucond(condvar) &*& init_condvar_ghost_args(?mutex,?transfer,?obs_transfer); 
    ensures cond(condvar) &*& mutex_of(condvar) == mutex &*& M(condvar) == transfer &*& M'(condvar) == obs_transfer;

lemma void g_chrgu(condvar condvar);
    requires umutex(mutex_of(condvar), ?Wt, ?Ot) &*& obs(?O);
    ensures umutex(mutex_of(condvar), Wt, finc(Ot,condvar)) &*& obs(cons(condvar,O));

lemma void g_chrgu'(int n, condvar condvar);
    requires umutex(mutex_of(condvar), ?Wt, ?Ot) &*& obs(?O) &*& n >= 0;
    ensures umutex(mutex_of(condvar), Wt, finc'(n,Ot,condvar)) &*& obs(ntimes_list(nat_of_int(n),condvar,O));// obs(cons(condvar,O));

lemma void g_chrgl(condvar condvar);
    requires mutex_held(mutex_of(condvar), ?f, ?Wt, ?Ot) &*& obs(?O);
    ensures mutex_held(mutex_of(condvar), f, Wt, finc(Ot,condvar)) &*& obs(cons(condvar,O));

lemma void g_dischu(condvar condvar);
    requires umutex(mutex_of(condvar), ?Wt, ?Ot) &*& obs(?O) &*& enfo(condvar,Wt,fdec(Ot,condvar)) == true;// &*& 0 < Ot(condvar);
    ensures umutex(mutex_of(condvar), Wt, fdec(Ot,condvar)) &*& obs(remove(condvar,O));

lemma void g_dischl(condvar condvar);
    requires mutex_held(mutex_of(condvar), ?f, ?Wt, ?Ot) &*& obs(?O) &*& enfo(condvar,Wt,fdec(Ot,condvar)) == true;// &*& 0 < Ot(condvar);
    ensures mutex_held(mutex_of(condvar), f, Wt, fdec(Ot,condvar)) &*& obs(remove(condvar,O));
    
lemma void g_Ot_isbag(mutex mutex, condvar condvar);
    requires mutex_held(mutex, ?f, ?Wt, ?Ot);
    ensures mutex_held(mutex, f, Wt, Ot) &*& Ot(condvar) >= 0;

lemma void cond_plus(condvar cv)
  requires [?f1]cond(cv) &*& [?f2]cond(cv);
  ensures [f1+f2]cond(cv);
{}

lemma void cond_frac(struct condvar *c1);
  requires cond(c1) &*& [?f]cond (c1) &*& 0 < f;
  ensures false;        

lemma void u_cond_frac(struct condvar *c1);
  requires ucond(c1) &*& [?f]cond(c1);
  ensures false;        

lemma void ucond_frac(struct condvar *c1);
  requires ucond(c1) &*& ucond (c1);
  ensures false;        

lemma void cond_frac'(struct condvar *c1);
  requires [?f]cond(c1);
  ensures [f]cond(c1) &*& 0 < f &*& f <= 1;        
@*/

mutex create_mutex();
    //@ requires create_mutex_ghost_args(?wlevel);
    //@ ensures result != 0 &*& umutex(result, empb ,empb) &*& mutex_of(result)==result &*& wait_level_of(result) == wlevel;
    
void mutex_acquire(mutex mutex);
    //@ requires [?f]mutex(mutex) &*& obs(?O) &*& mutex_inv(mutex, ?p) &*& w_level_below_all(mutex,O) == true;
    //@ ensures mutex_held(mutex, f, ?Wt, ?Ot) &*& p(Wt,Ot) &*& obs(cons(mutex,O)) &*& true;

void mutex_release(mutex mutex);
    //@ requires mutex_held(mutex, ?f, ?Wt, ?Ot) &*& mutex_inv(mutex,?p) &*& p(Wt, Ot) &*& obs(?O);
    //@ ensures [f]mutex(mutex) &*& obs(remove(mutex,O));

condvar create_condvar();
    //@ requires create_condvar_ghost_args(?wlevel); 
    //@ ensures ucond(result) &*& wait_level_of(result) == wlevel;

void condvar_wait(condvar condvar, mutex mutex);
    /*@ requires [?fc]cond(condvar) &*& mutex_held(mutex, ?f, ?Wt, ?Ot) &*& mutex_inv(mutex,?inv) &*& inv(finc(Wt,condvar), Ot) &*& MP(condvar,?trn) &*& M'P(condvar,?O') &*& obs(?O) &*&
                 w_level_below_all(condvar,remove(mutex,O))==true &*& w_level_below_all(mutex,append(O',remove(mutex,O))) == true &*& enfo(condvar,finc(Wt,condvar),Ot)==true;@*/
    //@ ensures [fc]cond(condvar) &*& mutex_held(mutex, f, ?Wt', ?Ot') &*& inv(Wt', Ot') &*& obs(append(O',O)) &*& trn();

void condvar_signal(condvar condvar);
    //@ requires obs(?O) &*& [?fc]cond(condvar) &*& mutex_held(?mutex, ?f, ?Wt, ?Ot) &*& MP(condvar,?transfer) &*& M'P(condvar,?O') &*& (Wt(condvar) <= 0 ? true : transfer()) &*& (0 < Wt(condvar) || O' == nil);
    //@ ensures obs(minus(O,O')) &*& [fc]cond(condvar) &*& mutex_held(mutex, f, fdec(Wt,condvar), Ot);

void condvar_broadcast(condvar condvar);
    //@ requires [?fc]cond(condvar) &*& mutex_held(?mutex, ?f, ?Wt, ?Ot) &*& MP(condvar,no_transfer) &*& M'P(condvar,nil);
    //@ ensures [fc]cond(condvar) &*& mutex_held(mutex, f, removeAll(Wt,condvar), Ot);

#endif    
