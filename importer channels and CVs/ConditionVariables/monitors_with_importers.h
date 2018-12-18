/*
  Monitors
*/

#ifndef MONITORS_WITH_IMPORTERS_H
#define MONITORS_WITH_IMPORTERS_H

#include "levels_with_importers.h"
//@#include "ghost_cells.gh"

struct mutex;
struct condvar;

typedef struct mutex *mutex;
typedef struct condvar *condvar;

/*@
fixpoint mutex mutex_of(void* condvar);

fixpoint predicate(fixpoint(void*, unsigned int), fixpoint(void*, unsigned int), fixpoint(void*, unsigned int)) inv(struct mutex* mutex);
@*/

/*@
predicate umutex(mutex mutex; fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot, fixpoint(void*, unsigned int) It);

predicate mutex(mutex mutex;);

predicate mutex_held(mutex mutex; real frac, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot, fixpoint(void*, unsigned int) It);

predicate ucond(condvar condvar;);

predicate cond(condvar condvar; predicate() M, list<void*> M');

predicate create_mutex_ghost_args(real wlevel) = true;

predicate init_mutex_ghost_args(predicate(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot, fixpoint(void*, unsigned int) Rt) lockinv) = true;

predicate create_condvar_ghost_args(real wlevel) = true;

predicate init_condvar_ghost_args<T>(mutex mutex, predicate() transfer, list<void*> obs_transfer) = true;

predicate mutex_inv(mutex mutex; predicate(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot, fixpoint(void*, unsigned int) It) lockinv) = lockinv == inv(mutex);
@*/

/*@
typedef lemma void invariant_preserved(struct mutex *m, predicate(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot, fixpoint(void*, unsigned int) It) p, list<void*> O1, list<void*> O2, list<void*> R, predicate() res)();
    requires mutex_held(m, ?f, ?Wt1, ?Ot1, ?It1) &*& mutex_inv(m, p) &*& p(Wt1,Ot1,It1) &*& obs(O1,R);
    ensures mutex_held(m, f, ?Wt2, ?Ot2, ?It2) &*& mutex_inv(m, p) &*& p(Wt2,Ot2,It2) &*& obs(O2,R) &*& res();

lemma void run_in_cs(struct mutex *m);
  requires [?f]mutex(m) &*& obs(?O1,?R1) &*& mutex_inv(m, ?p) &*& is_invariant_preserved(?ip,m,p,O1,?O2,R1,?res);
  ensures [f]mutex(m) &*& obs(O2,R1) &*& res() &*& is_invariant_preserved(ip,m,p,O1,O2,R1,res);
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
    requires umutex(mutex_of(condvar), ?Wt, ?Ot, ?It) &*& obs(?O, ?R);
    ensures umutex(mutex_of(condvar), Wt, finc(Ot,condvar), It) &*& obs(cons(condvar,O), R);

lemma void g_chrgu'(int n, condvar condvar);
    requires umutex(mutex_of(condvar), ?Wt, ?Ot, ?It) &*& obs(?O, ?R) &*& n >= 0;
    ensures umutex(mutex_of(condvar), Wt, finc'(n,Ot,condvar), It) &*& obs(ntimes_list(nat_of_int(n),condvar,O), R);

lemma void g_chrgl(condvar condvar);
    requires mutex_held(mutex_of(condvar), ?f, ?Wt, ?Ot, ?It) &*& obs(?O, ?R);
    ensures mutex_held(mutex_of(condvar), f, Wt, finc(Ot,condvar), It) &*& obs(cons(condvar,O), R);

lemma void g_dischu(condvar condvar);
    requires umutex(mutex_of(condvar), ?Wt, ?Ot, ?It) &*& obs(?O, ?R) &*& enfo(condvar,Wt,fdec(Ot,condvar))==true; //safe_obs(condvar,Wt,fdec(Ot,condvar)) == true;// &*& 0 < Ot(condvar);
    ensures umutex(mutex_of(condvar), Wt, fdec(Ot,condvar), It) &*& obs(remove(condvar,O), R);

lemma void g_dischl(condvar condvar);
    requires mutex_held(mutex_of(condvar), ?f, ?Wt, ?Ot, ?It) &*& obs(?O, ?R) &*& enfo(condvar,Wt,fdec(Ot,condvar)) == true;// &*& 0 < Ot(condvar);
    ensures mutex_held(mutex_of(condvar), f, Wt, fdec(Ot,condvar), It) &*& obs(remove(condvar,O), R);
    
lemma void g_Ot_isbag(mutex mutex, condvar condvar);
    requires mutex_held(mutex, ?f, ?Wt, ?Ot, ?It);
    ensures mutex_held(mutex, f, Wt, Ot, It) &*& Ot(condvar) >= 0;

lemma void cond_plus(condvar cv)
  requires [?f1]cond(cv,?M,?M') &*& [?f2]cond(cv,M,M');
  ensures [f1+f2]cond(cv,M,M');
{}

lemma void cond_frac(struct condvar *c1);
  requires cond(c1,?M,?M') &*& [?f]cond (c1,M,M') &*& 0 < f;
  ensures false;        

lemma void u_cond_frac(struct condvar *c1);
  requires ucond(c1) &*& [?f]cond(c1,?M,?M');
  ensures false;        

lemma void ucond_frac(struct condvar *c1);
  requires ucond(c1) &*& ucond (c1);
  ensures false;        

lemma void cond_frac'(struct condvar *c1);
  requires [?f]cond(c1,?M,?M');
  ensures [f]cond(c1,M,M') &*& 0 < f &*& f <= 1;        
  
lemma void neq_cond_mutex(struct condvar *v, void* m);
  requires [?f]cond(v,?M,?M') &*& umutex(m,?Wt,?Ot,?It);
  ensures [f]cond(v,M,M') &*& umutex(m,Wt,Ot,It) &*& (void*) v != m;     
@*/

mutex create_mutex();
    //@ requires create_mutex_ghost_args(?wlevel);
    //@ ensures result != 0 &*& umutex(result, empb ,empb, empb) &*& mutex_of(result)==result &*& level_of(result) == wlevel;
    
void mutex_acquire(mutex mutex);
    //@ requires [?f]mutex(mutex) &*& obs(?O, ?R) &*& mutex_inv(mutex, ?p) &*& object_lt_objects(mutex,O) == true;
    //@ ensures mutex_held(mutex, f, ?Wt, ?Ot, ?It) &*& p(Wt,Ot,It) &*& obs(cons(mutex,O), R);

void mutex_release(mutex mutex);
    //@ requires mutex_held(mutex, ?f, ?Wt, ?Ot, ?It) &*& mutex_inv(mutex,?p) &*& p(Wt, Ot, It) &*& obs(?O, ?R);
    //@ ensures [f]mutex(mutex) &*& obs(remove(mutex,O), R);

condvar create_condvar();
    //@ requires create_condvar_ghost_args(?wlevel); 
    //@ ensures ucond(result) &*& level_of(result) == wlevel;

void condvar_wait(condvar condvar, mutex mutex);
    /*@ requires [?fc]cond(condvar,?M,?M') &*& mutex_held(mutex, ?f, ?Wt, ?Ot, ?It) &*& mutex_inv(mutex,?inv) &*& inv(finc(Wt,condvar), Ot, It) &*& obs(?O, ?R) &*&
                 object_lt_objects(condvar,remove(mutex,O))==true &*& object_lt_objects(mutex,remove(mutex,O)) == true &*& enfo(condvar,finc(Wt,condvar),Ot)==true; @*/
    //@ ensures [fc]cond(condvar,M,M') &*& mutex_held(mutex, f, ?Wt', ?Ot', ?It') &*& inv(Wt', Ot', It') &*& obs(O, R) &*& M();

void condvar_signal(condvar condvar);
    //@ requires obs(?O, ?R) &*& [?fc]cond(condvar,?M,?M') &*& mutex_held(?mutex, ?f, ?Wt, ?Ot, ?It) &*& (Wt(condvar) <= 0 ? true : M());
    //@ ensures obs(O, R) &*& [fc]cond(condvar,M,M') &*& mutex_held(mutex, f, fdec(Wt,condvar), Ot, It);

void condvar_broadcast(condvar condvar);
    //@ requires [?fc]cond(condvar,no_transfer,nil) &*& mutex_held(?mutex, ?f, ?Wt, ?Ot, ?It);
    //@ ensures [fc]cond(condvar,no_transfer,nil) &*& mutex_held(mutex, f, removeAll(Wt,condvar), Ot, It);

#endif    
