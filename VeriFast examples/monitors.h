#ifndef MONITORS_H
#define MONITORS_H

#include "obligations.h"
#include "bags.gh"

struct mutex;
struct cvar;

typedef struct mutex *mutex;
typedef struct cvar *cvar;

/*@
fixpoint mutex mutex_of(void* cvar);
fixpoint predicate(fixpoint(void*, unsigned int), fixpoint(void*, unsigned int)) inv(struct mutex* mutex);
@*/

/*@
predicate umutex(mutex mutex; fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot);
predicate mutex(mutex mutex;);
predicate mutex_held(mutex mutex; real frac, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot);
predicate ucond(cvar cvar;);
predicate cond(cvar cvar; predicate() M, list<void*> M');
predicate create_mutex_ghost_args(pair<list<void*>, real> wlevel) = true;
predicate init_mutex_ghost_args(predicate(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) lockinv) = true;
predicate create_cvar_ghost_args(pair<list<void*>, real> level, bool more_obligations, option< pair<list<void*>, real> > partner_level) = true;
predicate init_cvar_ghost_args(mutex mutex, predicate() transfer, list<void*> obs_transfer) = true;
predicate mutex_inv(mutex mutex; predicate(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) lockinv) = lockinv == inv(mutex);
@*/

/*@
typedef lemma void invariant_preserved(struct mutex *m, predicate(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) p, list<void*> O1, list<void*> O2, predicate() res)();
    requires mutex_held(m, ?f, ?Wt1, ?Ot1) &*& mutex_inv(m, p) &*& p(Wt1,Ot1) &*& obs(O1);
    ensures mutex_held(m, f, ?Wt2, ?Ot2) &*& mutex_inv(m, p) &*& p(Wt2,Ot2) &*& obs(O2) &*& res();

lemma void run_in_cs(struct mutex *m);
  requires [?f]mutex(m) &*& obs(?O1) &*& mutex_inv(m, ?p) &*& is_invariant_preserved(?ip,m,p,O1,?O2,?res);
  ensures [f]mutex(m) &*& obs(O2) &*& res() &*& is_invariant_preserved(ip,m,p,O1,O2,res);

typedef lemma void spurious(predicate(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) p, predicate() trn, cvar cvar)();
    requires p(?Wt,?Ot) &*& 0 < Wt(cvar);
    ensures p(fdec(Wt,cvar),Ot) &*& trn();
@*/



/*@
lemma void init_mutex(mutex mutex);
    requires umutex(mutex, ?Wt, ?Ot) &*& init_mutex_ghost_args(?p) &*& p(Wt,Ot);
    ensures mutex(mutex) &*& inv(mutex)==p;

lemma void init_cvar(cvar cvar);
    requires ucond(cvar) &*& init_cvar_ghost_args(?mutex, ?transferred_permissions, ?transferred_obligations); 
    ensures cond(cvar, transferred_permissions, transferred_obligations) &*& mutex_of(cvar) == mutex;

lemma void g_chrgu(cvar cvar);
    requires umutex(mutex_of(cvar), ?Wt, ?Ot) &*& obs(?O);
    ensures umutex(mutex_of(cvar), Wt, finc(Ot,cvar)) &*& obs(cons(cvar,O));

lemma void g_chrgu'(int n, cvar cvar);
    requires umutex(mutex_of(cvar), ?Wt, ?Ot) &*& obs(?O) &*& n >= 0;
    ensures umutex(mutex_of(cvar), Wt, finc'(n,Ot,cvar)) &*& obs(ntimes_list(nat_of_int(n),cvar,O));

lemma void g_chrgl(cvar cvar);
    requires mutex_held(mutex_of(cvar), ?f, ?Wt, ?Ot) &*& obs(?O);
    ensures mutex_held(mutex_of(cvar), f, Wt, finc(Ot,cvar)) &*& obs(cons(cvar,O));

lemma void g_dischu(cvar cvar);
    requires umutex(mutex_of(cvar), ?Wt, ?Ot) &*& obs(?O) &*& safe_obs(cvar,Wt,fdec(Ot,cvar)) == true;
    ensures umutex(mutex_of(cvar), Wt, fdec(Ot,cvar)) &*& obs(remove(cvar,O));

lemma void g_dischl(cvar cvar);
    requires mutex_held(mutex_of(cvar), ?f, ?Wt, ?Ot) &*& obs(?O) &*& safe_obs(cvar,Wt,fdec(Ot,cvar)) == true;
    ensures mutex_held(mutex_of(cvar), f, Wt, fdec(Ot,cvar)) &*& obs(remove(cvar,O));

lemma void cond_frac(cvar cvar);
  requires cond(cvar, ?M, ?M') &*& [?f]cond (cvar, ?M1, ?M1') &*& 0 < f;
  ensures false;        

        
lemma void g_Ot_isbag(mutex mutex, cvar cvar);
    requires mutex_held(mutex, ?f, ?Wt, ?Ot);
    ensures mutex_held(mutex, f, Wt, Ot) &*& Ot(cvar) >= 0;
@*/

mutex create_mutex();
    //@ requires create_mutex_ghost_args(?wlevel);
    //@ ensures result != 0 &*& umutex(result, empb ,empb) &*& mutex_of(result)==result &*& level(result) == wlevel &*& level'(result) == none &*& P(result) == false;
    
void mutex_acquire(mutex mutex);
    //@ requires [?f]mutex(mutex) &*& obs(?O) &*& mutex_inv(mutex, ?p) &*& no_cycle(mutex,O) == true;
    //@ ensures mutex_held(mutex, f, ?Wt, ?Ot) &*& p(Wt,Ot) &*& obs(cons(mutex,O)) &*& true;

void mutex_release(mutex mutex);
    //@ requires mutex_held(mutex, ?f, ?Wt, ?Ot) &*& mutex_inv(mutex,?p) &*& p(Wt, Ot) &*& obs(?O);
    //@ ensures [f]mutex(mutex) &*& obs(remove(mutex,O));

cvar create_cvar();
    //@ requires create_cvar_ghost_args(?level, ?more_obligations, ?partner_level); 
    //@ ensures ucond(result) &*& level(result) == level &*& P(result) == more_obligations &*& level'(result) == partner_level;

void cvar_wait(cvar cvar, mutex mutex);
    /*@ requires obs(?O) &*& [?fc]cond(cvar, ?M, ?M') &*& mutex_held(mutex, ?f, ?Wt, ?Ot) &*& mutex_inv(mutex,?inv) &*& inv(finc(Wt,cvar), Ot) &*& 
          mutex_of(cvar) == mutex &*& no_cycle(cvar,remove(mutex,O))==true &*& no_cycle(mutex,append(M',remove(mutex,O))) == true &*& safe_obs(cvar,finc(Wt,cvar),Ot)==true ; @*/
    //@ ensures [fc]cond(cvar, M, M') &*& mutex_held(mutex, f, ?Wt', ?Ot') &*& inv(Wt', Ot') &*& obs(append(M',O)) &*& M();

void cvar_spwk_wait(cvar cvar, mutex mutex);
    /*@ requires obs(?O) &*& [?fc]cond(cvar, ?M, ?M') &*& mutex_held(mutex, ?f, ?Wt, ?Ot) &*& mutex_inv(mutex,?inv) &*& inv(finc(Wt,cvar), Ot) &*& is_spurious()(_, inv, M, cvar) &*&
          mutex_of(cvar) == mutex &*& no_cycle(cvar,remove(mutex,O))==true &*& no_cycle(mutex,append(M',remove(mutex,O))) == true &*& safe_obs(cvar,finc(Wt,cvar),Ot)==true ; @*/
    //@ ensures [fc]cond(cvar, M, M') &*& mutex_held(mutex, f, ?Wt', ?Ot') &*& inv(Wt', Ot') &*& obs(append(M',O)) &*& M();

void cvar_signal(cvar cvar);
    //@ requires obs(?O) &*& [?fc]cond(cvar, ?M, ?M') &*& mutex_held(?mutex, ?f, ?Wt, ?Ot) &*& (Wt(cvar) <= 0 ? true : M()) &*& (0 < Wt(cvar) || M' == nil);
    //@ ensures obs(minus(O,M')) &*& [fc]cond(cvar, M, M') &*& mutex_held(mutex, f, fdec(Wt,cvar), Ot);

void cvar_broadcast(cvar cvar);
    //@ requires [?fc]cond(cvar, ?M, nil) &*& mutex_held(?mutex, ?f, ?Wt, ?Ot) &*& n_times(Wt(cvar),M);
    //@ ensures [fc]cond(cvar, M, nil) &*& mutex_held(mutex, f, removeAll(Wt,cvar), Ot);

#endif    
