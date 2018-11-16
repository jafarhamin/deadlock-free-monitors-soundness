# include "stdlib.h"
# include "monitors.h"
# include "dining_philosophers.h"
//@ #include "ghost_counters.gh"

enum State {Thinking, Hungry, Eating}; 

struct philosopher{
  enum State state;
  condvar cv;
  struct philosopher* next;
  struct philosopher* previous;  
  int number;
};

typedef struct philosopher *philosopher;

struct dining_philosophers{
  philosopher phs;
  mutex m;
  int size;
}; 

/*@
fixpoint int st(enum State state){
  return state == Eating ? 1 : 0;
}

fixpoint bool nin<t>(list<t> l, t x){
  return !mem(x,l);
}

predicate cv_phs(philosopher ph, philosopher ph2, list<condvar> cvs) = 
  [_]ph->cv |-> ?cv &*&
  [_]cond(cv) &*&  
  [_]ph->next |-> ?next &*&
  [_]ph->previous |-> ?previous &*&
  [_]next->previous |-> ph &*&
  [_]previous->next |-> ph &*&
  ph != next &*& ph != previous &*& next != previous &*&  
  cvs == cons(cv,?cvs0) &*&
  mem(cv,cvs0) == false &*&
  ph == ph2 ? cvs0 == nil :  
  cv_phs(next, ph2, cvs0);

predicate philosopher(philosopher ph, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot, mutex m, philosopher previous, philosopher next) =
  ph->number |-> ?number &*&
  [_]ph->cv |-> ?cv &*&
  cv != (void*)m &*&
  mutex_of(cv) == m &*&
  [_]ph->next |-> next &*&
  [_]ph->previous |-> previous &*&
  [_]next->cv |-> ?next_cv &*&
  [_]previous->cv |-> ?previous_cv &*&    
  [1/3]next->state |-> ?next_state &*& 
  [1/3]ph->state |-> ?state &*&   
  [1/3]previous->state |-> ?previous_state &*&
  [_]next->previous |-> ph &*&
  [_]previous->next |-> ph &*&
  ph != next &*& ph != previous &*& next != previous &*&
  [2/3]cond(cv) &*& M(cv) == no_transfer &*&
  M'(cv) == cons(previous_cv,cons(next_cv,nil)) &*&
  wait_level_lt(wait_level_of(m), wait_level_of(cv)) == true &*&
  (state == Hungry ? 0 < Wt(cv) : Wt(cv) <= 0) &*&
  0 <= Wt(cv) &*& Wt(cv) <= 1 &*&
  (Wt(cv) <= 0 || 0 < st(previous_state) + st(next_state)) &*&
  st(previous_state) + st(next_state) <= Ot(cv);

predicate philosophers(philosopher ph, philosopher ph2, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot, mutex m) = 
  [_]ph->previous |-> ?previous &*&
  philosopher(ph, Wt, Ot, m, previous, ?next) &*&
  ph == ph2 ? true :  
  philosophers(next,ph2,Wt,Ot,m);

predicate_ctor ph_inv(dining_philosophers dph)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) = 
  [_]dph->m |-> ?m &*&  
  [_]dph->size |-> ?size &*&  
  [_]dph->phs |-> ?ph &*&
  [_]ph->previous |-> ?previous &*&
  philosophers(ph,previous,Wt,Ot,m);
  
predicate dphs(dining_philosophers dph, list<void*> cvs) =
  [_]dph->m |-> ?m &*& 
  [_]dph->size |-> ?size &*& 
  [_]dph->phs |-> ?phs &*&
  [_]phs->previous |-> ?phs_previous &*& 
  cv_phs(phs,phs_previous,cvs) &*& 
  1 < length(cvs) &*& 
  inv(m) == ph_inv(dph) &*&
  length(cvs) == size &*& 
  wait_level_of(m) == pair({new_dining_philosophers}, 0r) &*&
  [_]mutex(m);

predicate in_list(philosopher ph, philosopher ph2, philosopher phs) =
  ph == phs ? true : ph != ph2 &*& 
  [_]ph->next |-> ?next &*&
  [_]ph->previous |-> ?previous &*&
  [_]next->previous |-> ph &*&
  [_]previous->next |-> ph &*&
  ph != next &*& ph != previous &*& next != previous &*&
  in_list(next, ph2, phs);

lemma void nth_cons<t> (list<t> xs, t x, int i)
  requires 0 <= i &*& i < length(xs) &*& xs != nil;
  ensures nth(i,xs) == nth(i+1,cons(x,xs));
{
  switch (xs){
    case nil:
    case cons(x0,xs0):
  }  
}

lemma void drop_index<t> (list<t> l, int i, int j)
  requires j <= i &*& 0 <= j &*& j < length(l) &*& i < length(l);
  ensures nth(i-j,drop(j,l)) == nth(i,l);
{
  switch (l){
    case nil:
    case cons(x,xs): 
      if (j==0){
      }
      else{
        drop_index(xs,i-1,j-1);
        assert nth(i-j,drop(j-1,xs)) == nth(i-1,xs);
        assert nth(i-1,xs) == nth(i,l);
      }
  }
}

lemma void mem_drop0<t> (list<t> l, t x, int n)
  requires 0 <= n &*& mem(x, drop(n,l)) == true;
  ensures mem(x, l) == true;
{
  switch (l){
    case nil:
    case cons(x0,xs0):
      if (n==0){
      }
      else{
        mem_drop0(xs0,x,n-1);
      }
  }
}

lemma void mem_drop<t> (list<t> l, t x, int n, int m)
  requires 0 <= m &*& m <= n &*& mem(x, drop(n,l)) == true;
  ensures mem(x, drop(m,l)) == true;
{
  switch (l){
    case nil:
    case cons(x0,xs0):
      if (m == 0){
        mem_drop0(l,x,n);
      }
      else if (mem(x, drop(n-1,xs0)) == true){
        mem_drop(xs0, x, n-1, m-1);
        assert mem(x, drop(m-1,xs0)) == true;
        assert drop(m-1,xs0) == drop(m,cons(x0,xs0));
      }
      else{
      }
  }
}

lemma void drop_drop<t>(list<t> l, int i)
  requires 0 <= i &*& i+1 <= length(l); 
  ensures drop(i+1,l) == drop(1,drop(i,l));
{
  switch (l){
    case nil: 
    case cons(x,xs): 
      if(i != 0){
        drop_drop(xs,i-1);
      }
  }
}

lemma void forall_nth<t> (list<t> l, fixpoint(t, bool) fp, int i)
  requires forall(l,fp) == true &*& 0 <= i &*& i < length(l);
  ensures fp(nth(i,l)) == true;
{
  switch(l){
    case nil:
    case cons(x,xs): 
      if (i!=0){        
        forall_nth(xs, fp, i-1);
      }
  }
}

lemma void wlevel_cons(list<void*> l, list< pair<list<void*>, real> > l', void* v)
  requires map_wlevels(l, drop(1,l')) == true &*& wait_level_of(v) == nth(0,l') &*& length(l) < length(l');
  ensures map_wlevels(cons(v,l),l') == true;
{
  switch (l'){
    case nil:
    case cons(x',xs'):
  }
}

lemma void wlevel_nth(list<void*> l, list< pair<list<void*>, real> > l', int i)
  requires map_wlevels(l,l') == true &*& 0 <= i &*& i < length(l);
  ensures wait_level_of(nth(i,l)) == nth(i,l');
{
  switch (l){
    case nil:
    case cons(x,xs): 
      switch (l'){
        case nil:
        case cons(x',xs'): 
          if (i != 0)
            wlevel_nth(xs,xs',i-1);
      }
  }
}

lemma void foo_pre(philosopher ph1)
  requires [?f1]ph1->previous |-> ?x &*& [?f2]ph1->previous |-> ?y;
  ensures [f1]ph1->previous |-> x &*& [f2]ph1->previous |-> x &*& x == y;
{}

lemma void foo_next(philosopher ph1)
  requires [?f1]ph1->next |-> ?x &*& [?f2]ph1->next |-> ?y;
  ensures [f1]ph1->next |-> x &*& [f2]ph1->next |-> x &*& x == y;
{}

lemma void foo_cv(philosopher ph1)
  requires [?f1]ph1->cv |-> ?x &*& [?f2]ph1->cv |-> ?y;
  ensures [f1]ph1->cv |-> x &*& [f2]ph1->cv |-> x &*& x == y;
{}

lemma void foo_state(philosopher ph1)
  requires [?f1]ph1->state |-> ?x &*& [?f2]ph1->state |-> ?y;
  ensures [f1]ph1->state |-> x &*& [f2]ph1->state |-> x &*& x == y;
{}

lemma void split_list(philosopher ph, philosopher ph2, philosopher phs)
  requires philosophers(ph, ph2, ?Wt,?Ot,?m) &*& [_]phs->previous |-> ?phs_previous &*& [_]phs_previous->next |-> phs &*& ph != phs &*& ph != ph2 &*& in_list(ph, ph2, phs);
  ensures philosophers(ph, phs_previous, Wt,Ot,m) &*& philosophers(phs, ph2,Wt,Ot,m) &*& in_list(ph, ph2, phs);
{
  open philosophers(ph, ph2, Wt,Ot,m);
  assert philosopher(ph, Wt, Ot, m, ?previous, ?next);
  if (ph == phs_previous){
    open philosopher(ph, Wt, Ot, m, previous, next);  
    close philosopher(ph, Wt, Ot, m, previous, next);      
    close philosophers(ph, phs_previous, Wt,Ot,m);
  }
  else{
    if (next == phs){
      open philosopher(ph, Wt, Ot, m, previous, next);  
      close philosopher(ph, Wt, Ot, m, previous, next);      
    }
    if (next == ph2){
      open philosopher(ph, Wt, Ot, m, previous, next);  
      close philosopher(ph, Wt, Ot, m, previous, next);      
      open in_list(ph, ph2, phs);
      open in_list(next, ph2, phs); 
    }
    else{
      open philosopher(ph, Wt, Ot, m, previous, next);  
      close philosopher(ph, Wt, Ot, m, previous, next);      
      open in_list(ph, ph2, phs);
      split_list(next, ph2, phs);
      close in_list(ph, ph2, phs);
      close philosophers(ph, phs_previous, Wt,Ot,m);
    }
  }
}

lemma void philosophers_in_list(philosopher ph, philosopher ph2)
  requires philosophers(ph, ph2,?Wt,?Ot,?m);
  ensures philosophers(ph, ph2,Wt,Ot,m) &*& in_list(ph, ph2, ph2);
{
  if (ph==ph2){
    close in_list(ph, ph2, ph2);
  }
  else{
    open philosophers(ph, ph2,Wt,Ot,m);
    open philosopher(ph, Wt, Ot, m, ?previous, ?next);  
    close philosopher(ph, Wt, Ot, m, previous, next);      
    philosophers_in_list(next,ph2);
    close philosophers(ph, ph2,Wt,Ot,m);
    close in_list(ph, ph2, ph2);  
  }
}

lemma void cvs_in_list(philosopher ph, philosopher ph2)
  requires [?fd]cv_phs(ph, ph2,?ph1);
  ensures [fd]cv_phs(ph, ph2,ph1) &*& in_list(ph, ph2, ph2);
{
  if (ph==ph2){
    close in_list(ph, ph2, ph2);
  }
  else{
    open cv_phs(ph, ph2,ph1);
    assert [_]ph->next |-> ?next;
    cvs_in_list(next,ph2);
    close [fd]cv_phs(ph, ph2,ph1);
    close in_list(ph, ph2, ph2);  
  }
}

lemma void merge_list(philosopher ph, philosopher ph2, philosopher ph2_next, philosopher ph3)
  requires philosophers(ph, ph2,?Wt,?Ot,?m) &*& [_]ph2->next |-> ph2_next &*& [_]ph2_next->previous |-> ph2 &*& philosophers(ph2_next, ph3, Wt,Ot,m) &*& ph != ph3 &*& ph2 != ph3;
  ensures philosophers(ph, ph3, Wt,Ot,m);
{
  open philosophers(ph, ph2,Wt,Ot,m);
  assert philosopher(ph, Wt, Ot, m, ?previous, ?next);  
  if (ph==ph2){
    open philosopher(ph, Wt, Ot, m, previous, next);  
    close philosopher(ph, Wt, Ot, m, previous, next);      
    close philosophers(ph, ph3, Wt,Ot,m);
  }
  else{
    if (next == ph3){
      open philosopher(ph, Wt, Ot, m, previous, next);  
      close philosopher(ph, Wt, Ot, m, previous, next);     
      if (ph2_next != ph3){
        philosophers_in_list(ph2_next, ph3);
        split_list(ph2_next, ph3, ph3);
      }
      open philosophers(ph3, ph3, Wt,Ot,m);
      open philosopher(ph3, Wt, Ot, m, _, _);
      open philosophers(next, ph2, Wt,Ot,m);        
      open philosopher(next, Wt, Ot, m, _, _);
    }
    else{
      open philosopher(ph, Wt, Ot, m, previous, next);  
      close philosopher(ph, Wt, Ot, m, previous, next);      
      merge_list(next, ph2, ph2_next, ph3);
      close philosophers(ph, ph3, Wt,Ot,m);    
    }
  }
}

lemma void in_list_weak(philosopher ph, philosopher ph2, philosopher phs)
  requires in_list(ph, ph2, phs) &*& [_]ph2->next |-> ?ph2_next &*& [_]ph2_next->previous |-> ph2 &*& ph != ph2_next;
  ensures in_list(ph, ph2_next, phs) &*& [_]ph2->next |-> ph2_next &*& [_]ph2_next->previous |-> ph2;
{
  open in_list(ph, ph2, phs);
  if (ph == ph2){
    close in_list(ph, ph2_next, phs);
  }
  else if (ph == phs){
    close in_list(ph, ph2_next, phs);
  }
  else{
    assert [_]ph->next |-> ?next;
    if (next == ph2_next){
      foo_pre(ph2_next);
    }
    in_list_weak(next, ph2, phs);
    close in_list(ph, ph2_next, phs);  
  }
}

lemma void next_in_list(philosopher phs, philosopher phs_previous, philosopher ph)
  requires in_list(phs, phs_previous, ph) &*& [_]ph->next |-> ?next &*& [_]ph->previous |-> ?previous &*& [_]next->previous |-> ph  &*& [_]previous->next |-> ph &*& 
    ph != next &*& ph != previous &*& previous != next &*& phs != phs_previous &*& ph != phs_previous;
  ensures in_list(phs, phs_previous, next);
{
  open in_list(phs, phs_previous, ph);
  if (phs == ph){
    close in_list(next, phs_previous, next);
    close in_list(ph, phs_previous, next);
  }
  else{
    assert [_]phs->next |-> ?phs_next;
    if (phs_next == phs_previous){
      open in_list(phs_next, phs_previous, ph);
    }
    else{
    if (phs == next){
      leak in_list(_, _, _);
      close in_list(phs, phs_previous, next);        
    }
    else{
      next_in_list(phs_next, phs_previous, ph);    
      close in_list(phs, phs_previous, next);  
    }
    }
  }
}

lemma void has_previous(philosopher ph, philosopher ph2)
  requires philosophers(ph, ph2,?Wt,?Ot,?m) &*& ph != ph2;
  ensures philosophers(ph,ph2,Wt,Ot,m) &*& [_]ph2->previous |-> ?ph2_pre &*& [_]ph2_pre->next |-> ph2;
{
  open philosophers(ph,ph2,Wt,Ot,m);
  assert philosopher(ph, Wt, Ot, m, ?previous, ?next);  
  if (next == ph2){
    open philosopher(ph, Wt, Ot, m, previous, next);  
    close philosopher(ph, Wt, Ot, m, previous, next);      
    close philosophers(ph,ph2,Wt,Ot,m);  
  }
  else{
    open philosopher(ph, Wt, Ot, m, previous, next);  
    close philosopher(ph, Wt, Ot, m, previous, next);      
    has_previous(next,ph2);
    close philosophers(ph,ph2,Wt,Ot,m);  
  }
}

lemma void split_list_cv(philosopher ph, philosopher ph2, philosopher phs)
  requires [?fd]cv_phs(ph, ph2, ?cvs) &*& [_]phs->previous |-> ?phs_previous &*& [_]phs_previous->next |-> phs &*& 
    [_]phs->next |-> ?phs_next &*& [_]phs_next->previous |-> phs &*& phs_next != phs &*& phs_previous != phs &*& 
    phs_next != phs_previous &*& ph != phs &*& ph != ph2 &*& in_list(ph, ph2, phs);
  ensures [fd]cv_phs(ph, phs_previous, ?cvs1) &*& [fd]cv_phs(phs, ph2, ?cvs2) &*& in_list(ph, ph2, phs) &*& cvs == append(cvs1,cvs2) &*& forall(cvs1,(nin)(cvs2)) == true;
{
  open cv_phs(ph, ph2, cvs);
  if (ph == phs_previous){
    foo_next(ph);
    close [fd]cv_phs(ph, phs_previous, take(1,cvs));
  }
  else{
    assert [_]ph->next |-> ?next;
    if (next == phs){
      foo_pre(phs);
    }
    if (next == ph2){
      assert in_list(ph, ph2, phs);
      open in_list(ph, ph2, phs);    
      open in_list(next, ph2, phs); 
    }
    else{
      open in_list(ph, ph2, phs);
      split_list_cv(next, ph2, phs);
      assert [fd]cv_phs(next, phs_previous, ?a);
      assert [fd]cv_phs(phs, ph2, ?b);
      close in_list(ph, ph2, phs);
      close [fd]cv_phs(ph, phs_previous,cons(nth(0,cvs),a));
    }
  }
}

lemma void merge_list_cv(philosopher ph, philosopher ph2, philosopher ph2_next, philosopher ph3)
  requires [?fd]cv_phs(ph, ph2,?cvs1) &*& [_]ph2->next |-> ph2_next &*& [_]ph2_next->previous |-> ph2 &*& [fd]cv_phs(ph2_next, ph3, ?cvs2) &*& ph != ph3 &*& ph2 != ph3 &*& 
    in_list(ph, ph3, ph2_next) &*& ph != ph2_next &*& forall(cvs1,(nin)(cvs2)) == true;
  ensures [fd]cv_phs(ph, ph3, append(cvs1,cvs2)) &*& in_list(ph, ph3, ph2_next);
{
  open cv_phs(ph, ph2,cvs1);
  assert [_]ph->next |-> ?next;  
  if (ph==ph2){
    foo_next(ph);
    close [fd]cv_phs(ph, ph3, append(cvs1,cvs2));
  }
  else{
    if (next == ph3){
      close [fd]cv_phs(ph, ph2,cvs1);
      open in_list(ph, ph3, ph2_next);  
      if (next == ph2_next)
        foo_pre(next);
      open in_list(next, ph3, ph2_next); 
    }
    else{
      open in_list(ph, ph3, ph2_next);    
      if (next == ph2_next)
        foo_pre(next);
      merge_list_cv(next, ph2, ph2_next, ph3);
      close [fd]cv_phs(ph, ph3, append(cvs1,cvs2));    
      close in_list(ph, ph3, ph2_next);
    }
  }
}

lemma void last_index(philosopher phs)
  requires [?fd]cv_phs(phs,?phs_previous,?cvs) &*& length(cvs) >= 1;
  ensures [fd]cv_phs(phs,phs_previous,cvs) &*& [_]phs_previous->cv |-> nth(length(cvs)-1,cvs);
{
  open cv_phs(phs, phs_previous,cvs);
  if (phs == phs_previous){}
  else{
    assert [_]phs->next |-> ?phs_next;
    if (length(cvs) == 1){
      open cv_phs(phs_next, phs_previous, drop(1,cvs));    
    }
    else{
      last_index(phs_next);
      drop_index(cvs,length(cvs)-1,1);
    }
  }
  close [fd]cv_phs(phs, phs_previous,cvs);  
}

lemma void unique_cvs(philosopher phs, int i, int j)
  requires [?fd]cv_phs(phs,?phs_previous,?cvs) &*& 0 <= i &*& 0 <= j &*& i < length(cvs) &*& j < length(cvs) &*& nth(i,cvs) == nth(j,cvs);
  ensures [fd]cv_phs(phs,phs_previous,cvs) &*& i == j;
{
  open cv_phs(phs,phs_previous,cvs);
  if (phs == phs_previous){
    if (0 < i || 0 < j){}
  }
  else{
    assert [_]phs->next |-> ?phs_next;
    if (i==0){
      if (j!=0){
      }    
    }
    else{
      unique_cvs(phs_next, i-1, j-1);
    }
  }
  close [fd]cv_phs(phs,phs_previous,cvs);
}

lemma void has_previous_in_list(philosopher phs, philosopher ph2)
  requires in_list(phs, ?phs_previous, ph2) &*& phs != ph2;
  ensures in_list(phs, phs_previous, ph2) &*& [_]ph2->previous |-> ?ph2_pre &*& [_]ph2_pre->next |-> ph2;
{
  open in_list(phs, phs_previous, ph2);
  assert in_list(?phs_next, phs_previous, ph2);  
  if (phs_next == ph2){
  }
  else{
    has_previous_in_list(phs_next, ph2);
  }
  close in_list(phs, phs_previous, ph2);  
}

lemma void mem_cvs(philosopher phs, philosopher ph)
  requires [?fd]cv_phs(phs, ?phs_previous, ?cvs) &*& in_list(phs, phs_previous, ph) &*& [_]ph->cv |-> ?cv &*& ph != phs;
  ensures [fd]cv_phs(phs, phs_previous, cvs) &*& in_list(phs, phs_previous, ph) &*& [_]ph->cv |-> cv &*& mem(cv,drop(1,cvs)) == true;
{
  open cv_phs(phs, phs_previous, cvs);
  if (phs == phs_previous){
    open in_list(phs, phs_previous, ph);
  }
  else{
    assert [_]phs->next |-> ?phs_next;
    if (phs_next == ph){
      open cv_phs(phs_next, phs_previous, drop(1,cvs));      
      close [fd]cv_phs(phs_next, phs_previous, drop(1,cvs));      
    }
    else{
      open in_list(phs, phs_previous, ph);
      mem_cvs(phs_next, ph);
      assert mem(cv, drop(1,drop(1,cvs))) == true;
      assert mem(cv, drop(2,cvs)) == true;
      mem_drop(cvs,cv,2,1);
      assert mem(cv, drop(1,cvs)) == true;      
      close in_list(phs, phs_previous, ph);
    }
  }
  close [fd]cv_phs(phs, phs_previous, cvs);  
}

lemma void nin_cvs(philosopher ph1, void* cv)
  requires cv_phs(ph1,?ph2,?cvs) &*& ucond(cv);
  ensures cv_phs(ph1,ph2,cvs) &*& ucond(cv) &*& mem(cv,cvs) == false;
{
  open cv_phs(ph1,ph2,cvs);
  assert [_]ph1->cv |-> ?cv1;
  assert [_]ph1->next |-> ?ph1_next;
  if (cv==cv1)
    u_cond_frac(cv);
  if (ph1==ph2){
  }
  else{
    nin_cvs(ph1_next,cv);
  }
  close cv_phs(ph1,ph2,cvs);  
}

lemma void unique_phs(philosopher phs, philosopher ph1, philosopher ph2)
  requires [?fd]cv_phs(phs, ?phs_previous, ?cvs) &*& in_list(phs, phs_previous, ph1) &*& in_list(phs, phs_previous, ph2) &*& [_]ph1->cv |-> ?cv &*& [_]ph2->cv |->cv;
  ensures [fd]cv_phs(phs, phs_previous, cvs) &*& in_list(phs, phs_previous, ph1) &*& in_list(phs, phs_previous, ph2) &*& [_]ph1->cv |-> cv &*& [_]ph2->cv |->cv &*& ph1 == ph2;
{
  open cv_phs(phs, phs_previous, cvs);
  if (phs == phs_previous){
    open in_list(phs, phs_previous, ph1);
    open in_list(phs, phs_previous, ph2);
    foo_cv(ph1);
    close in_list(phs, phs_previous, ph2);
    close in_list(phs, phs_previous, ph1);
  }
  else{
    assert [_]phs->next |-> ?phs_next;
    if (phs == ph1){
      foo_cv(phs);    
      if (phs == ph2){
      }
      else{
         close [fd]cv_phs(phs, phs_previous, cvs);      
         mem_cvs(phs,ph2);
         assert mem(cv,drop(1,cvs)) == true;   
      }   
    }
    else if (phs == ph2){
      foo_cv(phs);     
      close [fd]cv_phs(phs, phs_previous, cvs);               
      mem_cvs(phs,ph1);
      }  
    else{    
      open in_list(phs, phs_previous, ph1);
      open in_list(phs, phs_previous, ph2);
      assert [_]phs->next |-> phs_next;    
      unique_phs(phs_next, ph1, ph2);
      close in_list(phs, phs_previous, ph2);
      close in_list(phs, phs_previous, ph1);
    }
  }
  close [fd]cv_phs(phs, phs_previous, cvs);  
}

lemma void previous_index0(philosopher phs, philosopher ph, int i)
  requires [?fd]cv_phs(phs,?phs_previous,?cvs) &*& 0 < i &*& i < length(cvs) &*& 
    [_]ph->cv |-> nth(i,cvs) &*& [_]ph->previous |-> ?previous &*& [_]previous->cv |-> ?previous_cv &*& in_list(phs, phs_previous, ph);
  ensures [fd]cv_phs(phs,phs_previous,cvs) &*& [_]ph->cv |-> nth(i,cvs) &*& in_list(phs, phs_previous, ph) &*&
    [_]ph->previous |-> previous &*& [_]previous->cv |-> previous_cv &*& previous_cv == nth(i-1,cvs);
{
  open cv_phs(phs, phs_previous,cvs);
  if (ph==phs){
    foo_cv(ph);
    close cv_phs(phs, phs_previous,cvs);    
    unique_cvs(ph,0,i);
  }
  else{
    assert [_]phs->next |-> ?phs_next;    
    assert [_]phs->cv |-> ?phs_cv;    
    assert [fd]cv_phs(phs_next, phs_previous, drop(1,cvs));
     if (i==1){
       open cv_phs(phs_next, phs_previous,drop(1,cvs)); 
       close [fd]cv_phs(phs_next, phs_previous,drop(1,cvs)); 
       close [fd]cv_phs(phs, phs_previous,cvs);           
       close in_list(phs_next, phs_previous, phs_next);                
       close in_list(phs, phs_previous, phs_next);         
       unique_phs(phs,ph,phs_next);
       leak in_list(phs, phs_previous, phs_next);         
       foo_pre(ph);
       foo_cv(previous);       
     }
     else{  
       open in_list(phs, phs_previous, ph);                
       previous_index0(phs_next,ph,i-1);
       close in_list(phs, phs_previous, ph);                       
       close [fd]cv_phs(phs, phs_previous,cvs);        
    }
  }
}

lemma void previous_index(philosopher phs, philosopher ph, int i)
  requires [?fd]cv_phs(phs,?phs_previous,?cvs) &*& [_]phs->previous |-> phs_previous &*& 0 <= i &*& i < length(cvs) &*& 
    [_]ph->cv |-> nth(i,cvs) &*& [_]ph->previous |-> ?previous &*& [_]previous->cv |-> ?previous_cv &*& in_list(phs, phs_previous, ph);
  ensures [fd]cv_phs(phs,phs_previous,cvs) &*& [_]phs->previous |-> phs_previous &*& [_]ph->cv |-> nth(i,cvs) &*& in_list(phs, phs_previous, ph) &*&
    [_]ph->previous |-> previous &*& [_]previous->cv |-> previous_cv &*& 0 < i ? previous_cv == nth(i-1,cvs) : previous_cv == nth(length(cvs)-1,cvs);
{
  if (0 < i){
    previous_index0(phs, ph, i);
  }
  else{
    close in_list(phs, phs_previous, phs);
    open cv_phs(phs,phs_previous,cvs);
    close [fd]cv_phs(phs,phs_previous,cvs);
    unique_phs(phs,phs,ph);
    leak in_list(phs, phs_previous, phs);    
    foo_pre(ph);
    last_index(phs);
  }
}

lemma void next_index0(philosopher phs, philosopher ph, int j)
  requires [?fd]cv_phs(phs,?phs_previous,?cvs) &*& [_]ph->cv |-> nth(j,cvs) &*& 0 <= j &*& j < length(cvs) - 1 &*& 
    [_]ph->next |-> ?next &*& [_]next->cv |-> ?next_cv &*& in_list(phs, phs_previous, ph);
  ensures [fd]cv_phs(phs,phs_previous,cvs) &*& [_]ph->cv |-> nth(j,cvs) &*& [_]ph->next |-> next &*& 
    [_]next->cv |-> next_cv &*& next_cv == nth(j+1,cvs) &*& in_list(phs, phs_previous, ph);
{
  open cv_phs(phs, phs_previous,cvs);
  if (ph == phs_previous){
    close [fd]cv_phs(phs, phs_previous,cvs);  
    last_index(phs); 
    unique_cvs(phs,j,length(cvs)-1);     
  }
  else{
    assert [_]phs->next |-> ?phs_next;
    if (phs == ph){
      foo_cv(phs);
      foo_next(phs);      
      open cv_phs(phs_next, phs_previous,drop(1,cvs));          
      close [fd]cv_phs(phs_next, phs_previous,drop(1,cvs));   
      close [fd]cv_phs(phs, phs_previous,cvs);                     
      unique_cvs(phs,0,j);           
    }
    else{
      if (j==0){
        close [fd]cv_phs(phs, phs_previous,cvs);          
        close in_list(phs, phs_previous, phs);        
        unique_phs(phs, ph, phs);
      }
      else{
        drop_index(cvs,j,1);  
        open in_list(phs, phs_previous, ph);
        next_index0(phs_next, ph, j-1);
        close in_list(phs, phs_previous, ph);      
        close [fd]cv_phs(phs, phs_previous,cvs);                           
      }
    }
  }
}

lemma void has_previous_last_list(philosopher phs)
  requires in_list(phs, ?phs_previous,?ph) &*& phs != ph;
  ensures in_list(phs,phs_previous,ph) &*& [_]ph->previous |-> ?previous &*& [_]previous->next |-> ph;
{
  open in_list(phs,phs_previous,ph);
  assert [_]phs->next |-> ?phs_next;
  if (ph == phs_next){}
  else{
    has_previous_last_list(phs_next);
  }
  close in_list(phs,phs_previous,ph);  
}

lemma void next_index(philosopher phs, philosopher ph, int j)
  requires [?fd]cv_phs(phs,?phs_previous,?cvs) &*& [_]phs->previous |-> phs_previous &*& [_]ph->cv |-> nth(j,cvs) &*& 0 <= j &*& j <= length(cvs) - 1 &*& 
    [_]ph->next |-> ?next &*& [_]next->cv |-> ?next_cv &*& in_list(phs, phs_previous, ph) &*& length(cvs) > 1;
  ensures [fd]cv_phs(phs,phs_previous,cvs) &*& [_]phs->previous |-> phs_previous &*& [_]ph->cv |-> nth(j,cvs) &*& [_]ph->next |-> next &*& 
    [_]next->cv |-> next_cv &*& in_list(phs, phs_previous, ph) &*& j == length(cvs) - 1 ? next_cv == nth(0,cvs) : next_cv == nth(j+1,cvs) ;
{
  if (j == length(cvs) - 1){
    if (ph == phs){
      open cv_phs(phs,phs_previous,cvs);
      close [fd]cv_phs(phs,phs_previous,cvs);
      unique_cvs(ph,0,j);
    }
    else{
      last_index(phs);
      cvs_in_list(phs, phs_previous);
      unique_phs(phs,phs_previous,ph);
      leak in_list(phs, phs_previous, phs_previous);
      open cv_phs(phs,phs_previous,cvs);
      close [fd]cv_phs(phs,phs_previous,cvs);
      foo_cv(next);
    }
  }
  else{
    next_index0(phs, ph, j);  
  }
}

lemma void update_inc_wt(philosopher ph, philosopher ph2, condvar cv)
  requires [2/3]cond(cv) &*& philosophers(ph, ph2, ?Wt,?Ot,?m);
  ensures [2/3]cond(cv) &*& philosophers(ph,ph2,finc(Wt,cv),Ot,m);
{
  open philosophers(ph, ph2, Wt,Ot,m);
  if (ph==ph2){
    open philosopher(ph, Wt, Ot, m, ?previous, ?next);
    assert [_]ph->cv |-> ?phcv;
    if (cv == phcv){
      cond_plus(cv);
      cond_frac'(cv);
    }
    assert cv != phcv;
    close philosopher(ph, finc(Wt,cv), Ot, m, previous, next);
    close philosophers(ph,ph2,finc(Wt,cv),Ot,m);;
  }
  else{
    open philosopher(ph, Wt, Ot, m, ?previous, ?next);
    update_inc_wt(next, ph2, cv);
    assert [_]ph->cv |-> ?phcv;
    if (cv == phcv){
      cond_plus(cv);
      cond_frac'(cv);
    }
    assert cv != phcv;
    close philosopher(ph, finc(Wt,cv), Ot, m, previous, next);    
    close philosophers(ph,ph2,finc(Wt,cv),Ot,m);
  }
}

lemma void update_dec_wt(philosopher ph, philosopher ph2, condvar cv)
  requires [2/3]cond(cv) &*& philosophers(ph, ph2, ?Wt,?Ot,?m);
  ensures [2/3]cond(cv) &*& philosophers(ph,ph2,fdec(Wt,cv),Ot,m);
{
  open philosophers(ph, ph2, Wt,Ot,m);
  if (ph==ph2){
    open philosopher(ph, Wt, Ot, m, ?previous, ?next);
    assert [_]ph->cv |-> ?phcv;
    if (cv == phcv){
      cond_plus(cv);
      cond_frac'(cv);
    }
    assert cv != phcv;
    close philosopher(ph, fdec(Wt,cv), Ot, m, previous, next);
    close philosophers(ph,ph2,fdec(Wt,cv),Ot,m);;
  }
  else{
    open philosopher(ph, Wt, Ot, m, ?previous, ?next);
    update_dec_wt(next, ph2, cv);
    assert [_]ph->cv |-> ?phcv;
    if (cv == phcv){
      cond_plus(cv);
      cond_frac'(cv);
    }
    assert cv != phcv;
    close philosopher(ph, fdec(Wt,cv), Ot, m, previous, next);    
    close philosophers(ph,ph2,fdec(Wt,cv),Ot,m);
  }
}

lemma void update_inc_ot(philosopher ph, philosopher ph2, condvar cv)
  requires [2/3]cond(cv) &*& philosophers(ph, ph2, ?Wt,?Ot,?m);
  ensures [2/3]cond(cv) &*& philosophers(ph,ph2,Wt,finc(Ot,cv),m);
{
  open philosophers(ph, ph2, Wt,Ot,m);
  if (ph==ph2){
    open philosopher(ph, Wt, Ot, m, ?previous, ?next);
    assert [_]ph->cv |-> ?phcv;
    if (cv == phcv){
      cond_plus(cv);
      cond_frac'(cv);
    }
    assert cv != phcv;
    close philosopher(ph, Wt, finc(Ot,cv), m, previous, next);
    close philosophers(ph,ph2,Wt,finc(Ot,cv),m);;
  }
  else{
    open philosopher(ph, Wt, Ot, m, ?previous, ?next);
    update_inc_ot(next, ph2, cv);
    assert [_]ph->cv |-> ?phcv;
    if (cv == phcv){
      cond_plus(cv);
      cond_frac'(cv);
    }
    assert cv != phcv;
    close philosopher(ph, Wt, finc(Ot,cv), m, previous, next);    
    close philosophers(ph,ph2, Wt, finc(Ot,cv),m);
  }
}

lemma void update_dec_ot(philosopher ph, philosopher ph2, condvar cv)
  requires [2/3]cond(cv) &*& philosophers(ph, ph2, ?Wt,?Ot,?m);
  ensures [2/3]cond(cv) &*& philosophers(ph,ph2,Wt,fdec(Ot,cv),m);
{
  open philosophers(ph, ph2, Wt,Ot,m);
  if (ph==ph2){
    open philosopher(ph, Wt, Ot, m, ?previous, ?next);
    assert [_]ph->cv |-> ?phcv;
    if (cv == phcv){
      cond_plus(cv);
      cond_frac'(cv);
    }
    assert cv != phcv;
    close philosopher(ph, Wt, fdec(Ot,cv), m, previous, next);
    close philosophers(ph,ph2,Wt,fdec(Ot,cv),m);;
  }
  else{
    open philosopher(ph, Wt, Ot, m, ?previous, ?next);
    update_dec_ot(next, ph2, cv);
    assert [_]ph->cv |-> ?phcv;
    if (cv == phcv){
      cond_plus(cv);
      cond_frac'(cv);
    }
    assert cv != phcv;
    close philosopher(ph, Wt, fdec(Ot,cv), m, previous, next);    
    close philosophers(ph,ph2, Wt, fdec(Ot,cv),m);
  }
}
@*/

dining_philosophers new_dining_philosophers(int size)
  //@ requires create_dphs_ghost_args(?wlevels) &*& forall(wlevels,(wait_level_lt)(pair({new_dining_philosophers}, 0r))) == true &*& length(wlevels) == size &*& 2 < size;
  //@ ensures dphs(result, ?cvs) &*& map_wlevels(cvs,wlevels) == true &*& length(cvs) == size;
{
  //@ open create_dphs_ghost_args(wlevels);
  //@ close create_mutex_ghost_args(pair({new_dining_philosophers}, 0r));
  struct mutex *m = create_mutex();
  //@ assert umutex(m,?Wt,?Ot);

  philosopher phs = malloc(sizeof(struct philosopher));
  if (phs == 0)
    abort();
    
  philosopher ph1 = malloc(sizeof(struct philosopher));
  if (ph1 == 0)
    abort();

  philosopher ph2 = malloc(sizeof(struct philosopher));
  if (ph2 == 0)
    abort();
        
  phs->next = ph1;
  phs->previous = ph2;
  ph1->next = ph2;
  ph1->previous = phs;
  ph2->next = phs;
  ph2->previous = ph1;
  
  phs->state = Thinking;
  ph1->state = Thinking;
  ph2->state = Thinking;
  phs->number = 0;
  ph1->number = 1;
  ph2->number = 2;

  //@ close create_condvar_ghost_args(nth(0,wlevels));
  struct condvar *v0 = create_condvar();

  //@ forall_nth (wlevels, (wait_level_lt)(pair({new_dining_philosophers}, 0r)), 0);  
  //@ forall_nth (wlevels, (wait_level_lt)(pair({new_dining_philosophers}, 0r)), size-2);  
  //@ forall_nth (wlevels, (wait_level_lt)(pair({new_dining_philosophers}, 0r)), size-1);      
  
  //@ close create_condvar_ghost_args(nth(size-2,wlevels));
  struct condvar *v1 = create_condvar();

  //@ close create_condvar_ghost_args(nth(size-1,wlevels));
  struct condvar *v2 = create_condvar();

  //@ if (v1 == v2) ucond_frac(v1);    
  //@ if (v0 == v2) ucond_frac(v2);    
  //@ if (v0 == v1) ucond_frac(v1);    
  //@ close init_condvar_ghost_args(m,no_transfer,cons(v1,cons(v0,nil)));
  //@ init_condvar(v2);
                                
  phs->cv = v0;
  ph1->cv = v1;
  ph2->cv = v2;

  //@ leak [_]ph1->next |-> _;
  //@ leak [_]ph2->next |-> _;
  //@ leak [_]phs->previous |-> _;
  //@ leak [_]ph2->previous |-> _;
  //@ leak [_]phs->cv |-> _;
  //@ leak [_]ph1->cv |-> _;
  //@ leak [_]ph2->cv |-> _;
  //@ close philosopher(ph2, Wt, Ot, m, ph1, phs);  
  //@ close philosophers(ph2,ph2,Wt,Ot,m); 
  //@ leak [_]cond(v2);                   
  //@ close cv_phs(ph2,ph2,cons(v2,nil));
  //@ nth_drop(0,size-1, wlevels);
  //@ wlevel_cons(nil, drop(size-1,wlevels), v2);
  int i = 3;
  while(i < size)
    /*@ invariant 3 <= i &*& i <= size &*&
          phs->next |-> ?phs_next &*&
          phs_next->previous |-> phs &*&
          [_]phs_next->next |-> ?phs_next_next &*&          
          phs_next->number |-> _ &*&
          [_]phs_next->cv |-> ?phs_next_cv &*&
          [_]phs_next_next->cv |-> ?phs_next_next_cv &*&          
          [1/3]phs_next_next->state |-> Thinking &*& 
          [1/3]ph2->state |-> Thinking &*&                  
          [2/3]phs_next->state |-> Thinking &*& 
          [1/3]phs->state |-> Thinking &*&           
          [_]phs_next_next->previous |-> phs_next &*&
          ucond(phs_next_cv) &*&   
          wait_level_lt(wait_level_of(m), wait_level_of(phs_next_cv)) == true &*&
          phs_next != ph2 &*&
          phs != phs_next_next &*&
          ucond(v0) &*&   
          cv_phs(phs_next_next,ph2,?cvs) &*&
          length(cvs) == i-2 &*&
          mem(phs_next_cv,cvs) == false &*&
          mem(v0,cvs) == false &*&
          wait_level_of(phs_next_cv) == nth(size-i+1,wlevels) &*&
          map_wlevels(cvs,drop(size-i+2,wlevels)) == true &*&          
          v0 != phs_next_cv &*&
          malloc_block_philosopher(ph2) &*&
          philosophers(phs_next_next,ph2,Wt,Ot,m);
    @*/
  {
    //@ close create_condvar_ghost_args(nth(size-i,wlevels));
    struct condvar *cv = create_condvar();
    //@ forall_nth (wlevels, (wait_level_lt)(pair({new_dining_philosophers}, 0r)), size-i);  
    //@ drop_drop(wlevels,size-i+1);
    //@ nth_drop(0,size-i+1,wlevels);    
    //@ wlevel_cons(cvs, drop(size-i+1,wlevels), phs_next_cv);      
    philosopher ph = malloc(sizeof(struct philosopher));
    if (ph == 0)
      abort();
    ph->state = Thinking;
    ph->number = i;
    ph->cv = cv;    
    ph->previous = phs;
    ph->next = phs->next;
    phs->next->previous = ph;      
    phs->next = ph;
    i++;    
    //@ if (cv == phs_next_cv) ucond_frac(cv);
    //@ if (v0 == cv) ucond_frac(cv);
    //@ nin_cvs(phs_next_next,cv);
    //@ leak [_]ph->next |-> _;
    //@ leak [_]ph->cv |-> _;    
    //@ leak malloc_block_philosopher(ph);
    //@ leak [_]phs_next->previous |-> _;
    //@ close init_condvar_ghost_args(m,no_transfer,cons(cv,cons(phs_next_next_cv,nil)));
    //@ init_condvar(phs_next_cv);
    //@ close philosopher(phs_next, Wt, Ot, m, ph, phs_next_next);
    //@ close philosophers(phs_next,ph2,Wt,Ot,m);
    //@ leak [_]cond(phs_next_cv);    
    //@ close cv_phs(phs_next,ph2,cons(phs_next_cv,cvs));
    //@ leak [_]cond(phs_next_cv);
  }
  //@ leak [_]phs_next->previous |-> phs;  
  //@ leak [_]phs->next |-> phs_next;  
  //@ close init_condvar_ghost_args(m,no_transfer,cons(v0,cons(phs_next_next_cv,nil)));
  //@ init_condvar(phs_next_cv);
  
  //@ close philosopher(phs_next, Wt, Ot, m, phs, phs_next_next);     
  //@ close philosophers(phs_next,ph2,Wt,Ot,m);  
  //@ close init_condvar_ghost_args(m,no_transfer,cons(v2,cons(phs_next_cv,nil)));
  //@ init_condvar(v0);
  //@ close philosopher(phs, Wt, Ot, m, ph2, phs_next);             
  //@ close philosophers(phs,ph2,Wt,Ot,m);
  //@ leak [_]cond(phs_next_cv);
  //@ close cv_phs(phs_next,ph2,cons(phs_next_cv,cvs));  
  //@ leak [_]cond(v0);  
  //@ close cv_phs(phs,ph2,cons(v0,cons(phs_next_cv,cvs))); 
  //@ drop_drop(wlevels,1);  
  //@ nth_drop(0,1,wlevels);
  //@ wlevel_cons(cvs, drop(1,wlevels), phs_next_cv);        
  //@ wlevel_cons(cons(phs_next_cv,cvs), drop(0,wlevels), v0);        
              
  dining_philosophers dp = malloc(sizeof(struct dining_philosophers));
  if (dp == 0)
    abort();
  dp->phs = phs;
  dp->m = m;
  dp->size = size;
  //@ leak dp->m |-> _;
  //@ leak dp->size |-> _;
  //@ leak dp->phs |-> _;
  //@ close ph_inv(dp)(Wt,Ot);        
  //@ close init_mutex_ghost_args(ph_inv(dp));
  //@ init_mutex(m);
  //@ leak [_]mutex(m);  
  //@ leak malloc_block_philosopher(phs);
  //@ leak malloc_block_philosopher(ph1);
  //@ leak malloc_block_philosopher(ph2);
  //@ leak malloc_block_dining_philosophers(dp);
  //@ leak [_]cond(phs_next_cv);
  //@ leak [_]cond(v0);
  //@ leak [_]cond(v2);  
  //@ close dphs(dp, cons(v0,cons(phs_next_cv,cvs)));  
  return dp;
} 

void pickup(dining_philosophers dph, int i)
  //@ requires obs(?O) &*& [?fd]dphs(dph,?cvs) &*& w_level_below_all(nth(i,cvs),O) == true &*& 0 <= i &*& i < length(cvs) &*& wait_level_below_obs(pair({(pickup)}, 0r), O) == true;
  //@ ensures obs(cons((void*)nth((i+length(cvs)-1)%length(cvs),cvs),cons((void*)nth((i+1)%length(cvs),cvs),O))) &*& [fd]dphs(dph, cvs);
{
  //@ open dphs(dph,cvs);
  //@ assert [_]dph->m |-> ?m;
  //@ assert [_]dph->phs |-> ?phs;  
  //@ assert [_]phs->previous |-> ?phs_previous;  
  //@ close mutex_inv(m, ph_inv(dph));
  //@ wait_level_lt_below_obs(wait_level_of(m), pair({(pickup)}, 0r), O);
  mutex_acquire(dph->m);
  //@ assert mutex_held(m, ?f, ?Wt, ?Ot);
  //@ open ph_inv(dph)(Wt,Ot);
  //@ open philosophers(phs, phs_previous, Wt,Ot,m);
  //@ open philosopher(phs, Wt, Ot, m, _, ?phs_next);  
  //@ close philosopher(phs, Wt, Ot, m, phs_previous, phs_next);      
  //@ close philosophers(phs, phs_previous, Wt,Ot,m);
    
  philosopher ph = dph->phs;
  
  //@ open cv_phs(phs, phs_previous, cvs);
  //@ assert [_]ph->cv |-> nth(0,cvs);
  //@ close [fd]cv_phs(phs, phs_previous, cvs);

  //@ close in_list(phs, phs_previous, phs);
  //@ previous_index(phs, phs, 0);
  //@ mod_minus(length(cvs),1);
  int j=0;
  //@ close in_list(ph, phs_previous, phs);  
  //@ close in_list(phs, phs_previous, phs);    
  //@ assert in_list(ph, phs_previous, phs);    
  while(j<i)
    /*@ invariant j<=i &*& 0 <= j &*&
          [_]ph->previous |-> ?previous &*& 
          [_]ph->next |-> ?next &*&
          [_]next->previous |-> ph &*&
          [_]previous->next |-> ph &*&
          [_]ph->cv |-> nth(j,cvs) &*&
          [_]phs_previous->cv |-> nth(length(cvs)-1,cvs) &*&
          [_]phs->cv |-> nth(0,cvs) &*&
          ph != next &*& ph != previous &*& next != previous &*&            
          philosophers(ph, previous, Wt, Ot, m) &*&
          [fd]cv_phs(phs, phs_previous, cvs) &*&
          in_list(phs, phs_previous, ph) &*&
          in_list(ph, previous, phs);
    @*/
  {
    //@ open philosophers(ph, previous, Wt, Ot, m);
    //@ open philosopher(ph, Wt, Ot, m, _, _);  
    //@ close philosopher(ph, Wt, Ot, m, previous, next);          
    //@ open philosophers(next, previous, Wt, Ot, m);
    //@ open philosopher(next, Wt, Ot, m, _, _);  
    //@ close philosopher(next, Wt, Ot, m, ph, ?next_next);          
    //@ close philosophers(ph, ph, Wt, Ot, m);
    //@ merge_list(next_next, previous, ph, ph);
    //@ close philosophers(next, ph, Wt, Ot, m);
    /*@
      if (ph == phs_previous){
        foo_cv(ph);
        unique_cvs(phs,length(cvs)-1,j); 
      }
    @*/
    //@ next_index0(phs, ph, j);
    //@ next_in_list(phs, phs_previous, ph);
    /*@ if (ph != phs){
          open in_list(ph, previous, phs);
          in_list_weak(next, previous, phs);
        }
        else{
          leak in_list(phs, previous, phs);         
          philosophers_in_list(next, phs);
        }
    @*/
    ph = ph->next;   
    j++;
  }
  //@ has_previous(ph,previous);
  //@ assert [_]previous->previous |-> ?pre_pre;
  //@ philosophers_in_list(ph, previous);
  //@ split_list(ph, previous, previous);
  //@ open philosophers(previous, previous, Wt,Ot,m);
  //@ open philosopher(previous,Wt,Ot,m, _,_); 
   
  //@ close philosopher(previous,Wt,Ot,m, pre_pre,ph);  
  //@ open philosopher(previous,Wt,Ot,m, pre_pre,ph);  
    
  //@ open philosophers(ph, pre_pre, Wt,Ot,m);
  //@ open philosopher(ph,Wt,Ot,m,_,_);
  //@ open philosophers(next, pre_pre, Wt,Ot,m);
  //@ open philosopher(next,Wt,Ot,m, _,?next_next);

  //@ assert [_]previous->state |-> ?previous_state;  
  //@ assert [_]ph->state |-> ?state;  
  //@ assert [_]next->state |-> ?next_state;
  //@ assert [_]next_next->state |-> ?next_next_state;
  //@ assert [_]ph->cv |-> ?cv; 
  //@ assert [_]next->cv |-> ?next_cv;    
  //@ assert [_]previous->cv |-> ?previous_cv;      
  //@ assert [_]pre_pre->cv |-> ?pre_pre_cv;    
  //@ assert [_]next_next->cv |-> ?next_next_cv;  
  
  //@ previous_index(phs, ph,i);  
  //@ if (0 < i) mod_plus(length(cvs),i-1);
  //@ next_index(phs, ph,i);  
  //@ mod_plus(length(cvs),0);
  //@ if (i+1<length(cvs)) mod_plus_le(length(cvs), i+1);
  /*@
    if (cv == next_cv){
      cond_plus(cv);
      cond_frac'(cv);
    }
  @*/
  /*@
    if (cv == previous_cv){
      cond_plus(cv);
      cond_frac'(cv);
    }
  @*/
  /*@
    if (previous == next_next){
        if (next != pre_pre){
          foo_pre(next_next);
        }
      foo_cv(next);
    }
  @*/
    
  if (ph->state != Thinking)
    abort();
  ph->state = Hungry;

  if (ph->next->state == Eating || ph->previous->state == Eating){
    /*@
      if (phs != ph){
        split_list_cv(phs, phs_previous, ph);        
      }
    @*/
    //@ open cv_phs(ph, phs_previous, ?cvs1);
    /*@
    if (next != pre_pre){
      if (ph == phs){
        foo_next(ph);
        foo_pre(ph);
        foo_cv(ph);
        foo_cv(previous);        
        foo_pre(next);  
        foo_next(previous);      
        foo_cv(next);        
      }    
      else if (ph == phs_previous){
        foo_next(ph);
        foo_next(phs);      
        foo_pre(phs);      
        foo_pre(next_next);
        foo_cv(ph);             
        foo_cv(next);     
      }
      else if (next == phs_previous){
        foo_next(next);
        foo_pre(phs);    
        foo_cv(next);          
        foo_cv(next_next);             
      }
      if (ph == phs_next){
        foo_pre(ph);
        foo_pre(phs);
        foo_cv(ph);                     
        foo_cv(previous); 
      }
      else if (previous == phs){   
        foo_pre(previous);                 
        foo_next(previous);                       
      }
      else if (previous == next_next){ 
        if (next != pre_pre){
          foo_pre(next_next);
        }
      }
      close philosopher(next,finc(Wt,cv),Ot,m, ph,next_next);    
      update_inc_wt(next_next,pre_pre,cv);  
    }
    else{
      if (ph == phs){
        foo_next(ph);
        foo_pre(ph);
        foo_cv(ph);
        foo_pre(next);  
        foo_next(previous); 
        foo_state(next);
      } 
      else if (ph == phs_previous){
        foo_next(ph);
        foo_next(phs);      
        foo_pre(phs);      
        foo_pre(next_next);
        foo_state(next);
        foo_cv(ph);
        foo_cv(next);     
      }
      else if (next == phs_previous){
        foo_next(next);
        foo_next(phs);      
        foo_pre(phs);      
        foo_state(next);
        foo_cv(ph);
        foo_cv(previous);                                   
      }
      else if (ph == phs_next){
        foo_pre(ph);
        foo_pre(phs);
       }
      else if (previous == phs){   
        foo_pre(previous);                 
      }
      else if (previous == next_next){ 
        foo_state(next);                                                
      }
      close philosopher(next,finc(Wt,cv),Ot,m, ph,next_next);          
    }
  @*/
  //@ close philosophers(next, pre_pre, finc(Wt,cv),Ot,m);
  /*@
    if (ph == phs_previous){}
    else if (ph == phs){}
    else if (next == phs){
      foo_pre(phs);      
    }
    else if (next == phs_next){   
      foo_pre(next);                 
    }
    else if (previous == phs_previous){   
      foo_next(phs_previous);                       
    }
  @*/

  //@ close philosopher(ph,finc(Wt,cv),Ot,m,previous,next);
  //@ close philosophers(ph, pre_pre, finc(Wt,cv),Ot,m);
  //@ close philosopher(previous,finc(Wt,cv),Ot,m, pre_pre,ph);  
  //@ close philosophers(previous, previous, finc(Wt,cv),Ot,m);
  //@ merge_list(ph,pre_pre,previous, previous);
  /*@
    if (ph != phs){
      assert [_]previous->next |-> ?ph_test;
      if (ph_test != ph){
        foo_next(previous);
      }
      assert [_]phs->previous |-> ?phs_previous_test1;
      if (phs_previous_test1 != phs_previous)
        foo_pre(phs);
      assert [_]phs_previous->next |-> ?phs_test1;
      if (phs_test1 != phs)
        foo_next(phs_previous);
      split_list(ph,previous,phs);
      merge_list(phs,previous, ph, phs_previous);
    }
    else{
      if (previous != phs_previous){
        foo_pre(ph);
      }
    }
  @*/
    
    //@ close ph_inv(dph)(finc(Wt,cv),Ot);    
    //@ close MP(cv,no_transfer);  
    //@ close M'P(cv,cons(previous_cv,cons(next_cv,nil))); 
    condvar_wait(ph->cv, dph->m);
    //@ open no_transfer();
    //@ leak [_]cond(cv);
    //@ close [fd]cv_phs(ph, phs_previous, cvs1);    
    /*@
      if (phs != ph){
        merge_list_cv(phs, previous, ph, phs_previous);        
      }
    @*/
  }
  else{
    ph->state = Eating; 
  //@ g_chrgl(next_cv);
  //@ g_chrgl(previous_cv);

  /*@
    if (next != pre_pre){
      update_inc_ot(next_next, pre_pre, next_cv);        
      update_inc_ot(next_next, pre_pre, previous_cv);        
    }
  @*/
  //@ close philosopher(next,Wt,finc(finc(Ot,next_cv),previous_cv),m, ph,next_next);  
  //@ close philosophers(next, pre_pre, Wt,finc(finc(Ot,next_cv),previous_cv),m);
  //@ close philosopher(ph,Wt,finc(finc(Ot,next_cv),previous_cv),m,previous,next);
  //@ close philosophers(ph, pre_pre, Wt,finc(finc(Ot,next_cv),previous_cv),m);
  //@ close philosopher(previous,Wt,finc(finc(Ot,next_cv),previous_cv),m, pre_pre,ph);  
  //@ close philosophers(previous, previous, Wt,finc(finc(Ot,next_cv),previous_cv),m);
  //@ merge_list(ph,pre_pre,previous, previous);
  /*@
    if (ph != phs){
      if (previous == phs_previous){
        foo_next(phs_previous);
      }
      split_list(ph,previous,phs);
      assert [_]previous->next |-> ?ph_test1;      
      if (ph_test1 != ph){
        foo_next(previous);
      }
      merge_list(phs,previous, ph, phs_previous);
    }
    else{
      if (previous != phs_previous){
        foo_pre(ph);
      }
      assert philosophers(phs,phs_previous,Wt,finc(finc(Ot,next_cv),previous_cv),m);    
    }
  @*/    
    //@ close ph_inv(dph)(Wt,finc(finc(Ot,next_cv),previous_cv));        
  }
  mutex_release(dph->m);      
  //@ close [fd]dphs(dph,cvs);    
  //@ leak in_list(_,_,_);  
  //@ leak in_list(_,_,_);  
  //@ leak in_list(_,_,_);  
  //@ leak in_list(_,_,_); 
  //@ leak [_]cond(_);   
}

void test(philosopher ph)
  /*@ requires obs(?O) &*& ph->state |-> ?state &*& [_]ph->cv |-> ?cv &*& [?f0]cond(cv) &*&
        [_]ph->next |-> ?next &*& [?f1]next->state |-> ?next_state &*& [_]next->cv |-> ?next_cv &*&
        [_]ph->previous |-> ?previous &*& [?f2]previous->state |-> ?previous_state &*& [_]previous->cv |-> ?previous_cv &*&
        mutex_held(mutex_of(cv), ?f, ?Wt, ?Ot) &*& Wt(cv) <= 1 &*& 1 + st(previous_state) + st(next_state) <= Ot(cv) &*&
        (previous_state == Thinking || next_state == Thinking) &*& (state == Hungry ? 0 < Wt(cv) : Wt(cv) <= 0) &*&
        M(cv) == no_transfer &*& M'(cv) == cons(previous_cv,cons(next_cv,nil)) &*&
        mutex_of(next_cv) == mutex_of(cv) &*& mutex_of(cv) == mutex_of(previous_cv);
  @*/
  /*@ ensures obs(remove((void*)cv,O)) &*& [_]ph->cv |-> cv &*& [f0]cond(cv) &*&
        [_]ph->next |-> next &*& [f1]next->state |-> next_state &*&
        [_]ph->previous |-> previous &*& [f2]previous->state |-> previous_state &*&
        (next_state != Eating && previous_state != Eating && state == Hungry) ?
        ph->state |-> Eating &*& mutex_held(mutex_of(cv), f, fdec(Wt,cv), fdec(finc(finc(Ot,next_cv),previous_cv),cv)):
        ph->state |-> state &*& mutex_held(mutex_of(cv), f, Wt, fdec(Ot,cv));
  @*/
{
  if (ph->next->state != Eating && ph->previous->state != Eating && ph->state == Hungry){
    ph->state = Eating;
    //@ if (Wt(cv)>0) close no_transfer();
    //@ close MP(cv,no_transfer);
    //@ close M'P(cv,cons(previous_cv,cons(next_cv,nil)));      
    //@ g_chrgl(next_cv);
    //@ g_chrgl(previous_cv);
    condvar_signal(ph->cv);
    //@ minus_self(O,previous_cv);
    //@ g_dischl(cv);    
  }
  /*@
    if (ph->next->state != Eating && ph->previous->state != Eating && state == Hungry){}
    else g_dischl(cv);
  @*/
}

void putdown(dining_philosophers dph, int i)
  //@ requires obs(?O) &*& [?fd]dphs(dph,?cvs) &*& 0 <= i &*& i < length(cvs) &*& wait_level_below_obs(pair({(putdown)}, 0r), O) == true;
  //@ ensures obs(remove((void*)nth((i-1+length(cvs))%length(cvs),cvs),remove((void*)nth((i+1)%length(cvs),cvs),O))) &*& [fd]dphs(dph, cvs);
{
  //@ open dphs(dph,cvs);
  //@ assert [_]dph->m |-> ?m;
  //@ assert [_]dph->phs |-> ?phs;  
  //@ assert [_]phs->previous |-> ?phs_previous;  
  //@ close mutex_inv(m, ph_inv(dph));
  //@ wait_level_lt_below_obs(wait_level_of(m), pair({(putdown)}, 0r), O);
  mutex_acquire(dph->m);
  //@ assert mutex_held(m, ?f, ?Wt, ?Ot);
  //@ open ph_inv(dph)(Wt,Ot);
  //@ open philosophers(phs, phs_previous, Wt,Ot,m);
  //@ open philosopher(phs, Wt, Ot, m, _, ?phs_next);  
  //@ close philosopher(phs, Wt, Ot, m, phs_previous, phs_next);      
  //@ close philosophers(phs, phs_previous, Wt,Ot,m);

    
  philosopher ph = dph->phs;
  
  //@ open cv_phs(phs, phs_previous, cvs);
  //@ assert [_]ph->cv |-> nth(0,cvs);
  //@ close [fd]cv_phs(phs, phs_previous, cvs);

  //@ close in_list(phs, phs_previous, phs);
  //@ previous_index(phs, phs, 0);
  //@ mod_minus(length(cvs),1);
 
  int j=0;
  
  //@ close in_list(ph, phs_previous, phs);  
  //@ close in_list(phs, phs_previous, phs);    
  while(j<i)
    /*@ invariant j <= i &*& 0 <= j &*&
          [_]ph->previous |-> ?previous &*& 
          [_]ph->next |-> ?next &*&
          [_]next->previous |-> ph &*&
          [_]previous->next |-> ph &*&
          [_]ph->cv |-> nth(j,cvs) &*&
          [_]phs_previous->cv |-> nth(length(cvs)-1,cvs) &*&
          [_]phs->cv |-> nth(0,cvs) &*&
          ph != next &*& ph != previous &*& next != previous &*&            
          philosophers(ph, previous, Wt, Ot, m) &*&
          [fd]cv_phs(phs, phs_previous, cvs) &*&
          in_list(phs, phs_previous, ph) &*&
          in_list(ph, previous, phs);
    @*/
  {
    //@ open philosophers(ph, previous, Wt, Ot, m);
    //@ open philosopher(ph, Wt, Ot, m, _, _);  
    //@ close philosopher(ph, Wt, Ot, m, previous, next);          
    //@ open philosophers(next, previous, Wt, Ot, m);
    //@ open philosopher(next, Wt, Ot, m, _, _);  
    //@ close philosopher(next, Wt, Ot, m, ph, ?next_next);          
    //@ close philosophers(ph, ph, Wt, Ot, m);
    //@ merge_list(next_next, previous, ph, ph);
    //@ close philosophers(next, ph, Wt, Ot, m);
    /*@
      if (ph == phs_previous){
        foo_cv(ph);
        unique_cvs(phs,length(cvs)-1,j); 
      }
    @*/
    //@ next_index0(phs, ph, j);
    //@ next_in_list(phs, phs_previous, ph);
    /*@ if (ph != phs){
          open in_list(ph, previous, phs);
          in_list_weak(next, previous, phs);
        }
        else{
          leak in_list(phs, previous, phs);         
          philosophers_in_list(next, phs);
        }
    @*/
    ph = ph->next;   
    j++;
  }
  /*@
    if (ph == phs){
      foo_next(phs);                      
      foo_pre(phs);                              
      foo_cv(phs);  
      foo_cv(phs_previous);        
      foo_next(phs_previous);                                          
      foo_pre(phs_next);                                          
    }
  @*/
  //@ has_previous(ph,previous);
  //@ assert [_]previous->previous |-> ?pre_pre;
  //@ philosophers_in_list(ph, previous);
  //@ split_list(ph, previous, previous);
  //@ open philosophers(previous, previous, Wt,Ot,m);
  //@ open philosopher(previous,Wt,Ot,m, _,_); 
  //@ close philosopher(previous,Wt,Ot,m, pre_pre,ph);         
  //@ open philosophers(ph, pre_pre, Wt,Ot,m);  
  //@ open philosopher(ph,Wt,Ot,m, _,_); 
  //@ close philosopher(ph,Wt,Ot,m, previous,next);         
  //@ open philosophers(next, pre_pre, Wt,Ot,m);    

  //@ open philosopher(next,Wt,Ot,m, _,_); 
  //@ assert [_]next->next |-> ?next_next;
  //@ close philosopher(next,Wt,Ot,m, ph,next_next);         

  //@ assert [_]ph->cv |-> ?cv;    
  //@ assert [_]next->cv |-> ?next_cv;    
  //@ assert [_]next_next->cv |-> ?next_next_cv;      
  //@ assert [_]previous->cv |-> ?previous_cv;  
  
  //@ previous_index(phs, ph,i);  
  //@ if (0 < i) mod_plus(length(cvs),i-1);
  //@ next_index(phs, ph,i);  
  //@ mod_plus(length(cvs),0);
  //@ if (i+1<length(cvs)) mod_plus_le(length(cvs), i+1);
  /*@
    if (next_next == previous){
      open philosopher(previous,Wt,Ot,m, pre_pre,ph); 
      open philosopher(ph,Wt,Ot,m, previous,next); 
      open philosopher(next,Wt,Ot,m, ph,next_next);
      assert [_]next_next->previous |-> ?next_test;
      if (next_test != next){
        foo_pre(next_next);
      }
      assert [_]previous->previous |-> ?pre_pre_test;
      if (pre_pre_test != pre_pre){
        foo_pre(previous);
      }
    }
    else{
      open philosophers(next_next, pre_pre, Wt,Ot,m);
      open philosopher(next_next,Wt,Ot,m, _,?next_next_next);
      if (next_next_next == ph){}
      else if (next_next_next == previous){
        assert [_]previous->previous |-> ?pre_pre_test; 
        if (pre_pre_test != pre_pre)
          foo_pre(previous);      
        assert [_]previous->cv |-> ?previous_cv_test;
        if (previous_cv_test != previous_cv)
          foo_cv(previous);   
      }
      else{}
      open philosopher(previous,Wt,Ot,m, pre_pre,ph); 
      open philosopher(ph,Wt,Ot,m, previous,next); 
      open philosopher(next,Wt,Ot,m, ph,next_next);
    }
  @*/   

  /*@
    if (cv == next_cv){
      cond_plus(cv);
      cond_frac'(cv);
    }    
  @*/
  /*@
    if (previous_cv == next_cv){
      cond_plus(next_cv);
      cond_frac'(next_cv);
    }    
  @*/
    
  //@ assert [_]ph->state |-> ?state0;
  //@ assert [_]previous->state |-> ?previous_state;
  //@ assert [_]pre_pre->state |-> ?pre_pre_state;
  //@ assert [_]next->state |-> ?next_state;
  //@ assert [_]next_next->state |-> ?next_next_state;
  //@ assert [_]pre_pre->cv |-> ?pre_pre_cv;
  if (ph->state != Eating)
    abort();
  ph->state = Thinking;
  //@ assert [_]ph->state |-> ?state;
  
  test(ph->next);
  //@ assert [_]next->state |-> ?next_state1;  
  //@ assert [_]pre_pre->state |-> ?pre_pre_state1;    
  
  //@ assert mutex_held(m, f, ?Wt0, ?Ot0);
  /*@
    if (next_next == previous){
    }
    else if (next_next == pre_pre) {
      assert [_]next_next->next |-> ?next_next_next;
      close philosopher(next_next,Wt0,Ot0,m, next,next_next_next);
      close philosophers(next_next, pre_pre, Wt0,Ot0,m);
      assert [_]next_next->cv |-> ?next_next_cv_test;
      if (next_next_cv_test != next_next_cv)
        foo_cv(next_next);
      close philosopher(next,Wt0,Ot0,m, ph,next_next);
      close philosophers(next, pre_pre, Wt0,Ot0,m);
      has_previous(next,pre_pre);
      assert [_]pre_pre->previous |-> ?pre_pre_pre;
      philosophers_in_list(next, pre_pre);
      split_list(next, pre_pre, pre_pre);
      open philosophers(pre_pre, pre_pre, Wt0,Ot0,m);      
      open philosopher(pre_pre,Wt0,Ot0,m, _,_);
      leak in_list(next,pre_pre,pre_pre);
      assert [_]previous->cv |-> ?previous_cv_test;
      if (previous_cv_test != previous_cv)
        foo_cv(previous);            
      assert [_]pre_pre->cv |-> ?pre_pre_cv_test;
      if (pre_pre_cv_test != pre_pre_cv)
        foo_cv(pre_pre);            
    } 
    else{
      assert [_]next_next->next |-> ?next_next_next;          
      if (next_next_state != Eating && state != Eating && next_state == Hungry){
        update_dec_wt(next_next_next,pre_pre,next_cv);
        update_inc_ot(next_next_next,pre_pre,next_next_cv);
        update_inc_ot(next_next_next,pre_pre,cv);        
        update_dec_ot(next_next_next,pre_pre,next_cv);        
      }
      else{
        update_dec_ot(next_next_next,pre_pre,next_cv);      
      }

      close philosopher(next_next,Wt0,Ot0,m, next,next_next_next);
      close philosophers(next_next, pre_pre, Wt0,Ot0,m);
      close philosopher(next,Wt0,Ot0,m, ph,next_next);
      close philosophers(next, pre_pre, Wt0,Ot0,m);
      has_previous(next,pre_pre);
      assert [_]pre_pre->previous |-> ?pre_pre_pre;
      philosophers_in_list(next, pre_pre);
      split_list(next, pre_pre, pre_pre);
      open philosophers(pre_pre, pre_pre, Wt0,Ot0,m);      
      open philosopher(pre_pre,Wt0,Ot0,m, _,_);
      leak in_list(next,pre_pre,pre_pre); 
    }    
  @*/

  test(ph->previous);                
  //@ assert [_]previous->state |-> ?previous_state1;
  //@ assert mutex_held(m, f, ?Wt2, ?Ot2);
  /*@
    if (next_next == previous){
      close philosopher(previous,Wt2,Ot2,m,pre_pre,ph);
      close philosophers(previous, previous, Wt2,Ot2,m);
      close philosopher(next,Wt2,Ot2,m,ph,next_next);   
      close philosophers(next, pre_pre, Wt2,Ot2,m);    
      close philosopher(ph,Wt2,Ot2,m,previous,next);      
      close philosophers(ph, pre_pre, Wt2,Ot2,m);  
    }
    else if (next_next == pre_pre){
      assert [_]pre_pre->previous |-> ?pre_pre_pre;
      if (state != Eating && pre_pre_state1 != Eating && previous_state == Hungry){
        update_dec_wt(next,pre_pre_pre,previous_cv);
        update_inc_ot(next,pre_pre_pre,cv);        
        update_inc_ot(next,pre_pre_pre,pre_pre_cv);
        update_dec_ot(next,pre_pre_pre,previous_cv);
      }
      else{
        update_dec_ot(next,pre_pre_pre,previous_cv);      
      }
           
      close philosopher(previous,Wt2,Ot2,m,pre_pre,ph);
      close philosophers(previous, previous, Wt2,Ot2,m);    
      close philosopher(pre_pre,Wt2,Ot2,m,pre_pre_pre,previous);
      close philosophers(pre_pre, pre_pre, Wt2,Ot2,m);
      
      close philosopher(ph,Wt2,Ot2,m,previous,next);      
      close philosophers(ph, pre_pre_pre, Wt2,Ot2,m);      
      merge_list(ph,pre_pre_pre,pre_pre, pre_pre);
    }    
    else{
      assert [_]pre_pre->previous |-> ?pre_pre_pre;    
      if (ph == pre_pre_pre){
        foo_next(ph);
      }      
      if (state != Eating && pre_pre_state1 != Eating && previous_state == Hungry){
        update_dec_wt(next,pre_pre_pre,previous_cv);
        update_inc_ot(next,pre_pre_pre,cv);        
        update_inc_ot(next,pre_pre_pre,pre_pre_cv);
        update_dec_ot(next,pre_pre_pre,previous_cv);
      }
      else{
        update_dec_ot(next,pre_pre_pre,previous_cv);      
      }
      
      close philosopher(previous,Wt2,Ot2,m,pre_pre,ph);
      close philosophers(previous, previous, Wt2,Ot2,m);    
      close philosopher(pre_pre,Wt2,Ot2,m,pre_pre_pre,previous);
      close philosophers(pre_pre, pre_pre, Wt2,Ot2,m);
      close philosopher(ph,Wt2,Ot2,m,previous,next);     
      close philosophers(ph, pre_pre_pre, Wt2,Ot2,m);      
      merge_list(ph,pre_pre_pre,pre_pre, pre_pre);
  }    
  @*/
  //@ merge_list(ph,pre_pre,previous, previous);
  /*@
    if (ph != phs){
      if (previous == phs_previous){
        foo_next(previous);
      }
      split_list(ph,previous,phs);
      assert [_]previous->next |-> ?ph_test1;      
      if (ph_test1 != ph){
        foo_next(previous);
      }
      merge_list(phs,previous, ph, phs_previous);
    }
    else{
      if (previous != phs_previous){
        foo_pre(ph);
      }
      assert philosophers(phs,phs_previous,Wt2,Ot2,m);    
    }
  @*/    
  //@ close ph_inv(dph)(Wt2,Ot2); 
  //@ leak in_list(_,_,_);   
  //@ leak in_list(_,_,_);   
  //@ leak in_list(_,_,_);   
  //@ leak in_list(_,_,_);     
  mutex_release(dph->m);      
  //@ close [fd]dphs(dph,cvs);  
  //@ leak [_]cond(_);
}




