#include "stdlib.h"
#include "monitors.h"
#include "readers_writers.h"
//@ #include "ghost_counters.gh"

struct read_write {
   int aw;
   int ar;
   int ww;
   struct mutex *m;   
   condvar vr;
   condvar vw;
   //@ int grdrs;
   //@ int gawtrs;   
};

/*@
predicate reader_writer(struct read_write *b; void* grd, void* gwr, int ardrs, int awrtrs) = 
  [_]b->m |-> ?m &*& 
  [_]b->vr |-> grd &*& 
  [_]b->vw |-> gwr &*& 
  [_]b->grdrs |-> ardrs &*&                
  [_]b->gawtrs |-> awrtrs &*&
  [_]mutex(m) &*& 
  [_]cond(grd,no_transfer,nil) &*&
  [_]cond(gwr,vwtrn(awrtrs),cons(gwr,nil)) &*&  
  inv(m) == read_write(b,grd,gwr) &*&
  wait_level_of(m) == pair({(create_readers_writers)}, 0r) &*&
  wait_level_lt(wait_level_of(m), wait_level_of(grd)) == true &*&
  wait_level_lt(wait_level_of(m), wait_level_of(gwr)) == true &*&
  wait_level_lt(wait_level_of(gwr), wait_level_of(grd)) == true &*&  
  mutex_of(grd)==m &*& 
  mutex_of(gwr)==m;

predicate_ctor vwtrn(int i)() = tic(i);

predicate_ctor read_write(struct read_write *b, struct condvar *vr, struct condvar *vw)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) = 
  b->aw |-> ?aw &*& 
  b->ar |-> ?ar &*& 
  b->ww |-> ?ww &*& 
  [_]b->m |-> ?m &*& 
  [_]b->vr |-> vr &*& 
  [_]b->vw |-> vw &*& 
  [_]b->grdrs |-> ?grdrs &*&   
  [_]b->gawtrs |-> ?gawtrs &*&   
  ctr(grdrs,ar) &*&  
  ctr(gawtrs,aw) &*&  
  vr != vw &*&  
  aw >= 0 &*& 
  ar >= 0 &*& 
  ww >= 0 &*&
  (Wt(vr) <= 0 || 0 < aw + ww) &*&
  aw + ww <= Ot(vr) &*&
  Wt(vw) == ww &*&
  (Wt(vw) <= 0 || 0 < ar + aw) &*&  
  ar + aw <= Ot(vw);
@*/

struct read_write *create_readers_writers()
    /*@ requires create_rw_ghost_args(?wr_wlevel, ?rd_wlevel) &*& wait_level_lt(wr_wlevel, rd_wlevel) == true &*&
          wait_level_lt(pair({(create_readers_writers)}, 0r), wr_wlevel) == true &*&
          wait_level_lt(pair({(create_readers_writers)}, 0r), rd_wlevel) == true; @*/
    //@ ensures reader_writer(result, ?rd, ?wr, ?ardrs, ?awrtrs) &*& wait_level_of(wr) == wr_wlevel &*& wait_level_of(rd) == rd_wlevel;
{
    //@ leak create_rw_ghost_args(wr_wlevel, rd_wlevel);
    //@ close create_mutex_ghost_args(pair({(create_readers_writers)}, 0r));
    struct mutex *m = create_mutex();
    
    //@ int gawtrs = new_ctr();    
    //@ close create_condvar_ghost_args(wr_wlevel);    
    condvar vw = create_condvar();
    //@ close create_condvar_ghost_args(rd_wlevel);
    condvar vr = create_condvar();
    
    //@ if (vw == vr) ucond_frac(vw);

    //@ close init_condvar_ghost_args(m,vwtrn(gawtrs),cons(vw,nil));        
    //@ init_condvar(vw); 
    
    //@ close init_condvar_ghost_args(m,no_transfer,nil);    
   //@ init_condvar(vr); 
    struct read_write *b = malloc(sizeof(struct read_write));
    if (b==0)
      abort();
    b->ww = 0;
    b->aw = 0;
    b->ar = 0;
    b->m = m;
    b->vw = vw;
    b->vr = vr;
    //@ b->grdrs = new_ctr();
    //@ b->gawtrs = gawtrs; 
    
    //@ leak [_]b->vw |-> _;
    //@ leak [_]b->vr |-> _;
    //@ leak [_]b->m |-> _;    
    //@ leak [_]b->grdrs |-> _;        
    //@ leak [_]b->gawtrs |-> _;    
    //@ leak [_]malloc_block_read_write(_);
    //@ leak [_]cond(vr,_,_);
    //@ leak [_]cond(vw,_,_);
    //@ close init_mutex_ghost_args(read_write(b,vr,vw));
    //@ close read_write(b,vr,vw)(empb,empb);
    //@ init_mutex(m);
    //@ leak [_]mutex(m);
    //@ close reader_writer(b,vr,vw, b->grdrs, b->gawtrs);
    return b;
}

void reader_enter(struct read_write *b)
  //@ requires [_]reader_writer(b, ?rd, ?wr, ?ardrs, ?awrtrs) &*& obs(?O) &*& w_level_below_all(rd,O) == true &*& wait_level_below_obs(pair({reader_enter}, 0r), O) == true;
  //@ ensures [_]reader_writer(b, rd, wr, ardrs, awrtrs) &*& obs(cons(wr,O)) &*& tic(ardrs);
{
  //@ open reader_writer(b,rd,wr, ardrs, awrtrs);
  //@ assert [_]b->m |-> ?m;   
  //@ close mutex_inv(m,read_write(b,rd,wr));
  //@ wait_level_lt_below_obs(wait_level_of(m), pair({reader_enter}, 0r), O);
  mutex_acquire(b->m);
  //@ open read_write(b,rd,wr)(?Wt1,?Ot1);
  //@ leak [_]b->vr |-> rd;
  //@ leak [_]b->vw |-> wr;
  //@ assert ctr(ardrs,_); 
  while (b->aw + b->ww > 0)
  /*@ invariant b->aw |-> ?aw &*& 
	b->ar |-> ?ar &*& 
	b->ww |-> ?ww &*& 
	[_]b->m |-> m &*& 
	[_]b->vr |-> rd &*& 
	[_]b->vw |-> wr &*& 
	[_]b->grdrs |-> ardrs &*&   
	[_]b->gawtrs |-> awrtrs &*&   
	ctr(ardrs,ar) &*&  
	ctr(awrtrs,aw) &*& 
	[_]cond(rd,no_transfer,nil) &*&
	[_]cond(wr,vwtrn(awrtrs),cons(wr,nil)) &*&  
	aw >= 0 &*& 
	ar >= 0 &*& 
	ww >= 0 &*&
	mutex_held(m, _, ?Wt, ?Ot) &*&
	(Wt(rd) <= 0 || 0 < aw + ww) &*&
	aw + ww <= Ot(rd) &*&
        Wt(wr) == ww &*&	
       (Wt(wr) <= 0 || 0 < ar + aw) &*&  
        ar + aw <= Ot(wr) &*&
	obs(cons(m,O)); @*/
  {
    //@ close read_write(b,rd,wr)(finc(Wt,rd),Ot);
    //@ close mutex_inv(m,read_write(b,rd,wr));
    condvar_wait(b->vr, b->m);
    //@ open read_write(b,rd,wr)(_,_);        
    //@ open no_transfer();
  }
  b->ar = b->ar + 1;
  //@ inc_ctr(ardrs);
  //@ g_chrgl(wr);
  //@ close read_write(b,rd,wr)(Wt,finc(Ot,wr));
  //@ close mutex_inv(m,read_write(b,rd,wr));  
  mutex_release(b->m);
  //@ leak [_]mutex(m);  
  }

void reader_exit(struct read_write *b)
  //@ requires [_]reader_writer(b, ?rd, ?wr, ?ardrs, ?awrtrs) &*& obs(cons(wr,?O)) &*& tic(ardrs) &*& wait_level_below_obs(pair({reader_exit}, 0r), cons(wr,O)) == true;
  //@ ensures [_]reader_writer(b, rd, wr, ardrs, awrtrs) &*& obs(O);
{    
  //@ open reader_writer(b,rd,wr, ardrs, awrtrs);
  //@ assert [_]b->m |-> ?m;     
  //@ close mutex_inv(m,read_write(b,rd,wr)); 
  //@ wait_level_lt_below_obs(wait_level_of(m), pair({reader_exit}, 0r), cons(wr,O));
  mutex_acquire(b->m); 
  //@ open read_write(b,rd,wr)(?Wt2,?Ot2);
  //@ dec_ctr(ardrs);
  //@ inc_ctr(ardrs);
  b->ar = b->ar - 1;
  //@ assert ctr(?grdrs2,?rdrds2);
  //@ dec_ctr(grdrs2);
  if (b->ww > 0){
    //@ inc_ctr(awrtrs);     
    /*@ if (Wt2(wr)>0){
          close vwtrn(awrtrs)();
        }
    @*/  
    condvar_signal(b->vw);
    //@ minus_nil(cons(m,cons(wr,O)));
    b->ww --;
    b->aw ++;    
  }
  else{
    //@ g_dischl(wr);      
  }
  //@ assert mutex_held(m,_,?Wte,?Ote); 
  //@ close read_write(b,rd,wr)(Wte,Ote);
  //@ close mutex_inv(m,read_write(b,rd,wr));  
  mutex_release(b->m);     
  //@ leak [_]mutex(m);
}

void writer_enter(struct read_write *b)
  //@ requires [_]reader_writer(b, ?rd, ?wr, ?ardrs, ?awrtrs) &*& obs(?O) &*& w_level_below_all(rd,O) == true &*& wait_level_below_obs(pair({writer_enter}, 0r), O) == true;
  //@ ensures [_]reader_writer(b, rd, wr, ardrs, awrtrs) &*& obs(cons(wr,cons(rd,O))) &*& tic(awrtrs);
{
  //@ open reader_writer(b,rd,wr, ardrs, awrtrs);
  //@ assert [_]b->m |-> ?m;     
  //@ close mutex_inv(m,read_write(b,rd,wr));
  //@ wait_level_lt_below_obs(wait_level_of(m), pair({writer_enter}, 0r), O);
  mutex_acquire(b->m);
  //@ open read_write(b,rd,wr)(_,_);
  //@ g_chrgl(rd);  
  //@ assert mutex_held(m, _, ?Wt, ?Ot);
  if (b->aw + b->ar > 0)
  {
    b->ww = b->ww + 1;
    //@ close read_write(b,rd,wr)(finc(Wt,wr),Ot);
    //@ close mutex_inv(m,read_write(b,rd,wr));
    //@ wait_level_lt_below_obs(wait_level_of(wr), wait_level_of(rd), O);
    condvar_wait(b->vw, b->m);
    //@ open read_write(b,rd,wr)(_,_);
    //@ open vwtrn(awrtrs)();
  }
  else{    
    b->aw = b->aw + 1;
    //@ inc_ctr(awrtrs);      
    //@ g_chrgl(wr);    
  }
  //@ assert mutex_held(m, _, ?Wt2, ?Ot2);  
  //@ close read_write(b,rd,wr)(Wt2,Ot2);  
  //@ close mutex_inv(m,read_write(b,rd,wr));  
  mutex_release(b->m);
  //@ leak [_]mutex(m);
}

void writer_exit(struct read_write *b)
  //@ requires [_]reader_writer(b, ?rd, ?wr, ?ardrs, ?awrtrs) &*& obs(cons(wr,cons(rd,?O))) &*& tic(awrtrs) &*& wait_level_below_obs(pair({writer_exit}, 0r), cons(wr,cons(rd,O))) == true;// &*& tic(wwrtrs);
  //@ ensures [_]reader_writer(b, rd, wr, ardrs, awrtrs) &*& obs(O);
{
  //@ open reader_writer(b,rd,wr, ardrs, awrtrs);
  //@ assert [_]b->m |-> ?m;     
  //@ close mutex_inv(m,read_write(b,rd,wr));
  //@ wait_level_lt_below_obs(wait_level_of(m), pair({writer_exit}, 0r), cons(wr,cons(rd,O)));
  mutex_acquire(b->m);
  //@ open read_write(b,rd,wr)(?Wt2,?Ot2);
  b->aw = b->aw - 1;
  //@ dec_ctr(awrtrs); 
  if (b->ww > 0){  
    //@ inc_ctr(awrtrs); 
    /*@ if (Wt2(wr)>0){
          close vwtrn(awrtrs)();
        }
    @*/
    condvar_signal(b->vw); 
    //@ minus_nil(cons(m,cons(wr,cons(rd,O))));
    b->ww --;
    b->aw ++; 
  }
  else{
    //@ assert b->ww |-> ?ww;
    //@ assert ww <= 0;
    //@ g_dischl(wr);  
    condvar_broadcast(b->vr);
  }
  //@ g_dischl(rd);
  //@ assert mutex_held(m,_,?Wte,?Ote);  
  //@ close read_write(b,rd,wr)(Wte,Ote);       
  //@ close mutex_inv(m,read_write(b,rd,wr));  
  mutex_release(b->m); 
  //@ leak [_]mutex(m);
}
