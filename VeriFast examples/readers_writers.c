#include "stdlib.h"
#include "monitors.h"
#include "readers_writers.h"
//@ #include "ghost_counters.gh"

struct read_write {
   int aw;
   int ar;
   int ww;
   struct mutex *m;   
   cvar vr;
   cvar vw;
   //@ int gw;  
   //@ int grdrs;
   //@ int gwtrs;
   //@ int gawtrs;   
};

/*@
predicate reader_writer(struct read_write *b; void* grd, void* gwr, int ardrs, int awrtrs) = 
  [_]b->m |-> ?m &*& 
  [_]b->vr |-> grd &*& 
  [_]b->vw |-> gwr &*& 
  [_]b->gw |-> ?gw &*& 
  [_]b->grdrs |-> ardrs &*&                
  [_]b->gawtrs |-> awrtrs &*&
  [_]mutex(m) &*& 
  inv(m) == read_write(b,grd,gwr) &*& 
  level'(grd) == none &*&  
  level'(gwr) == some(level(gwr)) &*&
  wait_level_lt(level(m), level(grd)) == true &*&
  wait_level_lt(level(m), level(gwr)) == true &*&
  wait_level_lt(level(gwr), level(grd)) == true &*&  
  level'(m) == none;

predicate_ctor creditor(struct read_write *b)() = [_]b->gw |-> ?gw &*& tic(gw);

predicate_ctor read_write(struct read_write *b, cvar vr, cvar vw)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) = 
  b->aw |-> ?aw &*& 
  b->ar |-> ?ar &*& 
  b->ww |-> ?ww &*& 
  [_]b->m |-> ?m &*& 
  [_]b->vr |-> vr &*& 
  [_]b->vw |-> vw &*& 
  [_]b->gw |-> ?gw &*&
  [_]b->grdrs |-> ?grdrs &*&   
  [_]b->gwtrs |-> ?gwtrs &*&   
  [_]b->gawtrs |-> ?gawtrs &*&   
  ctr(gw,?Cw) &*&
  ctr(grdrs,ar) &*&  
  ctr(gwtrs,ww) &*&    
  ctr(gawtrs,aw) &*&    
  [_]cond(vr,nothing,nil) &*&
  [_]cond(vw,creditor(b),nil) &*&
  aw >= 0 &*& 
  ar >= 0 &*& 
  ww >= 0 &*&
  vr != vw &*& 
  mutex_of(vr)==m &*& 
  mutex_of(vw)==m &*&
  P(vr) == false &*& 
  P(vw) == true &*&        
  (Wt(vr) <= 0 || 0 < aw + ww) &*&
  aw + ww <= Ot(vr) &*&
  Wt(vw) + Cw + aw + ar <= Ot(vw) &*&
  Wt(vw) < 1 || Wt(vw) < Ot(vw);
@*/

struct read_write *create_readers_writers()
    /*@ requires create_rw_ghost_args(?wr_wlevel, ?rd_wlevel) &*& wait_level_lt(wr_wlevel, rd_wlevel) == true &*&
          wait_level_lt(pair({(create_readers_writers)}, 0r), wr_wlevel) == true &*&
          wait_level_lt(pair({(create_readers_writers)}, 0r), rd_wlevel) == true; @*/
    //@ ensures reader_writer(result, ?rd, ?wr, ?ardrs, ?awrtrs) &*& level(wr) == wr_wlevel &*& level(rd) == rd_wlevel;
{
    //@ leak create_rw_ghost_args(wr_wlevel, rd_wlevel);
    //@ close create_mutex_ghost_args(pair({(create_readers_writers)}, 0r));
    struct mutex *m = create_mutex();
    
    //@ int gw = new_ctr();
    //@ close create_cvar_ghost_args(wr_wlevel,true,some(wr_wlevel));    
    cvar vw = create_cvar();

    //@ close create_cvar_ghost_args(rd_wlevel,false,none);    
    cvar vr = create_cvar();
    //@ close init_cvar_ghost_args(m,nothing,nil);       
    //@ init_cvar(vr);
    
    struct read_write *b = malloc(sizeof(struct read_write));
    if (b==0) abort();
    
    //@ close init_cvar_ghost_args(m,creditor(b),nil);    
    //@ init_cvar(vw);
    
    b->ww = 0;
    b->aw = 0;
    b->ar = 0;
    b->m = m;
    b->vw = vw;
    b->vr = vr;
    //@ b->gw = gw;
    //@ b->grdrs = new_ctr();
    //@ b->gwtrs = new_ctr();    
    //@ b->gawtrs = new_ctr();    
    
    //@ leak [_]b->vw |-> _;
    //@ leak [_]b->vr |-> _;
    //@ leak [_]b->m |-> _;    
    //@ leak [_]b->gw |-> _;    
    //@ leak [_]b->grdrs |-> _;        
    //@ leak [_]b->gwtrs |-> _;            
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
  //@ requires [_]reader_writer(b, ?rd, ?wr, ?ardrs, ?awrtrs) &*& obs(?O) &*& w_level_below_all(rd,O) == true;
  //@ ensures [_]reader_writer(b, rd, wr, ardrs, awrtrs) &*& obs(cons(wr,O)) &*& tic(ardrs);
{
  //@ open reader_writer(b,rd,wr, ardrs, awrtrs);
  //@ assert [_]b->m |-> ?m;   
  //@ close mutex_inv(m,read_write(b,rd,wr));
  //@ wait_level_lt_below_obs(level(m), level(rd), O);  
  mutex_acquire(b->m);
  //@ open read_write(b,rd,wr)(?Wt1,?Ot1);
  //@ leak [_]b->vr |-> rd;
  //@ leak [_]b->vw |-> wr;
  //@ assert [_]b->gw |-> ?gw;
  //@ assert ctr(ardrs,_); 
  //@ assert [_]b->gwtrs |-> ?wwrtrs; 
  while (b->aw + b->ww > 0)
  /*@ invariant b->aw |-> ?aw &*& 
	b->ar |-> ?ar &*& 
	b->ww |-> ?ww &*& 
	[_]b->m |-> m &*& 
	[_]b->vr |-> rd &*& 
	[_]b->vw |-> wr &*& 
	[_]b->gw |-> gw &*&
	[_]b->grdrs |-> ardrs &*&   
	[_]b->gwtrs |-> wwrtrs &*&   
	[_]b->gawtrs |-> awrtrs &*&   
	ctr(gw,?Cw) &*&
	ctr(ardrs,ar) &*&  
	ctr(wwrtrs,ww) &*&    
	ctr(awrtrs,aw) &*&   
	[_]cond(rd,nothing,nil) &*&
	[_]cond(wr,creditor(b),nil) &*&
	aw >= 0 &*& 
	ar >= 0 &*& 
	ww >= 0 &*&
	mutex_held(m, _, ?Wt, ?Ot) &*&
	(Wt(rd) <= 0 || 0 < aw + ww) &*&
	aw + ww <= Ot(rd) &*&
	Wt(wr) + Cw + aw + ar <= Ot(wr) &*&
	Wt(wr) < 1 || Wt(wr) < Ot(wr) &*&
	obs(cons(m,O)); @*/
  {
    //@ close read_write(b,rd,wr)(finc(Wt,rd),Ot);
    //@ close mutex_inv(m,read_write(b,rd,wr));
    /*@ produce_lemma_function_pointer_chunk spurious(read_write(b,rd,wr), nothing, rd)() {
     open read_write(b,rd,wr)(?Wt2,?Ot2);
     close read_write(b,rd,wr)(fdec(Wt2,rd),Ot2);
     close nothing();}; @*/
    cvar_spwk_wait(b->vr, b->m);
    //@ open read_write(b,rd,wr)(_,_);        
    //@ open nothing();
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
  //@ requires [_]reader_writer(b, ?rd, ?wr, ?ardrs, ?awrtrs) &*& obs(cons(wr,?O)) &*& tic(ardrs) &*& w_level_below_all(rd, O) == true;
  //@ ensures [_]reader_writer(b, rd, wr, ardrs, awrtrs) &*& obs(O);
{    
  //@ open reader_writer(b,rd,wr, ardrs, awrtrs);
  //@ assert [_]b->m |-> ?m;     
  //@ close mutex_inv(m,read_write(b,rd,wr)); 
  //@ wait_level_lt_below_obs(level(m), level(rd), O);  
  mutex_acquire(b->m); 
  //@ open read_write(b,rd,wr)(?Wt2,?Ot2);
  //@ dec_ctr(ardrs);
  //@ inc_ctr(ardrs);    
  b->ar = b->ar - 1;
  //@ assert ctr(?grdrs2,?rdrds2);
  //@ dec_ctr(grdrs2);
  //@ assert [_]b->gw |-> ?gw;  
  /*@ if (Wt2(wr)>0){
        inc_ctr(gw);
        close creditor(b)();
      } @*/
  cvar_signal(b->vw);
  //@ minus_nil(cons(m,cons(wr,O)));
  //@ inc_ctr(gw);  
  //@ dec_ctr(gw);  
  //@ g_dischl(wr);
  //@ assert mutex_held(m,_,?Wte,?Ote); 
  //@ close read_write(b,rd,wr)(Wte,Ote);
  //@ close mutex_inv(m,read_write(b,rd,wr));  
  mutex_release(b->m);     
  //@ leak [_]mutex(m);
}

void writer_enter(struct read_write *b)
  //@ requires [_]reader_writer(b, ?rd, ?wr, ?ardrs, ?awrtrs) &*& obs(?O) &*& w_level_below_all(rd,O) == true;// &*& wait_level_below_obs(pair({writer_enter}, 0r), O) == true;
  //@ ensures [_]reader_writer(b, rd, wr, ardrs, awrtrs) &*& obs(cons(wr,cons(rd,O))) &*& tic(awrtrs);
{
  //@ open reader_writer(b,rd,wr, ardrs, awrtrs);
  //@ assert [_]b->m |-> ?m;     
  //@ close mutex_inv(m,read_write(b,rd,wr));
  //@ wait_level_lt_below_obs(level(m), level(rd), O);    
  mutex_acquire(b->m);
  //@ open read_write(b,rd,wr)(_,_);
  //@ g_chrgl(rd);  
  //@ g_chrgl(wr);
  //@ assert [_]b->gw |-> ?gw;  
  //@ inc_ctr(gw);
  //@ assert [_]b->gwtrs |-> ?wwrtrs;
  while (b->aw + b->ar > 0)
  /*@ invariant b->aw |-> ?aw &*& 
	b->ar |-> ?ar &*& 
	b->ww |-> ?ww &*& 
	[_]b->m |-> m &*& 
	[_]b->vr |-> rd &*& 
	[_]b->vw |-> wr &*& 
	[_]b->gw |-> gw &*&
	[_]b->grdrs |-> ardrs &*&   
	[_]b->gwtrs |-> wwrtrs &*&   
	[_]b->gawtrs |-> awrtrs &*&   
	ctr(gw,?Cw) &*&
	ctr(ardrs,ar) &*&  
	ctr(wwrtrs,ww) &*&    
	ctr(awrtrs,aw) &*&   
	[_]cond(rd,nothing,nil) &*&
	[_]cond(wr,creditor(b),nil) &*&
	aw >= 0 &*& 
	ar >= 0 &*& 
	ww >= 0 &*&
	mutex_held(m, _, ?Wt, ?Ot) &*&
	aw + ww < Ot(rd) &*&
	Wt(wr) + Cw + aw + ar <= Ot(wr) &*&
	Wt(wr) < 1 || Wt(wr) < Ot(wr) &*&
	obs(cons((void*)wr,cons((void*)rd,cons(m,O)))) &*& 
	tic(gw); @*/
  {
    b->ww = b->ww + 1;
    //@ inc_ctr(wwrtrs);
    //@ dec_ctr(gw);
    //@ close read_write(b,rd,wr)(finc(Wt,wr),Ot);
    //@ close mutex_inv(m,read_write(b,rd,wr));
    /*@ produce_lemma_function_pointer_chunk spurious(read_write(b,rd,wr), creditor(b), wr)() {
     open read_write(b,rd,wr)(?Wt2,?Ot2);
     assert [_]b->gw |-> ?gw2;
     inc_ctr(gw2);
     close read_write(b,rd,wr)(fdec(Wt2,wr),Ot2);
     close creditor(b)();}; @*/
    //@ remove_all_all(fst(level(rd)));
  //@ wait_level_lt_below_obs(level(wr), level(rd), O);        
    //@ below_count(wr,O);    
    //@ count_same(wr,O);
    cvar_spwk_wait(b->vw, b->m);
    //@ open read_write(b,rd,wr)(_,_);

    b->ww = b->ww - 1;
    //@ dec_ctr(wwrtrs);    
    //@ open creditor(b)();
   }   
  b->aw = b->aw + 1;
  //@ inc_ctr(awrtrs);  
  //@ dec_ctr(gw);
  //@ close read_write(b,rd,wr)(Wt,Ot);  
  //@ close mutex_inv(m,read_write(b,rd,wr));  
  mutex_release(b->m);
  //@ leak [_]mutex(m);
}

void writer_exit(struct read_write *b)
  //@ requires [_]reader_writer(b, ?rd, ?wr, ?ardrs, ?awrtrs) &*& obs(cons(wr,cons(rd,?O))) &*& tic(awrtrs) &*& w_level_below_all(rd,O) == true;
  //@ ensures [_]reader_writer(b, rd, wr, ardrs, awrtrs) &*& obs(O);
{
  //@ open reader_writer(b,rd,wr, ardrs, awrtrs);
  //@ assert [_]b->m |-> ?m;     
  //@ close mutex_inv(m,read_write(b,rd,wr));
  //@ wait_level_lt_below_obs(level(m), level(rd), O);      
  mutex_acquire(b->m);
  //@ open read_write(b,rd,wr)(?Wt2,?Ot2);
  b->aw = b->aw - 1;
  //@ dec_ctr(awrtrs); 
  //@ assert [_]b->gw |-> ?gw;    
  /*@ if (Wt2(wr)>0){
        inc_ctr(gw);
        close creditor(b)();
      }
  @*/
  cvar_signal(b->vw); 
  //@ minus_nil(cons(m,cons(wr,cons(rd,O))));
  //@ inc_ctr(gw);  
  //@ dec_ctr(gw);  
  //@ g_dischl(wr);   
  if (b->ww == 0){
    //@ assert mutex_held(m,_,?Wt0,?Ot0);    
    //@ n_times_no_transfer(Wt0(b->vr));
    cvar_broadcast(b->vr);
  }
  //@ g_dischl(rd);
  //@ assert mutex_held(m,_,?Wte,?Ote);  
  //@ close read_write(b,rd,wr)(Wte,Ote);       
  //@ close mutex_inv(m,read_write(b,rd,wr));  
  mutex_release(b->m);     
  //@ leak [_]mutex(m);
}
