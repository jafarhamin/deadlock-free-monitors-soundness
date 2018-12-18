#include "stdlib.h"
#include "channels.h"
#include "threads.h"

/*@
fixpoint bool U<T>(T msg){
  return true;
}

fixpoint bool C(pair<int, channel> msg){
  return fst(msg) == 0;
}

predicate_ctor Mch(channel ch)(pair<int, channel> message) = 
  [_]channel(snd(message),Mch'(ch),M'ch',U) &*&
  Mr(snd(message)) == nil &*& 
  Ser(snd(message)) == false;

fixpoint list<void*> M'ch(void* ch, pair<int, channel> message){
  return fst(message) == 0 ? nil : cons(snd(message),nil);
}

predicate_ctor Mch'(channel ch)(int message) = trandit(ch);

fixpoint list<void*> M'ch'(int message){
  return nil;
}

predicate_family_instance thread_run_data(server_thread)(list<void*> tobs, list<void*> tims, struct channel *ch) =
  [_]channel(ch,Mch(ch),(M'ch)(ch),C) &*&
  credit(ch) &*&
  Mr(ch) == cons(1r,nil) &*&
  level_of(ch) == 2r &*&
  Ser(ch) == false &*&
  tobs == nil &*&
  tims == cons(ch,nil);
@*/

int process(int request)
  //@ requires true;
  //@ ensures 1 < result;
{
  return 2;
}

int done()
  //@ requires true;
  //@ ensures result == 0 ;
{
  return 0;
}

void server(struct channel *ch)
  //@ requires obs(nil, cons(ch,nil)) &*& [_]channel(ch,Mch(ch),(M'ch)(ch),C) &*& credit(ch) &*& Mr(ch) == cons(1r,nil) &*& level_of(ch) == 2r &*& Ser(ch) == false;
  //@ ensures obs(nil, nil);
{
  pair<int, channel> reqch';
  reqch' = receive(ch);
  //@ open Mch(ch)(_);
  int done = done();
  while(fst(reqch') != done)
    /*@ invariant obs(fst(reqch') == 0 ? nil : cons(snd(reqch'),nil),nil) &*&
          (fst(reqch') == 0 ? true : credit(ch)) &*&
          [_]channel(ch,Mch(ch),(M'ch)(ch),C) &*&
          [_]channel(snd(reqch'),Mch'(ch),M'ch',U) &*&
          Mr(snd(reqch')) == nil; @*/
    {
    //@ g_trandit(ch);
    int res = process(fst(reqch'));       
    //@ close Mch'(ch)(res);  
    send(snd(reqch'), res);
    reqch' = receive(ch);
    //@ open Mch(ch)(_);  
  }  
}

void client(struct channel *ch)
  //@ requires obs(cons(ch,nil), nil) &*& [_]channel(ch,Mch(ch),(M'ch)(ch),C) &*& trandit(ch) &*& Mr(ch) == cons(1r,nil) &*& Ser(ch) == false &*& level_of(ch) == 2r;
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args(1r, nil, false);
  struct channel *ch' = create_channel();
  //@ close init_channel_ghost_args<int>(Mch'(ch), M'ch', U);
  //@ init_channel(ch');  
  //@ leak channel(ch',Mch'(ch),M'ch',U);
  //@ g_credit(ch');
  int req = 12;
  //@ close Mch(ch)(pair(req,ch'));  
  send(ch,pair(req,ch'));
  int res = receive(ch');
  //@ open Mch'(ch)(_);
  
  //@ g_credit(ch');
  //@ close Mch(ch)(pair(req,ch'));  
  send(ch,pair(req,ch'));
  res = receive(ch');
  //@ open Mch'(ch)(_);

    
  //@ close Mch(ch)(pair(0,ch'));
  int done = done();
  send(ch,pair(done,ch')); 
}

void server_thread(struct channel *ch)  //@ : thread_run
  //@ requires thread_run_data(server_thread)(?tobs, ?tims, ch) &*& obs(tobs, tims);
  //@ ensures obs(nil, nil);
{
  //@ open thread_run_data(server_thread)(_,_,_);
  server(ch);
}

void main()
  //@ requires obs(nil, nil);
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args(2r, cons(1r,nil),false);
  struct channel *ch = create_channel();
  //@ close init_channel_ghost_args< pair<int, channel> >(Mch(ch), (M'ch)(ch),C);
  //@ init_channel(ch);
  //@ leak channel(ch,Mch(ch),(M'ch)(ch),_);  
  //@ g_trandit(ch);  
  //@ g_credit(ch);    
  
  //@ close thread_run_data(server_thread)(nil,cons(ch,nil),ch);
  thread_start(server_thread, ch);
  client(ch);
}
