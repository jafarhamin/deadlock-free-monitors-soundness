#include "stdlib.h"
#include "channels.h"
#include "threads.h"

/*@
predicate_ctor Mch(channel ch)(pair<int, channel> message) = 
  [_]channel(snd(message),Mch'(ch),M'ch') &*&
  Mr(snd(message)) == nil &*& 
  S(snd(message)) == false;

fixpoint list<void*> M'ch(pair<int, channel> message){
  return fst(message) == 0 ? nil : cons(snd(message),nil);
}

predicate_ctor Mch'(channel ch)(int message) = trandit(ch);

fixpoint list<void*> M'ch'(int message){
  return nil;
}

predicate_family_instance thread_run_data(server_thread)(list<void*> tobs, list<void*> tims, struct channel *ch) =
  [_]channel(ch,Mch(ch),M'ch) &*&
  S(ch) == true &*&
  tobs == nil &*&
  tims == cons(ch,nil);
@*/

int process(int request)
  //@ requires true;
  //@ ensures true;
{
  return 1;
}

void server_thread(struct channel *ch)  //@ : thread_run
  //@ requires thread_run_data(server_thread)(?tobs, ?tims, ch) &*& obs(tobs, tims);
  //@ ensures obs(nil, nil);
{
  //@ open thread_run_data(server_thread)(_,_,_);
  pair<int, channel> reqch';
  reqch' = receive(ch);
  //@ open Mch(ch)(_);
  while(fst(reqch') != 0)
    /*@ invariant obs(fst(reqch') == 0 ? nil : cons(snd(reqch'),nil),nil) &*&
          [_]channel(ch,Mch(ch),M'ch) &*&
          [_]channel(snd(reqch'),Mch'(ch),M'ch') &*&
          Mr(snd(reqch')) == nil &*&
          S(snd(reqch')) == false; @*/
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
  /*@ requires obs(nil, nil) &*& [_]channel(ch,Mch(ch),M'ch) &*& trandit(ch) &*& Mr(ch) == cons(2r,nil) &*& S(ch) == true; @*/
  //@ ensures obs(nil, nil) &*& trandit(ch);
{
  //@ close create_channel_ghost_args(2r, nil, false);
  struct channel *ch' = create_channel();
  //@ close init_channel_ghost_args<int>(Mch'(ch), M'ch');
  //@ init_channel(ch');  
  //@ leak channel(ch',Mch'(ch),M'ch');
  //@ g_credit(ch');
  int req = 12;
  //@ close Mch(ch)(pair(req,ch'));  
  send(ch,pair(req,ch'));
  int res = receive(ch');
  //@ open Mch'(ch)(_);
}

void terminating_client(struct channel *ch)
  /*@ requires obs(nil, nil) &*& [_]channel(ch,Mch(ch),M'ch) &*& trandit(ch) &*& Mr(ch) == cons(2r,nil) &*& S(ch) == true; @*/
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args(2r, nil, false);
  struct channel *ch' = create_channel();
  //@ close init_channel_ghost_args<int>(Mch'(ch), M'ch');
  //@ init_channel(ch');  
  //@ leak channel(ch',Mch'(ch),M'ch');
  //@ g_credit(ch');
  int req = 12;
  //@ close Mch(ch)(pair(req,ch'));  
  send(ch,pair(req,ch'));
  int res = receive(ch');
  //@ open Mch'(ch)(_);
  //@ close Mch(ch)(pair(0,ch'));
  int done = 0;
  send(ch,pair(done,ch'));  
}

void main_1()
  //@ requires obs(nil, nil);
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args(1r, cons(2r,nil),true);
  struct channel *ch = create_channel();
  //@ close init_channel_ghost_args< pair<int, channel> >(Mch(ch), M'ch);
  //@ init_channel(ch);
  //@ leak channel(ch,Mch(ch),M'ch);  
  //@ g_trandit(ch);  
  
  //@ close thread_run_data(server_thread)(nil,cons(ch,nil),ch);
  thread_start(server_thread, ch);
  client(ch);
  //@ leak trandit(ch);   
}

void main_2()
  //@ requires obs(nil, nil);
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args(1r, cons(2r,nil),true);
  struct channel *ch = create_channel();
  //@ close init_channel_ghost_args< pair<int, channel> >(Mch(ch), M'ch);
  //@ init_channel(ch);
  //@ leak channel(ch,Mch(ch),M'ch);  
  //@ g_trandit(ch);  
  
  //@ close thread_run_data(server_thread)(nil,cons(ch,nil),ch);
  thread_start(server_thread, ch);
  terminating_client(ch);
}
