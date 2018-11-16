#include "stdlib.h"
#include "channels.h"
#include "threads.h"

/*@
predicate_ctor Mch(channel ch)(pair<int, channel> message) = 
  Mr(snd(message)) == nil &*& 
  M(snd(message)) == Mch'(ch) &*& 
  M'(snd(message)) == M'ch' &*& 
  S(snd(message)) == false;

fixpoint list<void*> M'ch(pair<int, channel> message){
  return fst(message) == 0 ? nil : cons(snd(message),nil);
}

predicate_ctor Mch'(channel ch)(int message) = trandit(ch);

fixpoint list<void*> M'ch'(int message){
  return nil;
}

predicate_family_instance thread_run_data(server_thread)(list<void*> tobs, list<void*> tims, struct channel *ch) =
  M(ch) == Mch(ch) &*&
  M'(ch) == M'ch &*&
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
  //@ close MP(ch,Mch(ch));
  reqch' = receive(ch);
  //@ open Mch(ch)(_);
  while(fst(reqch') != 0)
    /*@ invariant obs(fst(reqch') == 0 ? nil : cons(snd(reqch'),nil),nil) &*&
          M(snd(reqch')) == Mch'(ch) &*&
          M'(snd(reqch')) == M'ch' &*&
          Mr(snd(reqch')) == nil &*&
          S(snd(reqch')) == false; @*/
    {
    //@ g_trandit(ch);
    //@ close MP(snd(reqch'),Mch'(ch)); 
    //@ g_trandit(snd(reqch'));    
    int res = process(fst(reqch'));       
    //@ close Mch'(ch)(res);    
    send(snd(reqch'), res);
    //@ close MP(ch,Mch(ch));
    reqch' = receive(ch);
    //@ open Mch(ch)(_);  
  }  
}

void client(struct channel *ch)
  /*@ requires obs(nil, nil) &*& trandit(ch) &*& M(ch) == Mch(ch) &*& Mr(ch) == cons(2r,nil) &*& M'(ch) == M'ch &*& S(ch) == true; @*/
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args<int>(2r, cons(ch,nil), nil, Mch'(ch), M'ch', false);
  struct channel *ch' = create_channel();
  //@ assume (M(ch')==Mch'(ch));
  //@ close MP(ch,Mch(ch));
  //@ g_credit(ch');
  int req = 12;
  //@ close Mch(ch)(pair(req,ch'));  
  send(ch,pair(req,ch'));
  //@ close MP(ch',Mch'(ch));
  receive(ch');
  //@ open Mch'(ch)(_);
  
  //@ close Mch(ch)(pair(0,ch'));
  //@ close MP(ch,Mch(ch));
  int done = 0;
  send(ch,pair(done,ch'));  
}

void main()
  //@ requires obs(nil, nil);
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args< pair<int, channel> >(1r, nil, cons(2r,nil), /*Mch(ch)*/ Mch(0), M'ch, true);
  struct channel *ch = create_channel();
  //@ assume (M(ch) == Mch(ch)); // Can be avoided by adding an extra ghost command g_init_channel
  
  //@ g_trandit(ch);  
  
  //@ close thread_run_data(server_thread)(nil,cons(ch,nil),ch);
  thread_start(server_thread, ch);
  client(ch);   
}
