#include "stdlib.h"
#include "channels.h"
#include "threads.h"

/*@
predicate Mch(pair<int, channel> message) = M(snd(message)) == Mch' &*& Mr(snd(message)) == nil &*& M'(snd(message)) == M'ch';

fixpoint list<void*> M'ch(pair<int, channel> message){
  return cons(snd(message),nil);
}

predicate Mch'(int message) = true;

fixpoint list<void*> M'ch'(int message){
  return nil;
}

predicate_family_instance thread_run_data(server_thread)(list<void*> tobs, list<void*> tims, struct channel *ch) =
  credit(ch) &*& 
  M(ch) == Mch &*&
  M'(ch) == M'ch &*&
  S(ch) == false &*&  
  tobs == nil &*&
  tims == cons(ch,nil);
@*/

void server_thread(struct channel *ch)  //@ : thread_run
  //@ requires thread_run_data(server_thread)(?tobs, ?tims, ch) &*& obs(tobs, tims);
  //@ ensures obs(nil, nil);
{
  //@ open thread_run_data(server_thread)(_,_,_);
  pair<int, channel> reqch';
  //@ close MP(ch,Mch);
  reqch' = receive(ch);
  //@ open Mch(_);  
  //@ close MP(snd(reqch'),Mch');  
  //@ close Mch'(12);
  //@ g_trandit(snd(reqch'));
  send(snd(reqch'),12);
}

void client(struct channel *ch)
  //@ requires obs(cons(ch,nil), nil) &*& trandit(ch) &*& M(ch) == Mch &*& Mr(ch) == cons(2r,nil) &*& M'(ch) == M'ch;
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args<int>(2r, cons(ch,nil), nil, Mch', M'ch', false);
  struct channel *ch' = create_channel();
  //@ assume (M(ch')==Mch');    
  //@ close Mch(pair(12,ch'));
  //@ close MP(ch,Mch);
  //@ g_credit(ch');
  send(ch,pair(12,ch'));
  //@ close MP(ch',Mch');
  receive(ch');
  //@ open Mch'(_);
}

void main()
  //@ requires obs(nil, nil);
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args< pair<int, channel> >(1r, nil, cons(2r,nil), Mch, M'ch, false);
  struct channel *ch = create_channel();
  //@ assume (M(ch) == Mch); // Can be avoided by adding an extra ghost command g_init_channel
    
  //@ g_credit(ch);
  //@ g_trandit(ch);  
  
  //@ close thread_run_data(server_thread)(nil,cons(ch,nil),ch);
  thread_start(server_thread, ch);
  client(ch);   
}
