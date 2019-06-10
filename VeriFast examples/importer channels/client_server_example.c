#include "stdlib.h"
#include "channels.h"
#include "threads.h"

/*@
predicate Mch(pair<int, channel> message) = [_]channel(snd(message),Mch',M'ch') &*& Mr(snd(message)) == nil;

fixpoint list<void*> M'ch(pair<int, channel> message){
  return cons(snd(message),nil);
}

predicate Mch'(int message) = true;

fixpoint list<void*> M'ch'(int message){
  return nil;
}

predicate_family_instance thread_run_data(server_thread)(list<void*> tobs, list<void*> tims, struct channel *ch) =
  [_]channel(ch,Mch,M'ch) &*&
  credit(ch) &*& 
  Ser(ch) == false &*&  
  tobs == nil &*&
  tims == cons(ch,nil);
@*/

void server_thread(struct channel *ch)  //@ : thread_run
  //@ requires thread_run_data(server_thread)(?tobs, ?tims, ch) &*& obs(tobs, tims);
  //@ ensures obs(nil, nil);
{
  //@ open thread_run_data(server_thread)(tobs,tims,ch);
  server(ch);
}


void client(struct channel *ch)
  //@ requires obs(cons(ch,nil), nil) &*& [_]channel(ch,Mch,M'ch) &*& trandit(ch) &*& Mr(ch) == cons(1r,nil);
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args(1r, nil, false);
  struct channel *ch' = create_channel<int>();
  //@ close init_channel_ghost_args<int>(Mch', M'ch');  
  //@ init_channel(ch');
  //@ leak channel(ch',Mch',M'ch');
  //@ close Mch(pair(12,ch'));
  //@ g_credit(ch');
  send(ch,pair(12,ch'));
  int res = receive(ch');
  //@ open Mch'(_);  
}

void server(struct channel *ch)
  //@ requires obs(nil, cons(ch,nil)) &*& [_]channel(ch,Mch,M'ch) &*& credit(ch) &*& Ser(ch) == false;
  //@ ensures obs(nil, nil);
{
  pair<int, channel> reqch';
  reqch' = receive(ch);
  //@ open Mch(_);  
  //@ close Mch'(12);
  send(snd(reqch'),12);
}

void main()
  //@ requires obs(nil, nil);
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args(1r, cons(1r,nil), false);
  struct channel *ch = create_channel();
  //@ close init_channel_ghost_args< pair<int, channel> >(Mch, M'ch);
  //@ init_channel(ch);  
  //@ leak channel(ch,_,_);
  //@ g_credit(ch);
  //@ g_trandit(ch);  
  
  //@ close thread_run_data(server_thread)(nil,cons(ch,nil),ch);
  thread_start(server_thread, ch);
  client(ch);
}
