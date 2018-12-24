#include "stdlib.h"
#include "channels.h"
#include "threads.h"

/*@
predicate_ctor Ms(channel s)(pair<int, channel> message) = 
  [_]channel(snd(message),Mch'(s),(M'ch')(s)) &*&
  Mr(snd(message)) == nil &*& 
  Ser(snd(message)) == false;

fixpoint list<void*> M's(void* s, pair<int, channel> message){
  return cons(snd(message),nil);
}

predicate_ctor Mch'(channel s)(int message) = trandit(s);

fixpoint list<void*> M'ch'(void* ch, int message){
  return nil;
}

predicate_family_instance thread_run_data(server_thread)(list<void*> tobs, list<void*> tims, struct channel *s) =
  [_]channel(s,Ms(s),(M's)(s)) &*&
  Mr(s) == cons(1r,nil) &*&
  Ser(s) == true &*&
  tobs == nil &*&
  tims == cons(s,nil);
@*/

int process(int request)
  //@ requires true;
  //@ ensures true;
{
  return request;
}

void server(struct channel *s)
  //@ requires obs(nil, cons(s,nil)) &*& [_]channel(s,Ms(s),(M's)(s)) &*& Mr(s) == cons(1r,nil) &*& Ser(s) == true;
  //@ ensures obs(nil, nil);
{
  pair<int, channel> reqch';
  while(true)
    //@ invariant obs(nil,cons(s,nil)) &*& [_]channel(s,Ms(s),(M's)(s));
    {
    reqch' = receive(s);
    //@ open Ms(s)(_);    
    //@ g_trandit(s);
    int res = process(fst(reqch'));       
    //@ close Mch'(s)(res);  
    send(snd(reqch'), res);
  }  
}

void client(struct channel *s)
  //@ requires obs(nil, nil) &*& [_]channel(s,Ms(s),(M's)(s)) &*& trandit(s) &*& Mr(s) == cons(1r,nil) &*& Ser(s) == true;
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args(1r, nil, false);
  struct channel *ch' = create_channel();
  //@ close init_channel_ghost_args<int>(Mch'(s), (M'ch')(s));
  //@ init_channel(ch');  
  //@ leak channel(ch',Mch'(s),(M'ch')(s));
  //@ g_credit(ch');
  int req = 12;
  //@ close Ms(s)(pair(req,ch'));  
  send(s,pair(req,ch'));
  int res = receive(ch');
  //@ open Mch'(s)(_);
  //@ close Ms(s)(pair(0,ch'));
  int done = 0;
  send(s,pair(done,ch')); 
}

void server_thread(struct channel *s)  //@ : thread_run
  //@ requires thread_run_data(server_thread)(?tobs, ?tims, s) &*& obs(tobs, tims);
  //@ ensures obs(nil, nil);
{
  //@ open thread_run_data(server_thread)(_,_,_);
  server(s); 
}

void main()
  //@ requires obs(nil, nil);
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args(2r, cons(1r,nil),true);
  struct channel *s = create_channel();
  //@ close init_channel_ghost_args< pair<int, channel> >(Ms(s), (M's)(s));
  //@ init_channel(s);
  //@ leak channel(s,_,_);  
  //@ g_trandit(s);  
 
  //@ close thread_run_data(server_thread)(nil,cons(s,nil),s);
  thread_start(server_thread, s);
  client(s);
}
