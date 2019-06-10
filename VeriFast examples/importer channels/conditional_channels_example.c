#include "stdlib.h"
#include "channels.h"
#include "threads.h"

/*@
predicate_ctor Mch(channel ch)(pair<int, channel> message) = 
  [_]channel(snd(message),Mch'(ch),(M'ch')(ch)) &*&
  Mr(snd(message)) == cons(1r,nil) &*& 
  Ser(snd(message)) == false &*&
  fst(message) == 0 ? true : trandit(snd(message));

fixpoint list<void*> M'ch(pair<int, channel> message){
  return fst(message) == 0 ? nil : cons(snd(message),nil);
}

predicate_ctor Mch'(channel ch)(int message) = trandit(ch);

fixpoint list<void*> M'ch'(channel ch,int message){
  return cons(ch,nil);
}

predicate_family_instance thread_run_data(server_thread)(list<void*> tobs, list<void*> tims, struct channel *ch) =
  [_]channel(ch,Mch(ch),M'ch) &*&
  credit(ch) &*&
  Mr(ch) == cons(1r,nil) &*&
  level_of(ch) == 1r &*&
  Ser(ch) == false &*&
  tobs == nil &*&
  tims == cons(ch,nil);
@*/

int process(int request);
  //@ requires true;
  //@ ensures 1 < result;

int done();
  //@ requires true;
  //@ ensures result == 0 ;

void server_thread(struct channel *ch)  //@ : thread_run
  //@ requires thread_run_data(server_thread)(?tobs, ?tims, ch) &*& obs(tobs, tims);
  //@ ensures obs(nil, nil);
{
  //@ open thread_run_data(server_thread)(_,_,_);
  server(ch);
}

void client(struct channel *ch)
  //@ requires obs(cons(ch,nil), nil) &*& [_]channel(ch,Mch(ch),M'ch) &*& trandit(ch) &*& Mr(ch) == cons(1r,nil) &*& Ser(ch) == false &*& level_of(ch) == 1r;
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args(1r, cons(1r,nil), false);
  struct channel *ch' = create_channel();
  //@ close init_channel_ghost_args<int>(Mch'(ch), (M'ch')(ch));
  //@ init_channel(ch');  
  //@ leak channel(ch',_,_);
  //@ g_credit(ch');
  //@ g_trandit(ch');
  
  int req = 12;
  
  //@ close Mch(ch)(pair(req,ch'));  
  send(ch,pair(req,ch'));
  int res = receive(ch');
  //@ open Mch'(ch)(_);
  
  //@ g_credit(ch');
  //@ g_trandit(ch');  
  //@ close Mch(ch)(pair(req,ch'));  
  send(ch,pair(req,ch'));
  res = receive(ch');
  //@ open Mch'(ch)(_);

  //@ close Mch(ch)(pair(0,ch'));
  int done = done();
  send(ch,pair(done,ch')); 
}

void server(struct channel *ch)
  //@ requires obs(nil, cons(ch,nil)) &*& [_]channel(ch,Mch(ch),M'ch) &*& credit(ch) &*& Mr(ch) == cons(1r,nil) &*& level_of(ch) == 1r &*& Ser(ch) == false;
  //@ ensures obs(nil, nil);
{
  pair<int, channel> reqch';
  reqch' = receive(ch);
  //@ open Mch(ch)(_);
  int done = done();
  while(fst(reqch') != done)
    /*@ invariant obs(fst(reqch') == 0 ? nil : cons(snd(reqch'),nil),nil) &*&    
          (fst(reqch') == 0 ? true : trandit(snd(reqch'))) &*&
          [_]channel(ch,Mch(ch),M'ch) &*&
          [_]channel(snd(reqch'),Mch'(ch),(M'ch')(ch)) &*&
          Mr(snd(reqch')) == cons(1r,nil); @*/
    {
    //@ g_trandit(ch);
    int res = process(fst(reqch'));       
    //@ close Mch'(ch)(res);  
    //@ g_credit(ch);
    send(snd(reqch'), res);
    reqch' = receive(ch);
    //@ open Mch(ch)(_);  
  }  
}

void main()
  //@ requires obs(nil, nil);
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args(1r, cons(1r,nil),false);
  struct channel *ch = create_channel();
  //@ close init_channel_ghost_args< pair<int, channel> >(Mch(ch), M'ch);
  //@ init_channel(ch);
  //@ leak channel(ch,_,_);  
  //@ g_trandit(ch);  
  //@ g_credit(ch);    
  
  //@ close thread_run_data(server_thread)(nil,cons(ch,nil),ch);
  thread_start(server_thread, ch);
  client(ch);
}
