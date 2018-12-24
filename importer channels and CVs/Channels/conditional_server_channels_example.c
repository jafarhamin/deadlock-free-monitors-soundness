#include "stdlib.h"
#include "channels.h"
#include "threads.h"

/*@
predicate Mch'(pair<int, channel> message) = 
  [_]channel(snd(message),Mch,M'ch) &*&
  level_of(snd(message)) == 2r &*&     
  Mr(snd(message)) == cons(1r,nil) &*&   
  trandit(snd(message));  

fixpoint list<void*> M'ch'(pair<int, channel> message){
  return cons(snd(message),nil);
}

predicate Mch(pair<int, channel> message) = 
  [_]channel(snd(message),Mch',M'ch') &*&
  Mr(snd(message)) == cons(2r,nil) &*& 
  (fst(message) == 0 ? true : trandit(snd(message))) &*&
  Ser(snd(message)) == false;

fixpoint list<void*> M'ch(pair<int, channel> message){
  return fst(message) == 0 ? nil : cons(snd(message),nil);
}

predicate Ms(pair<int, channel> message) = 
  [_]channel(snd(message),Mch',M'ch') &*&
  Mr(snd(message)) == cons(2r,nil) &*& 
  trandit(snd(message)) &*&
  Ser(snd(message)) == false;

fixpoint list<void*> M's(pair<int, channel> message){
  return cons(snd(message),nil);
}

predicate_family_instance thread_run_data(server_thread)(list<void*> tobs, list<void*> tims, struct channel *s) =
  [_]channel(s,Ms,M's) &*&
  Mr(s) == cons(1r,nil) &*&
  Ser(s) == true &*&
  tobs == nil &*&
  tims == cons(s,cons(s,nil));
  
predicate_family_instance thread_run_data(cserver_thread)(list<void*> tobs, list<void*> tims, struct channel *ch) =
  [_]channel(ch,Mch,M'ch) &*&
  credit(ch) &*&
  Mr(ch) == cons(1r,nil) &*&
  level_of(ch) == 2r &*&
  Ser(ch) == false &*&
  tobs == nil &*&
  tims == cons(ch,nil);  

predicate_family_instance thread_run_data(client_thread)(list<void*> tobs, list<void*> tims, struct channel *s) =
  [_]channel(s,Ms,M's) &*& 
  trandit(s) &*& 
  Mr(s) == cons(1r,nil) &*& 
  Ser(s) == true &*&
  tobs == nil &*&
  tims == nil;
@*/

int process(int request)
  //@ requires true;
  //@ ensures 1 < result ;
{
  return 2;
}

int done()
  //@ requires true;
  //@ ensures result == 0 ;
{
  return 0;
}

int through()
  //@ requires true;
  //@ ensures result == 1 ;
{
  return 1;
}

void cserver(struct channel *ch)
  //@ requires obs(nil, cons(ch,nil)) &*& [_]channel(ch,Mch,M'ch) &*& credit(ch) &*& Mr(ch) == cons(1r,nil) &*& level_of(ch) == 2r &*& Ser(ch) == false;
  //@ ensures obs(nil, nil);
{
  pair<int, channel> reqch';
  reqch' = receive(ch);
  //@ open Mch(_);
  int done = done();
  while(fst(reqch') != done)
    /*@ invariant obs(fst(reqch') == 0 ? nil : cons(snd(reqch'),nil),nil) &*&
          (fst(reqch') == 0 ? true : trandit(snd(reqch'))) &*&
          [_]channel(ch,Mch,M'ch) &*&
          [_]channel(snd(reqch'),Mch',M'ch') &*&
          Mr(snd(reqch')) == cons(2r,nil); @*/
    {
    //@ g_trandit(ch);
    int res = process(fst(reqch'));
    //@ close Mch'(pair(res,ch));
    //@ assert [_]channel(snd(reqch'),Mch',M'ch');  
    //@ g_credit(ch);    
    send(snd(reqch'), pair(res,ch));
    reqch' = receive(ch);
    //@ open Mch(_);  
  }  
}

void server(struct channel *s)
  //@ requires obs(nil, cons(s,cons(s,nil))) &*& [_]channel(s,Ms,M's) &*& Mr(s) == cons(1r,nil) &*& Ser(s) == true;
  //@ ensures obs(nil, nil);
{
  pair<int, channel> reqch';
  while(true)
    //@ invariant obs(nil,cons(s,cons(s,nil))) &*& [_]channel(s,Ms,M's);
    {
    reqch' = receive(s);
    //@ open Ms(_);
    //@ assert [_]channel(snd(reqch'),Mch',M'ch');
    //@ close create_channel_ghost_args(2r, cons(1r,nil),false);
    struct channel *ch = create_channel();
    //@ close init_channel_ghost_args< pair<int, channel> >(Mch, M'ch);
    //@ init_channel(ch);
    //@ leak channel(ch,_,_);  
    int through = through();
    //@ g_trandit(ch);
    //@ g_credit(ch);    
    //@ close Mch'(pair(through,ch));    
    send(snd(reqch'),pair(through,ch));
    //@ close thread_run_data(cserver_thread)(nil,cons(ch,nil),ch);
    thread_start(cserver_thread, ch);
    //@ g_trandit(s);   
    //@ leak trandit(s);       
  }  
}

void client(struct channel *s)
  //@ requires obs(nil, nil) &*& [_]channel(s,Ms,M's) &*& trandit(s) &*& Mr(s) == cons(1r,nil) &*& Ser(s) == true;
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args(1r, cons(2r,nil), false);
  struct channel *ch' = create_channel();
  //@ close init_channel_ghost_args< pair<int, channel> >(Mch', M'ch');
  //@ init_channel(ch');  
  //@ leak channel(ch',_,_);
  //@ g_credit(ch');
  //@ g_trandit(ch');
  int through = through();
  //@ close Ms(pair(through,ch'));  
  send(s,pair(through,ch'));
  pair<int, channel> thrch;   
  thrch = receive(ch');
  //@ open Mch'(_);
  if (fst(thrch) != 1) abort();
  //@ g_trandit(ch');   
  //@ close Mch(pair(2,ch'));
  //@ g_credit(ch');
  send(snd(thrch), pair(2,ch'));   
  pair<int, channel> resch;   
  resch = receive(ch');  
  if (fst(resch) == 1) abort();  
  if (snd(resch) != snd(thrch)) abort();  
  //@ open Mch'(resch);
  int done = done();
  //@ close Mch(pair(done,ch'));
  send(snd(resch),pair(done,ch')); 
}

void server_thread(struct channel *s)  //@ : thread_run
  //@ requires thread_run_data(server_thread)(?tobs, ?tims, s) &*& obs(tobs, tims);
  //@ ensures obs(nil, nil);
{
  //@ open thread_run_data(server_thread)(_,_,_);
  server(s); 
}

void cserver_thread(struct channel *s)  //@ : thread_run
  //@ requires thread_run_data(cserver_thread)(?tobs, ?tims, s) &*& obs(tobs, tims);
  //@ ensures obs(nil, nil);
{
  //@ open thread_run_data(cserver_thread)(_,_,_);
  cserver(s); 
}

void client_thread(struct channel *s)  //@ : thread_run
  //@ requires thread_run_data(client_thread)(?tobs, ?tims, s) &*& obs(tobs, tims);
  //@ ensures obs(nil, nil);
{
  //@ open thread_run_data(client_thread)(_,_,_);
  client(s); 
}

void main()
  //@ requires obs(nil, nil);
  //@ ensures obs(nil, nil);
{
  //@ close create_channel_ghost_args(2r, cons(1r,nil),true);
  struct channel *s = create_channel();
  //@ close init_channel_ghost_args< pair<int, channel> >(Ms,M's);
  //@ init_channel(s);
  //@ leak channel(s,_,_);  
  //@ g_trandit(s);  
  //@ g_trandit(s);  

  //@ close thread_run_data(server_thread)(nil,cons(s,cons(s,nil)),s);
  thread_start(server_thread, s);
  
  //@ close thread_run_data(client_thread)(nil,nil,s);
  thread_start(client_thread, s);  
  
  client(s);  
}
