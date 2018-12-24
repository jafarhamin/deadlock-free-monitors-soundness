/*
  Queues
*/

#include "stdlib.h"
#include "levels_with_importers.h"
#include "ghost_bags.h"

struct node{
    struct node *next;
    void* value;
};

struct queue {
    struct node *first;
    //@ void* gb;
};  

/*@
predicate node(struct node *first, void* gb, predicate(void* x) M, fixpoint(void* x, list<void*>) M', list<void*> elems) =
  first == 0 ? elems == nil :
  malloc_block_node(first) &*&  
  first->value |-> ?value &*&  
  first->next |-> ?next &*&
  gbag(gb,M'(value)) &*&
  M(value) &*&
  node(next, gb, M, M', ?next_elems) &*&
  elems == cons(value,next_elems);

predicate queue(struct queue *q, list<void*> elems, predicate(void* x) M, fixpoint(void* x, list<void*>) M') =
  q != 0 &*&
  q->first |-> ?first &*& 
  [_]q->gb |-> ?gb &*&
  Mr(q) == Mr(gb) &*&
  node(first, gb, M, M', elems);
  
predicate trandit_q(struct queue *q) = [_]q->gb |-> ?gb &*& trandit(gb);

predicate create_queue_ghost_args(list<real> Mr, predicate(void* x) M, fixpoint(void* x, list<void*>) M') = true;  

predicate lseg(struct node *first, struct node *last, void* gb, predicate(void* x) M, fixpoint(void* x, list<void*>) M', list<void*> elems) =
    first == last ?
        elems == nil
    :
        first != 0 &*&
        first->value |-> ?value &*& first->next |-> ?next &*& malloc_block_node(first) &*& gbag(gb,M'(value)) &*& M(value) &*&

        lseg(next, last, gb, M, M', ?next_elems) &*& elems == cons(value,next_elems);

lemma void nodes_to_lseg_lemma(struct node *first)
    requires node(first, ?gb, ?M, ?M', ?elems);
    ensures lseg(first, 0, gb, M, M', elems);
{
    open node(first, gb, M, M', elems);
    if (first != 0) {
        nodes_to_lseg_lemma(first->next);
    }
    close lseg(first, 0, gb, M, M', elems);
}

lemma void lseg_to_nodes_lemma(struct node *first)
    requires lseg(first, 0, ?gb, ?M, ?M', ?elems);
    ensures node(first, gb, M, M', elems);
{
    open lseg(first, 0, gb, M, M', elems);
    if (first != 0) {
        lseg_to_nodes_lemma(first->next);
    }
    close node(first, gb, M, M', elems);
}

lemma void lseg_add_lemma(struct node *first)
    requires lseg(first, ?last, ?gb, ?M, ?M', ?elems) &*& last != 0 &*& last->value |-> ?value &*& last->next |-> ?next &*& malloc_block_node(last) &*& gbag(gb,M'(value)) &*& M(value) &*& lseg(next, 0, gb, M, M', ?elems0);
    ensures lseg(first, next, gb, M, M', append(elems, cons(value,nil))) &*& lseg(next, 0, gb, M, M', elems0);
{
    open lseg(first, last, gb, M, M', elems);
    if (first == last) {
        close lseg(next, next, gb, M, M', nil);
    } else {
        lseg_add_lemma(first->next);
    }
    open lseg(next, 0, gb, M, M', elems0);
    close lseg(next, 0, gb, M, M', elems0);;
    close lseg(first, next, gb, M, M', append(elems, cons(value,nil)));
}


lemma void lseg_add_lemma2(struct node *first);
    requires lseg(first, ?mid, ?gb, ?M, ?M', ?elems1) &*& lseg(mid, ?last, gb, M, M', ?elems2) &*& first != last;
    ensures lseg(first, last, gb, M, M', append(elems1, elems2));

@*/
struct queue* create_queue()
    //@ requires create_queue_ghost_args(?Mr,?M,?M');
    //@ ensures queue(result,nil,M,M') &*& Mr(result) == Mr;
{
    //@ open create_queue_ghost_args(Mr,M,M');
    struct queue *queue = malloc(sizeof(struct queue));
    if (queue == 0) 
      abort();
    queue -> first = 0;
    //@ leak queue->gb |-> ?gb;
    //@ assume(Mr(queue) == Mr);    
    //@ assume(Mr(gb) == Mr);  
    //@ close node(0,gb,M,M',nil);      
    //@ close queue(queue,nil,M,M');
    //@ leak malloc_block_queue(queue);
    return queue;
}

int size_of(struct queue *q);
    //@ requires queue(q,?elems,?M,?M') &*& q != 0;
    //@ ensures queue(q,elems,M,M') &*& result == length(elems);

void enqueue(struct queue *q, void* value)
    //@ requires obs(?O,?R) &*& queue(q,?elems,?M,?M') &*& M(value) &*& trandit_q((void*)q) &*& forall(map(level_of, M'(value)),(mem')(Mr(q))) == true;
    //@ ensures obs(minus(O,M'(value)), R) &*& queue(q,append(elems,cons(value,nil)),M,M');
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->value = value;
    n->next = 0;
    //@ open queue(q,elems,M,M');
    //@ open trandit_q(q);      
    //@ gbag_add(q->gb,M'(value)); 
    if (q->first == 0){
      //@ open node(q->first, q->gb, M, M', elems);
      //@ close node(q->first, q->gb, M, M', elems);
      q->first = n;
      //@ close node(n,q->gb,M,M',cons(value,nil));
      //@ close queue(q,cons(value,elems),M,M');
      return;
    }
    //@ assert [_]q->gb |-> ?gb;

    struct node *first = q->first;
    //@ nodes_to_lseg_lemma(first);   
    struct node *tmp = first;   
    //@ close lseg(first, first, gb, M, M', nil);  
    //@ open lseg(first, 0, gb, M, M', elems);
    while (tmp->next != 0)
    /*@ invariant lseg(first, tmp, gb, M, M', ?elems0) &*& 
          malloc_block_node(tmp) &*& 
          tmp->value |-> ?tvalue &*& 
          tmp->next |-> ?tnext &*& 
          gbag(gb,M'(tvalue)) &*& 
          M(tvalue) &*&
	  tmp != 0 &*&
          lseg(tnext, 0, gb, M, M', ?elems1); @*/
    {
      tmp = tmp->next;
      //@ lseg_add_lemma(first);      
      //@ open lseg(tnext, 0, gb, M, M', elems1);      
    }
    //@ assume(elems == append(elems0,cons(tvalue,elems1)));
    tmp->next = n;
    //@ open lseg(0, 0, _, _, _, _); 
    //@ close lseg(0, 0, gb, M, M', nil);    
    //@ close lseg(n, 0, gb, M, M', cons(value,nil));
    //@ lseg_add_lemma(first);   
    //@ lseg_add_lemma2(first);   
    //@ lseg_to_nodes_lemma(first);    
    //@ close queue(q,append(elems,cons(value,nil)),M,M');
}

void* dequeue(struct queue *q)
    //@ requires obs(?O,?R) &*& queue(q,?elems,?M,?M') &*& [_]q->gb |-> ?gb &*& length(elems) >= 1;
    //@ ensures obs(append(O,M'(result)), remove(gb,R)) &*& queue(q,take(length(elems)-1,elems),M,M') &*& M(result);
{
  //@ open queue(q,elems,M,M');
  struct node *first = q->first;
  //@ open node(first,q->gb,M,M',elems);  
  //@ assert first->next |-> ?rnext;
  //@ assert node(rnext,gb,M,M',?elems0);    
  q->first = first->next;
  //@ gbag_remove(q->gb,M'(first->value));
  //@ assume(elems0 == take(length(elems)-1,elems));
  //@ close queue(q,take(length(elems)-1,elems),M,M');
  void* result = first->value;
  free(first);
  return result;
}

#endif