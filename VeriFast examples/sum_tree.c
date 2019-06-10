#include "stdlib.h"
#include "levels.h"
#include "buffers.h"
#include "threads.h"

int rand();
    //@ requires true;
    //@ ensures true;

struct tree {
    struct tree *left;
    struct tree *right;
    int value;
};

/*@
predicate tree(struct tree *t) =
  t == 0 ? true :
    t->left |-> ?left &*& 
    t->right |-> ?right &*& 
    t->value |-> _ &*& 
    malloc_block_tree(t) &*&
    tree(left) &*& tree(right);
@*/

struct tree *make_tree(int depth)
  //@ requires true;
  //@ ensures tree(result);
{
  if (depth == 0) {
    //@ close tree(0);
    return 0;
  } else {
    struct tree *left = make_tree(depth - 1);
    struct tree *right = make_tree(depth - 1);
    int value = rand();
    struct tree *t = malloc(sizeof(struct tree));
    if (t == 0) abort();
    t->left = left;
    t->right = right;
    t->value = value;
    //@ close tree(t);
    return t;
  }
}

struct sum_data {
    struct tree* tree;
    struct buffer* buffer;
};

/*@
predicate_family_instance thread_run_data(tree_compute_sum_thread)(list<void*> tobs, struct sum_data *sum_data) =
  [_]sum_data->tree |-> ?tree &*&
  [_]sum_data->buffer |-> ?b &*& 
  [_]tree(tree) &*& 
  [_]buffer(b,?v) &*& 
  wait_level_below_obs(pair({tree_compute_sum}, 0r), cons(v,nil)) == true &*&
  tobs == cons(v,nil);
@*/

void tree_compute_sum_thread(struct sum_data *sum_data)  //@ : thread_run
  //@ requires thread_run_data(tree_compute_sum_thread)(?tobs,sum_data) &*& obs(tobs);
  //@ ensures obs(nil);
{
  //@ open thread_run_data(tree_compute_sum_thread)(_,_);
  tree_compute_sum(sum_data);
}

void tree_compute_sum(struct sum_data* sum_data)
    //@ requires obs(?O) &*& [_]sum_data->tree |-> ?tree &*& [_]sum_data->buffer |-> ?b &*& [_]tree(tree) &*& [_]buffer(b,?v) &*& wait_level_below_obs(pair({tree_compute_sum}, 0r), O) == true;
    //@ ensures obs(remove(v,O)) &*& [_]sum_data->tree |-> tree &*& [_]sum_data->buffer |-> b &*& [_]tree(tree) &*& [_]buffer(b,v);
{
  int result = 0;
  if (sum_data->tree != 0){
    //@ wait_level_betweens(pair({tree_compute_sum}, 0r), O);
    //@ leak exists(?wlevell);
    //@ close create_buffer_ghost_args(wlevell);    
    struct buffer* bl = create_buffer();    
    //@ leak buffer(bl,?vl);    

    //@ wait_level_betweens(pair({tree_compute_sum}, 0r), O);
    //@ leak exists(?wlevelr);
    //@ close create_buffer_ghost_args(wlevelr);    
    struct buffer* br = create_buffer();    
    //@ leak buffer(br,?vr);   

    //@ open tree(tree);        
    
    struct sum_data* sml = malloc(sizeof(struct sum_data));
    if (sml == 0) abort();
    sml->buffer = bl;
    sml->tree = tree->left;
    //@ leak malloc_block_sum_data(sml);     
    //@ leak [_]sml->tree |-> _;   
    //@ leak [_]sml->buffer |-> _;   

    struct sum_data* smr = malloc(sizeof(struct sum_data));
    if (smr == 0) abort();
    smr->buffer = br;
    smr->tree = tree->right;    
    //@ leak malloc_block_sum_data(smr);
    //@ leak [_]smr->tree |-> _;   
    //@ leak [_]smr->buffer |-> _;   
        
    //@ close thread_run_data(tree_compute_sum_thread)(cons(vl,nil),sml);
    thread_start(tree_compute_sum_thread, sml);   

    //@ close thread_run_data(tree_compute_sum_thread)(cons(vr,nil),smr);
    thread_start(tree_compute_sum_thread, smr);   
    //@ minus_nil(cons(vr,O));    
          
    //@ assume(func_lt(get_when_ready,tree_compute_sum));
    //@ wait_level_lt_below_obs(pair({get_when_ready}, 0r), pair({tree_compute_sum}, 0r), O);

    int leftSum = get_when_ready(bl);        
    int rightSum = get_when_ready(br);                    

    result = leftSum + rightSum + tree->value;
    }
  //@ assume(func_lt(set_and_notify,tree_compute_sum));
  //@ wait_level_lt_below_obs(pair({set_and_notify}, 0r), pair({tree_compute_sum}, 0r), O);
  set_and_notify(sum_data->buffer,result);    
}

void main()
  //@ requires obs(nil);
  //@ ensures obs(nil);
{
  struct tree* tree = make_tree(5);
  //@ leak tree(_);
  
  //@ close create_buffer_ghost_args(pair({(main)}, 0r));
  struct buffer* b = create_buffer();
  //@ leak buffer(b,?v);
  

  struct sum_data* sum_data = malloc(sizeof(struct sum_data));
  if (sum_data == 0) abort();
  sum_data->buffer = b;
  sum_data->tree = tree;    
  //@ leak malloc_block_sum_data(sum_data);
  //@ leak [_]sum_data->tree |-> _;   
  //@ leak [_]sum_data->buffer |-> _;   
        
  //@ close thread_run_data(tree_compute_sum_thread)(cons(v,nil),sum_data);
  thread_start(tree_compute_sum_thread, sum_data);   
}
