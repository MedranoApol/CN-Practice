// searchTree.c

// ** Search through the binary tree searching for a value

#include "tree.h"

/*@
function [rec] (datatype tree) search(datatype tree sapling, i32 value)
{
    match sapling 
    {
        Tree_Nil {} => 
        {
            Tree_Nil{}
        }
        Tree_Cons {root: rt, left: lb, right: rb} =>
        {
            let lb_search = search(lb, value);
            let rb_search = search(rb, value);
            ((value == rt) ? sapling :
            ((value < rt) ? lb_search : rb_search))
        }
    }
}

predicate {datatype tree post, datatype tree ret} BothOwned (pointer t, pointer r)
{
  if (ptr_eq(t,r)) {
    take rv = IntTree(r);
    return {post: rv, ret: rv};
  }
  else {
    take tv = IntTree(t);
    take rv = IntTree(r);
    return {post: tv, ret: rv};
  }
}

@*/

struct TreeNode* TreeNode_search(struct TreeNode* t, int value)
/*@ requires take t1 = IntTree(t);
    ensures  take t2 = BothOwned(t, return);
                  t2.post == t1;
                  t2.ret == search(t1, value);
@*/
{   
    if (t == 0)
    {
        /*@ unfold search(t1, value); @*/
        return 0;
    }
    else
    {
        /*@ unfold search(t1, value); @*/
        struct TreeNode* result_left = TreeNode_search(t->left, value);
        struct TreeNode* result_right = TreeNode_search(t->right, value);
        return ((value == t->root) ? t :
        ((value < t->root) ? result_left : result_right));
    }
}