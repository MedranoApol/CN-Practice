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
             t1 == (ptr_eq(t, return) ? (t2.ret) : (t2.post));
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
        if (t->root == value)
        {
            return t;
        }
        else
        {
            /*@ unfold search(t1, value); @*/
            struct TreeNode* result;
            if (value < t->root)
            {   
                result = TreeNode_search(t->left, value);
                return result;
            }
            else
            {
                result = TreeNode_search(t->right, value);
                return result;
            }
            
        }
    }
}