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
@*/

struct TreeNode* TreeNode_search(struct TreeNode* t, int value)
/*@ requires take t1 = Owned<struct TreeNode>(t);
             take t1_ = IntTree(t);
             t != NULL;
    ensures  take t2 = Owned<struct TreeNode>(t);
             take ret = IntTree(return);
             let result = search(t1_, value);
             ret == (is_null(return) ? Tree_Nil{} : result);
             t1 == t2;
@*/
{   
    if (t == 0)
    {
        /*@ unfold search(t1_, value); @*/
        return 0;
    }
    else
    {
        /*@ unfold search(t1_, value); @*/
        struct TreeNode* result_left = TreeNode_search(t->left, value);
        struct TreeNode* result_right = TreeNode_search(t->right, value);
        if (value == t->root) {
            return t;
        } else if (value < t->root) {
            return result_left;
        } else {
            return result_right;
        }
    }
}