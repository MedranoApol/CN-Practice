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
            let left_branch = search(lb, value);
            let right_branch = search(rb, value);
            ((value == rt) ? sapling :
            ((value < rt) ? left_branch : right_branch))
        }
    }
}


@*/

struct TreeNode* TreeNode_search(struct TreeNode* t, int value)
/*@ requires take t1 = IntTree(t);
    ensures  take t2 = IntTree(t);
                  t1 == t2;
             take ret = Owned<struct TreeNode>(return);
             take ret_left = IntTree(ret.left);
             take ret_right = IntTree(ret.right);
             take retur = IntTree(return);
             let result = search(t1, value);
            retur == (is_null(return) ? Tree_Nil{} : Tree_Cons{root: value, left: ret_left, right: ret_right});
            retur == result;
@*/
{   
    if (t == 0)
    {
        /*@ unfold search(t1, value); @*/
        return 0;
    }
    else
    {
        
        if (t->root == value)
        {
            /*@ unfold search(t1, value); @*/
            return t;
        }
        else
        {
            if (value < t->root)
            {   
                
                return TreeNode_search(t->left, value);
            }
            else
            {
                return TreeNode_search(t->right, value);
            }
        }
    }
}