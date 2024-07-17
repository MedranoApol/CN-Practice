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
            ((value == rt) ? sapling :
            ((value < rt) ? search(lb, value) : search(rb, value)))
        }
    }
}


@*/

struct TreeNode* TreeNode_search(struct TreeNode* t, int value)
/*@ requires take t1 = IntTree(t);
    ensures take t2 = IntTree(t);
    take ret = IntTree(return);
        ret == search(t1, value); 
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
            if (value < t->root)
            {   
                /*@ unfold search(t1, value); @*/
                return TreeNode_search(t->left, value);
            }
            else
            {
                /*@ unfold search(t1, value); @*/
                return TreeNode_search(t->right, value);
            }
        }
    }
}