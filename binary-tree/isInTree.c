// returns true or false, if value is an node in the binary tree

#include "tree.h"

/*@
function [rec] (u32) exists(datatype tree sapling, i32 value)
{
    match sapling 
    {
        Tree_Nil {} => 
        {
            0u32
        }
        Tree_Cons {root: rt, left: lb, right: rb} =>
        {   
            let lb_exist = exists(lb, value);
            let rb_exist = exists(rb, value);  
            ((value == rt)
                ? 1u32
                : ((value < rt) ? lb_exist  : rb_exist))
        }
    }
}
@*/


typedef enum { false, true } bool;

bool TreeNode_isInTree (struct TreeNode* t, int value)
/*@ requires take t1 = IntTree(t);
    ensures  take t2 = IntTree(t);
                  t1 == t2;
            return == exists(t1, value);
@*/
{   
    if (t == 0)
    {
        /*@ unfold exists(t1, value); @*/
        return false;
    }
    else
    {
        
        if (t->root == value)
        {
            /*@ unfold exists(t1, value); @*/
            return true;
        }
        else
        {
            if (value < t->root)
            {      
                /*@ unfold exists(t1, value); @*/
                return TreeNode_isInTree(t->left, value);
            }
            else
            {
                /*@ unfold exists(t1, value); @*/
                return TreeNode_isInTree(t->right, value);
            }
        }
    }
}