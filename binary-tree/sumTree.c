// sumTree.c

// ** Sums up all the nodes of the binary tree

#include "tree.h"

/*@
function [rec] (u32) sum(datatype tree sapling)
{
    match sapling 
    {
        Tree_Nil {} => 
        {
            0u32
        }
        Tree_Cons {root: rt, left: l, right: r} => 
        {
            let rt_val = (u32) rt;
            let sum_lb = sum(l);
            let sum_rb = sum(r);
            (rt_val + sum_lb + sum_rb)
        }
    }
}


@*/

unsigned int TreeNode_sum(struct TreeNode* t)
/*@ requires take t1 = IntTree(t);
    ensures  take t2 = IntTree(t);
                 t1 == t2;
             return == sum(t1);
@*/
{   
    
    if (t == 0)
    {
        /*@ unfold sum(t1); @*/
        return 0;
    }
    else
    {
        /*@ unfold sum(t1); @*/
        unsigned int sum_lb = TreeNode_sum(t->left);
        unsigned int sum_rb = TreeNode_sum(t->right);
        unsigned int root_val = t->root;
        return (root_val + sum_lb + sum_rb);
    }   
}