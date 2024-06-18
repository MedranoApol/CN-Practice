// lengthTree.c

// ** Function which counts all the nodes in the tree

#include "tree.h"

/*@
function [rec] (u32) depth (datatype tree sapling)
{
    match sapling 
    {
        Tree_Nil {} => 
        {
            0u32
        }
        Tree_Cons {root: rt, left: l, right: r} => 
        {
            let lb = depth(l);
            let rb = depth(r);
            ((lb > rb) ? (1u32 + lb) : (1u32 + rb))
        }
    }
}

@*/

unsigned int TreeNode_depth(struct TreeNode* t)
/*@ requires take t1 = IntTree(t);
    ensures take t2 = IntTree(t);
                 t1 == t2;
             return == depth(t1);
@*/
{
    if (t == 0)
    {
        /*@ unfold depth(t1); @*/
        return 0;
    }
    else
    {
        /*@ unfold depth(t1); @*/
        unsigned int lb = TreeNode_depth(t->left);
        unsigned int rb = TreeNode_depth(t->right);
        return ((lb > rb) ? (1 + lb) : (1 + rb));
    }   
}