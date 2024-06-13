// lengthTree.c

// ** Function which counts all the nodes in the tree

#include "tree.h"

/*@
function [rec] (u32) length (datatype tree sapling)
{
    match sapling 
    {
        Tree_Nil {} => 
        {
            0u32
        }
        Tree_Cons {root: rt, left: l, right: r} => 
        {
            let lb = length(l);
            let rb = length(r);
            (1u32 + lb + rb)
        }
    }
}

@*/

unsigned int TreeNode_length(struct TreeNode* t)
/*@ requires take t1 = IntTree(t);
    ensures take t2 = IntTree(t);
                 t1 == t2;
             return == length(t1);
@*/
{
    if (t == 0)
    {
        /*@ unfold length(t1); @*/
        return 0;
    }
    else
    {
        /*@ unfold length(t1); @*/
        unsigned int lb = TreeNode_length(t->left);
        unsigned int rb = TreeNode_length(t->right);
        return (1 + lb + rb);
    }   
}