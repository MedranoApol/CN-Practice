// insertTree.c

// ** verfication for inserting a new node into binary tree
// ** It implements an algorithm that will insert the node at its appropiate spot
// ** depending on its value relative to the rest of the nodes

#include "tree.h"
#include "createTreeNode.c"

/*@ 
function [rec] (datatype tree) insert (datatype tree sapling, i32 value)
{
    match sapling 
    {
        Tree_Nil{} => 
        {
            Tree_Cons{root: value, left: Tree_Nil{}, right: Tree_Nil{}}
        }
        Tree_Cons{root: rt, left: lb, right: rb} => 
        {
            ((value < rt) ? Tree_Cons {root: rt, left: insert(lb, value), right: rb} :
            (( value > rt) ? Tree_Cons {root: rt, left: lb, right: insert(rb, value)} : sapling))
        }
    }
}
@*/

struct TreeNode* TreeNode_insert(struct TreeNode* t, int value)
/*@ requires take root = IntTree(t);
    ensures take ret = IntTree(return);
        ret == insert(root, value);
@*/
{
    if (t == 0)
    {
        /*@ unfold insert(root, value); @*/
        return TreeNode_create_node(value);
    }
    else
    {
        /*@ unfold insert(root, value); @*/
        if (value < t->root)
        {
            t->left = TreeNode_insert(t->left, value);
        }   
        else if (value > t->root)
        {
            t->right = TreeNode_insert(t->right, value);
        }
    }
    return t;   
}
