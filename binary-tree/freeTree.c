// freeTree.c

// ** deallocates all the memory used up from binary tree thus deleting all the nodes
// ** pruning the tree and completely excavating the roots 

#include "tree.h"

void TreeNode_free_tree (struct TreeNode* t)
/*@  requires take v1 = IntTree(t); @*/
{
    if (t == 0)
    {
        return;
    } 
    else
    {
        TreeNode_free_tree(t->right);
        TreeNode_free_tree(t->left);
        freeTreeNode(t);
    }
}