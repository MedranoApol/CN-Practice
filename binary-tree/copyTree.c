// copyTree.c

// ** takes in binary tree, Returns copy of it

#include "tree.h"

struct TreeNode* TreeNode_copy (struct TreeNode* t)
/*@ requires take L1 = IntTree(t);
    ensures  take L1_ = IntTree(t);
             take L2  = IntTree(return);
                  L1 == L1_;
                  L1 == L2;
@*/
{
    if (t == 0)
    {
        return TreeNode_nil();
    }
    else
    {
        struct TreeNode* new_left = TreeNode_copy(t->left);
        struct TreeNode* new_right = TreeNode_copy(t->right);
        return TreeNode_cons_both(t->root, new_left, new_right);
    }
}