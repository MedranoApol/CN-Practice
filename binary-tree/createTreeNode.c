// createTreeNode.c

// ** Intializes new node with value given as its argument

#include "tree.h"

struct TreeNode* TreeNode_create_node(int value)
/*@ ensures take N = IntTree(return);
        N == Tree_Cons {root: value, left: Tree_Nil{}, right: Tree_Nil{}};
@*/
{
    struct TreeNode* node = mallocTreeNode();
    node->root = value;
    node->left = 0;
    node->right = 0;
    return node;
}