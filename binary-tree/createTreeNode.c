// createTreeNode.c

// ** Initializes new node with value given as its argument

#include "tree.h"

struct TreeNode* TreeNode_create_node(int value)
/*@ ensures take T = IntTree(return);
        T == Tree_Cons {root: value, left: Tree_Nil{}, right: Tree_Nil{}};
        !is_null(return);
        rt(T) == value;
@*/
{
    struct TreeNode* node = mallocTreeNode();
    node->root = value;
    node->left = 0;
    node->right = 0;
    return node;
}