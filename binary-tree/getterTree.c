// getterTree.c

// ** Extracts the members of a given tree node
// ** This is the C implementation of the CN-functions in tree3.h

#include "tree.h"

int get_Tree_Root (struct TreeNode *t)
/*@ requires take v1 = IntTree(t);
    ensures  take v2 = IntTree(t);
                  v1 == v2;
            return == rt(v2);
@*/
{
    if (t)
    {
        return t->root;
    }
    else
    {
        return 0;
    }
}

struct TreeNode* get_Tree_Left (struct TreeNode *t)
/*@ requires take v1 = Owned<struct TreeNode>(t);
             take v1_left = Owned<struct TreeNode>(v1.left);
    ensures  take v2 = Owned<struct TreeNode>(t);
             take v2_left = Owned<struct TreeNode>(v2.left);
             v1 == v2 && v1_left == v2_left;
    return == ((is_null(t)) ? (t) : (v1.left));
@*/
{
    if (t)
    {
        return t->left;
    }
    else
    {
        return 0;
    }
}

struct TreeNode* get_Tree_Right (struct TreeNode *t)
/*@ requires take v1 = Owned<struct TreeNode>(t);
             take v1_right = Owned<struct TreeNode>(v1.right);
    ensures  take v2 = Owned<struct TreeNode>(t);
             take v2_right = Owned<struct TreeNode>(v2.right);
             v1 == v2 && v1_right == v2_right;
    return == ((is_null(t)) ? (t) : (v1.right));
@*/
{
    if (t)
    {
        return t->right;
    }
    else
    {
        return 0;
    }
}