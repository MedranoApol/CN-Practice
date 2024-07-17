// copyTree.c

// ** takes in binary tree, Returns copy of it

#include "tree.h"

struct TreeNode* TreeNode_nil()
/*@ ensures take ret = IntTree(return);
            ret == Tree_Nil{};
 @*/
{
  return 0;
}

struct TreeNode* TreeNode_cons_both(int r, struct TreeNode* left_b, struct TreeNode* right_b)
/*@ requires take lb = IntTree(left_b);
             take rb = IntTree(right_b);
             (lb == Tree_Nil{} || rt(lb) < r) && (rb == Tree_Nil{} || rt(rb) >= r);
    ensures take ret = IntTree(return);
            ret == Tree_Cons{root: r, left: lb, right: rb};
@*/
{
  struct TreeNode *p = mallocTreeNode();
  p->root = r;
  p->left = left_b;
  p->right = right_b;
  return p;
}

struct TreeNode* TreeNode_copy (struct TreeNode* t)
/*@ requires take T1 = IntTree(t);
    ensures  take T1_ = IntTree(t);
             take T2  = IntTree(return);
                  T1 == T1_;
                  T1 == T2;
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