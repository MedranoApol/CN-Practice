// tree4.h

// ** Defines C functions that initialize or root insert for the Binary Tree data structure
// ** Also gives each function their own associating CN verification

struct TreeNode* TreeNode_nil()
/*@ ensures take ret = IntTree(return);
            ret == Tree_Nil{};
 @*/
{
  return 0;
}

struct TreeNode* TreeNode_cons_left(int r, struct TreeNode* left_b)
/*@ requires take lb = IntTree(left_b);
             take rb = IntTreeNull(left_b);
    ensures take ret = IntTree(return);
            ret == Tree_Cons{root: r, left: lb, right: rb};
 @*/
{
  struct TreeNode *p = mallocTreeNode();
  p->root = r;
  p->left = left_b;
  p->right = 0;
  return p;
}

struct TreeNode* TreeNode_cons_right(int r, struct TreeNode* right_b)
/*@ requires take rb = IntTree(right_b);
            take lb = IntTreeNull(right_b);
    ensures take ret = IntTree(return);
            ret == Tree_Cons{root: r, left: lb, right: rb};
 @*/
{
  struct TreeNode *p = mallocTreeNode();
  p->root = r;
  p->left = 0;
  p->right = right_b;
  return p;
}

struct TreeNode* TreeNode_cons_both(int r, struct TreeNode* left_b, struct TreeNode* right_b)
/*@ requires take lb = IntTree(left_b);
             take rb = IntTree(right_b);
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

//**** I know you don't insert from the top of binary tree usually  *****//
//**** This was for CN practice purposes since I had a guide        *****//