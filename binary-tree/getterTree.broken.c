// getterTree.broken.c

// ** Working version is in getterTree.c
// ** Keeping this around as motivation, I was this close to sending this in for help
// ** However, I was able to find a solution, so this displays a little bit of my madness


     //EVERYTHING WORKS UNTILL THE LAST TWO FUNCTIONS//
// ----------------------------------------------------------//
// ** Defines structure of Binary Tree Nodes                 //
// ** Defines the specs for allocating and freeing the Nodes //
// ----------------------------------------------------------//

struct TreeNode {
    int root;
    struct TreeNode* left;
    struct TreeNode* right;
};

extern struct TreeNode* mallocTreeNode();
/*@ spec mallocTreeNode();
    requires true;
    ensures take u = Block<struct TreeNode>(return);
            return != NULL;
@*/ 

extern void freeTreeNode (struct TreeNode *p);
/*@ spec freeTreeNode(pointer p);
    requires take u = Block<struct TreeNode>(p);
    ensures true;
@*/

//-----------------------------------------------------------------//
//  ** Defines the CN datatype for the Binary Tree Nodes           //
//  ** Also, defines CN predicates for intialization verification  //
//-----------------------------------------------------------------//

/*@

datatype tree {
    Tree_Nil {},
    Tree_Cons {i32 root, datatype tree left, datatype tree right}
}

predicate (datatype tree) IntTree(pointer p) {

    if (is_null(p))
    {
        return Tree_Nil{};
    }
    else
    {
        take T = Owned<struct TreeNode>(p);
        take lb = IntTree(T.left);
        take rb = IntTree(T.right);
        return (Tree_Cons {root: T.root, left: lb, right: rb});
    }
}

predicate (datatype tree) IntTreeNull(pointer p) {
  return Tree_Nil{};
}


@*/

//------------------------------------------------------------------------//
// ** Defines basic CN functions to extract a member of the tree datatype //
//------------------------------------------------------------------------//

/*@
function (i32) rt (datatype tree sapling) {
  match sapling {
    Tree_Nil {} => {
      0i32
    }
    Tree_Cons {root : root, left : _, right: _} => {
      root
    }
  }
}

function (datatype tree) lb (datatype tree sapling) {
  match sapling {
    Tree_Nil {} => {
      Tree_Nil {}
    }
    Tree_Cons {root : _, left : left, right: _} => {
      left
    }
  }
}

function (datatype tree) rb (datatype tree sapling) {
  match sapling {
    Tree_Nil {} => {
      Tree_Nil {}
    }
    Tree_Cons {root : _, left : _, right: right} => {
      right
    }
  }
}
@*/

                
//----------------------------------------------//
// **This one builds just fine, so issues here! //
//----------------------------------------------//

int get_Tree_Root (struct TreeNode *p)
/*@ requires take v1 = IntTree(p);
    ensures  take v2 = IntTree(p);
                  v1 == v2;
            return == rt(v2);
@*/
{
    if (p)
    {
        return p->root;
    }
    else
    {
        return 0;
    }
}

                /*BROKENNN BELOW*/
//--------------------------------------------//
// These next two functions give me issues,   //
// I will put the error message at the bottom //
//--------------------------------------------//

struct TreeNode* get_Tree_Left (struct TreeNode *p)
/*@ requires take v1 = IntTree(p);
    ensures  take v2 = IntTree(p);
             take v3 = IntTree(return);
        v1 == v2 && v3 == lb(v1) && v3 == lb(v2);
@*/
{
    if (p)
    {
        return p->left;
    }
    else
    {
        return 0;
    }
}

struct TreeNode* get_Tree_Right (struct TreeNode *p)
/*@ requires take v1 = IntTree(p);
    ensures  take v2 = IntTree(p);
             take v3 = IntTree(return);
        v1 == v2 && v3 == rb(v1) && v3 == rb(v2);
@*/
{
    if (p)
    {
        return p->right;
    }
    else
    {
        return 0;
    }
}