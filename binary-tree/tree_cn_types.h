// tree2.h

// ** Defines the CN datatype for the Binary Tree Nodes
// ** Also, defines CN predicates for intialization verification

/*@

datatype tree {
    Tree_Nil {},
    Tree_Cons {i32 root, datatype tree left, datatype tree right}
}

predicate (datatype tree) IntTree(pointer p) 
{
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

predicate (datatype tree) IntTreeNull(pointer p) 
{
  return Tree_Nil{};
}

@*/



