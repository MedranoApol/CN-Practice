// tree2.h

// ** Defines the CN datatype for the Binary Tree Nodes
// ** Also, defines CN predicates for initialization verification

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
        take left_b = IntTree(T.left);
        assert (left_b == Tree_Nil{} || rt(left_b) < T.root);
        take right_b = IntTree(T.right);
        assert (right_b == Tree_Nil{} || rt(right_b) >= T.root);
        return (Tree_Cons {root: T.root, left: left_b, right: right_b});
    }
}

@*/



