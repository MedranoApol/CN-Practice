// insertTree.c

// ** verification for inserting a new node into binary tree
// ** It implements an algorithm that will insert the node at its appropiate spot
// ** depending on its value relative to the rest of the nodes

#include "tree.h"
#include "createTreeNode.c"

/*@ 
function [rec] (datatype tree) insert (datatype tree sapling, i32 value)
{
    match sapling 
    {
        Tree_Nil{} => 
        {
            Tree_Cons{root: value, left: Tree_Nil{}, right: Tree_Nil{}}
        }
        Tree_Cons{root: rt, left: lb, right: rb} => 
        {

            ((value < rt) ? Tree_Cons {root: rt, left: insert(lb, value), right: rb} :
            Tree_Cons {root: rt, left: lb, right: insert(rb, value)})
        }
    }
}
@*/

struct TreeNode* TreeNode_insert(struct TreeNode* t, int value)
/*@ requires take T1 = IntTree(t);
    ensures take ret = IntTree(return);  
                !is_null(return);                                                    
@*/
{
    if (t == 0)
    {
        // /*@ unfold insert(Tree_Cons {left: Tree_Nil {}, right: Tree_Nil {}, root: 1i32}, 0i32); @*/
        // /*@ unfold insert(Tree_Cons {left: Tree_Nil {}, right: Tree_Nil {}, root: 1i32}, 1i32); @*/
        // /*@ unfold insert(Tree_Cons {left: Tree_Nil {}, right: Tree_Nil {}, root: 1i32}, 2i32); @*/
        // /*@ unfold insert(T1, value); @*/
        struct TreeNode *add = TreeNode_create_node(value);
        // /*@ assert((*add).root == value); @*/
        return add;
    }
    else
    {
        // /*@ unfold insert(Tree_Cons {left: Tree_Nil {}, right: Tree_Nil {}, root: 1i32}, 0i32); @*/
        // /*@ unfold insert(Tree_Cons {left: Tree_Nil {}, right: Tree_Nil {}, root: 1i32}, 1i32); @*/
        // /*@ unfold insert(Tree_Cons {left: Tree_Nil {}, right: Tree_Nil {}, root: 1i32}, 2i32); @*/
                    
        /*@ split_case(is_null(t)); @*/
        /*@ split_case(is_null((*t).left)); @*/
        /*@ split_case(is_null((*t).right)); @*/

        /*@ unfold insert(T1, value); @*/
        if (value < t->root)
        {
//            /*@ unfold insert(T1, value); @*/ 
//            if (t->left != 0)
//            {
//              /*@ assert((is_null((*t).left)) || ((*(*t).left).root < (*t).root)); @*/
//            }
//            t->left = TreeNode_insert(t->left, value);
//            /*@ assert(!is_null((*t).left)); @*/
//            /*@ assert ((*(*t).left).root < (*t).root); @*/
// 
//             return t;
                if (t->left == 0)
                {
                    /*@ unfold insert(T1, value); @*/
                    struct TreeNode *add = TreeNode_create_node(value);
                    // /*@ assert((*add).root == value); @*/
                    t->left = add;
                    
                    return t;
                }
                else 
                {

                    t->left = TreeNode_insert(t->left, value);
                    return t;
                }
        }   
        else
        {
           /*@ unfold insert(T1, value); @*/
        //    t->right = TreeNode_insert(t->right, value);
        //    /*@ assert (ptr_eq((*t).right, NULL) || (*(*t).right).root >= (*t).root); @*/ 
        //     return t;
            if (t->right == 0)
                {
                    /*@ unfold insert(T1, value); @*/
                    struct TreeNode *add = TreeNode_create_node(value);
                    // /*@ assert((*add).root == value); @*/
                    t->right = add;
                    return t;
                }
                else {
                    t->right = TreeNode_insert(t->right, value);
                    return t;
                }
        }
    }
}
