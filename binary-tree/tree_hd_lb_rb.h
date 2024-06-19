// tree3.h

// ** Defines basic CN functions to extract a member of the tree datatype

/*@
function (i32) rt (datatype tree sapling) 
{
  match sapling 
  {
    Tree_Nil {} => 
    {
      0i32
    }
    Tree_Cons {root : root, left : _, right: _} => 
    {
      root
    }
  }
}

function (datatype tree) lb (datatype tree sapling) 
{
  match sapling 
  {
    Tree_Nil {} => 
    {
      Tree_Nil {}
    }
    Tree_Cons {root : _, left : left, right: _} => 
    {
      left
    }
  }
}

function (datatype tree) rb (datatype tree sapling) 
{
  match sapling 
  {
    Tree_Nil {} => 
    {
      Tree_Nil {}
    }
    Tree_Cons {root : _, left : _, right: right} => 
    {
      right
    }
  }
}
@*/
