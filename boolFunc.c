typedef enum { false, true } bool;
/*
predicate (bool) RemainderEqualZero (i32 x, i32 y)
{
    (x != 0) && ()
}


predicate (bool) Eq_x_y (i32 x, i32 y)
{




    
}
*/


bool divisor (int x, int y)
/*@ requires let cond = RemainderEqualZero(x, y);
                x != 0;
    ensures return == ((cond == 0i32) ? (1u32) : (0u32));
@*/
{
    if (x == 0)
    {
        return false;
    }
    if (y % x == 0)
    {
        return true;
    }
    else
    {
        return false;
    }
}