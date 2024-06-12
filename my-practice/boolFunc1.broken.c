
/*

function (bool) Eq (i32 a, i32 b)
{
    (a == b)
}

function (bool) Gt (i32 a, i32 b)
{
    (a > b)
}

function (bool) Is_Zero (i32 a)
{
    (0i32 == a)
}
*/

/*@

function [rec] (i32) RemainderEqualZero (i32 x, i32 y)
{
    (x == 0i32) ? 0i32 : 
    ((y == x) ? 1i32 : 
    ((y > x) ? RemainderEqualZero(x, (y - x)) : 0i32))
}

@*/



//***           checks if x is a divisor of y                        ***//
//***           which is syntatically written x | y                  ***//
//***      So when y is divided by x, there is no remainder          ***//
//***     which is equivalent to y = x * a for some integer a        ***//
//***     This is done recursively without '%' & '/' operators       ***//

int divisor (int x, int y)
/*@  ensures let cond_ = RemainderEqualZero(x, y);
        x == 5i32 && y == 15i32;
        return == cond_;
@*/
{
    int TRUE = 1;
    int FALSE = 0;
    x = 3;
    y = 15;

    if (x == 0)
    /*@ unfold RemainderEqualZero(x, y) @*/
    {
        return FALSE;
    }
    else
    {
        if ( y == x )
        /*@ unfold RemainderEqualZero(x, y) @*/
        {
            return TRUE;
        }
        else
        {
            if ( y > x )
            /*@ unfold RemainderEqualZero(x, y) @*/
            {
                int temp = y - x;
                return divisor(x, temp);
            }
            else
            {
                return FALSE;
            }
        }
    }
}