//***           checks if x is a divisor of y                        ***//
//***           which is syntatically written x | y                  ***//
//***      So when y is divided by x, there is no remainder          ***//
//***     which is equivalent to y = x * a for some integer a        ***//
//***     This is done recursively without '%' & '/' operators       ***//

/*@
function [rec] (u32) RemainderEqualZero (i32 x, i32 y)
{
    (x == 0i32) ? 0u32 : 
    ((y == x) ? 1u32 : 
    ((y > x) ? RemainderEqualZero(x, (y - x)) : 0u32))
}
@*/

typedef enum { false, true } bool;

bool divisor (int x, int y)
/*@  ensures let cond_ = RemainderEqualZero(3i32, 15i32);
        return == cond_;
@*/
{
    x = 3;
    y = 15;

    if (x == 0)
    {
        return false;
    }
    else
    {
        if ( y == x )
        {
            return true;
        }
        else
        {
            if ( y > x )
            {
                int temp = y - x;
                return divisor(x, temp);
            }
            else
            {
                return true;
            }
        }
    }
}