//***           checks if x is a divisor of y                        ***//
//***           which is syntactically written x | y                 ***//
//***      So when y is divided by x, there is no remainder          ***//
//***     which is equivalent to y = x * a for some integer a        ***//
//***     This is done recursively without '%' & '/' operators       ***//

/*@
function [rec] (u32) RemainderEqualZero (i32 x, i32 y)
{
    let temp = y - x;
    (x == 0i32) ? 0u32 : 
    ((y == 0i32 || x == 1i32 || y == x) ? 1u32 :
    ((y > x) ? RemainderEqualZero(x, temp) : 0u32))
}
@*/

typedef enum { false, true } bool;

bool five_divisor_of_15 (int x, int y)
/*@  requires x == 5i32 && y == 15i32;
     ensures return == RemainderEqualZero(5i32, 15i32);
@*/
{
    int temp = y - x;
    if (x == 0)
    {
        return false;
    }
    else
    {
        if (y == 0 || x == 1 || x == y)
        {
            return true;
        }
        else 
        {
            if (y > x)
            {
                return five_divisor_of_15(x, temp);
            }
            else
            {
                return false;
            }
        }
    }
}

void call_func()
/*@ requires true; @*/
{
    bool val = five_divisor_of_15(5, 15);
}