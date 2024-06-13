/*@
function [rec] (i32) IntegerDiv (i32 x, i32 y)
{
    let temp = y - x;
    (x <= 0i32 || y <= 0i32) ? 0i32 : 
    ((y > x) ? 0i32 : (1i32 + IntegerDiv(temp, y)))
}
@*/

int integerDivison (int a, int b)
/*@ requires let diff = (i64) a - (i64) b;
    -2147483648i64 <= diff; diff <= 2147483647i64;
    ensures return == IntegerDiv(a, b);
@*/
{
    unsigned int temp = a - b;
    if (b <= 0 || a <= 0)
    {
        return 0;
    }
    else
    {
        if ( b > a )
        {
            return 0;
        }
        else
        {
            return (1 + (integerDivison(temp, b)));
        }
    }
}