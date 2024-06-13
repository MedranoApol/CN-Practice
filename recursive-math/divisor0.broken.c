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

unsigned int divisor (int x, int y)
/*@ requires x != 0i32;
        let dif = (i64) y - (i64) x;
    -2147483648i64 <= dif; dif <= 2147483647i64; 
    ensures return == RemainderEqualZero(x, y);
@*/
{
    unsigned int F = 0;
    unsigned int T = 1;

    int temp = y - x;
    return ((x == 0) ? F : 
    ((y == 0 || x == 1) ? T :
    ((y > x) ? divisor(x, temp) : F)));
}