/*@
function [rec] (i32) Remainder (i32 x, i32 y)
{
    let temp = x - y;
    (y <= 0i32) ? 2147483647i32 : 
    ((x == 0i32 || y == x) ? 0i32 :
    ((x > y) ? Remainder(temp, y) : x))
}
@*/

int modulo_operator (int x, int y)
/*@ requires y != 0i32;
        let dif = (i64) x - (i64) y;
    -2147483648i64 <= dif; dif <= 2147483647i64; 
    ensures return == Remainder(x, y);
@*/
{
   if (y <= 0)
   {
        return 2147483647;
   }
   else
   {
        if (x == 0 || x == y)
        {
            return 0;
        }
        else
        {
            if (x > y)
            {
                modulo_operator((x-y), y);
            }
            else
            {
                return x; 
            }
        }     
   }

}