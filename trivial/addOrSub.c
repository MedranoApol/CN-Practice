int add_or_subtract (int x, int y)
/*@ requires let sum = (i64) x + (i64) y;
             let diff = (i64) x - (i64) y;
            -2147483648i64 <= sum; sum <= 2147483647i64;
            -2147483648i64 <= diff; diff <= 2147483647i64;
    ensures return == ((x > y) ? (i32) diff : (i32) sum);
@*/
{
    if (x > y)
    {
        return x - y;
    }

    return x + y;

}