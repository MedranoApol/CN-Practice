void add_or_subtract_write_pointer (int x, int y, int* p)
/*@ requires take p1 = Block<int>(p);
            let sum = (i64) x + (i64) y;
            let diff = (i64) x - (i64) y;
            -2147483648i64 <= sum; sum <= 2147483647i64;
            -2147483648i64 <= diff; diff <= 2147483647i64;
    ensures take p2 = Owned<int>(p);
            p2 == ((x > y) ? ((i32) diff) : ((i32) sum));
@*/
{
    if (x > y)      *p = x - y;
    else            *p = x + y;
}