int add_or_subtract_pointer (int* p, int* q)
/*@ requires take p1 = Owned<int>(p);
             take q1 = Owned<int>(q);
             let sum = (i64) p1 + (i64) q1;
             let diff = (i64) p1 - (i64) q1;
             -2147483648i64 <= sum; sum <= 2147483647i64;
            -2147483648i64 <= diff; diff <= 2147483647i64;
    ensures take p2 = Owned<int>(p);
            take q2 = Owned<int>(q);
            p2 == p1 && q1 == q2;
            return == ((p1 > q1) ? (i32) diff : (i32) sum);
@*/
{
    int x = *p;
    int y = *q;

    if (x > y)
    {
        return (x - y);
    }

    return x + y;
}