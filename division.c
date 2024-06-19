int division (int x, int y)
/*@ requires y != 0i32;
    ensures return == (y != 0i32 ? (x/y) : (0i32));
@*/
{
    if (y != 0) return (x / y);
    else    return 0;
}