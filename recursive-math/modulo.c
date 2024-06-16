int modulo (int x, int y)
/*@ requires y != 0i32;
    ensures return == mod(x, y);
@*/
{
    /*@ assert (true); @*/
    return x / y;
}