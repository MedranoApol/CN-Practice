unsigned int addition (unsigned int x, unsigned int y)
/*@ requires let sum = (u64) x + (u64) y;
                sum <= 4294967295u64;
    ensures return == (u32) sum;
@*/
{
    if (x == 0)
    {
        return y;
    }
    else
    {
        return (1 + addition (x -1 , y));
    }
}