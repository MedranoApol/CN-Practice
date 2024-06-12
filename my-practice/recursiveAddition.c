int addition (int x, int y)
{
    if ( x == 0)
    {
        return y;
    }
    else
    {
        return (1 + addition (x -1 , y));
    }
}