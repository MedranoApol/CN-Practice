typedef enum { false, true } bool;

bool reflexivity (int x, int y)
/*@ ensures return == ((x == y) ? (1u32) : (0u32)); @*/
{
    if (x == y)
    {
        return true; // 1 being true
    }
    else
    {
        return false; // 0 being true
    }
}