typedef enum { FALSE, TRUE } bool;

/*@

function (bool) Eq (i32 a, i32 b)
{
    (a == b)
}

function (bool) Gt (i32 a, i32 b)
{
    (a > b)
}

function (bool) Is_Zero (i32 a)
{
    (0i32 == a)
}

function [rec] (u32) RemainderEqualZero (i32 x, i32 y)
{
    let is_x_zero = Is_Zero(x);
    let eq_x_y = Eq(x, y);
    let gt_y_x = Gt(y, x);
    
    match is_x_zero {
        true => { 0u32 }
        false => {
            match eq_x_y {
                true => { 1u32 }
                false => {
                    match gt_y_x {
                        true => { RemainderEqualZero (x, (y-x))}
                        false => { 0u32}
}

@*/


bool divisor (int x, int y)
/*@ requires let cond = RemainderEqualZero(x, y);
                    x != 0;
    ensures return == ((cond) ? (1u32) : (0u32));
@*/
{
    if (x == 0)
    {
        return FALSE;
    }
    else
    {
        if ( y == x )
        {
            return TRUE;
        }
        else
        {
            if ( y > x )
            {
                return divisor(x, (y-x));
            }
            else
            {
                return FALSE;
            }
        }
    }
}