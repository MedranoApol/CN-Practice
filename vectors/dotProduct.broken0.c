struct Vector {int x; int y; int z;};

/*@
function (i64) Multi (i32 x, i32 y)
{
    ((i64) x * (i64) y)
}
@*/

int dotProduct(struct Vector *v1, struct Vector *v2)
/*@ requires take V1 = Owned<struct Vector>(v1);
             take V2 = Owned<struct Vector>(v2);
             let x_mult = Multi(V1.x, V2.x);
             let y_mult = Multi(V1.y, V2.y);
             let z_mult = Multi(V1.z, V2.z);
             let dot = x_mult + y_mult + z_mult;
    -2147483648i64 <= dot; dot <= 2147483647i64;
    ensures take V1_ = Owned<struct Vector>(v1);
            take V2_ = Owned<struct Vector>(v2);
            V1 == V1_ && V2 == V2_;
            return == (i32) dot;
@*/ 
{
    int v1_x = v1->x, v1_y = v1->y, v1_z = v1->z, v2_x = v2->x, v2_y = v2->y, v2_z = v2->z;

    int x_multi = v1_x * v2_x;
    int y_multi = v1_y * v2_y;
    int z_multi = v1_z * v2_z;
    int dot_product = x_multi + y_multi + z_multi;
    
    return dot_product;
}