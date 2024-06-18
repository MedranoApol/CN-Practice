struct Vector {int x; int y; int z;};


int dotProduct(struct Vector *v1, struct Vector *v2)
/*@ requires take V1 = Owned<struct Vector>(v1);
             take V2 = Owned<struct Vector>(v2);
             let x_mult = (i64) V1.x * (i64) V2.x;
             let y_mult = (i64) V1.y * (i64) V2.y;
             let z_mult = (i64) V1.z * (i64) V2.z;
             let dot = x_mult + y_mult + z_mult;
    -2147483648i64 <= dot; dot <= 2147483647i64;
    ensures take V1_ = Owned<struct Vector>(v1);
            take V2_ = Owned<struct Vector>(v2);
                V1.x == V1_.x && V2.x == V2_.x;
                V1.y == V1_.y && V2.y == V2_.y;
                V1.z == V1_.z && V2.z == V2_.z;
            return == (i32) dot;
@*/ 
{
    int v1_x = v1->x;
    int v1_y = v1->y;
    int v1_z = v1->z;
    int v2_x = v2->x;
    int v2_y = v2->y;
    int v2_z = v2->z;

    int x_multi = v1_x * v2_x;
    int y_multi = v1_y * v2_y;
    int z_multi = v1_z * v2_z;
    int dot_product = x_multi + y_multi + z_multi;
    
    return dot_product;
}