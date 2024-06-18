struct Vector {int x, int y, int z};

// Function to calculate the dot product of two vectors
int dotProduct(const struct* Vector v1, const struct* Vector v2)
/*@ requires take V1 = Owned<struct Vector>(v1);
             take V2 = Owned<struct Vector>(v2);
             let x_mult = (i64) V1.x * (i64) V2.x;
             let y_mult = (i64) V1.y * (i64) V2.y;
             let z_mult = (i64) V1.z * (i64) V2.z;
             let dot = x_mult + y_mult + z_mult;
    -2147483648i64 <= dot; dot <= 2147483647i64;
    ensures take V1_ = Owned<struct Vector>(v1);
    ensures take V2_ = Owned<struct Vector>(v2);
             V1_ == V2_;
        return == (i32) dot;
@*/ 
{
    return v1->x * v2->x + v1->y * v2->y + v1->z * v2->z;
}

// Function to calculate the cross product of two vectors
Vector crossProduct(const Vector* v1, const Vector* v2) {
    Vector result;
    result.x = v1->y * v2->z - v1->z * v2->y;
    result.y = v1->z * v2->x - v1->x * v2->z;
    result.z = v1->x * v2->y - v1->y * v2->x;
    return result;
}

// Function to get the x component of a vector
int getXComponent(const Vector* v) {
    return v->x;
}

// Function to get the y component of a vector
int getYComponent(const Vector* v) {
    return v->y;
}

// Function to get the z component of a vector
int getZComponent(const Vector* v) {
    return v->z;
}

// Function to calculate the direction vector from v1 to v2
Vector directionVector(const Vector* v1, const Vector* v2) {
    Vector dir;
    double distance = vectorDistance(v1, v2);
    if (distance == 0) {
        dir.x = dir.y = dir.z = 0;
    } else {
        dir.x = (v2->x - v1->x) / distance;
        dir.y = (v2->y - v1->y) / distance;
        dir.z = (v2->z - v1->z) / distance;
    }
    return dir;
}