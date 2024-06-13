struct trinomial { int a; int b; int c; };

struct tri_prime { int dA; int dB; };

void derivation (struct trinomial* f, struct tri_prime* f_prime)
/*@ requires take p1 = Owned<struct trinomial>(f);
             take q1 = Block<struct tri_prime>(f_prime);
             let a_ = (i64) p1.a * 2i64;
             -2147483648i64 <= a_; a_ <= 2147483647i64;
    ensures  take p2 = Owned<struct trinomial>(f);
             take q2 = Owned<struct tri_prime>(f_prime);
             p1 == p2;
             p1.a * 2i32 == q2.dA;
             p1.b == q2.dB;
@*/
{
    int a_value = f->a;
    int b_value = f->b;
    f_prime->dA = a_value * 2;
    f_prime->dB = b_value;
}