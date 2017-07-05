typedef struct {
    uint64_t X[4];
    uint64_t Y[4];
    uint64_t Z[4];
} P256_POINT;

typedef struct {
    uint64_t X[4];
    uint64_t Y[4];
} P256_POINT_AFFINE;

void ecp_nistz256_point_add_affine(P256_POINT *r,
                                   const P256_POINT *a,
                                   const P256_POINT_AFFINE *b);
