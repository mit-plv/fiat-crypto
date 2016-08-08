#!/bin/sh

cat << EOF
#include <stdint.h>

typedef struct { uint64_t v[10]; } fe25519;
typedef struct { fe25519 X, Y, Z, T; } ge25519;
 
void ge25519_add(ge25519 *R, ge25519 *P, ge25519 *Q) {
EOF

python -c "print ('\n'.join('\tuint64_t %s_%s_%d = %s->%s.v[%i];'%(P,c,i,P,c,i) for i in range(10) for c in 'XYZT' for P in 'PQ'))"
grep '^\s*(\*\s*let' SpecificCurve25519.v | sed 's#(\*##g' | sed 's#\s*let#\tuint64_t#g' | sed 's#:=#=#g' | sed 's#\s\+in#;#g' | sed 's#\s*\*)##g'
grep -A4 '^\s*(\*\s*let' SpecificCurve25519.v | tail -4 | tr -dc '0123456789x \n' | python -c "import sys; print ('\tge25519 ret = {{' + '},\n\t{'.join(', '.join(line.split()) for line in sys.stdin) + '}};')"

cat << EOF
  *R = ret;
}
EOF
