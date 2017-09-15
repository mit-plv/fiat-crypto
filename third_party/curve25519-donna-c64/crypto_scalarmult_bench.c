extern void curve25519_donna(unsigned char *output, const unsigned char *a,
                             const unsigned char *b);

void crypto_scalarmult_bench(unsigned char* buf) {
  curve25519_donna(buf, buf+32, buf+64);
}
