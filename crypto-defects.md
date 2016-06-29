Here is an incomplete list of defects in cryptographic implementations. We
should make sure our verification rules out the possibility of similar mistakes
appearing in our code.

| Reference                                                           | Specification               | Implementation              | Defect        |
| ------------------------------------------------------------------- | --------------------------- | --------------------------- | ------------- |
| [openssl#3607](https://rt.openssl.org/Ticket/Display.html?id=3607)  | P256 field element squaring | 64-bit Montgomery form, AMD64 | limb overflow |
| [go#13515](https://github.com/golang/go/issues/13515)               | Modular exponentiation      | uintptr-sized Montgomery form, Go | carry handling |
| [NaCl ed25519 (p. 2)](https://tweetnacl.cr.yp.to/tweetnacl-20131229.pdf) | F25519 mul, square          | 64-bit pseudo-Mersenne, AMD64     | carry handling |
| [openssl#0c687d7e](https://git.openssl.org/gitweb/?p=openssl.git;a=commitdiff;h=dc3c5067cd90f3f2159e5d53c57b92730c687d7e;ds=sidebyside) | Poly1305 | 32-bit pseudo-Mersenne, x86 and ARM | bad truncation |
| [openssl#ef5c9b11](https://github.com/openssl/openssl/commit/29851264f11ccc70c6c0140d7e3d8d93ef5c9b11) | Modular exponentiation | 64-bit Montgomery form, AMD64 | carry handling |
| [nettle#09e3ce4d](https://git.lysator.liu.se/nettle/nettle/commit/c71d2c9d20eeebb985e3872e4550137209e3ce4d) | secp-256r1 modular reduction | | carry handling |
