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
| [socat#7](http://www.dest-unreach.org/socat/contrib/socat-secadv7.html) | DH in Z*p | irrelevant | non-prime p |
| [invalid-curve](http://euklid.org/pdf/ECC_Invalid_Curve.pdf) | NIST ECDH | irrelevant | not onCurve |
| [donna#8edc799f](https://github.com/agl/curve25519-donna/commit/2647eeba59fb628914c79ce691df794a8edc799f) | F25519 internal to wire |  32-bit pseudo-Mersenne, C | non-canonical |
| [end-to-end#340](https://github.com/google/end-to-end/issues/340) | Curve25519 library | twisted Edwards coordinates | (0, 1) = ∞ |
| [CVE-2006-4339](https://web.archive.org/web/20071010042708/http://www.imc.org/ietf-openpgp/mail-archive/msg14307.html) | RSA-PKCS-1 sig. verification | irrelevant | padding check |
| [CVE-2014-3570](https://github.com/openssl/openssl/commit/a7a44ba55cb4f884c6bc9ceac90072dea38e66d0) | Bignum squaring | asm |  limb overflow |
| [ref/sc25519.c:84](https://github.com/floodyberry/supercop/blob/master/crypto_sign/ed25519/ref/sc25519.c#L84) | x mod (order of Curve25519) |  Barrett reduction (code is likely correct) | "XXX" comment |
| [ic#237002094](https://github.com/mit-plv/fiat-crypto/pull/42#issuecomment-237002094) | Barrett reduction for p256 | 1 conditional subtraction instead of 2 | unkown if ok |
| [openssl#1593](https://rt.openssl.org/Ticket/Display.html?id=1593&user=guest&pass=guest) | P384 modular reduction | carry handling | [exploitable](https://eprint.iacr.org/2011/633.pdf) |
| [go#fa09811d](https://github.com/golang/crypto/commit/84e98f45760e87786b7f24603b8166a6fa09811d) | poly1305 reduction | AMD64 asm, missing subtraction of 3 | found quickly |
| [jose-adobe](https://blogs.adobe.com/security/2017/03/critical-vulnerability-uncovered-in-json-encryption.html) | ECDH-ES | 5 libraries | not onCurve |
| [tweetnacl-m\[15\]](http://seb.dbzteam.org/blog/2014/04/28/tweetnacl_arithmetic_bug.html) | GF(2^255-19) freeze | bit-twiddly C | bounds? typo? |
| [tweetnacl-U32](https://web.archive.org/web/20160305001036/http://blog.skylable.com/2014/05/tweetnacl-carrybit-bug/) | irrelevant | bit-twiddly C | `sizeof(long)!=32` |
| [CVE-2017-3732](https://www.openssl.org/news/secadv/20170126.txt) | x^2 mod m | Montgomery form, AMD64 assembly | [carry](https://boringssl.googlesource.com/boringssl/+/d103616db14ca9587f074efaf9f09a48b8ca80cb%5E%21/), exploitable |
| [openssl#c2633b8f](https://git.openssl.org/gitweb/?p=openssl.git;a=commitdiff;h=b62b2454fadfccaf5e055a1810d72174c2633b8f;ds=sidebyside) | a + b mod p256 |  Montgomery form, AMD64 assembly | [non-canonical](https://mta.openssl.org/pipermail/openssl-dev/2016-August/008179.html) |
| [openssl#59dfcabf](https://git.openssl.org/gitweb/?p=openssl.git;a=commitdiff;h=e3057a57caf4274ea1fb074518e4714059dfcabf;ds=sidebyside) | Weier. affine <-> Jacobian |  Montgomery form, AMD64 and C | ∞ confusion |
| [openssl#a970db05](https://git.openssl.org/gitweb/?p=openssl.git;a=commitdiff;h=bbe9769ba66ab2512678a87b0d9b266ba970db05;ds=sidebyside) | Poly1305 |  Lazy reduction in x86 asm | lost bit 59 |
| [openssl#6825d74b](https://git.openssl.org/gitweb/?p=openssl.git;a=commitdiff;h=1ea8ae5090f557fea2e5b4d5758b10566825d74b;ds=sidebyside) | Poly1305 | AVX2 addition and reduction | bounds? |
| [openssl#74acf42c](https://git.openssl.org/gitweb/?p=openssl.git;a=commitdiff;h=4b8736a22e758c371bc2f8b3534dc0c274acf42c;ds=sidebyside) | Poly1305 | multiple implementations | incorrect carrying |
| [ed25519.py](https://ed25519.cr.yp.to/python/ed25519.py) | Ed25519 | accepts signatures other impls reject | missing h mod l |
| [CryptoNote](https://getmonero.org/2017/05/17/disclosure-of-a-major-bug-in-cryptonote-based-currencies.html) | Anti-double-spending tag |  additive curve25519 curve point | need order(P) = l |
|[bitcoin#eed71d85](https://github.com/bitcoin-core/secp256k1/commit/5de4c5dffd22aa4510a5c97d0ad4a9c2eed71d85) | ECDSA-secp256k1 x*B | mixed addition Jacobian+Affine | missing case |




Not covered in the above list: memory mismanagement (buffer overrun, use-after-free, uninitialized read, null dereference), timing attacks (branch, cache, instruction). While these issues are very important, there are good programming disciplines for avoiding them without verifying intricate details of the computation.
