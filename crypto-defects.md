Here is an incomplete list of defects in cryptographic implementations. We
should make sure our verification rules out the possibility of similar mistakes
appearing in our code.

| Reference                                                           | Specification               | Implementation              | Defect        |
| ------------------------------------------------------------------- | --------------------------- | --------------------------- | ------------- |
| [openssl#3607](https://rt.openssl.org/Ticket/Display.html?id=3607)  | P256 field element squaring | 64-bit Montgomery form, asm | limb overflow |
|                                                                     |                             |                             |               |
|                                                                     |                             |                             |               |
