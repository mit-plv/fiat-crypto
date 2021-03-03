Fiat-Go: Synthesized Correct-by-Construction Go Code for Cryptographic Primitives via Fiat-Crypto
=================================================================================================

Testing
-------
[![Test Generated Go](https://github.com/mit-plv/fiat-crypto/actions/workflows/go.yml/badge.svg?branch=master)](https://github.com/mit-plv/fiat-crypto/actions/workflows/go.yml?query=branch%3Amaster)

License
-------

Fiat-Crypto and all generated code is distributed under the terms of the MIT License, the Apache License (Version 2.0), and the BSD 1-Clause License; users may pick which license to apply.

See [`COPYRIGHT`](./COPYRIGHT), [`LICENSE-MIT`](./LICENSE-MIT), [`LICENSE-APACHE`](./LICENSE-APACHE), and [`LICENSE-BSD-1`](./LICENSE-BSD-1) for details.

Links
-----

- [Andres Erbsen, Jade Philipoom, Jason Gross, Robert Sloan, Adam Chlipala. Simple High-Level Code For Cryptographic Arithmetic -- With Proofs, Without Compromises. Proceedings of the IEEE Symposium on Security & Privacy 2019 (S&P'19). May 2019.](http://adam.chlipala.net/papers/FiatCryptoSP19/FiatCryptoSP19.pdf)
  + This paper describes multiple field arithmetic implementations, and an older version of the compilation pipeline (preserved [here](https://github.com/mit-plv/fiat-crypto/tree/sp2019latest)). It is somewhat space-constrained, so some details are best read about in theses below.
- [Jade Philipoom. Correct-by-Construction Finite Field Arithmetic in Coq. MIT Master's Thesis. February 2018.](http://adam.chlipala.net/theses/jadep_meng.pdf)
  + Chapters 3 and 4 contain a detailed walkthrough of the field arithmetic implementations (again, targeting the previous compilation pipeline)
- [Andres Erbsen. Crafting Certified Elliptic Curve Cryptography Implementations in Coq. MIT Master's Thesis. June 2017.](
http://adam.chlipala.net/theses/andreser_meng.pdf)
  + Section 3 contains a whirlwind introduction to synthesizing field arithmetic code using coq, without assuming Coq skills, but covering a tiny fraction of the overall library. Sections 5 and 6 contain the only write-up on the elliptic-curve library in this repository.
- [Jason Gross. Performance Engineering of Proof-Based Software Systems at Scale. MIT Doctoral Thesis. February 2021.](http://adam.chlipala.net/theses/jgross.pdf)
  + Chapters 4 and 5 describe the reflective program transformation framework at the center of the newest compilation pipeline.
