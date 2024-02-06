Fiat-Crypto: Synthesizing Correct-by-Construction Code for Cryptographic Primitives
===================================================================================

Building
--------
[![CI (Coq, Docker)](https://github.com/mit-plv/fiat-crypto/actions/workflows/coq-docker.yml/badge.svg?branch=master)](https://github.com/mit-plv/fiat-crypto/actions/workflows/coq-docker.yml?query=branch%3Amaster)
[![CI (Coq, Debian)](https://github.com/mit-plv/fiat-crypto/actions/workflows/coq-debian.yml/badge.svg?branch=master)](https://github.com/mit-plv/fiat-crypto/actions/workflows/coq-debian.yml?query=branch%3Amaster)
[![CI (Coq, Alpine)](https://github.com/mit-plv/fiat-crypto/actions/workflows/coq-alpine.yml/badge.svg?branch=master)](https://github.com/mit-plv/fiat-crypto/actions/workflows/coq-alpine.yml?query=branch%3Amaster)
[![CI (Coq, Arch Linux)](https://github.com/mit-plv/fiat-crypto/actions/workflows/coq-archlinux.yml/badge.svg?branch=master)](https://github.com/mit-plv/fiat-crypto/actions/workflows/coq-archlinux.yml?query=branch%3Amaster)
[![CI (Coq, Windows)](https://github.com/mit-plv/fiat-crypto/actions/workflows/coq-windows.yml/badge.svg?branch=master)](https://github.com/mit-plv/fiat-crypto/actions/workflows/coq-windows.yml?query=branch%3Amaster)
[![CI (Coq, MacOS)](https://github.com/mit-plv/fiat-crypto/actions/workflows/coq-macos.yml/badge.svg?branch=master)](https://github.com/mit-plv/fiat-crypto/actions/workflows/coq-macos.yml?query=branch%3Amaster)

[![Release][release-shield]][release-link]
[![Zulip][zulip-shield]][zulip-link]
[![Rust Crate][crate-shield]][crate-link]
[![Go Reference][pkg.go-shield]][pkg.go-link]

[release-shield]: https://img.shields.io/github/v/release/mit-plv/fiat-crypto.svg?logo=github&include_prereleases
[release-link]: https://github.com/mit-plv/fiat-crypto/releases

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-informational.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/247791-fiat-crypto

[crate-shield]: https://img.shields.io/crates/v/fiat-crypto.svg
[crate-link]: https://crates.io/crates/fiat-crypto

[pkg.go-shield]: https://pkg.go.dev/badge/github.com/mit-plv/fiat-crypto/fiat-go.svg
[pkg.go-link]: https://pkg.go.dev/github.com/mit-plv/fiat-crypto/fiat-go

🌐 Try out synthesis [on the web](https://mit-plv.github.io/fiat-crypto/)!
(Supported by [`js_of_ocaml`](https://ocsigen.org/js_of_ocaml/latest/manual/overview) compilation.)

This repository requires [Coq](https://coq.inria.fr/) [8.18](https://github.com/coq/coq/releases/tag/V8.18.0) or later.
Note that if you install Coq from Ubuntu aptitude packages, you need `libcoq-ocaml-dev` in addition to `coq`.
Note that in some cases (such as installing Coq via homebrew on Mac), you may also need to install `ocaml-findlib` (for `ocamlfind`).
The extracted OCaml code for the standalone binaries requires [OCaml](https://ocaml.org/) [4.08](https://ocaml.org/p/ocaml/4.08.0) or later.
We suggest downloading [the latest version of Coq](https://github.com/coq/coq/wiki#coq-installation).
Generation of JSON code via the Makefile also requires `jq`.

Alternatively, choose your package-manager to install dependencies:

Package Manager | Command Line Invocation |
--|--|
Aptitude (Ubuntu / Debian) | `apt install coq ocaml-findlib libcoq-ocaml-dev jq` |
Homebrew (OS X) | `brew install coq ocaml-findlib coreutils jq` |
Pacman (Archlinux) | `pacman -S coq ocaml-findlib ocaml-zarith jq` |

You can clone this repository with

    git clone --recursive https://github.com/mit-plv/fiat-crypto.git

Git submodules are used for some dependencies. If you did not clone with `--recursive`, run

    git submodule update --init --recursive

from inside the repository.
Then run:

    make

You can check out [our CI](https://github.com/mit-plv/fiat-crypto/actions?query=branch%3Amaster+workflow%3A%22CI+%28Coq%29%22) to see how long the build should take; as of the last update to this line in the README, it takes about 1h10m to run `make -j2` on Coq 8.11.1.

If you want to build only the command-line binaries used for generating code, you can save a bit of time by making only the `standalone-unified-ocaml` target with

    make standalone-unified-ocaml

Usage (Generating C Files)
--------------------------

The Coq development builds binary compilers that generate code using some implementation strategy.
The parameters (modulus, hardware multiplication input bitwidth, etc.) are specified on the command line of the compiler.
The generated C code is written to standard output.

A collection of C files for popular curves can be made with

    make c-files

The C files will appear in [`fiat-c/src/`](./fiat-c/src/).

Just the compilers generating these C files can be made with

    make standalone-ocaml

or `make standalone-haskell` for compiler binaries generated with Haskell, or `make standalone` for both the Haskell and OCaml compiler binaries.
The binaries are located in `src/ExtractionOcaml/` and `src/ExtractionHaskell/` respectively.

There is one compiler binary for all implementation strategies:

 - `fiat_crypto`

This binary takes arguments for the strategy:

 - `saturated-solinas`
 - `unsaturated-solinas`
 - `word-by-word-montgomery`
 - `dettman-multiplication`
 - `solinas-reduction`
 - `base-conversion`

Passing no arguments, or passing `-h` or `--help` (or any other invalid arguments) will result in a usage message being printed.  These binaries output C code on stdout.

Here are some examples of ways to invoke the binaries (from the directories that they live in):

    # Generate code for 2^255-19
    ./fiat_crypto unsaturated-solinas '25519' '64' '5' '2^255 - 19' carry_mul carry_square carry_scmul121666 carry add sub opp selectznz to_bytes from_bytes > curve25519_64.c # 1
    ./fiat_crypto unsaturated-solinas '25519' '32' '10' '2^255 - 19' carry_mul carry_square carry_scmul121666 carry add sub opp selectznz to_bytes from_bytes > curve25519_32.c # 2

    # Generate code for NIST-P256 (2^256 - 2^224 + 2^192 + 2^96 - 1)
    ./fiat_crypto word-by-word-montgomery 'p256' '32' '2^256 - 2^224 + 2^192 + 2^96 - 1' > p256_32.c # 3
    ./fiat_crypto word-by-word-montgomery 'p256' '64' '2^256 - 2^224 + 2^192 + 2^96 - 1' > p256_64.c # 4

Try out the above on the web [🌐<sub>1</sub>][web-1-link] [🌐<sub>2</sub>][web-2-link] [🌐<sub>3</sub>][web-3-link] [🌐<sub>4</sub>][web-4-link].
You can find more examples in the [`Makefile`](./Makefile).

[web-1-link]: https://mit-plv.github.io/fiat-crypto/?argv=%5B%22unsaturated-solinas%22%2C%2225519%22%2C%2264%22%2C%225%22%2C%222%5E255-19%22%2C%22carry_mul%22%2C%22carry_square%22%2C%22carry_scmul121666%22%2C%22carry%22%2C%22add%22%2C%22sub%22%2C%22opp%22%2C%22selectznz%22%2C%22to_bytes%22%2C%22from_bytes%22%5D&interactive
[web-2-link]: https://mit-plv.github.io/fiat-crypto/?argv=%5B%22unsaturated-solinas%22%2C%2225519%22%2C%2232%22%2C%2210%22%2C%222%5E255-19%22%2C%22carry_mul%22%2C%22carry_square%22%2C%22carry_scmul121666%22%2C%22carry%22%2C%22add%22%2C%22sub%22%2C%22opp%22%2C%22selectznz%22%2C%22to_bytes%22%2C%22from_bytes%22%5D&interactive
[web-3-link]: https://mit-plv.github.io/fiat-crypto/?argv=%5B%22word-by-word-montgomery%22%2C%22p256%22%2C%2232%22%2C%222%5E256-2%5E224%2B2%5E192%2B2%5E96-1%22%5D&interactive
[web-4-link]: https://mit-plv.github.io/fiat-crypto/?argv=%5B%22word-by-word-montgomery%22%2C%22p256%22%2C%2264%22%2C%222%5E256-2%5E224%2B2%5E192%2B2%5E96-1%22%5D&interactive

Note that for large primes, you may need to increase the stack size to avoid stack overflows.  For example:

    ulimit -S -s 1048576; ./fiat_crypto word-by-word-montgomery --static gost_512_paramSetB 32 '2^511 + 111'

This sets the stack size to 1 GB (= 1024 MB = 1024 * 1024 KB = 1048576 KB) before running the command.
As of the last edit of this line, this command takes about an hour to run, but does in fact complete successfully.
Without a sufficiently large stack-size, it instead stack overflows.

Usage (Generating Bedrock2 Files)
---------------------------------
Output is supported to the research language [bedrock2](https://github.com/mit-plv/bedrock2).
The Coq development builds binary compilers that generate code using some implementation strategy.
The parameters (modulus, hardware multiplication input bitwidth, etc.) are specified on the command line of the compiler.
The generated bedrock2 code is then written to standard output using the bedrock2 C backend.

A collection of bedrock2/C files for popular curves can be made with

    make bedrock2-files

The bedrock2/C files will appear in [`fiat-bedrock2/src/`](./fiat-bedrock2/src/).

Just the compilers generating these bedrock2/C files can be made with

    make standalone-ocaml

or `make standalone-haskell` for binaries generated with Haskell, or `make standalone` for both the Haskell and OCaml binaries.
The binaries are located in `src/ExtractionOcaml/` and `src/ExtractionHaskell/` respectively.

There is one compiler binary for all implementation strategies:

 - `bedrock2_fiat_crypto`

This binary takes arguments for the strategy:

 - `saturated-solinas`
 - `unsaturated-solinas`
 - `word-by-word-montgomery`
 - `dettman-multiplication`
 - `solinas-reduction`
 - `base-conversion`

Passing no arguments, or passing `-h` or `--help` (or any other invalid arguments) will result in a usage message being printed.  These binaries output bedrock2/C code on stdout.

Here are some examples of ways to invoke the binaries (from the directories that they live in):

    # Generate code for 2^255-19
    ./bedrock2_fiat_crypto unsaturated-solinas --no-wide-int --widen-carry --widen-bytes --split-multiret --no-select '25519' '64' '5' '2^255 - 19' carry_mul carry_square carry_scmul121666 carry add sub opp selectznz to_bytes from_bytes > curve25519_64.c # 1
    ./bedrock2_fiat_crypto unsaturated-solinas --no-wide-int --widen-carry --widen-bytes --split-multiret --no-select '25519' '32' '10' '2^255 - 19' carry_mul carry_square carry_scmul121666 carry add sub opp selectznz to_bytes from_bytes > curve25519_32.c # 2

    # Generate code for NIST-P256 (2^256 - 2^224 + 2^192 + 2^96 - 1)
    ./bedrock2_fiat_crypto word-by-word-montgomery --no-wide-int --widen-carry --widen-bytes --split-multiret --no-select 'p256' '32' '2^256 - 2^224 + 2^192 + 2^96 - 1' > p256_32.c # 3
    ./bedrock2_fiat_crypto word-by-word-montgomery --no-wide-int --widen-carry --widen-bytes --split-multiret --no-select 'p256' '64' '2^256 - 2^224 + 2^192 + 2^96 - 1' > p256_64.c # 4

    # Generate code for 2^130 - 5
    ./bedrock2_fiat_crypto unsaturated-solinas --no-wide-int --widen-carry --widen-bytes --split-multiret --no-select 'poly1305' '64' '3' '2^130 - 5' > poly1305_64.c # 5
    ./bedrock2_fiat_crypto unsaturated-solinas --no-wide-int --widen-carry --widen-bytes --split-multiret --no-select 'poly1305' '32' '5' '2^130 - 5' > poly1305_32.c # 6

Try out the above on the web [🌐<sub>1</sub>][web-bedrock2-1-link] [🌐<sub>2</sub>][web-bedrock2-2-link] [🌐<sub>3</sub>][web-bedrock2-3-link] [🌐<sub>4</sub>][web-bedrock2-4-link] [🌐<sub>5</sub>][web-bedrock2-5-link] [🌐<sub>6</sub>][web-bedrock2-6-link].
You can find more examples in [`Makefile.examples`](./Makefile.examples).

[web-bedrock2-1-link]: https://mit-plv.github.io/fiat-crypto/?argv=%5B%22unsaturated-solinas%22%2C%22--lang%22%2C%22bedrock2%22%2C%22--no-wide-int%22%2C%22--widen-carry%22%2C%22--widen-bytes%22%2C%22--split-multiret%22%2C%22--no-select%22%2C%2225519%22%2C%2264%22%2C%225%22%2C%222%5E255-19%22%2C%22carry_mul%22%2C%22carry_square%22%2C%22carry_scmul121666%22%2C%22carry%22%2C%22add%22%2C%22sub%22%2C%22opp%22%2C%22selectznz%22%2C%22to_bytes%22%2C%22from_bytes%22%5D&interactive
[web-bedrock2-2-link]: https://mit-plv.github.io/fiat-crypto/?argv=%5B%22unsaturated-solinas%22%2C%22--lang%22%2C%22bedrock2%22%2C%22--no-wide-int%22%2C%22--widen-carry%22%2C%22--widen-bytes%22%2C%22--split-multiret%22%2C%22--no-select%22%2C%2225519%22%2C%2232%22%2C%2210%22%2C%222%5E255-19%22%2C%22carry_mul%22%2C%22carry_square%22%2C%22carry_scmul121666%22%2C%22carry%22%2C%22add%22%2C%22sub%22%2C%22opp%22%2C%22selectznz%22%2C%22to_bytes%22%2C%22from_bytes%22%5D&interactive
[web-bedrock2-3-link]: https://mit-plv.github.io/fiat-crypto/?argv=%5B%22word-by-word-montgomery%22%2C%22--lang%22%2C%22bedrock2%22%2C%22--no-wide-int%22%2C%22--widen-carry%22%2C%22--widen-bytes%22%2C%22--split-multiret%22%2C%22--no-select%22%2C%22p256%22%2C%2232%22%2C%222%5E256-2%5E224%2B2%5E192%2B2%5E96-1%22%5D&interactive
[web-bedrock2-4-link]: https://mit-plv.github.io/fiat-crypto/?argv=%5B%22word-by-word-montgomery%22%2C%22--lang%22%2C%22bedrock2%22%2C%22--no-wide-int%22%2C%22--widen-carry%22%2C%22--widen-bytes%22%2C%22--split-multiret%22%2C%22--no-select%22%2C%22p256%22%2C%2264%22%2C%222%5E256-2%5E224%2B2%5E192%2B2%5E96-1%22%5D&interactive
[web-bedrock2-5-link]: https://mit-plv.github.io/fiat-crypto/?argv=%5B%22unsaturated-solinas%22%2C%22--lang%22%2C%22bedrock2%22%2C%22--no-wide-int%22%2C%22--widen-carry%22%2C%22--widen-bytes%22%2C%22--split-multiret%22%2C%22--no-select%22%2C%22poly1305%22%2C%2264%22%2C%223%22%2C%222%5E130-5%22%5D&interactive
[web-bedrock2-6-link]: https://mit-plv.github.io/fiat-crypto/?argv=%5B%22unsaturated-solinas%22%2C%22--lang%22%2C%22bedrock2%22%2C%22--no-wide-int%22%2C%22--widen-carry%22%2C%22--widen-bytes%22%2C%22--split-multiret%22%2C%22--no-select%22%2C%22poly1305%22%2C%2232%22%2C%225%22%2C%222%5E130-5%22%5D&interactive

License
-------

Fiat-Crypto is distributed under the terms of the MIT License, the Apache License (Version 2.0), and the BSD 1-Clause License; users may pick which license to apply.

See [`COPYRIGHT`](./COPYRIGHT), [`LICENSE-MIT`](./LICENSE-MIT), [`LICENSE-APACHE`](./LICENSE-APACHE), and [`LICENSE-BSD-1`](./LICENSE-BSD-1) for details.


Reading About The Code
----------------------

- [Andres Erbsen, Jade Philipoom, Jason Gross, Robert Sloan, Adam Chlipala. Simple High-Level Code For Cryptographic Arithmetic -- With Proofs, Without Compromises. To Appear in Proceedings of the IEEE Symposium on Security & Privacy 2019 (S&P'19). May 2019.](http://adam.chlipala.net/papers/FiatCryptoSP19/FiatCryptoSP19.pdf). This paper describes multiple field arithmetic implementations, and an older version of the compilation pipeline (preserved [here](https://github.com/mit-plv/fiat-crypto/tree/sp2019latest)). It is somewhat space-constrained, so some details are best read about in theses below.
- [Jade Philipoom. Correct-by-Construction Finite Field Arithmetic in Coq. MIT Master's Thesis. February 2018.](http://adam.chlipala.net/theses/jadep_meng.pdf) Chapters 3 and 4 contain a detailed walkthrough of the field arithmetic implementations (again, targeting the previous compilation pipeline).
- [Andres Erbsen. Crafting Certified Elliptic Curve Cryptography Implementations in Coq. MIT Master's Thesis. June 2017.](
http://adam.chlipala.net/theses/andreser_meng.pdf) Section 3 contains a whirlwind introduction to synthesizing field arithmetic code using coq, without assuming Coq skills, but covering a tiny fraction of the overall library. Sections 5 and 6 contain the only write-up on the elliptic-curve library in this repository.
- [Jason Gross. Performance Engineering of Proof-Based Software Systems at Scale. MIT Doctoral Thesis. February 2021.](http://adam.chlipala.net/theses/jgross.pdf) Chapters 4 and 5 describe the reflective program transformation framework at the center of the newest compilation pipeline.
- The newest compilation pipeline as a whole does not have a separate document yet, but this README does go over it in some detail.


Status of Backends
------------------

Fiat Cryptography contains a number of backends; the final step of the pipeline is transforming from straight-line C-like code to expressions in whatever language is being targeted.
The Bedrock2 backend comes with proofs that the Bedrock2 AST matches the semantics of our internal AST, but none of the other backends have any proofs about them.
While the transformations are not particularly involved, and our proofs ensure that we have picked integer sizes large enough to store values at each operation, there is no verification that the particular integer size casts that we emit are sufficient to ensure that gcc, clang, or whatever compiler is used on the code correctly selects integer sizes for expressions correctly.
Note that even the C code printed by the Bedrock2 backend does not have proofs that the conversion to strings is correct.

Hence we provide here a table of the extent to which the various backends are maintained, tested, and proven.
A :heavy_check_mark: in "maintainer" means that the Fiat Cryptography maintainers are fully maintaining and testing the backend; :white_check_mark: means maintenance by external contributors.
We do not provide any quality guarantees for code generated by the backends.

Backend | Maintainer / Person of Contact | Build Checked by CI | Generated Code Tested | Internal AST Proven Correct
:-- | :-- | :-- | :-- | :--
C | :heavy_check_mark: @JasonGross / entire team | :heavy_check_mark: | :heavy_check_mark: (BoringSSL test-suite) |
Bedrock2/C | :heavy_check_mark: @andres-erbsen / entire team | :heavy_check_mark: | :heavy_check_mark: (BoringSSL test-suite) | :heavy_check_mark:
Go | :white_check_mark: @mdempsky | :heavy_check_mark: | |
Java | :x: Unmaintained | :heavy_check_mark: | :x: Known Buggy [#707](https://github.com/mit-plv/fiat-crypto/issues/707#issuecomment-763098543) |
JSON | Experimental | :white_check_mark: (only syntax) | |
Rust | :white_check_mark: | :heavy_check_mark: | :heavy_check_mark: ([Dalek Cryptography test-suite](https://github.com/dalek-cryptography/curve25519-dalek)) |
Zig | :white_check_mark: @jedisct1 | :heavy_check_mark: | :white_check_mark: ([Zig standard library](https://github.com/ziglang/zig/tree/master/lib/std/crypto/pcurves) (generated file [here](https://github.com/ziglang/zig/blob/master/lib/std/crypto/pcurves/p256/p256_64.zig)) (main CI [here](https://dev.azure.com/ziglang/zig/_build?definitionId=1&_a=summary&repositoryFilter=1&branchFilter=5%2C5%2C5%2C5%2C5%2C5%2C5%2C5))) |

### Contributing a new backend

We weclome new backends (as long as you're willing to maintain them).
We hope that the process of contributing a new backend is not too painful, and welcome feedback on how the process could be streamlined.
To contribute a new backend, follow the following steps (perhaps using, for example, [#936](https://github.com/mit-plv/fiat-crypto/pull/936), [#660](https://github.com/mit-plv/fiat-crypto/pull/660), [#638](https://github.com/mit-plv/fiat-crypto/pull/638), or [#570](https://github.com/mit-plv/fiat-crypto/pull/570) as examples):
- Add a new file to [`src/Stringification/`](./src/Stringification/) for your language, modeled after the existing file of your choice
- Run `git add` on your new file and then `make update-_CoqProject` to have the build system track your file
- Update [`src/CLI.v`](./src/CLI.v) to `Require Import` your file and add your language to [the list `default_supported_languages`](https://github.com/mit-plv/fiat-crypto/blob/8944697db11055abeeba252782d2bfd1e2b844cd/src/CLI.v#L212-L219) so that it can be passed to the binaries as an argument to `--lang`
- Update the `Makefile` in the following ways:
  - Consider adding a variable near `CARGO_BUILD` for the build invocation
  - Add targets to `.PHONY` analogous to `c-files`, `lite-c-files`, `test-c-files`, `only-test-c-files`
  - Add a variables analogous to `C_DIR`, `ALL_C_FILES`, and `LITE_C_FILES` for your language's generated files
  - Add targets analogous to `c-files` and `lite-c-files` and make `generated-files` and `lite-generated-files` depend on those targets respectively
  - Add build rules for `ALL_<YOUR-LANGUAGE>_FILES`
  - Add targets for `test-<your-language>-files` and `only-test-<your-language>-files`; both targets should have the same build rule, but `test-<your-language>-files` should depend on all the generated files of your language, while `only-test-<your-language>-files` should not have any build rule dependencies.
  - If you are developing a package, you can look for uses of `COPY_TO_FIAT_RUST` or `COPY_TO_FIAT_GO` to see how license files are copied
- Run `make` to generate all the relevant files of your language, and add the generated files to git
- Update `.gitignore` to ignore any compiled files generated by the compiler of your language (analogous to `.o` and `.a` for C)
- Create a file in [`.github/workflows/`](./.github/workflows/) like [`c.yml`](./.github/workflows/c.yml), [`go.yml`](./.github/workflows/go.yml), [`rust.yml`](./.github/workflows/rust.yml), etc, to test at least that the generated code compiles.
  - Optionally, also test the built code against some external project's crypto unit tests
- Update [`.gitattributes`](./.gitattributes) to mark your language's generated files as `text` and to mark the paths of the generated files as `linguist-generated` so that diffs don't clog up PR displays.
- Add your language to the table in preceeding section of the README indicating the status of your backend and marking your GitHub username as the maintainer.


Reading The Code
----------------

### Demo of Synthesis

The idea of the synthesis process is demoed in [`src/Demo.v`](./src/Demo.v).
We strongly recommend reading this before studying the full-scale system.

### Proofs About Elliptic Curves

We have some about elliptic curves, for example:

- [`src/Curves/Edwards/AffineProofs.v`](./src/Curves/Edwards/AffineProofs.v),
- [`src/Curves/Edwards/XYZT/Basic.v`](./src/Curves/Edwards/XYZT/Basic.v),
- [`src/Curves/Montgomery/AffineProofs.v`](./src/Curves/Montgomery/AffineProofs.v),
- [`src/Curves/Montgomery/XZProofs.v`](src/Curves/Montgomery/XZProofs.v).

### Actual Synthesis Pipeline

The entry point for clients of the PHOAS expressions we use is
`Language/API.v`.  Refer to comments in that file for an explanation
of the interface; the following text describes how the expressions are
generated, not how to interact with them.

The ordering of files (eliding `*Proofs.v` files) is:

```
Language/*.v
    ↑
    ├────────────────────────────────┬───────────────────────┬───────────────────────┐
AbstractInterpretation/*.v     MiscCompilerPasses.v    Rewriter/*.v     PushButtonSynthesis/ReificationCache.v      Arithmetic.v
    ↑                                ↑                       ↑                       ↑                                   ↑
Stringification/*.v                  │                       │                       │                        COperationSpecifications.v
    ↑                                │                       │                       │                                   ↑
    └────────────┬───────────────────┴───────────────────────┴────────┬──────────────┘                                   │
           BoundsPipeline.v                                  CompilersTestCases.v                                        │
                 ↑                                                                                                       │
                 └────────────┬──────────────────────────────────────────────────────────────────────────────────────────┘
                     PushButtonSynthesis/*.v
                              ↑
                   ┌──────────┴────────────────┐
                  CLI.v                SlowPrimeSynthesisExamples.v
                   ↑
        ┌──────────┴────────────────┐
StandaloneHaskellMain.v   StandaloneOCamlMain.v
        ↑                           ↑
ExtractionHaskell.v          ExtractionOCaml.v
```

Within each directory, the dependency graphs (again eliding `*Proofs.v` and related files) are:

Within `Language/`:
```
  Pre.v ←──────────────────────────────────────────────────────────────────────── IdentifierParameters.v
    ↑                                                                                        ↑
Language.v ←── IdentifiersBasicLibrary.v ←──── IdentifiersBasicGenerate.v ←── IdentifiersBasicGENERATED.v ←───────────────────────────── API.v
    ↑                        ↑                                                               ↑
    ├────────────────┐       └────────────────────────────┐                                  │
UnderLets.v    IdentifiersLibrary.v ←──────────── IdentifiersGenerate.v ←─────── IdentifiersGENERATED.v
                     ↑                                       ↑                               ↑
              IdentifiersLibraryProofs.v ←─── IdentifiersGenerateProofs.v ←─ IdentifersGENERATEDProofs.v
```

Within `Stringification/`:
```
Language.v
    ↑
   IR.v
    ↑
 ┌──┴───────┐
C.v       Rust.v
```

We will come back to the `Rewriter/*` files shortly.

The files contain:

- `Arithmetic.v`: All of the high-level field arithmetic stuff

- `COperationSpecifications.v`: The specifications for the various
  operations to be synthesized.
  TODO: This file should probably be renamed.

- `AbstractInterpretation/*.v`: type-code-based ZRange definitions, abstract
  interpretation of identifiers (which does let-lifting, for historical reasons,
  and the dependency on UnderLets should probably be removed), defines the
  passes:
  + PartialEvaluateWithBounds
  + PartialEvaluateWithListInfoFromBounds
  + CheckPartialEvaluateWithBounds

- `MiscCompilerPasses.v`: Defines the passes:
  + EliminateDead (dead code elimination)
  + Subst01 (substitute let-binders used 0 or 1 times)

- `Rewriter/*.v`: rewrite rules, rewriting.  See below for actual structure
  of files.  Defines the passes:
  + RewriteNBE
  + RewriteArith
  + RewriteArithWithCasts
  + RewriteStripLiteralCasts
  + RewriteToFancy
  + RewriteToFancyWithCasts
  + PartialEvaluate (which is just a synonym for RewriteNBE)

- Inside `Language/`:

  + `Pre.v`: A few definitions which are used in writing out rewrite
    rules and the interpretations of PHOAS identifiers, e.g.,
    `ident.cast`, `ident.eagerly`, `Thunked.list_rect`, etc

  + `Language.v`: Defines parts of the PHOAS basic infrastructure
        parameterized over base types and identifiers including:
    * PHOAS
    * reification
    * denotation/intepretation
    * utilities for inverting PHOAS exprs
    * default/dummy values of PHOAS exprs
    * default instantiation of generic PHOAS types
    * Gallina reification of ground terms
    * Flat/indexed syntax trees, and conversions to and from PHOAS

    Defines the passes:
    * ToFlat
    * FromFlat
    * GeneralizeVar

  + `API.v`: Specializes the type of PHOAS expressions to the
    particular identifiers we're using, and defines convenience
    notations, tactics, and definitions for some of the specialized
    versions.

  + `IdentifierParameters.v`: Defines a couple of definitions
    determining the identifiers and types used by the language.  These
    are used as input for the generation of identifier definitions.

  + `IdentifiersBasicLibrary.v`: Defines the package type holding basic
    identifier definitions.

  + `IdentifiersBasicGenerate.v`: Defines the tactics that generate
    all of the identifier-list-specific definitions used by the PHOAS
    machinery, in addition to defining the tactics that do reification
    based on the generated package.

  + `IdentifiersBasicGENERATED.v`: Basically autogenerated file that
    defines the inductives of base type codes and identifier codes
    (the first hand-written because it's short; the latter copy-pasted
    from a tactic that prints out the inductive), and calls the
    package-generation-tactic from `IdentifiersBasicGenerate.v`.

  + `UnderLets.v`: the UnderLets monad, a pass that does substitution
    of var-like things, a pass that inserts let-binders in the
    next-to-last line of code, substituting away var-like things (this
    is used to ensure that when we output C code, aliasing the input
    and the output arrays doesn't cause issues).
    Defines the passes:
    * SubstVar
    * SubstVarLike
    * SubstVarOrIdent

  The following files in `Language/` are used only by the rewriter:

  + `IdentifiersLibrary.v`: Some definitions about identifiers and
    pattern identifiers and raw identifiers.  Some of these
    definitions take generated definitions as arguments. Also defines
    a package record to hold all of the generated definitions.

  + `IdentifiersGenerate.v`: Tactics to generate definitions about
    untyped and pattern versions of identifiers for the rewriter.
    Culminates in a tactic which inhabits the package type defined in
    `IdentifiersLibrary.v`

  + `IdentifiersLibraryProofs.v`: proofs about definitions in
    IdentifiersLibrary.  Also defines a package to hold generated
    proofs that require destructing inductives not yet defined in this
    file.

  + `IdentifiersGenerateProofs.v`: tactics to prove lemmas to inhabit
    the package defined in `IdentifiersLibraryProofs.v`

  + `IdentifiersGENERATE.v`: identifiers / inductives and definitions
    generated by IdentifiersGenerate.

  + `IdentifiersGENERATEProofs.v`: proofs generated by
    IdentifiersGenerateProofs, about definitions in
    IdentifiersGENERATE

- Inside `Stringification/`:

  + `Language.v`: defines a printer (Show instance) for the PHOAS
    language, defines some common language-independent utilities for
    conversion to output code, and defines the spec/API of conversion
    from PHOAS to code in a language as strings.  (Depends on
    `AbstractInterpretation.v` for ZRange utilities.)  Defines the
    passes:
    * ToString.LinesToString
    * ToString.ToFunctionLines

  + `IR.v`: Defines a common IR for C and Rust (and maybe eventually
    other languages), and builds most of the infrastructure necessary
    for instantiating the LanguageSpecification API for a language
    with pointers and function calls

  + `C.v`: conversion to C code as strings.  Instantiates the API
    defined in `Stringification.Language`.

  + `Rust.v`: conversion to Rust code as strings.  Instantiates the
    API defined in `Stringification.Language`.

- `CompilersTestCases.v`: Various test cases to ensure everything is working

- `BoundsPipeline.v`: Assemble the various compiler passes together into
  a composed pipeline.  It is the final interface for the compiler.
  Also contains some tactics for applying the BoundsPipeline
  correctness lemma.

- `PushButtonSynthesis/ReificationCache.v`: Defines the cache that
  holds reified versions of operations, as well as the tactics that
  reify and apply things from the cache.

- `PushButtonSynthesis/*`: Reifies the various operations from
  `Arithmetic.v`, defines the compositions of the BoundsPipeline with
  these operations, proves that their interpretations satisfies the
  specs from `COperationSpecifications.v`, assembles the reified
  post-bounds operations into synthesis targets.  These are the files
  that `CLI.v` depends on:
  + `ReificationCache.v`:
      Defines the cache of pre-reified terms.  Splitting up
      reification from uses of the pipeline allows us to not have to
      re-reify big terms every time we change the pipeline or
      intermediate stages thereof.
  + `InvertHighLow.v`:
      Defines some common definitions, around splitting apart high and
      low bits of things, for Barrett and FancyMontgomeryReduction.
  + `Primitives.v`:
      Specializes the pipeline to basic "primitive" operations such as
      cmovznz, addcarryx, subborrowx, etc.
  + `SmallExamples.v`:
      Some small examples of using the pipeline.  Nothing depends on
      this file; it is for demonstration purposes only.
  + `*ReificationCache.v`:
      Holds the reified versions of the definitions used in the
      corresponding file.
  + `BarrettReduction.v`, `FancyMontgomeryReduction.v`,
    `SaturatedSolinas.v`, `UnsaturatedSolinas.v`, `WordByWordMontgomery.v`:
      Holds the instantiation of the pipeline to the corresponding
      implementation choice, as well as any relevant correctness
      proofs (such as that things assemble into a ring).

- `SlowPrimeSynthesisExamples.v`: Additional uses of the pipeline for
  primes that are kind-of slow, which I don't want extraction blocking
  on.  Also contains some debugging examples.

- `CLI.v`: Setting up all of the language-independent parts of extraction; relies
  on having a list of strings-or-error-messages for each pipeline, and on the
  arguments to that pipeline, and builds a parser for command line arguments for
  that.

- `StandaloneHaskellMain.v`, `StandaloneOCamlMain.v`, `ExtractionHaskell.v`,
  `ExtractionOCaml.v`: Extraction of pipeline to various languages


The files defined in `Rewriter/` are split up into the following
dependency graph (including some files from `Language/` at the top):
```
IdentifiersLibrary.v ←───────────────────────── IdentifiersGenerate.v ←──────────────────── IdentifiersGENERATED.v
    ↑ ↑                                                   ↑                                        ↑
    │ └──────────────── IdentifiersLibraryProofs.v ←──────┴─ IdentifiersGenerateProofs.v ←─ IdentifersGENERATEDProofs.v
    │                                     ↑                                                        ↑
    │                                     │                                                        │
    │                                     │                                                        │
    │                                     │                                                        │
    │                                     │                                                        │
Rewriter.v ←────────────────────── ProofsCommon.v ←──────────────────── ProofsCommonTactics.v      │
    ↑                                 ↗        ↖                                ↑                  │
Reify.v ←──────────────┐           Wf.v   InterpProofs.v                        │                  │
                       │              ↖        ↗                                │                  │
Rules.v                └──────────── AllTactics.v ──────────────────────────────┘                  │
    ↑                                      ↑       ┌───────────────────────────────────────────────┘
RulesProofs.v                         AllTacticsExtra.v
    ↑                                      ↑
    ├────────┬─────────────┬───────────────┴────────┬─────────────────────────────┐
    │   Passes/NBE.v    Passes/Arith.v    Passes/ArithWithCasts.v    Passes/StripLiteralCasts.v
    │        ↑             ↑                        ↑                             ↑
    │        └─────────────┴────────────────────────┴─────────────────────────────┴─────────────┐
    │                                                                                           │
    └────────┬──────────────────────────┐                                                       │
      Passes/ToFancy.v      Passes/ToFancyWithCasts.v                                           │
             ↑                          ↑                                                       │
             └───────┬──────────────────┴───────────────────────────────────────────────────────┘
                     │
                   All.v
```

- `Rules.v`: Defines the list of types of the rewrite rules that
  will be reified.  Largely independent of the expression language.

- `RulesProofs.v`: Proves all of the Gallina versions of the
  rewrite rules correct.

- `Rewriter.v`: Defines the rewriter machinery.  In particular, all of
  the rewriter definitions that have non-rewrite-rule-specific proofs
  about them are found in this file.

- `RewrierReify.v`: Defines reification of rewrite rules, continuing on
  from `Rewriter.v`, and culminates in the tactic
  `RewriteRules.Tactic.Build_RewriterT` and the tactic notation
  `make_Rewriter` which define a package of type
  `RewriteRules.GoalType.RewriterT`.  The `Build_*` tactic returns a
  `constr`, while the `make_*` tactic notation refines that `constr`
  in the goal.  Both tactics take two arguments: first a boolean
  `include_interp` which specifies whether (`true`) or not (`false`)
  to prefix the list of rewrite rules with the reduction-to-literal
  rewrite rules; and second a list of `bool * Prop` which is the list
  of rewrite rule types to reify, each paired with a boolean saying
  whether or not to try rewriting again in the output of the
  replacement for that rule.

- `ProofsCommon.v`: Defines the notion of interp-goodness and wf-goodness
  for rewrite rules, defines tactics to prove these notions, and
  contains a semi-arbitrary collection of proofs and definitions that
  are mostly shared between the wf proofs and the interp proofs.
  Importantly, this file defines everything needed to state and prove
  that specific rewrite rules are correct.  Additionally defines a
  package `RewriteRules.GoalType.VerifiedRewriter` which describes the
  type of the overall specialized rewriter together with its `Wf` and
  `Interp` proofs. (This package should perhaps move to another file?)

- `ProofsCommonTactics.v`: Defines the actual tactics used to prove that
  specific rewrite rules are correct, and to inhabit the packages
  defined in `ProofsCommon.v`.

- `Wf.v`: Proves wf-preservation of the generic rewriter,
  taking in wf-goodness of rewrite rules as a hypothesis.

- `InterpProofs.v`: Proves interp-correctness of the generic
  rewriter, taking in interp-goodness of rewrite rules as a
  hypothesis.

- `AllTactics.v`: Defines the tactic
  `RewriteRules.Tactic.make_rewriter` (and a similar tactic notation)
  which build the entire `VerifiedRewriter`.  They take in the
  `include_interp` as in `Rewriter.v` tactics, as well as an hlist of
  proofs of rewrite rules indexed over a `list (bool * Prop)` of
  rewrite rule types.  This is the primary interface for defining a
  rewriter from a list of rewrite rules.

- `AllTacticsExtra.v`: Specializes `AllTactics.v` to
  what's defined in `Identifier.v`

- `{NBE, Arith, ArithWithCasts, StripLiteralCasts, ToFancy,
  ToFancyWithCasts}.v`: Use the tactic from `AllTactics.v`
  together with the proven list of rewrite rules from
  `RulesProofs.v` to reify and reduce the corresponding pass
  and generate a rewriter.

- `All.v`: `Definition`less file that `Export`s the rewriters
  defined in `Rewriter/*.v`


Proofs files:
For `Language.v`, there is a semi-arbitrary split between two files
`Language.Inversion` and `Language.Wf`.
- `Inversion.v`:
  + classifies equality of type codes and exprs
  + type codes have decidable equality
  + correctness of the various type-transport definitions
  + correctness lemmas for the various `expr.invert_*` definitions
  + correctness lemmas for the various `reify_*` definitions in `Language.v`
  + `inversion_type`, which inverts equality of type codes
  + `type_beq_to_eq`, which converts boolean equality of types to
    Leibniz equality
  + `rewrite_type_transport_correct`, which rewrites with the
    correctness lemmas of the various type-transport definitions
  + `type.invert_one e` which does case analysis on any inductive type
     indexed over type codes, in a way that preserves information
     about the type of `e`, and generally works even when the goal is
     dependently typed over `e` and/or its type
  + `ident.invert`, which does case-analysis on idents whose type has
    structure (i.e., is not a var)
  + `ident.invert_match`, which does case-analysis on idents appearing as
    the discriminee of a `match` in the goal or in any hypothesis
  + `expr.invert`, which does case-analysis on exprs whose type has
    structure (i.e., is not a var)
  + `expr.invert_match`, which does case-analysis on exprs appearing as
    the discriminee of a `match` in the goal or in any hypothesis
  + `expr.invert_subst`, which does case-analysis on exprs which show up
    in hypotheses of the form `expr.invert_* _ = Some _`
  + `expr.inversion_expr`, which inverts equalities of exprs

- `Wf.v`: Depends on `Inversion.v`
  Defines:
  + expr.wf, expr.Wf, expr.wf3, expr.wf4, expr.Wf3, expr.Wf4
  + GeneralizeVar.Flat.wf
  + `expr.inversion_wf` (and variants), which invert `wf` hypotheses
  + `expr.wf_t` (and variants wf_unsafe_t and wf_safe_t) which make
     progress on `wf` goals; `wf_safe_t` should never turn a provable
     goal into an unprovable one, while `wf_unsafe_t` might.
  + `expr.interp_t` (and variants), which should make progress on
    equivalence-of-interp hypotheses and goals, but is not used much
    (mainly because I forgot I had defined it)
  + `prove_Wf`, which proves wf goals on concrete syntax trees in a more
    optimized way than `repeat constructor`
  Proves:
  + funext → (type.eqv ↔ Logic.eq) (`eqv_iff_eq_of_funext`)
  + type.related and type.eqv are PERs
  + Proper instances for `type.app_curried`, `type.and_for_each_lhs_of_arrow`
  + `type.is_not_higher_order` → Reflexive (type.and_for_each_lhs_of_arrow type.eqv)
  + iff between `type.related{,_hetero}` and related of `type.app_curried`
  + various properties of `type.and{,b_bool}for_each_lhs_of_arrow`
  + various properties of `type.eqv` and `ident.{gen_,}interp`
  + various properties of `ident.cast`
  + various properties of `expr.wf` (particularly of things defined in `Language.v`)
  + interp and wf proofs for the passes to/from Flat

- `UnderLetsProofs.v`: wf and interp lemmas for the various passes defined in `UnderLets.v`
- `MiscCompilerPassesProofs.v`: wf and interp lemmas for the various passes defined in `MiscCompilerPasses.v`
- `AbstractInterpretation/ZRangeProofs.v`: Proves correctness lemmas of the per-operation zrange-bounds-analysis functions
- `AbstractInterpretation/Wf.v`: wf lemmas for the AbstractInterpretation pass
- `AbstractInterpretation/Proofs.v`: interp lemmas for the
  AbstractInterpretation pass, and also correctness lemmas that
  combine Wf and interp
