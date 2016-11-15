[![Build Status](https://api.travis-ci.org/mit-plv/fiat-crypto.png?branch=master)](https://travis-ci.org/mit-plv/fiat-crypto)

Fiat-Crypto: Synthesizing Correct-by-Construction Assembly for Cryptographic Primitives
-----

NOTE: The github.com repo is only intermittently synced with
github.mit.edu.

To build (if your COQPATH variable is empty):

    make

To build (Coq 8.5):

	export COQPATH="$(pwd)/coqprime${COQPATH:+:}$COQPATH"
	make

To build with Coq 8.4

	export COQPATH="$(pwd)/coqprime-8.4${COQPATH:+:}$COQPATH"
	make

## Build Targets

- The default target, `make` or `make coq`, builds the main files, and requires 1.3 GB of RAM
- The small prime-specific files, `make small-specific-gen`, builds most of the prime-specific files, and also requires 1.3 GB of RAM
- The medium prime-specific files, `make medium-specific-gen`, additionally builds the files for `2^414-17`, and requires 5.4 GB of RAM
- The large prime-specific files, `make specific-gen`, additionally builds the files for `2^521-1`, and requires 26.6 GB of RAM
- Running `make .dir-locals.el` will give you a `.dir-locals.el` file which allows convenient browsing in emacs.

## Expected build times and versions

This code builds with Coq 8.4pl2-pl6, 8.5, 8.5pl1-pl3, and the tip of the v8.6 branch as of November 15, 2016.
As of November 15, 2016, using the tip of the v8.6 branch, the slowest files to build, and overall times, are in the table below.
For scaling purposes, passing the flag `TIMED=1` to make will print out the time it takes to build each file, as it builds them.

|Time      | File Name                                                              |
|----------|------------------------------------------------------------------------|
|4m16.33s  | SpecificGen/GF5211_32Reflective/Reified/Mul                            |
|3m23.12s  | SpecificGen/GF5211_32Bounded                                           |
|2m55.84s  | SpecificGen/GF5211_32                                                  |
|2m25.01s  | SpecificGen/GF41417_32Bounded                                          |
|1m47.24s  | SpecificGen/GF41417_32                                                 |
|1m44.75s  | SpecificGen/GF5211_32BoundedCommon                                     |
|1m32.33s  | Test/Curve25519SpecTestVectors                                         |
|1m17.22s  | CompleteEdwardsCurve/ExtendedCoordinates                               |
|1m13.83s  | Experiments/Ed25519                                                    |
|1m06.12s  | SpecificGen/GF41417_32BoundedCommon                                    |
|0m59.04s  | SpecificGen/GF41417_32Reflective/Reified/Mul                           |
|0m40.43s  | ModularArithmetic/Conversion                                           |
|0m37.59s  | SpecificGen/GF5211_32Reflective/CommonBinOp                            |
|0m34.60s  | Spec/Ed25519                                                           |
|0m33.27s  | SpecificGen/GF5211_32Reflective/CommonUnOpWireToFE                     |
|0m33.24s  | SpecificGen/GF5211_32Reflective/CommonUnOp                             |
|0m31.56s  | ModularArithmetic/ModularBaseSystemProofs                              |
|0m30.41s  | Specific/GF25519Bounded                                                |
|0m30.21s  | SpecificGen/GF25519_32Bounded                                          |
|0m30.18s  | SpecificGen/GF2519_32Bounded                                           |
|...       |...                                                                     |
|46m09.90s | Total Time                                                             |
