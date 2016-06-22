[![Build Status](https://api.travis-ci.org/mit-plv/fiat-crypto.png?branch=master)](https://travis-ci.org/mit-plv/fiat-crypto)

Fiat-Crypto: Synthesizing Correct-by-Construction Assembly for Cryptographic Primitives
-----

NOTE: The github.com repo is only intermittently synced with
github.mit.edu.

To build (Coq 8.5):

	export COQPATH="$(pwd)/coqprime${COQPATH:+:}$COQPATH"
	make

To build with Coq 8.4

	export COQPATH="$(pwd)/coqprime-8.4${COQPATH:+:}$COQPATH"
	make
