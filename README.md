[![Build Status](https://api.travis-ci.org/mit-plv/fiat-crypto.png?branch=master)](https://travis-ci.org/mit-plv/fiat-crypto)

Fiat-Crypto: Synthesizing Correct-by-Construction Assembly for Cryptographic Primitives
-----

NOTE: The github.com repo is only intermittently synced with
github.mit.edu.

To build:

	export COQPATH="$(pwd)/coqprime${COQPATH:+:}$COQPATH"
	make
