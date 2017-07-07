[![Build Status](https://api.travis-ci.org/mit-plv/fiat-crypto.png?branch=master)](https://travis-ci.org/mit-plv/fiat-crypto)

Fiat-Crypto: Synthesizing Correct-by-Construction Code for Cryptographic Primitives
-----

NOTE: The github.com repo is only intermittently synced with
github.mit.edu.

This repository has been tested with Coq 8.6. Coq 8.4 and older are known not to work. Coq 8.5 is not regularly tested, but we are not aware of fundamental reasons why it should not work.

To build (if your COQPATH variable is empty):

	make

To build:

	export COQPATH="$(pwd)/coqprime${COQPATH:+:}$COQPATH"
	make
