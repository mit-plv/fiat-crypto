This file is to list tractable, can-be-started-now expansions of the library.
None of this is necessarily going to happen, but better have it here than in
people's heads.

**poly1305** spec and simple implementation using existing field-arithmetic
synthesis tools and a Gallina-level loop. Possibly model this after the
implementation in go.crypto for AMD64.

**striping** for poly1305 -- evaluating a polynomial by splitting it into, for
example, 4 polynomials such that coefficient i is in polynomial i mod 4 and
evaluating the 4 polynomials in parallel, then combining results. Model this
after Andy Polyakov's AVX2 code in OpenSSL.

**precomputed** tables for ed25519 fixed-basepoint scalar multiplication. Model
after the ed25519 paper and the go.crypto implementation. This would include
implementing unsigned-to-signed conversion for bignums.

**fixed window** variable-basepoint scalar multiplication. Currently we use
binary exponentiation (window of 1 bit), but 4 would be much faster. See
go.crypto ed25519 for reference, or maybe go.crypto p256.

**homomorphism** from ed25519 to x25519 -- the signing scheme and key agreement
system use the same curve but in different coordinates. The ed25519
fixed-basepoint scalar multiplication with precomputed tables is faster than
x25519 scalar multiplication which cannot use precomputed tables, so one would
want to perform the computation in Edwards coordinates and then convert to
Montgomery-X coordinates. Model after blog post on imperialvolet.org. First
investigate whether this task actually depends on the next one.

**elligator** encoding of ed25519 points, primarily requiring a homomorphism
from Edwards coordinates to Weierstrass coordinates. This homomorphism would
also validate our transcription of the x25519 spec. Model after the "Elligator
2" in the Elligator paper and a imperialviolet.org post.

**subgroup** membership checks for ed25519 -- the group has order 8*prime, but
some algorithms require checking that the inputs are in the prime-order
subgroup. Model github.com/yahoo/coname VRF implementation for an implementation
of such checks, hopefully it also contains a reference to a paper that explained
why these checks are sufficient. Capitalize on this by implementing VxEdDSA as
specified by OpenWhisperSystems.

**decaf** cofactor removal for the ed448-goldilocks elliptic curve as explained
in the decaf paper. I don't know what a good use case for this would be, though.

**ECDSA** signature scheme specification, to complement EdDSA. Synthesize code
for some existing curve for to test it; the real target would be p256.

**freeze** (field element canonicalization) the way Mike Hamburg does it -- it
may or may not be better than our current one, but it very well might be less
code+proof.

**refined Montgomery multiplication** for p256 and maybe RSA. Model after the
work of Shay Gueron and Vlad Krasnov -- the code is in OpenSSL ("rsaz" and
"p256z" assembly for AMD64) and there are papers as well. Note that we already
have proofs and code generation for some variants of Montgomery multiplication,
so the first task would be to figure out how much of them can be reused.

**Chinese Remainder Theorem** decomposition and recombination for RSA signing,
maybe modeled after Brian Smith's ring library or go.crypto. Note that we would
first need to have some story for modular multiplication at RSA sizes.

**NewHope-simple** -- study it, see what would be needed to create an implementation.

**McBits** -- study it, see what would be needed to create an implementation.

**verified compilation** of PHOAS straight-line code to Jasmine-lang. This would
involve register allocation and instruction scheduling.

**verified compilation** of PHOAS code to VST C.

**loops** for our PHOAS language. Possibly hardcoded to [fold_left] of [seq], or
something else that is sufficient to encode C "for" loops. Importantly, we
should have a way to reify existing code

**modules** for our PHOAS language so we don't have to inline everything.
Basically we want to allow one Coq-level object to represent a collection of
PHOAS functions that may call one another. It should be possible to optimize one
function using a verified PHOAS pass of whatever and maintain the correctness
results of the other functions that call it.
