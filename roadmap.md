# Roadmap

A brief overview of possible long-term targets:

- Ed25519 Signing
	* Simplistic implementation: constant-time scalar multiplication
	* Fast implementation: fixed-base precomputed constant-time scalar multiplication (big tables)
	* Hardest part: ModularBaseSystem for exponent field (non-pseudomersenne modular arithmetic)
- Ed25519 Verification
	* Simplistic implementation: two non-constant time scalar multiplications, one addition (probably best thing to work on now)
	* Fast implemetation: double-scalar multiplication
	* Hardest part: optimizing double-scalar multiplication
- Ed25519 Batch Verification
	* Simplistic implementation: many single verifications
	* Fast implemetation: multi-scalar multiplication
	* Hardest part: max-heap of exponent scalars
- Key agreement (X25519)
	* X-coordinate-only Montgomery ladder (similar to square-and-multiply, but not identical)
	* Hardest part: proving correctness of differential addition (requires field, nontrivial proof)

## Common Subgoals

- Synthesis of optimized modular arithmetic (ModularBaseSystem) -- necessary for all targets
	* expression simplification (plus 0, times 1, etc.)
	* bounds/no-overflow proofs
	* automatic carry-chain synthesis (depends on bounds automation)
	* selection (bx + (not b)y) -- necessary for signing and key agreement
- Scalar arithmetic for exponents (non-pseudomersenne modular arithmetic) -- necessary for signing, batch verification
	* less performance-critical than ModularBaseSystem for pseudomersenne primes
	* constant-time for signing
	* add, sub, mul, reduce
- General theorems about elliptic curve arithmetic (requires field; proofs are hard and rely extensively on existing literature)
	* addition is commutative
	* our representations are interchangable (except MontgomeryX)
- Gallina with Words to Qhasm translation
	* simple expressions -- necessary for all targets
	* bounded loops -- necessary for all targets
	* lookup tables -- necessary for fast signing
	* function abstraction -- would improve performance of all targets, most important for fast verification/batch verification
- Wire format specification -- necessary for all targets
	* little byte-Endian integers
	* point compression
- Wire format decoding -- necessary for all targets
	* converting between BaseSystems whose digit weights are different sequences of powers of 2
	* single-coordinate point recovery (use X and a single bit to recover (X, Y)); needs field tactic 
- Interfacing with hash functions -- necessary for all signature targets
	* no specific properties, just that output is determined by input
