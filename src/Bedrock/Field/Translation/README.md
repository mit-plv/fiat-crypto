# Bedrock2 translation

The code in this subdirectory translates field arithmetic functions in
fiat-crypto's internal language to bedrock2 code.

## Structure

The top-level definition for the bedrock2 translation is `translate_func` from
`Func.v`; other files in this directory form the lower-level definitions on
which it depends.

`Parameters/` : helper tactics and default values relating to translation
parameters

`Proofs/` : proves that the functions in `Translation/` do their jobs
correctly. Generally, each `Translation/XYZ.v` has a `Translation/Proofs/XYZ.v`
that corresponds to it.

## Method

The translation process mirrors bedrock2 abstraction levels (see bedrock2's
`Syntax.v`):

1. `expr`, for expressions that don't set local variables, store anything, or
   otherwise change state
2. `cmd`, for expressions that do set local variables. In bedrock2 these are
   also allowed to store data. However, in this fiat-crypto backend the `cmd`
level is not allowed to read from or write to memory.
3. `func`, the top level, which wraps the output of the `cmd` phase and
   generates additional code to handle memory. The bedrock2 code produced by
   this backend always loads input arrays into local variables immediately
   after function invocation, and keeps everything in local variables until
   it's ready to store any output arrays at the end.

The choice to not allow the `cmd` level to modify memory was a tradeoff that
makes sense for the specific domain in which fiat-crypto operates, because you
basically always need to access all the information in your input array and
gain nothing by modifying it in place. Doing the loads immediately and the
stores at the very end also greatly simplified the proofs for the `cmd` level,
which can now assume that memory doesn't change. And, since the inputs are
read-only, it allowed `translate_func_correct` to use multiple separation-logic
preconditions instead of one (one for each input, one for the output), which
means it's possible to e.g.  add a bignum to itself and then store the result
in the same location, in place. The postcondition will be stated in terms of
the output precondition (so if you stored the result in one of the inputs, you
will of course lose information about that input).


Another thing to note about the translation is that it assumes all lists are
handled as arrays and passed as pointers, so if a function returns a list an
argument will be added to the bedrock2 implementation: a pointer in which to
store the output list. This happens automatically for all lists of integers in
the return type.

## Restrictions

Input to the bedrock2 translation must:

- contain only the subset of operations found in `Translation/Expr.v`
- have only one size of integer (see rewriter pipeline options `widen_bytes`
  and `widen_carry`)
- not have arithmetic oprations that return multiple values (for example, low
  and high half of the output), as these are untranslatable to bedrock2\*
- not use types other than integers, lists of integers, and tuples, although
  tuples can be arbitrarily nested
- not assign anything to lists

\* bedrock2 does support returning multiple values from a function, but
currently the compiler does not do function inlining so the relevant
substitution is peformed by the fiat-crypto rewriter instead. If bedrock2
started supporting multi-return arithmetic operations in the future the
translation has most of the code in place to handle that.
