# Bedrock2 field-arithmetic backend

The code in this subdirectory creates proofs and code for field arithmetic using
fiat-crypto's pipeline.

## Structure

`Common/` : generally useful definitions and proofs for bedrock2 field
 arithmetic

`Synthesis/` : tactics and proofs that string together the fiat-crypto pipeline
  and the bedrock2 translation, and that make it easy to create full suites of
  bedrock2 operations with proofs for different fields

`Translation/` : the compiler that translates from fiat-crypto's AST to
 bedrock2, and its correctness proofs

## Usage

Generally, you would (following the pattern in `Synthesis/Examples`) first
create a suite of field operations for your chosen field using the premade
synthesis tactics. For each field operation, you get a bedrock2 function, a
specification, and a proof that the function obeys the specification. Using
these, you can prove higher-level functions using the usual bedrock2 logic.

For more custom use cases, it's also possible to call the translator directly on
an arbitrary expression in fiat-crypto's AST. The top-level function for this
purpose is `translate_func` from `Translation/Func.v`, and its correctness proof
is `translate_func_correct` from `Translation/Proofs/Func.v`. To prove that the
expression is valid input to the compiler, it's also likely helpful to take a
look at the computable version of `valid_func` from
`Translation/Proofs/ValidComputable/Func.v`.

## Examples

Examples of generating, translating, and proving arithmetic operations can be
found in `Synthesis/Examples/` and `../End2End/*/Field*.v`.
Examples of generated output (printed as C code) can be found outside this
subdirectory, in the top-level `fiat-bedrock2` subdirectory. Please note that
the translation from bedrock2 to C is just for readability, and is unverified.
