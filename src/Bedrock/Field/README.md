# Bedrock2 backend

The code in this subdirectory translates functions in fiat-crypto's internal
language to bedrock2 code.

## Usage

Examples of generating, translating, and proving arithmetic operations can be
found in `Synthesis/Examples/`. Generally, you first create a suite of field
operations (for each operation, you get a bedrock2 function, a specification,
and a proof that the function obeys the specification), and then use those to
prove higher-level functions as usual using bedrock2 logic. It's also possible
to call the translator directly on an arbitrary expression in fiat-crypto's AST
(the top-level function is `translate_func`).

## Structure

The most important directories are:

`Translation/` : defines functions that manipulate a fiat-crypto expression and
translate it to bedrock2.

`Proofs/` : proves that the functions in `Translation/` do their jobs
correctly. Generally, each `Translation/XYZ.v` has a `Proofs/XYZ.v` that
corresponds to it.

`Synthesis/` : contains tactics and groundwork for creating suites of field
operation implementations with proofs, and examples of usage.

## Method

The translation process mirrors bedrock2 abstraction levels (see bedrock2's
`Syntax.v`):

1. `expr`, for expressions that don't set local variables, store anything, or
   otherwise change state
2. `cmd`, for expressions that do set local variables. In bedrock2 these are
   also allowed to store data. However, in this fiat-crypto backend the `cmd`
level is not allowed to read from or write to memory.
3. `func`, the top level, which is allowed to handle memory. The bedrock2 code
   produced by this backend always loads input arrays into local variables
immediately, and handles everything in local variables until it's ready to
store any output arrays at the end.

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
- have only one size of integer (uses options `widen_bytes` and
  `widen_carries`)
- not have functions that return multiple values, as these are untranslatable
  to bedrock2\*
- not use types other than integers, lists of integers, and tuples, although
  tuples can be arbitrarily nested
- not assign anything to lists

\* bedrock2 doesn't support carries or assigning to multiple values, but if it
did start supporting them in the future the translation has most of the code in
place to handle that.

## Example

To make things a little more concrete, here is the translation of addition for
curve25519 on 64-bit (see `Synthesis/Examples/X25519_64.v`):

fiat-crypto AST (input to the translation):
```
= fun x : API.type -> Type =>
  (λ x0
      x1 : x
             (type.base
                (base.type.list (base.type.type_base Compilers.Z))),
   expr_let x2 := #Compilers.ident_Z_cast @
                  ###r[0 ~> 18446744073709551615]%zrange @
                  (#Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   ($x0 [[0]]) +
                   #Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   ($x1 [[0]])) in
   expr_let x3 := #Compilers.ident_Z_cast @
                  ###r[0 ~> 18446744073709551615]%zrange @
                  (#Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   ($x0 [[1]]) +
                   #Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   ($x1 [[1]])) in
   expr_let x4 := #Compilers.ident_Z_cast @
                  ###r[0 ~> 18446744073709551615]%zrange @
                  (#Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   ($x0 [[2]]) +
                   #Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   ($x1 [[2]])) in
   expr_let x5 := #Compilers.ident_Z_cast @
                  ###r[0 ~> 18446744073709551615]%zrange @
                  (#Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   ($x0 [[3]]) +
                   #Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   ($x1 [[3]])) in
   expr_let x6 := #Compilers.ident_Z_cast @
                  ###r[0 ~> 18446744073709551615]%zrange @
                  (#Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   ($x0 [[4]]) +
                   #Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   ($x1 [[4]])) in
   expr_let x7 := #Compilers.ident_Z_cast @
                  ###r[0 ~> 18446744073709551615]%zrange @
                  (#Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   ($x0 [[5]]) +
                   #Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   ($x1 [[5]])) in
   expr_let x8 := #Compilers.ident_Z_cast @
                  ###r[0 ~> 18446744073709551615]%zrange @
                  (#Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   ($x0 [[6]]) +
                   #Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   ($x1 [[6]])) in
   expr_let x9 := #Compilers.ident_Z_cast @
                  ###r[0 ~> 18446744073709551615]%zrange @
                  (#Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   ($x0 [[7]]) +
                   #Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   ($x1 [[7]])) in
   expr_let x10 := #Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   (#Compilers.ident_Z_cast @
                    ###r[0 ~> 18446744073709551615]%zrange @
                    ($x0 [[8]]) +
                    #Compilers.ident_Z_cast @
                    ###r[0 ~> 18446744073709551615]%zrange @
                    ($x1 [[8]])) in
   expr_let x11 := #Compilers.ident_Z_cast @
                   ###r[0 ~> 18446744073709551615]%zrange @
                   (#Compilers.ident_Z_cast @
                    ###r[0 ~> 18446744073709551615]%zrange @
                    ($x0 [[9]]) +
                    #Compilers.ident_Z_cast @
                    ###r[0 ~> 18446744073709551615]%zrange @
                    ($x1 [[9]])) in
   [$x2; $x3; $x4; $x5; $x6; $x7; $x8; $x9; $x10; $x11])%expr
: API.Expr
    (type.base (base.type.list (base.type.type_base Compilers.Z)) ->
     type.base (base.type.list (base.type.type_base Compilers.Z)) ->
     type.base (base.type.list (base.type.type_base Compilers.Z)))
```

bedrock2 implementation (output of the translation):
```
= ("curve25519_add"%string,
  (["in0"%string; "in1"%string; "out0"%string], [],
  (((("x0"%string = *(uintptr_t*) ("in0" + (uintptr_t)0ULL);;
      "x1"%string = *(uintptr_t*) ("in0" + (uintptr_t)8ULL);;
      "x2"%string = *(uintptr_t*) ("in0" + (uintptr_t)16ULL);;
      "x3"%string = *(uintptr_t*) ("in0" + (uintptr_t)24ULL);;
      "x4"%string = *(uintptr_t*) ("in0" + (uintptr_t)32ULL);;
      "x5"%string = *(uintptr_t*) ("in0" + (uintptr_t)40ULL);;
      "x6"%string = *(uintptr_t*) ("in0" + (uintptr_t)48ULL);;
      "x7"%string = *(uintptr_t*) ("in0" + (uintptr_t)56ULL);;
      "x8"%string = *(uintptr_t*) ("in0" + (uintptr_t)64ULL);;
      "x9"%string = *(uintptr_t*) ("in0" + (uintptr_t)72ULL);;
      /*skip*/);;
     ("x10"%string = *(uintptr_t*) ("in1" + (uintptr_t)0ULL);;
      "x11"%string = *(uintptr_t*) ("in1" + (uintptr_t)8ULL);;
      "x12"%string =
      *(uintptr_t*) ("in1" + (uintptr_t)16ULL);;
      "x13"%string =
      *(uintptr_t*) ("in1" + (uintptr_t)24ULL);;
      "x14"%string =
      *(uintptr_t*) ("in1" + (uintptr_t)32ULL);;
      "x15"%string =
      *(uintptr_t*) ("in1" + (uintptr_t)40ULL);;
      "x16"%string =
      *(uintptr_t*) ("in1" + (uintptr_t)48ULL);;
      "x17"%string =
      *(uintptr_t*) ("in1" + (uintptr_t)56ULL);;
      "x18"%string =
      *(uintptr_t*) ("in1" + (uintptr_t)64ULL);;
      "x19"%string =
      *(uintptr_t*) ("in1" + (uintptr_t)72ULL);;
      /*skip*/);;
     /*skip*/);;
    "x20"%string = "x0" + "x10";;
    "x21"%string = "x1" + "x11";;
    "x22"%string = "x2" + "x12";;
    "x23"%string = "x3" + "x13";;
    "x24"%string = "x4" + "x14";;
    "x25"%string = "x5" + "x15";;
    "x26"%string = "x6" + "x16";;
    "x27"%string = "x7" + "x17";;
    "x28"%string = "x8" + "x18";;
    "x29"%string = "x9" + "x19";;
    "x30"%string = "x20";;
    "x31"%string = "x21";;
    "x32"%string = "x22";;
    "x33"%string = "x23";;
    "x34"%string = "x24";;
    "x35"%string = "x25";;
    "x36"%string = "x26";;
    "x37"%string = "x27";;
    "x38"%string = "x28";;
    "x39"%string = "x29";;
    /*skip*/);;
   (*(uintptr_t*) "out0" + (uintptr_t)0ULL = "x30");;
   (*(uintptr_t*) "out0" + (uintptr_t)8ULL = "x31");;
   (*(uintptr_t*) "out0" + (uintptr_t)16ULL = "x32");;
   (*(uintptr_t*) "out0" + (uintptr_t)24ULL = "x33");;
   (*(uintptr_t*) "out0" + (uintptr_t)32ULL = "x34");;
   (*(uintptr_t*) "out0" + (uintptr_t)40ULL = "x35");;
   (*(uintptr_t*) "out0" + (uintptr_t)48ULL = "x36");;
   (*(uintptr_t*) "out0" + (uintptr_t)56ULL = "x37");;
   (*(uintptr_t*) "out0" + (uintptr_t)64ULL = "x38");;
   (*(uintptr_t*) "out0" + (uintptr_t)72ULL = "x39");;
   /*skip*/)%bedrock_cmd))
: Defaults.bedrock_func
```
