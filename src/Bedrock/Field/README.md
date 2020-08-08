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
found in `Synthesis/Examples/`. Examples of generated output (printed as C code)
can be found outside this subdirectory, in the top-level `fiat-bedrock2`
subdirectory. Please note that the translation from bedrock2 to C is just for
readability, and is unverified.

Here is a prettified example of the fiat-crypto AST and corresponding bedrock2
code for curve25519 addition on 64-bit (see `Synthesis/Examples/X25519_64.v`):

Fiat-crypto AST (input to the translation):
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