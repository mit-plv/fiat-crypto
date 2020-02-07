Fiat-Crypto: Synthesizing Correct-by-Construction Code for Cryptographic Primitives
=====

Building
-----
[![CI (Coq)](https://github.com/mit-plv/fiat-crypto/workflows/CI%20(Coq)/badge.svg)](https://github.com/mit-plv/fiat-crypto/actions?query=workflow%3A%22CI+%28Coq%29%22+branch%3Amaster)

This repository requires Coq 8.9 or later. Note that if you install Coq from Ubuntu aptitude packages, you need `libcoq-ocaml-dev` in addition to `coq`.

Git submodules are used for some dependencies. If you did not clone with `--recursive`, run

    git submodule update --init --recursive

To build (if your COQPATH variable is empty):

       make

To build:

       export COQPATH="$(pwd)/rewriter/src:$(pwd)/coqprime/src:$(pwd)/bedrock2/bedrock2/src:$(pwd)/bedrock2/deps/coqutil/src${COQPATH:+:}$COQPATH"
       make

Usage
-----

The Coq development builds binary compilers that generate code using some implementation strategy.
The parameters (modulus, hardware multiplication input bitwidth, etc.) are are specified on the command line of the compiler.
The generated C code is written to standard output.

A collection of C files for popular curves can be made with

    make c-files

The C files will appear in the top-level directory.

Just the compilers generating these C files can be made with

    make standalone

or `make standalone-haskell` or `make standalone-ocaml` for binaries generated with just one compiler.
The binaries are located in `src/ExtractionOcaml/` and `src/ExtractionHaskell` respectively.

There is a separate compiler binary for each implementation strategy:

 - `saturated_solinas`
 - `unsaturated_solinas`
 - `word_by_word_montgomery`

Passing no arguments, or passing `-h` or `--help` (or any other invalid arguments) will result in a usage message being printed.  These binaries output C code on stdout.

Here are some examples of ways to invoke the binaries (from the directories that they live in):

    # Generate code for 2^255-19
    ./unsaturated_solinas '25519' '5' '2^255 - 19' '64' carry_mul carry_square carry_scmul121666 carry add sub opp selectznz to_bytes from_bytes > curve25519_64.c
    ./unsaturated_solinas '25519' '10' '2^255 - 19' '32' carry_mul carry_square carry_scmul121666 carry add sub opp selectznz to_bytes from_bytes > curve25519_32.c

    # Generate code for NIST-P256 (2^256 - 2^224 + 2^192 + 2^96 - 1)
    ./word_by_word_montgomery 'p256' '2^256 - 2^224 + 2^192 + 2^96 - 1' '32' > p256_32.c
    ./word_by_word_montgomery 'p256' '2^256 - 2^224 + 2^192 + 2^96 - 1' '64' > p256_64.c

You can find more examples in the `Makefile`.

Reading About The Code
----------------------

- [Andres Erbsen, Jade Philipoom, Jason Gross, Robert Sloan, Adam Chlipala. Simple High-Level Code For Cryptographic Arithmetic -- With Proofs, Without Compromises. To Appear in Proceedings of the IEEE Symposium on Security & Privacy 2019 (S&P'19). May 2019.](http://adam.chlipala.net/papers/FiatCryptoSP19/FiatCryptoSP19.pdf). This paper describes multiple field arithmetic implementations, and an older version of the compilation pipeline (preserved [here](https://github.com/mit-plv/fiat-crypto/tree/sp2019latest)). It is somewhat space-constrained, so some details are best read about in theses below.
- [Jade Philipoom. Correct-by-Construction Finite Field Arithmetic in Coq. MIT Master's Thesis. February 2018.](http://adam.chlipala.net/theses/jadep_meng.pdf) Chapters 3 and 4 contain a detailed walkthrough of the field arithmetic implementations (again, targeting the previous compilation pipeline).
- [Andres Erbsen. Crafting Certified Elliptic CurveCryptography Implementations in Coq. MIT Master's Thesis. June 2017.](
http://adam.chlipala.net/theses/andreser_meng.pdf) Section 3 contains a whirlwind introduction to synthesizing field arithmetic code using coq, without assuming Coq skills, but covering a tiny fraction of the overall library. Sections 5 and 6 contain the only write-up on the ellitpic-curve library in this repository.
- The newest compilation pipeline does not have a separate document yet, but this README does go over it in some detail.


Reading The Code
----------------

### Demo of Synthesis

The idea of the synthesis process is demoed in [`src/Demo.v`](./src/Demo.v).
We strongly recommend reading this before studying the full-scale system.

### Proofs About Elliptic Curves

We have some about elliptic curves, for example:

- [`src/Curves/Edwards/AffineProofs.v`](./src/Curves/Edwards/AffineProofs.v),
- [`src/Curves/Edwards/XYZT/Basic.v`](./src/Curves/Edwards/XYZT/Basic.v),
- [`src/Curves/Montgomery/AffineProofs.v`](./src/Curves/Montgomery/AffineProofs.v),
- [`src/Curves/Montgomery/XZProofs.v`](src/Curves/Montgomery/XZProofs.v).

### Actual Synthesis Pipeline

The entry point for clients of the PHOAS expressions we use is
`Language/API.v`.  Refer to comments in that file for an explanation
of the interface; the following text describes how the expressions are
generated, not how to interact with them.

The ordering of files (eliding `*Proofs.v` files) is:

```
Language/*.v
    ↑
    ├────────────────────────────────┬───────────────────────┬───────────────────────┐
AbstractInterpretation/*.v     MiscCompilerPasses.v    Rewriter/*.v     PushButtonSynthesis/ReificationCache.v      Arithmetic.v
    ↑                                ↑                       ↑                       ↑                                   ↑
Stringification/*.v                  │                       │                       │                        COperationSpecifications.v
    ↑                                │                       │                       │                                   ↑
    └────────────┬───────────────────┴───────────────────────┴────────┬──────────────┘                                   │
           BoundsPipeline.v                                  CompilersTestCases.v                                        │
                 ↑                                                                                                       │
                 └────────────┬──────────────────────────────────────────────────────────────────────────────────────────┘
                     PushButtonSynthesis/*.v
                              ↑
                   ┌──────────┴────────────────┐
                  CLI.v                SlowPrimeSynthesisExamples.v
                   ↑
        ┌──────────┴────────────────┐
StandaloneHaskellMain.v   StandaloneOCamlMain.v
        ↑                           ↑
ExtractionHaskell.v          ExtractionOCaml.v
```

Within each directory, the dependency graphs (again eliding `*Proofs.v` and related files) are:

Within `Language/`:
```
  Pre.v ←──────────────────────────────────────────────────────────────────────── IdentifierParameters.v
    ↑                                                                                        ↑
Language.v ←── IdentifiersBasicLibrary.v ←──── IdentifiersBasicGenerate.v ←── IdentifiersBasicGENERATED.v ←───────────────────────────── API.v
    ↑                        ↑                                                               ↑
    ├────────────────┐       └────────────────────────────┐                                  │
UnderLets.v    IdentifiersLibrary.v ←──────────── IdentifiersGenerate.v ←─────── IdentifiersGENERATED.v
                     ↑                                       ↑                               ↑
              IdentifiersLibraryProofs.v ←─── IdentifiersGenerateProofs.v ←─ IdentifersGENERATEDProofs.v
```

Within `Stringification/`:
```
Language.v
    ↑
   IR.v
    ↑
 ┌──┴───────┐
C.v       Rust.v
```

We will come back to the `Rewriter/*` files shortly.

The files contain:

- `Arithmetic.v`: All of the high-level field arithmetic stuff

- `COperationSpecifications.v`: The specifications for the various
  operations to be synthesized.
  TODO: This file should probably be renamed.

- `AbstractInterpretation/*.v`: type-code-based ZRange definitions, abstract
  interpretation of identifiers (which does let-lifting, for historical reasons,
  and the dependency on UnderLets should probably be removed), defines the
  passes:
  + PartialEvaluateWithBounds
  + PartialEvaluateWithListInfoFromBounds
  + CheckPartialEvaluateWithBounds

- `MiscCompilerPasses.v`: Defines the passes:
  + EliminateDead (dead code elimination)
  + Subst01 (substitute let-binders used 0 or 1 times)

- `Rewriter/*.v`: rewrite rules, rewriting.  See below for actual stucture
  of files.  Defines the passes:
  + RewriteNBE
  + RewriteArith
  + RewriteArithWithCasts
  + RewriteStripLiteralCasts
  + RewriteToFancy
  + RewriteToFancyWithCasts
  + PartialEvaluate (which is just a synonym for RewriteNBE)

- Inside `Language/`:

  + `Pre.v`: A few definitions which are used in writing out rewrite
    rules and the interpretations of PHOAS identifiers, e.g.,
    `ident.cast`, `ident.eagerly`, `Thunked.list_rect`, etc

  + `Language.v`: Defines parts of the PHOAS basic infrastructure
        parameterized over base types and identifiers including:
    . PHOAS
    . reification
    . denotation/intepretation
    . utilities for inverting PHOAS exprs
    . default/dummy values of PHOAS exprs
    . default instantiation of generic PHOAS types
    . gallina reification of ground terms
    . Flat/indexed syntax trees, and conversions to and from PHOAS

    Defines the passes:
    . ToFlat
    . FromFlat
    . GeneralizeVar

  + `API.v`: Specializes the type of PHOAS expressions to the
    particular identifiers we're using, and defines convenience
    notations, tactics, and definitions for some of the specialized
    versions.

  + `IdentifierParameters.v`: Defines a couple of definitions
    determining the identifiers and types used by the language.  These
    are used as input for the generation of identifier definitions.

  + `IdentifiersBasicLibrary.v`: Defines the package type holding basic
    identifier definitions.

  + `IdentifiersBasicGenerate.v`: Defines the tactics that generate
    all of the identifier-list-specific definitions used by the PHOAS
    machinery, in addition to defining the tactics that do reification
    based on the generated package.

  + `IdentifiersBasicGENERATED.v`: Basically autogenerated file that
    defines the inductives of base type codes and identifier codes
    (the first hand-written because it's short; the latter copy-pasted
    from a tactic that prints out the inductive), and calls the
    package-generation-tactic from `IdentifiersBasicGenerate.v`.

  + `UnderLets.v`: the UnderLets monad, a pass that does substitution
    of var-like things, a pass that inserts let-binders in the
    next-to-last line of code, substituting away var-like things (this
    is used to ensure that when we output C code, aliasing the input
    and the output arrays doesn't cause issues).
    Defines the passes:
    . SubstVar
    . SubstVarLike
    . SubstVarOrIdent

  The following files in `Language/` are used only by the rewriter:

  + `IdentifiersLibrary.v`: Some definitions about identifiers and
    pattern identifiers and raw identifiers.  Some of these
    definitions take generated definitions as arguments. Also defines
    a package record to hold all of the generated definitions.

  + `IdentifiersGenerate.v`: Tactics to generate definitions about
    untyped and pattern versions of identifiers for the rewriter.
    Culminates in a tactic which inhabits the package type defined in
    `IdentifiersLibrary.v`

  + `IdentifiersLibraryProofs.v`: proofs about definitions in
    IdentifiersLibrary.  Also defines a package to hold generated
    proofs that require destructing inductives not yet defined in this
    file.

  + `IdentifiersGenerateProofs.v`: tactics to prove lemmas to inhabit
    the package defined in `IdentifiersLibraryProofs.v`

  + `IdentifiersGENERATE.v`: identifiers / inductives and definitions
    generated by IdentifiersGenerate.

  + `IdentifiersGENERATEProofs.v`: proofs generated by
    IdentifiersGenerateProofs, about definitions in
    IdentifiersGENERATE

- Inside `Stringification/`:

  + `Language.v`: defines a printer (Show instance) for the PHOAS
    language, defines some common language-independent utilities for
    conversion to output code, and defines the spec/API of conversion
    from PHOAS to code in a language as strings.  (Depends on
    `AbstractInterpretation.v` for ZRange utilities.)  Defines the
    passes:
    . ToString.LinesToString
    . ToString.ToFunctionLines

  + `IR.v`: Defines a common IR for C and Rust (and maybe eventually
    other languages), and builds most of the infrastructure necessary
    for instantiating the LanguageSpecification API for a language
    with pointers and function calls

  + `C.v`: conversion to C code as strings.  Instantiates the API
    defined in `Stringification.Language`.

  + `Rust.v`: conversion to Rust code as strings.  Instantiates the
    API defined in `Stringification.Language`.

- `CompilersTestCases.v`: Various test cases to ensure everything is working

- `BoundsPipeline.v`: Assemble the various compiler passes together into
  a composed pipeline.  It is the final interface for the compiler.
  Also contains some tactics for applying the BoundsPipeline
  correctness lemma.

- `PushButtonSynthesis/ReificationCache.v`: Defines the cache that
  holds reified versions of operations, as well as the tactics that
  reify and apply things from the cache.

- `PushButtonSynthesis/*`: Reifies the various operations from
  `Arithmetic.v`, definies the compositions of the BoundsPipeline with
  these operations, proves that their interpretations satisfies the
  specs from `COperationSpecifications.v`, assembles the reified
  post-bounds operations into synthesis targets.  These are the files
  that `CLI.v` depends on:
  + `ReificationCache.v`:
      Defines the cache of pre-reified terms.  Splitting up
      reification from uses of the pipeline allows us to not have to
      re-reify big terms every time we change the pipeline or
      intermediate stages thereof.
  + `InvertHighLow.v`:
      Defines some common definitions, around plitting apart high and
      low bits of things, for Barrett and FancyMontgomeryReduction.
  + `Primitives.v`:
      Specializes the pipeline to basic "primitive" operations such as
      cmovznz, addcarryx, subborrowx, etc.
  + `SmallExamples.v`:
      Some small examples of using the pipeline.  Nothing depends on
      this file; it is for demonstration purposes only.
  + `*ReificationCache.v`:
      Holds the reified versions of the definitions used in the
      corresponding file.
  + `BarrettReduction.v`, `FancyMontgomeryReduction.v`,
    `SaturatedSolinas.v`, `UnsaturatedSolinas.v`, `WordByWordMontgomery.v`:
      Holds the instantiation of the pipeline to the corresponding
      implementation choice, as well as any relevant correctness
      proofs (such as that things assemble into a ring).

- `SlowPrimeSynthesisExamples.v`: Additional uses of the pipeline for
  primes that are kind-of slow, which I don't want extraction blocking
  on.  Also contains some debugging examples.

- `CLI.v`: Setting up all of the language-independent parts of extraction; relies
  on having a list of strings-or-error-messages for each pipeline, and on the
  arguments to that pipeline, and builds a parser for command line arguments for
  that.

- `StandaloneHaskellMain.v`, `StandaloneOCamlMain.v`, `ExtractionHaskell.v`,
  `ExtractionOCaml.v`: Extraction of pipeline to various languages


The files defined in `Rewriter/` are split up into the following
dependency graph (including some files from `Language/` at the top):
```
IdentifiersLibrary.v ←───────────────────────── IdentifiersGenerate.v ←──────────────────── IdentifiersGENERATED.v
    ↑ ↑                                                   ↑                                        ↑
    │ └──────────────── IdentifiersLibraryProofs.v ←──────┴─ IdentifiersGenerateProofs.v ←─ IdentifersGENERATEDProofs.v
    │                                     ↑                                                        ↑
    │                                     │                                                        │
    │                                     │                                                        │
    │                                     │                                                        │
    │                                     │                                                        │
Rewriter.v ←────────────────────── ProofsCommon.v ←──────────────────── ProofsCommonTactics.v      │
    ↑                                 ↗        ↖                                ↑                  │
Reify.v ←──────────────┐           Wf.v   InterpProofs.v                        │                  │
                       │              ↖        ↗                                │                  │
Rules.v                └──────────── AllTactics.v ──────────────────────────────┘                  │
    ↑                                      ↑       ┌───────────────────────────────────────────────┘
RulesProofs.v                         AllTacticsExtra.v
    ↑                                      ↑
    ├────────┬─────────────┬───────────────┴────────┬─────────────────────────────┐
    │   Passes/NBE.v    Passes/Arith.v    Passes/ArithWithCasts.v    Passes/StripLiteralCasts.v
    │        ↑             ↑                        ↑                             ↑
    │        └─────────────┴────────────────────────┴─────────────────────────────┴─────────────┐
    │                                                                                           │
    └────────┬──────────────────────────┐                                                       │
      Passes/ToFancy.v      Passes/ToFancyWithCasts.v                                           │
             ↑                          ↑                                                       │
             └───────┬──────────────────┴───────────────────────────────────────────────────────┘
                     │
                   All.v
```

- `Rules.v`: Defines the list of types of the rewrite rules that
  will be reified.  Largely independent of the expression language.

- `RulesProofs.v`: Proves all of the Gallina versions of the
  rewrite rules correct.

- `Rewriter.v`: Defines the rewriter machinery.  In particular, all of
  the rewriter definitions that have non-rewrite-rule-specific proofs
  about them are found in this file.

- `RewrierReify.v`: Defines reification of rewrite rules, continuing on
  from `Rewriter.v`, and culminates in the tactic
  `RewriteRules.Tactic.Build_RewriterT` and the tactic notation
  `make_Rewriter` which define a package of type
  `RewriteRules.GoalType.RewriterT`.  The `Build_*` tactic returns a
  `constr`, while the `make_*` tactic notation refines that `constr`
  in the goal.  Both tactics take two arguments: first a boolean
  `include_interp` which specifies whether (`true`) or not (`false`)
  to prefix the list of rewrite rules with the reduction-to-literal
  rewrite rules; and second a list of `bool * Prop` which is the list
  of rewrite rule types to reify, each paired with a boolean saying
  whether or not to try rewriting again in the output of the
  replacement for that rule.

- `ProofsCommon.v`: Defines the notion of interp-goodness and wf-goodness
  for rewrite rules, defines tactics to prove these notions, and
  contains a semi-arbitrary collection of proofs and definitions that
  are mostly shared between the wf proofs and the interp proofs.
  Importantly, this file defines everything needed to state and prove
  that specific rewrite rules are correct.  Additionally defines a
  package `RewriteRules.GoalType.VerifiedRewriter` which describes the
  type of the overall specialized rewriter together with its `Wf` and
  `Interp` proofs. (This package should perhaps move to another file?)

- `ProofsCommonTactics.v`: Defines the actual tactics used to prove that
  specific rewrite rules are correct, and to inhabit the packages
  defined in `ProofsCommon.v`.

- `Wf.v`: Proves wf-preservation of the generic rewriter,
  taking in wf-goodness of rewrite rules as a hypothesis.

- `InterpProofs.v`: Proves interp-correctness of the generic
  rewriter, taking in interp-goodness of rewrite rules as a
  hypothesis.

- `AllTactics.v`: Defines the tactic
  `RewriteRules.Tactic.make_rewriter` (and a similar tactic notation)
  which build the entire `VerifiedRewriter`.  They take in the
  `include_interp` as in `Rewriter.v` tactics, as well as an hlist of
  proofs of rewrite rules indexed over a `list (bool * Prop)` of
  rewrite rule types.  This is the primary interface for defining a
  rewriter from a list of rewrite rules.

- `AllTacticsExtra.v`: Specializes `AllTactics.v` to
  what's defined in `Identifier.v`

- `{NBE, Arith, ArithWithCasts, StripLiteralCasts, ToFancy,
  ToFancyWithCasts}.v`: Use the tactic from `AllTactics.v`
  together with the proven list of rewrite rules from
  `RulesProofs.v` to reify and reduce the corresponding pass
  and generate a rewriter.

- `All.v`: `Definition`less file that `Export`s the rewriters
  defined in `Rewriter/*.v`


Proofs files:
For `Language.v`, there is a semi-arbitrary split between two files
`Language.Inversion` and `Language.Wf`.
- `Inversion.v`:
  + classifies equality of type codes and exprs
  + type codes have decidable equality
  + correctness of the various type-transport definitions
  + correctness lemmas for the various `expr.invert_*` definitions
  + correctness lemmas for the various `reify_*` definitions in `Language.v`
  + `inversion_type`, which inverts equality of type codes
  + `type_beq_to_eq`, which converts boolean equality of types to
    Leibniz equality
  + `rewrite_type_transport_correct`, which rewrites with the
    correctness lemmas of the various type-transport definitions
  + `type.invert_one e` which does case analysis on any inductive type
     indexed over type codes, in a way that preserves information
     about the type of `e`, and generally works even when the goal is
     dependently typed over `e` and/or its type
  + `ident.invert`, which does case-anaylsis on idents whose type has
    structure (i.e., is not a var)
  + `ident.invert_match`, which does case-analysis on idents appearing as
    the discriminee of a `match` in the goal or in any hypothesis
  + `expr.invert`, which does case-anaylsis on exprs whose type has
    structure (i.e., is not a var)
  + `expr.invert_match`, which does case-analysis on exprs appearing as
    the discriminee of a `match` in the goal or in any hypothesis
  + `expr.invert_subst`, which does case-analysis on exprs which show up
    in hypotheses of the form `expr.invert_* _ = Some _`
  + `expr.inversion_expr`, which inverts equalities of exprs

- `Wf.v`: Depends on `Inversion.v`
  Defines:
  + expr.wf, expr.Wf, expr.wf3, expr.Wf3
  + GeneralizeVar.Flat.wf
  + `expr.inversion_wf` (and variants), which invert `wf` hypotheses
  + `expr.wf_t` (and variants wf_unsafe_t and wf_safe_t) which make
     progress on `wf` goals; `wf_safe_t` should never turn a provable
     goal into an unprovable one, while `wf_unsafe_t` might.
  + `expr.interp_t` (and variants), which should make progress on
    equivalence-of-interp hypotheses and goals, but is not used much
    (mainly because I forgot I had defined it)
  + `prove_Wf`, which proves wf goals on concrete syntax trees in a more
    optimized way than `repeat constructor`
  Proves:
  + funext → (type.eqv ↔ Logic.eq) (`eqv_iff_eq_of_funext`)
  + type.related and type.eqv are PERs
  + Proper instances for `type.app_curried`, `type.and_for_each_lhs_of_arrow`
  + `type.is_not_higher_order` → Reflexive (type.and_for_each_lhs_of_arrow type.eqv)
  + iff between `type.related{,_hetero}` and related of `type.app_curried`
  + various properties of `type.and{,b_bool}for_each_lhs_of_arrow`
  + various properties of `type.eqv` and `ident.{gen_,}interp`
  + various properties of `ident.cast`
  + various properties of `expr.wf` (particularly of things defined in `Language.v`)
  + interp and wf proofs for the passes to/from Flat

- `UnderLetsProofs.v`: wf and interp lemmas for the various passes defined in `UnderLets.v`
- `MiscCompilerPassesProofs.v`: wf and interp lemmas for the various passes defined in `MiscCompilerPasses.v`
- `AbstractInterpretation/ZRangeProofs.v`: Proves correctness lemmas of the per-operation zrange-bounds-analysis functions
- `AbstractInterpretation/Wf.v`: wf lemmas for the AbstractInterpretation pass
- `AbstractInterpretation/Proofs.v`: interp lemmas for the
  AbstractInterpretation pass, and also correctness lemmas that
  combine Wf and interp
