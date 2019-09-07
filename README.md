Fiat-Crypto: Synthesizing Correct-by-Construction Code for Cryptographic Primitives
=====

Building
-----
[![Build Status](https://api.travis-ci.org/mit-plv/fiat-crypto.png?branch=master)](https://travis-ci.org/mit-plv/fiat-crypto)

This repository requires coq 8.8 or later. 8.7 may work, but we don't use it ourselves.

Git submodules are used for some dependencies. If you did not clone with `--recursive`, run

    git submodule update --init --recursive

To build (if your COQPATH variable is empty):

       make

To build:

       export COQPATH="$(pwd)/coqprime/src${COQPATH:+:}$COQPATH"
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

### Actual Synthesis Pipeline

The ordering of files (eliding `*Proofs.v` files) is:

```
                     Language.v ←──────────────────────────────────────────────────┬───────────────────────────────┐
                       ↑                                                           │                               │
                       │                                                           │                               │
                 UnderLets.v                                                 MiscCompilerPasses.v  PushButtonSynthesis/ReificationCache.v
                    ↑       ↖                                                      ↑                               ↑
AbstractInterpretation.v  "Rewriter"                                               │                               │
         ↑                  ↑ ┌────────────────────────────────────────────────────┘                               │
LanguageStringification.v   │ │               Arithmetic.v                                                         │
↑    ↑  ┌───────────────────┴─┘                   ↑                                                                │
│  BoundsPipeline.v                     COperationSpecifications.v                                                 │
│     ↑                                           ↑                                                                │
│     └─────────────────────────┬─────────────────┴────────────────────────────────────────────────────────────────┘
CStringification.v     PushButtonSynthesis.v ←── Toplevel2.v ←───────────┐
↑                               ↑                                        │
│ ┌─────────────────────────────┘                       SlowPrimeSynthesisExamples.v
CLI.v
↑  ↑
│  └────────────────────────────┐
StandaloneHaskellMain.v   StandaloneOCamlMain.v
        ↑                           ↑
ExtractionHaskell.v          ExtractionOCaml.v
```

The files contain:

- Arithmetic.v: All of the high-level field arithmetic stuff

- Language.v:
  + PHOAS
  + reification
  + denotation/intepretation
  + utilities for inverting PHOAS exprs
  + default/dummy values of PHOAS exprs
  + default instantiation of generic PHOAS types
  + gallina reification of ground terms
  + Flat/indexed syntax trees, and conversions to and from PHOAS
  Defines the passes:
  + ToFlat
  + FromFlat
  + GeneralizeVar

- UnderLets.v: the UnderLets monad, a pass that does substitution of var-like
  things, a pass that inserts let-binders in the next-to-last line of code,
  substituting away var-like things (this is used to ensure that when we output
  C code, aliasing the input and the output arrays doesn't cause issues).
  Defines the passes:
  + SubstVarFstSndPairOppCast

- AbstractInterpretation.v: type-code-based ZRange definitions, abstract
  interpretation of identifiers (which does let-lifting, for historical reasons,
  and the dependency on UnderLets should probably be removed), defines the
  passes:
  + PartialEvaluateWithBounds
  + PartialEvaluateWithListInfoFromBounds
  + CheckPartialEvaluateWithBounds

- "Rewriter": rewrite rules, rewriting.  See below for actual stucture
  of files.  Defines the passes:
  + RewriteNBE
  + RewriteArith
  + RewriteArithWithCasts
  + RewriteStripLiteralCasts
  + RewriteToFancy
  + RewriteToFancyWithCasts
  + PartialEvaluate (which is just a synonym for RewriteNBE)

- MiscCompilerPasses.v: Defines the passes:
  + EliminateDead (dead code elimination)
  + Subst01 (substitute let-binders used 0 or 1 times)

- LanguageStringification.v: defines a printer (Show instance) for the
  PHOAS language, defines some common language-independent utilities
  for conversion to output code, and defines the spec/API of
  conversion from PHOAS to code in a language as strings.  (Depends on
  AbstractInterpretation.v for ZRange utilities.)  Defines the passes:
  + ToString.LinesToString
  + ToString.ToFunctionLines

- CStringification.v: conversion to C code as strings.  Instantiates
  the API defined in LanguageStringification.

- CompilersTestCases.v: Various test cases to ensure everything is working

- BoundsPipeline.v: Assemble the various compiler passes together into
  a composed pipeline.  It is the final interface for the compiler.
  Also contains some tactics for applying the BoundsPipeline
  correctness lemma.

- COperationSpecifications.v: The specifications for the various
  operations to be synthesized.
  TODO: This file should probably be renamed.

- PushButtonSynthesis/ReificationCache.v: Defines the cache that holds
  reified versions of operations, as well as the tactics that reify
  and apply things from the cache.

- PushButtonSynthesis.v: Reifies the various operations from
  Arithmetic.v, definies the compositions of the BoundsPipeline with
  these operations, proves that their interpretations satisfies the
  specs from COperationSpecifications.v, assembles the reified
  post-bounds operations into synthesis targets.  This is the file
  that CLI.v depends on.

- Toplevel2.v: Some not-quite-finished-but-kind-of-slow pipeline stuff
  + all the stuff that uses compilers + arithmetic, together with more
  examples.  Also has semi-broken fancy-machine stuff.  This should
  probably be merged into Toplevel1.v when working on the pipeline.

- SlowPrimeSynthesisExamples.v: Additional uses of the pipeline for
  primes that are kind-of slow, which I don't want extraction blocking
  on.

- CLI.v: Setting up all of the language-independent parts of extraction; relies
  on having a list of strings-or-error-messages for each pipeline, and on the
  arguments to that pipeline, and builds a parser for command line arguments for
  that.

- StandaloneHaskellMain.v, StandaloneOCamlMain.v, ExtractionHaskell.v,
  ExtractionOCaml.v: Extraction of pipeline to various languages


The files defined for "Rewriter" are split up into the following
dependency graph:
```
IdentifiersLibrary.v ←───────────────────────── IdentifiersGenerate.v ←──────────────────── IdentifiersGENERATED.v
    ↑ ↑                                                   ↑                                        ↑
    │ └──────────────── IdentifiersLibraryProofs.v ←──────┴─ IdentifiersGenerateProofs.v ←─ IdentifersGENERATEDProofs.v
    │                                     ↑                                                        ↑
Rewriter.v ←───────────────────────── RewriterWf1.v ←─────────────────── RewriterWf1Tactics.v      │
    ↑                                 ↗        ↖                                ↑                  │
RewriterReify.v ←──────┐   RewriterWf2.v   RewriterInterpProofs1.v              │                  │
                       │              ↖        ↗                                │                  │
RewriterRules.v        └─────── RewriterAllTactics.v ───────────────────────────┘                  │
    ↑                                      ↑                                                       │
RewriterRulesProofs.v                      │                                                       │
    ↑                                      │                                                       │
    ├────────┬─────────────┬───────────────┴────────┬─────────────────────────────┬────────────────┘
    │ Rewriter/NBE.v    Rewriter/Arith.v    Rewriter/ArithWithCasts.v    Rewriter/StripLiteralCasts.v
    │        ↑             ↑                        ↑                             ↑
    │        └─────────────┴────────────────────────┴─────────────────────────────┴─────────────┐
    │                                                                                           │
    └────────┬──────────────────────────┐                                                       │
      Rewriter/ToFancy.v  Rewriter/ToFancyWithCasts.v                                           │
             ↑                          ↑                                                       │
             └───────┬──────────────────┴───────────────────────────────────────────────────────┘
                     │
                RewriterAll.v
```

- RewriterRules.v: Defines the list of types of the rewrite rules that
  will be reified.  Largely independent of the expression language.

- RewriterRulesProofs.v: Proves all of the Gallina versions of the
  rewrite rules correct.

- IdentifiersLibrary.v: Some definitions about identifiers and pattern
  identifiers and raw identifiers.  Some of these definitions take
  generated definitions as arguments. Also defines a package record to
  hold all of the generated definitions.

- IdentifiersGenerate.v: Tactics to generate definitions about untyped
  and pattern versions of identifiers for the rewriter.  Culminates in
  a tactic which inhabits the package type defined in
  IdentifiersLibrary.v

- IdentifiersLibraryProofs.v: proofs about definitions in
  IdentifiersLibrary.  Also defines a package to hold generated proofs
  that require destructing inductives not yet defined in this file.

- IdentifiersGenerateProofs.v: tactics to prove lemmas to inhabit the
  package defined in IdentifiersLibraryProofs.v

- IdentifiersGENERATE.v: identifiers / inductives and definitions
  generated by IdentifiersGenerate.

- IdentifiersGENERATEProofs.v: proofs generated by
  IdentifiersGenerateProofs, about definitions in IdentifiersGENERATE

- Rewriter.v: Defines the rewriter machinery.  In particular, all of
  the rewriter definitions that have non-rewrite-rule-specific proofs
  about them are found in this file.

- RewrierReify.v: Defines reification of rewrite rules, continuing on
  from Rewriter.v, and culminates in the tactic
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

- RewriterWf1.v: Defines the notion of interp-goodness and wf-goodness
  for rewrite rules, defines tactics to prove these notions, and
  contains a semi-arbitrary collection of proofs and definitions that
  are mostly shared between the wf proofs and the interp proofs.
  Importantly, this file defines everything needed to state and prove
  that specific rewrite rules are correct.  Additionally defines a
  package `RewriteRules.GoalType.VerifiedRewriter` which describes the
  type of the overall specialized rewriter together with its `Wf` and
  `Interp` proofs. (This package should perhaps move to another file?)

- RewriterWf1Tactics.v: Defines the actual tactics used to prove that
  specific rewrite rules are correct, and to inhabit the packages
  defined in RewriterWf1.v.

- RewriterWf2.v: Proves wf-preservation of the generic rewriter,
  taking in wf-goodness of rewrite rules as a hypothesis.

- RewriterInterpProofs1.v: Proves interp-correctness of the generic
  rewriter, taking in interp-goodness of rewrite rules as a
  hypothesis.

- RewriterAllTactics.v: Defines the tactic
  `RewriteRules.Tactic.make_rewriter` (and a similar tactic notation)
  which build the entire `VerifiedRewriter`.  They take in the
  `include_interp` as in Rewriter.v tactics, as well as an hlist of
  proofs of rewrite rules indexed over a `list (bool * Prop)` of
  rewrite rule types.  This is the primary interface for defining a
  rewriter from a list of rewrite rules.

- Rewriter/{NBE, Arith, ArithWithCasts, StripLiteralCasts, ToFancy,
  ToFancyWithCasts}.v: Use the tactic from RewriterAllTactics.v
  together with the proven list of rewrite rules from
  RewriterRulesProofs.v to reify and reduce the corresponding pass and
  generate a rewriter.

- RewriterAll.v: `Definition`less file that `Export`s the rewriters
  defined in `Rewriter/*.v`


Proofs files:
For Language.v, there is a semi-arbitrary split between two files
`LanguageInversion` and `LanguageWf`.
- LanguageInversion.v:
  + classifies equality of type codes and exprs
  + type codes have decidable equality
  + correctness of the various type-transport definitions
  + correctness lemmas for the various `expr.invert_*` definitions
  + correctness lemmas for the various `reify_*` definitions in Language.v
  + inversion_type, which inverts equality of type codes
  + type_beq_to_eq, which converts boolean equality of types to
    Leibniz equality
  + rewrite_type_transport_correct, which rewrites with the
    correctness lemmas of the various type-transport definitions
  + `type.invert_one e` which does case analysis on any inductive type
     indexed over type codes, in a way that preserves information
     about the type of `e`, and generally works even when the goal is
     dependently typed over `e` and/or its type
  + ident.invert, which does case-anaylsis on idents whose type has
    structure (i.e., is not a var)
  + ident.invert_match, which does case-analysis on idents appearing as
    the discriminee of a `match` in the goal or in any hypothesis
  + expr.invert, which does case-anaylsis on exprs whose type has
    structure (i.e., is not a var)
  + expr.invert_match, which does case-analysis on exprs appearing as
    the discriminee of a `match` in the goal or in any hypothesis
  + expr.invert_subst, which does case-analysis on exprs which show up
    in hypotheses of the form `expr.invert_* _ = Some _`
  + expr.inversion_expr, which inverts equalities of exprs

- LanguageWf.v: Depends on LanguageInversion.v
  Defines:
  + expr.wf, expr.Wf, expr.wf3, expr.Wf3
  + GeneralizeVar.Flat.wf
  + expr.inversion_wf (and variants), which invert `wf` hypotheses
  + expr.wf_t (and variants wf_unsafe_t and wf_safe_t) which make
     progress on `wf` goals; `wf_safe_t` should never turn a provable
     goal into an unprovable one, while `wf_unsafe_t` might.
  + expr.interp_t (and variants), which should make progress on
    equivalence-of-interp hypotheses and goals, but is not used much
    (mainly because I forgot I had defined it)
  + prove_Wf, which proves wf goals on concrete syntax trees in a more
    optimized way than `repeat constructor`
  Proves:
  + funext → (type.eqv ↔ Logic.eq) (`eqv_iff_eq_of_funext`)
  + type.related and type.eqv are PERs
  + Proper instances for type.app_curried, type.and_for_each_lhs_of_arrow
  + type.is_not_higher_order → Reflexive (type.and_for_each_lhs_of_arrow type.eqv)
  + iff between type.related{,_hetero} and related of type.app_curried
  + various properties of type.and{,b_bool}for_each_lhs_of_arrow
  + various properties of type.eqv and ident.{gen_,}interp
  + various properties of ident.cast
  + various properties of expr.wf (particularly of things defined in Language.v)
  + interp and wf proofs for the passes to/from Flat

- UnderLetsProofs.v: wf and interp lemmas for the various passes defined in UnderLets.v
- MiscCompilerPassesProofs.v: wf and interp lemmas for the various passes defined in MiscCompilerPasses.v
- AbstractInterpretationZRangeProofs.v: Proves correctness lemmas of the per-operation zrange-bounds-analysis functions
- AbstractInterpretationWf.v: wf lemmas for the AbstractInterpretation pass
- AbstractInterpretationProofs.v: interp lemmas for the
  AbstractInterpretation pass, and also correctness lemmas that
  combine Wf and interp

There are also proofs about elliptic curves, for example:

- [`src/Curves/Edwards/AffineProofs.v`](./src/Curves/Edwards/AffineProofs.v),
- [`src/Curves/Edwards/XYZT/Basic.v`](./src/Curves/Edwards/XYZT/Basic.v),
- [`src/Curves/Montgomery/AffineProofs.v`](./src/Curves/Montgomery/AffineProofs.v),
- [`src/Curves/Montgomery/XZProofs.v`](src/Curves/Montgomery/XZProofs.v).
