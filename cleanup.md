# Fiat-Crypto Cleanup

The primary objectives here are to reduce the substantial amount of code-bloat
that fiat-crypto has accrued, and to use the lessons we've learned so far to
rewrite some parts of the library in ways that will cause us less future pain.
These changes will both make our own lives easier and make the library more
approachable to others.

## Overview

- Field Arithmetic Implementation (Base System): Rewrite using a new, less awkward representation (in progress).
- Elliptic Curves : Use dependently-typed division and enhance super-`nsatz` 
- Spec : Remove the stuff that does not belong in spec.
- Algebra/Prime Field libraries : Possibly introduce more bundling.
- Experiments/Ed25519 : Move the "spaghetti code" to the various parts of the library where it belongs.
- Util : Keep pretty much as-is, even if many lemmas are not used after rewrites.
- Compilery Bits : Reorganize and spend some time thinking about design.
- PointEncoding : Significant refactor, make interfaces line up and remove duplicated or redundant code.
- Specific/SpecificGen : Make a more general and nicely-presented catalog of examples for people to look at and be impressed by.

## Field Arithmetic Implementation

Originally, we represented field-element bignums using two lists, one
representing the constant weights (e.g. `[1, 2^26, 2^51,...] or [26, 25,
26,...]) and one with the variable runtime values. The new representation
couples the weights and the runtime values, (e.g `[(1, x0), (2^51, x1), (2^51,
x2), (2^26, x1)]`). 

This approach has several advantages, but the most important of these is that
the basic arithmetic operations have gotten much simpler. Here is the old
version of `mul`:

```
  (* mul' is multiplication with the SECOND ARGUMENT REVERSED and OUTPUT REVERSED *)
  Fixpoint mul_bi' (i:nat) (vsr:digits) :=
    match vsr with
    | v::vsr' => v * crosscoef i (length vsr') :: mul_bi' i vsr'
    | nil => nil
    end.
  Definition mul_bi (i:nat) (vs:digits) : digits :=
    zeros i ++ rev (mul_bi' i (rev vs)).

  (* mul' is multiplication with the FIRST ARGUMENT REVERSED *)
  Fixpoint mul' (usr vs:digits) : digits :=
    match usr with
      | u::usr' =>
        mul_each u (mul_bi (length usr') vs) .+ mul' usr' vs
      | _ => nil
    end.
  Definition mul us := mul' (rev us). 
```

This version doesn't even include a few hundred lines of proof needed to prove
that `mul` is correct or 150 lines of extra work in ModularBaseSystemOpt.v to
mark runtime operations. Here is the new `mul` and its proof:

```
  Definition mul (p q:list limb) : list limb :=
    List.flat_map (fun t => List.map (fun t' => (fst t * fst t', (snd t * snd t')%RT)) q) p.

  Lemma eval_map_mul a x q : eval (List.map (fun t => (a * fst t, x * snd t)) q) = a * x * eval q.
  Proof. induction q; simpl List.map; autorewrite with push_eval cancel_pair; nsatz. Qed.

  Lemma eval_mul p q : eval (mul p q) = eval p * eval q.
  Proof. induction p; simpl mul; autorewrite with push_eval cancel_pair; try nsatz. Qed.
```

The "RT" notation marks runtime operations, so there's no need for an extra step.

Besides shaving some orders of magnitude off of implementation effort, size,
and compile time, we also no longer need to carry around preconditions that
discuss the correspondence between the weights list and the runtime list (for
instance, that they have the same length). 

## Elliptic Curves

1. Division should be modified to use a dependent type for the denominator,
   which carries a proof that the denominator is nonzero. This removes some
ugliness (for instance, with proving homomorphisms, where it is necessary to
show that both divisions do similar things for all possible inputs. Division by
zero is undefined, so if zero is a possible input, this is challenging.) Also,
simply making it impossible to divide by zero more accurately matches how we
think of division.
2. Improve super-`nsatz` as described in Andres and Jason's Coq enhancements
   proposal.
 
## Spec

There's a bunch of clutter scattered across the files that either doesn't
belong in spec or could be expressed better. If someone went through all the
files and thought carefully about them, it would be time well spent.

Additionally, the things in Encoding.v and ModularWordEncoding.v will likely go
away during the PointEncoding cleanup. 

## Algebra/Prime Field Libraries

Mostly leave as-is, these are great examples of parts of fiat-crypto that are
currently nice, probably because they are fairly well-defined sections that
were designed all at once with the big picture in mind, instead of being
incrementally assembled and revised. We might want to consider bundling some of
the algebraic structures.

## Experiments/Ed25519.v

This file was assembled as we scrambled to meet the PLDI deadline and contains
mostly "glue" that makes different interfaces across fiat-crypto actually line
up with each other. We should have someone go through it and relocate that sort
of code to where it actually belongs, and/or make the necessary changes to
interfaces.

## Util

We should keep the Util files (especially the big ones like ZUtil and ListUtil)
mostly as-is, although once the old BaseSystem goes away most of the lemmas
won't be used by fiat-crypto. If compile time becomes a problem, we might want
to factor out the unused lemmas and store them separately, but we should not
get rid of anything that could be a candidate for Coq's standard library. 

## Compilery Bits

We should reorganize the compilery files (meaning bounds-checking, PHOAS, etc.)
to be more comprehensible to people who are not Jason. We should also remove
unnecessary code (are we ever going to use the code under the Assembly
directory?) and do another "think hard about whether these pieces are designed
well" session. 

## PointEncoding

These files are a mix of very very old code and code that was thrown in to make
things work right before the PLDI deadline. It just needs to have redundant
code removed and proof structures improved.


## Specific/SpecificGen

As we are transitioning from this being a research prototype to it being a Real
Thing People Might Look At, we might want to consider making a more presentable
and cohesive catalog of examples than we currently have.
