(** * Declaration of Hint Databases with lemmas about ℤ from the standard library *)
Require Import Coq.micromega.Lia Coq.micromega.Lqa.
Require Import Coq.ZArith.ZArith.
(* Should we [Require Import Coq.ZArith.Zhints.]? *)

Global Hint Extern 1 => lia : lia.
Global Hint Extern 1 => lra : lra.
Global Hint Extern 1 => nia : nia.

Ltac zutil_arith := solve [ lia | auto with nocore ].
Ltac zutil_arith_more_inequalities := solve [ zutil_arith | auto with zarith ].

(** Only hints that are always safe to apply (i.e., reversible), and
    which can reasonably be said to "simplify" the goal, should go in
    this database. *)
Create HintDb zsimplify discriminated.
(** Only hints that are always safe to apply, and "simplify" the goal,
    and don't require any side conditions, should go in this
    database. *)
Create HintDb zsimplify_fast discriminated.
(** Hints which turn [Z] operations on concrete positives into the
    corresponding operation on [Pos]. *)
Create HintDb zsimplify_Z_to_pos discriminated.
(** Only hints with no side conditions that strip constants, and
    nothing else. *)
Create HintDb zsimplify_const discriminated.
(** We create separate databases for two directions of transformations
      involving [Z.log2]; combining them leads to loops. *)
(* for hints that take in hypotheses of type [log2 _], and spit out conclusions of type [_ ^ _] *)
Create HintDb hyp_log2 discriminated.
(* for hints that take in hypotheses of type [_ ^ _], and spit out conclusions of type [log2 _] *)
Create HintDb concl_log2 discriminated.

(** "push" means transform [-f x] to [f (-x)]; "pull" means go the other way *)
Create HintDb push_Zopp discriminated.
Create HintDb pull_Zopp discriminated.
Create HintDb push_Zpow discriminated.
Create HintDb pull_Zpow discriminated.
Create HintDb push_Zmul discriminated.
Create HintDb pull_Zmul discriminated.
Create HintDb push_Zdiv discriminated.
Create HintDb pull_Zdiv discriminated.
Create HintDb push_Zadd discriminated.
Create HintDb pull_Zadd discriminated.
Create HintDb push_Zsub discriminated.
Create HintDb pull_Zsub discriminated.
Create HintDb pull_Zmod discriminated.
Create HintDb push_Zmod discriminated.
Create HintDb pull_Zof_nat discriminated.
Create HintDb push_Zof_nat discriminated.
Create HintDb pull_Zshift discriminated.
Create HintDb push_Zshift discriminated.
Create HintDb pull_Zof_N discriminated.
Create HintDb push_Zof_N discriminated.
Create HintDb pull_Zto_N discriminated.
Create HintDb push_Zto_N discriminated.
Create HintDb Zshift_to_pow discriminated.
Create HintDb Zpow_to_shift discriminated.
Create HintDb pull_Zmax discriminated.
Create HintDb push_Zmax discriminated.
Global Hint Extern 1 => progress autorewrite with push_Zopp in * : push_Zopp.
Global Hint Extern 1 => progress autorewrite with pull_Zopp in * : pull_Zopp.
Global Hint Extern 1 => progress autorewrite with push_Zpow in * : push_Zpow.
Global Hint Extern 1 => progress autorewrite with pull_Zpow in * : pull_Zpow.
Global Hint Extern 1 => progress autorewrite with push_Zmul in * : push_Zmul.
Global Hint Extern 1 => progress autorewrite with pull_Zmul in * : pull_Zmul.
Global Hint Extern 1 => progress autorewrite with push_Zadd in * : push_Zadd.
Global Hint Extern 1 => progress autorewrite with pull_Zadd in * : pull_Zadd.
Global Hint Extern 1 => progress autorewrite with push_Zsub in * : push_Zsub.
Global Hint Extern 1 => progress autorewrite with pull_Zsub in * : pull_Zsub.
Global Hint Extern 1 => progress autorewrite with push_Zdiv in * : push_Zmul.
Global Hint Extern 1 => progress autorewrite with pull_Zdiv in * : pull_Zmul.
Global Hint Extern 1 => progress autorewrite with pull_Zmod in * : pull_Zmod.
Global Hint Extern 1 => progress autorewrite with push_Zmod in * : push_Zmod.
Global Hint Extern 1 => progress autorewrite with pull_Zof_nat in * : pull_Zof_nat.
Global Hint Extern 1 => progress autorewrite with push_Zof_nat in * : push_Zof_nat.
Global Hint Extern 1 => progress autorewrite with pull_Zshift in * : pull_Zshift.
Global Hint Extern 1 => progress autorewrite with push_Zshift in * : push_Zshift.
Global Hint Extern 1 => progress autorewrite with Zshift_to_pow in * : Zshift_to_pow.
Global Hint Extern 1 => progress autorewrite with Zpow_to_shift in * : Zpow_to_shift.
Global Hint Extern 1 => progress autorewrite with pull_Zof_N in * : pull_Zof_N.
Global Hint Extern 1 => progress autorewrite with push_Zof_N in * : push_Zof_N.
Global Hint Extern 1 => progress autorewrite with pull_Zto_N in * : pull_Zto_N.
Global Hint Extern 1 => progress autorewrite with push_Zto_N in * : push_Zto_N.
Global Hint Extern 1 => progress autorewrite with push_Zmax in * : push_Zmax.
Global Hint Extern 1 => progress autorewrite with pull_Zmax in * : pull_Zmax.

(** For the occasional lemma that can remove the use of [Z.div] *)
Create HintDb zstrip_div.

Create HintDb Ztestbit discriminated.
Create HintDb Ztestbit_full discriminated.
