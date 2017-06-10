(** * Declaration of Hint Databases with lemmas about ℤ from the standard library *)
Require Import Coq.micromega.Psatz Coq.omega.Omega.
Require Import Coq.ZArith.ZArith.
(* Should we [Require Import Coq.ZArith.Zhints.]? *)

Hint Extern 1 => lia : lia.
Hint Extern 1 => lra : lra.
Hint Extern 1 => nia : nia.
Hint Extern 1 => omega : omega.

Ltac zutil_arith := solve [ omega | lia | auto with nocore ].
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
Hint Extern 1 => progress autorewrite with push_Zopp in * : push_Zopp.
Hint Extern 1 => progress autorewrite with pull_Zopp in * : pull_Zopp.
Hint Extern 1 => progress autorewrite with push_Zpow in * : push_Zpow.
Hint Extern 1 => progress autorewrite with pull_Zpow in * : pull_Zpow.
Hint Extern 1 => progress autorewrite with push_Zmul in * : push_Zmul.
Hint Extern 1 => progress autorewrite with pull_Zmul in * : pull_Zmul.
Hint Extern 1 => progress autorewrite with push_Zadd in * : push_Zadd.
Hint Extern 1 => progress autorewrite with pull_Zadd in * : pull_Zadd.
Hint Extern 1 => progress autorewrite with push_Zsub in * : push_Zsub.
Hint Extern 1 => progress autorewrite with pull_Zsub in * : pull_Zsub.
Hint Extern 1 => progress autorewrite with push_Zdiv in * : push_Zmul.
Hint Extern 1 => progress autorewrite with pull_Zdiv in * : pull_Zmul.
Hint Extern 1 => progress autorewrite with pull_Zmod in * : pull_Zmod.
Hint Extern 1 => progress autorewrite with push_Zmod in * : push_Zmod.
Hint Extern 1 => progress autorewrite with pull_Zof_nat in * : pull_Zof_nat.
Hint Extern 1 => progress autorewrite with push_Zof_nat in * : push_Zof_nat.
Hint Extern 1 => progress autorewrite with pull_Zshift in * : pull_Zshift.
Hint Extern 1 => progress autorewrite with push_Zshift in * : push_Zshift.
Hint Extern 1 => progress autorewrite with Zshift_to_pow in * : Zshift_to_pow.
Hint Extern 1 => progress autorewrite with Zpow_to_shift in * : Zpow_to_shift.
Hint Extern 1 => progress autorewrite with pull_Zof_N in * : pull_Zof_N.
Hint Extern 1 => progress autorewrite with push_Zof_N in * : push_Zof_N.
Hint Extern 1 => progress autorewrite with pull_Zto_N in * : pull_Zto_N.
Hint Extern 1 => progress autorewrite with push_Zto_N in * : push_Zto_N.
Hint Extern 1 => progress autorewrite with push_Zmax in * : push_Zmax.
Hint Extern 1 => progress autorewrite with pull_Zmax in * : pull_Zmax.

(** For the occasional lemma that can remove the use of [Z.div] *)
Create HintDb zstrip_div.

Create HintDb Ztestbit discriminated.
Create HintDb Ztestbit_full discriminated.

(** Work around bug #5019, that [zify] loops on dependent types.  We
    copy/paste [zify_nat_op] from the standard library and add a case
    to each of the [match isnat with ... end]. *)
Ltac zify_nat_op ::=
 match goal with
  (* misc type conversions: positive/N/Z to nat *)
  | H : context [ Z.of_nat (Pos.to_nat ?a) ] |- _ => rewrite (positive_nat_Z a) in H
  | |- context [ Z.of_nat (Pos.to_nat ?a) ] => rewrite (positive_nat_Z a)
  | H : context [ Z.of_nat (N.to_nat ?a) ] |- _ => rewrite (N_nat_Z a) in H
  | |- context [ Z.of_nat (N.to_nat ?a) ] => rewrite (N_nat_Z a)
  | H : context [ Z.of_nat (Z.abs_nat ?a) ] |- _ => rewrite (Zabs2Nat.id_abs a) in H
  | |- context [ Z.of_nat (Z.abs_nat ?a) ] => rewrite (Zabs2Nat.id_abs a)

  (* plus -> Z.add *)
  | H : context [ Z.of_nat (plus ?a ?b) ] |- _ => rewrite (Nat2Z.inj_add a b) in H
  | |- context [ Z.of_nat (plus ?a ?b) ] => rewrite (Nat2Z.inj_add a b)

  (* min -> Z.min *)
  | H : context [ Z.of_nat (min ?a ?b) ] |- _ => rewrite (Nat2Z.inj_min a b) in H
  | |- context [ Z.of_nat (min ?a ?b) ] => rewrite (Nat2Z.inj_min a b)

  (* max -> Z.max *)
  | H : context [ Z.of_nat (max ?a ?b) ] |- _ => rewrite (Nat2Z.inj_max a b) in H
  | |- context [ Z.of_nat (max ?a ?b) ] => rewrite (Nat2Z.inj_max a b)

  (* minus -> Z.max (Z.sub ... ...) 0 *)
  | H : context [ Z.of_nat (minus ?a ?b) ] |- _ => rewrite (Nat2Z.inj_sub_max a b) in H
  | |- context [ Z.of_nat (minus ?a ?b) ] => rewrite (Nat2Z.inj_sub_max a b)

  (* pred -> minus ... -1 -> Z.max (Z.sub ... -1) 0 *)
  | H : context [ Z.of_nat (pred ?a) ] |- _ => rewrite (pred_of_minus a) in H
  | |- context [ Z.of_nat (pred ?a) ] => rewrite (pred_of_minus a)

  (* mult -> Z.mul and a positivity hypothesis *)
  | H : context [ Z.of_nat (mult ?a ?b) ] |- _ =>
        pose proof (Nat2Z.is_nonneg (mult a b));
        rewrite (Nat2Z.inj_mul a b) in *
  | |- context [ Z.of_nat (mult ?a ?b) ] =>
        pose proof (Nat2Z.is_nonneg (mult a b));
        rewrite (Nat2Z.inj_mul a b) in *

  (* O -> Z0 *)
  | H : context [ Z.of_nat O ] |- _ => simpl (Z.of_nat O) in H
  | |- context [ Z.of_nat O ] => simpl (Z.of_nat O)

  (* S -> number or Z.succ *)
  | H : context [ Z.of_nat (S ?a) ] |- _ =>
     let isnat := isnatcst a in
     match isnat with
      | true => simpl (Z.of_nat (S a)) in H
      | _ => rewrite (Nat2Z.inj_succ a) in H
      | _ => change (Z.of_nat (S a)) with (Z_of_nat' (S a)) in H
     end
  | |- context [ Z.of_nat (S ?a) ] =>
     let isnat := isnatcst a in
     match isnat with
      | true => simpl (Z.of_nat (S a))
      | _ => rewrite (Nat2Z.inj_succ a)
      | _ => change (Z.of_nat (S a)) with (Z_of_nat' (S a))
     end

  (* atoms of type nat : we add a positivity condition (if not already there) *)
  | _ : (0 <= Z.of_nat ?a)%Z |- _ => hide_Z_of_nat a
  | _ : context [ Z.of_nat ?a ] |- _ =>
    pose proof (Nat2Z.is_nonneg a); hide_Z_of_nat a
  | |- context [ Z.of_nat ?a ] =>
    pose proof (Nat2Z.is_nonneg a); hide_Z_of_nat a
 end.
