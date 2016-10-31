Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.Specific.GF25519.
Require Import Bedrock.Word Crypto.Util.WordUtil.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Algebra.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Local Open Scope Z.

(* BEGIN aliases for word extraction *)
Definition word64 := Word.word 64.
Coercion word64ToZ (x : word64) : Z
  := Z.of_N (wordToN x).
Coercion ZToWord64 (x : Z) : word64 := NToWord _ (Z.to_N x).
Definition w64eqb (x y : word64) := weqb x y.

Lemma word64eqb_Zeqb x y : (word64ToZ x =? word64ToZ y)%Z = w64eqb x y.
Proof. apply wordeqb_Zeqb. Qed.

Arguments word64 : simpl never.
Global Opaque word64.

(* END aliases for word extraction *)

Local Arguments Z.pow_pos !_ !_ / .
Lemma ZToWord64ToZ x : 0 <= x < 2^64 -> word64ToZ (ZToWord64 x) = x.
Proof.
  intros; unfold word64ToZ, ZToWord64.
  rewrite ?wordToN_NToWord_idempotent, ?N2Z.id, ?Z2N.id
    by (omega || apply N2Z.inj_lt; rewrite ?N2Z.id, ?Z2N.id by omega; simpl in *; omega).
  reflexivity.
Qed.

(* BEGIN precomputation. *)
Local Notation b_of exp := (0, 2^exp + 2^(exp-3))%Z (only parsing). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)
Module Type WordIsBounded.
  Parameter is_boundedT : forall (lower upper : Z), word64 -> bool.
  Parameter Build_is_boundedT : forall {lower upper} {proj_word : word64},
      andb (lower <=? proj_word)%Z (proj_word <=? upper)%Z = true -> is_boundedT lower upper proj_word = true.
  Parameter project_is_boundedT : forall {lower upper} {proj_word : word64},
      is_boundedT lower upper proj_word = true -> andb (lower <=? proj_word)%Z (proj_word <=? upper)%Z = true.
End WordIsBounded.

Module Import WordIsBoundedDefault : WordIsBounded.
  Definition is_boundedT : forall (lower upper : Z), word64 -> bool
    := fun lower upper proj_word => andb (lower <=? proj_word)%Z (proj_word <=? upper)%Z.
  Definition Build_is_boundedT {lower upper} {proj_word : word64}
    : andb (lower <=? proj_word)%Z (proj_word <=? upper)%Z = true -> is_boundedT lower upper proj_word = true
    := fun x => x.
  Definition project_is_boundedT {lower upper} {proj_word : word64}
    : is_boundedT lower upper proj_word = true -> andb (lower <=? proj_word)%Z (proj_word <=? upper)%Z = true
    := fun x => x.
End WordIsBoundedDefault.

Definition bounded_word (lower upper : Z) := { proj_word : word64 | is_boundedT lower upper proj_word = true }.
Definition proj_word {lower upper} (v : bounded_word lower upper) := Eval cbv [proj1_sig] in proj1_sig v.
Definition word_bounded {lower upper} (v : bounded_word lower upper)
  : andb (lower <=? proj_word v)%Z (proj_word v <=? upper)%Z = true
  := project_is_boundedT (proj2_sig v).
Definition Build_bounded_word' {lower upper} proj_word word_bounded : bounded_word lower upper
  := exist _ proj_word (Build_is_boundedT word_bounded).
Arguments proj_word {_ _} _.
Arguments word_bounded {_ _} _.
Arguments Build_bounded_word' {_ _} _ _.
Definition Build_bounded_word {lower upper} (proj_word : word64) (word_bounded : andb (lower <=? proj_word)%Z (proj_word <=? upper)%Z = true)
  : bounded_word lower upper
  := Build_bounded_word'
       proj_word
       (match andb (lower <=? proj_word)%Z (proj_word <=? upper)%Z as b return b = true -> b = true with
        | true => fun _ => eq_refl
        | false => fun x => x
        end word_bounded).
Local Notation word_of exp := (bounded_word (fst (b_of exp)) (snd (b_of exp))).
Local Notation unbounded_word sz := (bounded_word 0 (2^sz-1)%Z).
Lemma word_to_unbounded_helper {x e : nat} : (x < pow2 e)%nat -> (Z.of_nat e <= 64)%Z -> ((0 <=? word64ToZ (ZToWord64 (Z.of_nat x))) && (word64ToZ (ZToWord64 (Z.of_nat x)) <=? 2 ^ (Z.of_nat e) - 1))%bool = true.
Proof.
  rewrite pow2_id; intro H; apply Nat2Z.inj_lt in H; revert H.
  rewrite Z.pow_Zpow; simpl Z.of_nat.
  intros H H'.
  assert (2^Z.of_nat e <= 2^64) by auto with zarith.
  rewrite ?ZToWord64ToZ by omega.
  match goal with
  | [ |- context[andb ?x ?y] ]
    => destruct x eqn:?, y eqn:?; try reflexivity; Z.ltb_to_lt
  end;
    intros; omega.
Qed.
Definition word_to_unbounded_word {sz} (x : word sz) : (Z.of_nat sz <=? 64)%Z = true -> unbounded_word (Z.of_nat sz).
Proof.
  refine (fun pf => Build_bounded_word (Z.of_N (wordToN x)) _).
  abstract (rewrite wordToN_nat, nat_N_Z; Z.ltb_to_lt; apply (word_to_unbounded_helper (wordToNat_bound x)); simpl; omega).
Defined.
Definition word32_to_unbounded_word (x : word 32) : unbounded_word 32.
Proof. apply (word_to_unbounded_word x); reflexivity. Defined.
Definition word31_to_unbounded_word (x : word 31) : unbounded_word 31.
Proof. apply (word_to_unbounded_word x); reflexivity. Defined.
Definition bounds : list (Z * Z)
  := Eval compute in
      [b_of 25; b_of 26; b_of 25; b_of 26; b_of 25; b_of 26; b_of 25; b_of 26; b_of 25; b_of 26].
Definition wire_digit_bounds : list (Z * Z)
  := Eval compute in
      List.repeat (0, 2^32-1)%Z 7 ++ ((0,2^31-1)%Z :: nil).

Local Opaque word64.
Definition fe25519W := Eval cbv (*-[word64]*) in (tuple word64 (length limb_widths)).
Definition wire_digitsW := Eval cbv (*-[word64]*) in (tuple word64 8).
Definition fe25519WToZ (x : fe25519W) : Specific.GF25519.fe25519
  := let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) := x in
     (x0 : Z, x1 : Z, x2 : Z, x3 : Z, x4 : Z, x5 : Z, x6 : Z, x7 : Z, x8 : Z, x9 : Z).
Definition fe25519ZToW (x : Specific.GF25519.fe25519) : fe25519W
  := let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) := x in
     (x0 : word64, x1 : word64, x2 : word64, x3 : word64, x4 : word64, x5 : word64, x6 : word64, x7 : word64, x8 : word64, x9 : word64).
Definition wire_digitsWToZ (x : wire_digitsW) : Specific.GF25519.wire_digits
  := let '(x0, x1, x2, x3, x4, x5, x6, x7) := x in
     (x0 : Z, x1 : Z, x2 : Z, x3 : Z, x4 : Z, x5 : Z, x6 : Z, x7 : Z).
Definition wire_digitsZToW (x : Specific.GF25519.wire_digits) : wire_digitsW
  := let '(x0, x1, x2, x3, x4, x5, x6, x7) := x in
     (x0 : word64, x1 : word64, x2 : word64, x3 : word64, x4 : word64, x5 : word64, x6 : word64, x7 : word64).

Definition app_7 {T} (f : wire_digitsW) (P : wire_digitsW -> T) : T.
Proof.
  cbv [wire_digitsW] in *.
  set (f0 := f).
  repeat (let g := fresh "g" in destruct f as [f g]).
  apply P.
  apply f0.
Defined.

Definition app_7_correct {T} f (P : wire_digitsW -> T) : app_7 f P = P f.
Proof.
  intros.
  cbv [wire_digitsW] in *.
  destruct_head' prod.
  reflexivity.
Qed.

Definition app_10 {T} (f : fe25519W) (P : fe25519W -> T) : T.
Proof.
  cbv [fe25519W] in *.
  set (f0 := f).
  repeat (let g := fresh "g" in destruct f as [f g]).
  apply P.
  apply f0.
Defined.

Definition app_10_correct {T} f (P : fe25519W -> T) : app_10 f P = P f.
Proof.
  intros.
  cbv [fe25519W] in *.
  destruct_head' prod.
  reflexivity.
Qed.

Definition appify2 {T} (op : fe25519W -> fe25519W -> T) (f g : fe25519W) :=
  app_10 f (fun f0 => (app_10 g (fun g0 => op f0 g0))).

Lemma appify2_correct : forall {T} op f g, @appify2 T op f g = op f g.
Proof.
  intros. cbv [appify2].
  etransitivity; apply app_10_correct.
Qed.

Definition uncurry_unop_fe25519W {T} (op : fe25519W -> T)
  := Eval cbv (*-[word64]*) in Tuple.uncurry (n:=length_fe25519) op.
Definition curry_unop_fe25519W {T} op : fe25519W -> T
  := Eval cbv (*-[word64]*) in fun f => app_10 f (Tuple.curry (n:=length_fe25519) op).
Definition uncurry_binop_fe25519W {T} (op : fe25519W -> fe25519W -> T)
  := Eval cbv (*-[word64]*) in uncurry_unop_fe25519W (fun f => uncurry_unop_fe25519W (op f)).
Definition curry_binop_fe25519W {T} op : fe25519W -> fe25519W -> T
  := Eval cbv (*-[word64]*) in appify2 (fun f => curry_unop_fe25519W (curry_unop_fe25519W op f)).

Definition uncurry_unop_wire_digitsW {T} (op : wire_digitsW -> T)
  := Eval cbv (*-[word64]*) in Tuple.uncurry (n:=length wire_widths) op.
Definition curry_unop_wire_digitsW {T} op : wire_digitsW -> T
  := Eval cbv (*-[word64]*) in fun f => app_7 f (Tuple.curry (n:=length wire_widths) op).


Definition fe25519 :=
  Eval cbv [fst snd] in
    let sanity := eq_refl : length bounds = length limb_widths in
    (word_of 25 * word_of 26 * word_of 25 * word_of 26 * word_of 25 * word_of 26 * word_of 25 * word_of 26 * word_of 25 * word_of 26)%type.
Definition wire_digits :=
  Eval cbv [fst snd Tuple.tuple Tuple.tuple'] in
    (unbounded_word 32 * unbounded_word 32 * unbounded_word 32 * unbounded_word 32
     * unbounded_word 32 * unbounded_word 32 * unbounded_word 32 * unbounded_word 31)%type.
Definition proj1_fe25519W (x : fe25519) : fe25519W
  := let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) := x in
     (proj_word x0, proj_word x1, proj_word x2, proj_word x3, proj_word x4,
      proj_word x5, proj_word x6, proj_word x7, proj_word x8, proj_word x9).
Coercion proj1_fe25519 (x : fe25519) : Specific.GF25519.fe25519
  := fe25519WToZ (proj1_fe25519W x).
Definition is_bounded (x : Specific.GF25519.fe25519) : bool
  := let res := Tuple.map2
                  (fun bounds v =>
                     let '(lower, upper) := bounds in
                     (lower <=? v) && (v <=? upper))%bool%Z
                  (Tuple.from_list _ (List.rev bounds) eq_refl) x in
     List.fold_right andb true (Tuple.to_list _ res).

Lemma is_bounded_proj1_fe25519 (x : fe25519) : is_bounded (proj1_fe25519 x) = true.
Proof.
  refine (let '(exist x0 p0, exist x1 p1, exist x2 p2, exist x3 p3, exist x4 p4,
                exist x5 p5, exist x6 p6, exist x7 p7, exist x8 p8, exist x9 p9)
            as x := x return is_bounded (proj1_fe25519 x) = true in
          _).
  cbv [is_bounded proj1_fe25519 proj1_fe25519W fe25519WToZ to_list length bounds from_list from_list' map2 on_tuple2 to_list' ListUtil.map2 List.map List.rev List.app proj_word].
  apply fold_right_andb_true_iff_fold_right_and_True.
  cbv [fold_right List.map].
  cbv beta in *.
  repeat split; auto using project_is_boundedT.
Qed.

Definition proj1_wire_digitsW (x : wire_digits) : wire_digitsW
  := let '(x0, x1, x2, x3, x4, x5, x6, x7) := x in
     (proj_word x0, proj_word x1, proj_word x2, proj_word x3, proj_word x4,
      proj_word x5, proj_word x6, proj_word x7).
Coercion proj1_wire_digits (x : wire_digits) : Specific.GF25519.wire_digits
  := wire_digitsWToZ (proj1_wire_digitsW x).
Definition wire_digits_is_bounded (x : Specific.GF25519.wire_digits) : bool
  := let res := Tuple.map2
                  (fun bounds v =>
                     let '(lower, upper) := bounds in
                     (lower <=? v) && (v <=? upper))%bool%Z
                  (Tuple.from_list _ (List.rev wire_digit_bounds) eq_refl) x in
     List.fold_right andb true (Tuple.to_list _ res).

Lemma is_bounded_proj1_wire_digits (x : wire_digits) : wire_digits_is_bounded (proj1_wire_digits x) = true.
Proof.
  refine (let '(exist x0 p0, exist x1 p1, exist x2 p2, exist x3 p3, exist x4 p4,
                exist x5 p5, exist x6 p6, exist x7 p7)
            as x := x return wire_digits_is_bounded (proj1_wire_digits x) = true in
          _).
  cbv [wire_digits_is_bounded proj1_wire_digits proj1_wire_digitsW wire_digitsWToZ to_list length wire_digit_bounds from_list from_list' map2 on_tuple2 to_list' ListUtil.map2 List.map List.rev List.app proj_word].
  apply fold_right_andb_true_iff_fold_right_and_True.
  cbv [fold_right List.map].
  cbv beta in *.
  repeat split; auto using project_is_boundedT.
Qed.

(** TODO: Turn this into a lemma to speed up proofs *)
Ltac unfold_is_bounded_in H :=
  unfold is_bounded, wire_digits_is_bounded, fe25519WToZ, wire_digitsWToZ in H;
  cbv [to_list length bounds wire_digit_bounds from_list from_list' map2 on_tuple2 to_list' ListUtil.map2 List.map fold_right List.rev List.app] in H;
  rewrite !Bool.andb_true_iff in H.

Definition Pow2_64 := Eval compute in 2^64.
Definition unfold_Pow2_64 : 2^64 = Pow2_64 := eq_refl.

Definition exist_fe25519W (x : fe25519W) : is_bounded (fe25519WToZ x) = true -> fe25519.
Proof.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) as x := x return is_bounded (fe25519WToZ x) = true -> fe25519 in
          fun H => (fun H' => (Build_bounded_word x0 _, Build_bounded_word x1 _, Build_bounded_word x2 _, Build_bounded_word x3 _, Build_bounded_word x4 _,
                               Build_bounded_word x5 _, Build_bounded_word x6 _, Build_bounded_word x7 _, Build_bounded_word x8 _, Build_bounded_word x9 _))
                     (let H' := proj1 (@fold_right_andb_true_iff_fold_right_and_True _) H in
                      _));
    [
    | | | | | | | | |
    | clearbody H'; clear H x;
      unfold_is_bounded_in H';
      exact H' ];
    destruct_head' and; simpl in *; auto;
      rewrite_hyp !*; reflexivity.
Defined.

Definition exist_fe25519' (x : Specific.GF25519.fe25519) : is_bounded x = true -> fe25519.
Proof.
  intro H; apply (exist_fe25519W (fe25519ZToW x)).
  abstract (
      hnf in x; destruct_head' prod;
      pose proof H as H';
      unfold_is_bounded_in H;
      destruct_head' and; simpl in *;
      Z.ltb_to_lt;
      rewrite ?ZToWord64ToZ by (simpl; omega);
      assumption
    ).
Defined.

Definition exist_fe25519 (x : Specific.GF25519.fe25519) : is_bounded x = true -> fe25519.
Proof.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) as x := x return is_bounded x = true -> fe25519 in
          fun H => _).
  let v := constr:(exist_fe25519' (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) H) in
  let rec do_refine v :=
      first [ let v' := (eval cbv [exist_fe25519W fe25519ZToW exist_fe25519' proj_word Build_bounded_word Build_bounded_word' snd fst] in (proj_word v)) in
              refine (Build_bounded_word v' _); abstract exact (word_bounded v)
            | let v' := (eval cbv [exist_fe25519W fe25519ZToW exist_fe25519' proj_word Build_bounded_word Build_bounded_word' snd fst] in (proj_word (snd v))) in
              refine (_, Build_bounded_word v' _);
              [ do_refine (fst v) | abstract exact (word_bounded (snd v)) ] ] in
  do_refine v.
Defined.

Lemma proj1_fe25519_exist_fe25519W x pf : proj1_fe25519 (exist_fe25519W x pf) = fe25519WToZ x.
Proof.
  revert pf.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) as x := x return forall pf : is_bounded (fe25519WToZ x) = true, proj1_fe25519 (exist_fe25519W x pf) = fe25519WToZ x in
          fun pf => _).
  reflexivity.
Qed.
Lemma proj1_fe25519W_exist_fe25519 x pf : proj1_fe25519W (exist_fe25519 x pf) = fe25519ZToW x.
Proof.
  revert pf.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) as x := x return forall pf : is_bounded x = true, proj1_fe25519W (exist_fe25519 x pf) = fe25519ZToW x in
          fun pf => _).
  reflexivity.
Qed.
Lemma proj1_fe25519_exist_fe25519 x pf : proj1_fe25519 (exist_fe25519 x pf) = x.
Proof.
  revert pf.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) as x := x return forall pf : is_bounded x = true, proj1_fe25519 (exist_fe25519 x pf) = x in
          fun pf => _).
  cbv [proj1_fe25519 exist_fe25519 proj1_fe25519W fe25519WToZ proj_word Build_bounded_word Build_bounded_word'].
  unfold_is_bounded_in pf.
  destruct_head' and.
  Z.ltb_to_lt.
  rewrite ?ZToWord64ToZ by (rewrite unfold_Pow2_64; cbv [Pow2_64]; omega).
  reflexivity.
Qed.

Definition exist_wire_digitsW (x : wire_digitsW) : wire_digits_is_bounded (wire_digitsWToZ x) = true -> wire_digits.
Proof.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7) as x := x return wire_digits_is_bounded (wire_digitsWToZ x) = true -> wire_digits in
          fun H => (fun H' => (Build_bounded_word x0 _, Build_bounded_word x1 _, Build_bounded_word x2 _, Build_bounded_word x3 _, Build_bounded_word x4 _,
                               Build_bounded_word x5 _, Build_bounded_word x6 _, Build_bounded_word x7 _))
                     (let H' := proj1 (@fold_right_andb_true_iff_fold_right_and_True _) H in
                      _));
    [
    | | | | | | |
    | clearbody H'; clear H x;
      unfold_is_bounded_in H';
      exact H' ];
    destruct_head' and; simpl in *; auto;
      rewrite_hyp !*; reflexivity.
Defined.

Definition exist_wire_digits' (x : Specific.GF25519.wire_digits) : wire_digits_is_bounded x = true -> wire_digits.
Proof.
  intro H; apply (exist_wire_digitsW (wire_digitsZToW x)).
  abstract (
      hnf in x; destruct_head' prod;
      pose proof H as H';
      unfold_is_bounded_in H;
      destruct_head' and; simpl in *;
      Z.ltb_to_lt;
      rewrite ?ZToWord64ToZ by (simpl; omega);
      assumption
    ).
Defined.

Definition exist_wire_digits (x : Specific.GF25519.wire_digits) : wire_digits_is_bounded x = true -> wire_digits.
Proof.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7) as x := x return wire_digits_is_bounded x = true -> wire_digits in
          fun H => _).
  let v := constr:(exist_wire_digits' (x0, x1, x2, x3, x4, x5, x6, x7) H) in
  let rec do_refine v :=
      first [ let v' := (eval cbv [exist_wire_digitsW wire_digitsZToW exist_wire_digits' proj_word Build_bounded_word Build_bounded_word' snd fst] in (proj_word v)) in
              refine (Build_bounded_word v' _); abstract exact (word_bounded v)
            | let v' := (eval cbv [exist_wire_digitsW wire_digitsZToW exist_wire_digits' proj_word Build_bounded_word Build_bounded_word' snd fst] in (proj_word (snd v))) in
              refine (_, Build_bounded_word v' _);
              [ do_refine (fst v) | abstract exact (word_bounded (snd v)) ] ] in
  do_refine v.
Defined.

Lemma proj1_wire_digits_exist_wire_digitsW x pf : proj1_wire_digits (exist_wire_digitsW x pf) = wire_digitsWToZ x.
Proof.
  revert pf.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7) as x := x return forall pf : wire_digits_is_bounded (wire_digitsWToZ x) = true, proj1_wire_digits (exist_wire_digitsW x pf) = wire_digitsWToZ x in
          fun pf => _).
  reflexivity.
Qed.
Lemma proj1_wire_digitsW_exist_wire_digits x pf : proj1_wire_digitsW (exist_wire_digits x pf) = wire_digitsZToW x.
Proof.
  revert pf.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7) as x := x return forall pf : wire_digits_is_bounded x = true, proj1_wire_digitsW (exist_wire_digits x pf) = wire_digitsZToW x in
          fun pf => _).
  reflexivity.
Qed.
Lemma proj1_wire_digits_exist_wire_digits x pf : proj1_wire_digits (exist_wire_digits x pf) = x.
Proof.
  revert pf.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7) as x := x return forall pf : wire_digits_is_bounded x = true, proj1_wire_digits (exist_wire_digits x pf) = x in
          fun pf => _).
  cbv [proj1_wire_digits exist_wire_digits proj1_wire_digitsW wire_digitsWToZ proj_word Build_bounded_word Build_bounded_word'].
  unfold_is_bounded_in pf.
  destruct_head' and.
  Z.ltb_to_lt.
  rewrite ?ZToWord64ToZ by (rewrite unfold_Pow2_64; cbv [Pow2_64]; omega).
  reflexivity.
Qed.

(* END precomputation *)

(* Precompute constants *)

Definition one := Eval vm_compute in exist_fe25519 Specific.GF25519.one_ eq_refl.

Definition zero := Eval vm_compute in exist_fe25519 Specific.GF25519.zero_ eq_refl.

Lemma fold_chain_opt_gen {A B} (F : A -> B) is_bounded ls id' op' id op chain
      (Hid_bounded : is_bounded (F id') = true)
      (Hid : id = F id')
      (Hop_bounded : forall x y, is_bounded (F x) = true
                                 -> is_bounded (F y) = true
                                 -> is_bounded (op (F x) (F y)) = true)
      (Hop : forall x y, is_bounded (F x) = true
                         -> is_bounded (F y) = true
                         -> op (F x) (F y) = F (op' x y))
      (Hls_bounded : forall n, is_bounded (F (nth_default id' ls n)) = true)
  : F (fold_chain_opt id' op' chain ls)
    = fold_chain_opt id op chain (List.map F ls)
    /\ is_bounded (F (fold_chain_opt id' op' chain ls)) = true.
Proof.
  rewrite !fold_chain_opt_correct.
  revert dependent ls; induction chain as [|x xs IHxs]; intros.
  { pose proof (Hls_bounded 0%nat).
    destruct ls; simpl; split; trivial; congruence. }
  { destruct x; simpl; unfold Let_In; simpl.
    rewrite (fun ls pf => proj1 (IHxs ls pf)) at 1; simpl.
    { do 2 f_equal.
      rewrite <- Hop, Hid by auto.
      rewrite !map_nth_default_always.
      split; try reflexivity.
      apply (IHxs (_::_)).
      intros [|?]; autorewrite with simpl_nth_default; auto.
      rewrite <- Hop; auto. }
    { intros [|?]; simpl;
        autorewrite with simpl_nth_default; auto.
      rewrite <- Hop; auto. } }
Qed.

Lemma encode_bounded x : is_bounded (encode x) = true.
Proof.
  pose proof (bounded_encode x).
  generalize dependent (encode x).
  intro t; compute in t; intros.
  destruct_head' prod.
  unfold Pow2Base.bounded in H.
  pose proof (H 0%nat); pose proof (H 1%nat); pose proof (H 2%nat);
    pose proof (H 3%nat); pose proof (H 4%nat); pose proof (H 5%nat);
      pose proof (H 6%nat); pose proof (H 7%nat); pose proof (H 8%nat);
        pose proof (H 9%nat); clear H.
  simpl in *.
  cbv [Z.pow_pos Z.mul Pos.mul Pos.iter nth_default nth_error value] in *.
  unfold is_bounded.
  apply fold_right_andb_true_iff_fold_right_and_True.
  cbv [is_bounded proj1_fe25519 to_list length bounds from_list from_list' map2 on_tuple2 to_list' ListUtil.map2 List.map List.rev List.app proj_word fold_right].
  repeat split; rewrite !Bool.andb_true_iff, !Z.leb_le; omega.
Qed.

Definition encode (x : F modulus) : fe25519
  := exist_fe25519 (encode x) (encode_bounded x).

Definition decode (x : fe25519) : F modulus
  := ModularBaseSystem.decode (proj1_fe25519 x).

Lemma proj1_fe25519_encode x
  : proj1_fe25519 (encode x) = ModularBaseSystem.encode x.
Proof.
  cbv [encode].
  generalize (encode_bounded x); generalize (ModularBaseSystem.encode x).
  intros y pf; intros; hnf in y; destruct_head_hnf' prod.
  cbv [proj1_fe25519 exist_fe25519 proj1_fe25519W Build_bounded_word Build_bounded_word' fe25519WToZ proj_word].
  unfold_is_bounded_in pf.
  destruct_head' and.
  Z.ltb_to_lt.
  rewrite ?ZToWord64ToZ by (rewrite unfold_Pow2_64; cbv [Pow2_64]; omega).
  reflexivity.
Qed.

Lemma decode_exist_fe25519 x pf
  : decode (exist_fe25519 x pf) = ModularBaseSystem.decode x.
Proof.
  hnf in x; destruct_head' prod.
  cbv [decode proj1_fe25519 exist_fe25519 proj1_fe25519W Build_bounded_word Build_bounded_word' fe25519WToZ proj_word].
  unfold_is_bounded_in pf.
  destruct_head' and.
  Z.ltb_to_lt.
  rewrite ?ZToWord64ToZ by (rewrite unfold_Pow2_64; cbv [Pow2_64]; omega).
  reflexivity.
Qed.

Definition div (f g : fe25519) : fe25519
  := exist_fe25519 (div (proj1_fe25519 f) (proj1_fe25519 g)) (encode_bounded _).

Definition eq (f g : fe25519) : Prop := eq (proj1_fe25519 f) (proj1_fe25519 g).


Notation ibinop_correct_and_bounded irop op
  := (forall x y,
         is_bounded (fe25519WToZ x) = true
         -> is_bounded (fe25519WToZ y) = true
         -> fe25519WToZ (irop x y) = op (fe25519WToZ x) (fe25519WToZ y)
            /\ is_bounded (fe25519WToZ (irop x y)) = true) (only parsing).
Notation iunop_correct_and_bounded irop op
  := (forall x,
         is_bounded (fe25519WToZ x) = true
         -> fe25519WToZ (irop x) = op (fe25519WToZ x)
            /\ is_bounded (fe25519WToZ (irop x)) = true) (only parsing).
Notation iunop_FEToZ_correct irop op
  := (forall x,
         is_bounded (fe25519WToZ x) = true
         -> word64ToZ (irop x) = op (fe25519WToZ x)) (only parsing).
Notation iunop_FEToWire_correct_and_bounded irop op
  := (forall x,
         is_bounded (fe25519WToZ x) = true
         -> wire_digitsWToZ (irop x) = op (fe25519WToZ x)
            /\ wire_digits_is_bounded (wire_digitsWToZ (irop x)) = true) (only parsing).
Notation iunop_WireToFE_correct_and_bounded irop op
  := (forall x,
         wire_digits_is_bounded (wire_digitsWToZ x) = true
         -> fe25519WToZ (irop x) = op (wire_digitsWToZ x)
            /\ is_bounded (fe25519WToZ (irop x)) = true) (only parsing).
