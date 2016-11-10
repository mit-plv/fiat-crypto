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
Require Import Crypto.Util.HList.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Algebra.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Local Open Scope Z.

(* BEGIN common curve-specific definitions *)
Definition bit_width : nat := 64%nat.
Local Notation b_of exp := (0, 2^exp + 2^(exp-3))%Z (only parsing). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)
Definition bounds_exp : tuple Z length_fe25519
  := Eval compute in
      Tuple.from_list length_fe25519 limb_widths eq_refl.
Definition bounds : tuple (Z * Z) length_fe25519
  := Eval compute in
      Tuple.map (fun e => b_of e) bounds_exp.
Definition wire_digit_bounds_exp : tuple Z (length wire_widths)
  := Eval compute in Tuple.from_list _ wire_widths eq_refl.
Definition wire_digit_bounds : tuple (Z * Z) (length wire_widths)
  := Eval compute in Tuple.map (fun e => (0,2^e-1)%Z) wire_digit_bounds_exp.
(* END common curve-specific definitions *)

(* BEGIN aliases for word extraction *)
Definition word64 := Word.word bit_width.
Coercion word64ToZ (x : word64) : Z := Z.of_N (wordToN x).
Coercion ZToWord64 (x : Z) : word64 := NToWord _ (Z.to_N x).
Definition NToWord64 : N -> word64 := NToWord _.
Definition word64ize (x : word64) : word64
  := Eval cbv [wordToN N.succ_double N.double] in NToWord64 (wordToN x).
Definition w64eqb (x y : word64) := weqb x y.

Global Arguments NToWord64 : simpl never.
Arguments word64 : simpl never.
Arguments bit_width : simpl never.
Global Opaque word64.
Global Opaque bit_width.

(* END aliases for word extraction *)

(* BEGIN basic types *)
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

Definition bounded_word (lower upper : Z)
  := { proj_word : word64 | is_boundedT lower upper proj_word = true }.
Local Notation word_of exp := (bounded_word (fst (b_of exp)) (snd (b_of exp))).
Local Notation unbounded_word sz := (bounded_word 0 (2^sz-1)%Z).

Local Opaque word64.
Definition fe25519W := Eval cbv (*-[word64]*) in (tuple word64 length_fe25519).
Definition wire_digitsW := Eval cbv (*-[word64]*) in (tuple word64 (length wire_widths)).
Definition fe25519 :=
  Eval cbv -[bounded_word Z.pow Z.sub Z.add] in
    hlist (fun e => word_of e) bounds_exp.
Definition wire_digits :=
  Eval cbv -[bounded_word Z.pow Z.sub Z.add] in
    hlist (fun e => unbounded_word e) wire_digit_bounds_exp.

Definition is_bounded_gen {n} (x : tuple Z n) (bounds : tuple (Z * Z) n) : bool
  := let res := Tuple.map2
                  (fun bounds v =>
                     let '(lower, upper) := bounds in
                     (lower <=? v) && (v <=? upper))%bool%Z
                  bounds x in
     List.fold_right andb true (Tuple.to_list _ res).

Definition is_bounded (x : Specific.GF25519.fe25519) : bool
  := is_bounded_gen (n:=length_fe25519) x bounds.

Definition wire_digits_is_bounded (x : Specific.GF25519.wire_digits) : bool
  := is_bounded_gen (n:=length wire_widths) x wire_digit_bounds.

(* END basic types *)

Section generic_destructuring.
  Fixpoint app_on' A n : forall T (f : tuple' A n) (P : forall x : tuple' A n, T x), T f
    := match n return forall T (f : tuple' A n) (P : forall x : tuple' A n, T x), T f with
       | O => fun T v P => P v
       | S n' => fun T v P => let '(v, x) := v in app_on' A n' _ v (fun v => P (v, x))
       end.
  Definition app_on {A n} : forall {T} (f : tuple A n) (P : forall x : tuple A n, T x), T f
    := match n return forall T (f : tuple A n) (P : forall x : tuple A n, T x), T f with
       | O => fun T v P => P v
       | S n' => @app_on' A n'
       end.
  Lemma app_on'_correct {A n T} f (P : forall x : tuple' A n, T x) : app_on' A n T f P = P f.
  Proof.
    induction n; simpl in *; destruct_head' prod; [ reflexivity | exact (IHn _ _ (fun t => P (t, _))) ].
  Qed.
  Lemma app_on_correct {A n T} f (P : forall x : tuple A n, T x) : app_on f P = P f.
  Proof. destruct n; [ reflexivity | apply app_on'_correct ]. Qed.

  Fixpoint app_on_h' A F n : forall ts T (f : @hlist' A n F ts) (P : forall x : @hlist' A n F ts, T x), T f
    := match n return forall ts T (f : @hlist' A n F ts) (P : forall x : @hlist' A n F ts, T x), T f with
       | O => fun ts T v P => P v
       | S n' => fun ts T v P => let '(v, x) := v in app_on_h' A F n' _ _ v (fun v => P (v, x))
       end.
  Definition app_on_h {A F n} : forall ts T (f : @hlist A n F ts) (P : forall x : @hlist A n F ts, T x), T f
    := match n return forall ts T (f : @hlist A n F ts) (P : forall x : @hlist A n F ts, T x), T f with
       | O => fun ts T v P => P v
       | S n' => @app_on_h' A F n'
       end.
  Lemma app_on_h'_correct {A F n ts T} f P : @app_on_h' A F n ts T f P = P f.
  Proof.
    induction n; simpl in *; destruct_head' prod; [ reflexivity | exact (IHn _ _ _ (fun h => P (h, f))) ].
  Qed.
  Lemma app_on_h_correct {A} F {n} ts {T} f P : @app_on_h A F n ts T f P = P f.
  Proof. destruct n; [ reflexivity | apply app_on_h'_correct ]. Qed.

  Definition app_wire_digitsW_dep {A T} (P : forall x : tuple A (length wire_widths), T x)
    : forall (f : tuple A (length wire_widths)), T f
    := Eval compute in fun f => @app_on A (length wire_widths) T f P.
  Definition app_wire_digitsW {A T} (f : tuple A (length wire_widths)) (P : tuple A (length wire_widths) -> T)
    := Eval compute in @app_wire_digitsW_dep A (fun _ => T) P f.
  Definition app_fe25519W_dep {A T} (P : forall x : tuple A length_fe25519, T x)
    : forall (f : tuple A length_fe25519), T f
    := Eval compute in fun f => @app_on A length_fe25519 T f P.
  Definition app_fe25519W {A T} (f : tuple A length_fe25519) (P : tuple A length_fe25519 -> T)
    := Eval compute in @app_fe25519W_dep A (fun _ => T) P f.
  Definition app_fe25519_dep {T} (P : forall x : fe25519, T x)
    : forall f : fe25519, T f
    := Eval compute in fun f => @app_on_h _ (fun e => word_of e) length_fe25519 bounds_exp T f P.
  Definition app_fe25519 {T} (f : fe25519) (P : hlist (fun e => word_of e) bounds_exp -> T)
    := Eval compute in @app_fe25519_dep (fun _ => T) P f.
  Definition app_wire_digits_dep {T} (P : forall x : wire_digits, T x)
    : forall f : wire_digits, T f
    := Eval compute in fun f => @app_on_h _ (fun e => unbounded_word e) (length wire_widths) wire_digit_bounds_exp T f P.
  Definition app_wire_digits {T} (f : wire_digits) (P : hlist (fun e => unbounded_word e) wire_digit_bounds_exp -> T)
    := Eval compute in @app_wire_digits_dep (fun _ => T) P f.

  Definition app_wire_digitsW_dep_correct {A T} f P : @app_wire_digitsW_dep A T P f = P f
    := app_on_correct f P.
  Definition app_wire_digitsW_correct {A T} f P : @app_wire_digitsW A T f P = P f
    := @app_wire_digitsW_dep_correct A (fun _ => T) f P.
  Definition app_fe25519W_dep_correct {A T} f P : @app_fe25519W_dep A T P f = P f
    := app_on_correct f P.
  Definition app_fe25519W_correct {A T} f P : @app_fe25519W A T f P = P f
    := @app_fe25519W_dep_correct A (fun _ => T) f P.
  Definition app_fe25519_dep_correct {T} f P : @app_fe25519_dep T P f = P f
    := app_on_h_correct (fun e => word_of e) bounds_exp f P.
  Definition app_fe25519_correct {T} f P : @app_fe25519 T f P = P f
    := @app_fe25519_dep_correct (fun _ => T) f P.
  Definition app_wire_digits_dep_correct {T} f P : @app_wire_digits_dep T P f = P f
    := app_on_h_correct (fun e => unbounded_word e) wire_digit_bounds_exp f P.
  Definition app_wire_digits_correct {T} f P : @app_wire_digits T f P = P f
    := @app_wire_digits_dep_correct (fun _ => T) f P.

  Definition appify2 {T} (op : fe25519W -> fe25519W -> T) (f g : fe25519W) :=
    app_fe25519W f (fun f0 => (app_fe25519W g (fun g0 => op f0 g0))).

  Lemma appify2_correct : forall {T} op f g, @appify2 T op f g = op f g.
  Proof.
    intros. cbv [appify2].
    etransitivity; apply app_fe25519W_correct.
  Qed.
End generic_destructuring.

Definition eta_fe25519W_sig (x : fe25519W) : { v : fe25519W | v = x }.
Proof.
  eexists; symmetry.
  repeat (etransitivity; [ apply surjective_pairing | apply f_equal2 ]); reflexivity.
Defined.
Definition eta_fe25519W (x : fe25519W) : fe25519W
  := Eval cbv [proj1_sig eta_fe25519W_sig] in proj1_sig (eta_fe25519W_sig x).
Definition eta_wire_digitsW_sig (x : wire_digitsW) : { v : wire_digitsW | v = x }.
Proof.
  eexists; symmetry.
  repeat (etransitivity; [ apply surjective_pairing | apply f_equal2 ]); reflexivity.
Defined.
Definition eta_wire_digitsW (x : wire_digitsW) : wire_digitsW
  := Eval cbv [proj1_sig eta_wire_digitsW_sig] in proj1_sig (eta_wire_digitsW_sig x).

Local Transparent word64.
Lemma word64ize_id x : word64ize x = x.
Proof. apply NToWord_wordToN. Qed.
Local Opaque word64.

Lemma word64eqb_Zeqb x y : (word64ToZ x =? word64ToZ y)%Z = w64eqb x y.
Proof. apply wordeqb_Zeqb. Qed.

Local Arguments Z.pow_pos !_ !_ / .
Lemma word64ToZ_ZToWord64 x : 0 <= x < 2^Z.of_nat bit_width -> word64ToZ (ZToWord64 x) = x.
Proof.
  intros; unfold word64ToZ, ZToWord64.
  rewrite wordToN_NToWord_idempotent, Z2N.id
    by (omega || apply N2Z.inj_lt; rewrite <- ?(N_nat_Z (Npow2 _)), ?Npow2_nat, ?Zpow_pow2, ?N2Z.id, ?Z2N.id, ?Z2Nat.id by omega; omega).
  reflexivity.
Qed.
Lemma ZToWord64_word64ToZ x : ZToWord64 (word64ToZ x) = x.
Proof.
  intros; unfold word64ToZ, ZToWord64.
  rewrite N2Z.id, NToWord_wordToN; reflexivity.
Qed.

(* BEGIN precomputation. *)

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
Lemma word_to_unbounded_helper {x e : nat} : (x < pow2 e)%nat -> (Z.of_nat e <= Z.of_nat bit_width)%Z -> ((0 <=? word64ToZ (ZToWord64 (Z.of_nat x))) && (word64ToZ (ZToWord64 (Z.of_nat x)) <=? 2 ^ (Z.of_nat e) - 1))%bool = true.
Proof.
  rewrite pow2_id; intro H; apply Nat2Z.inj_lt in H; revert H.
  rewrite Z.pow_Zpow; simpl Z.of_nat.
  intros H H'.
  assert (2^Z.of_nat e <= 2^Z.of_nat bit_width) by auto with zarith.
  rewrite ?word64ToZ_ZToWord64 by omega.
  match goal with
  | [ |- context[andb ?x ?y] ]
    => destruct x eqn:?, y eqn:?; try reflexivity; Z.ltb_to_lt
  end;
    intros; omega.
Qed.
Definition word_to_unbounded_word {sz} (x : word sz) : (Z.of_nat sz <=? Z.of_nat bit_width)%Z = true -> unbounded_word (Z.of_nat sz).
Proof.
  refine (fun pf => Build_bounded_word (Z.of_N (wordToN x)) _).
  abstract (rewrite wordToN_nat, nat_N_Z; Z.ltb_to_lt; apply (word_to_unbounded_helper (wordToNat_bound x)); simpl; omega).
Defined.
Definition word32_to_unbounded_word (x : word 32) : unbounded_word 32.
Proof. apply (word_to_unbounded_word x); reflexivity. Defined.
Definition word31_to_unbounded_word (x : word 31) : unbounded_word 31.
Proof. apply (word_to_unbounded_word x); reflexivity. Defined.

Local Opaque word64.
Declare Reduction app_tuple_map := cbv [app_wire_digitsW app_fe25519W app_fe25519 HList.mapt HList.mapt' Tuple.map on_tuple List.map List.app length_fe25519 List.length wire_widths Tuple.from_list Tuple.from_list' Tuple.to_list Tuple.to_list' fst snd].
Definition fe25519WToZ (x : fe25519W) : Specific.GF25519.fe25519
  := Eval app_tuple_map in
      app_fe25519W x (Tuple.map (fun v : word64 => v : Z)).
Definition fe25519ZToW (x : Specific.GF25519.fe25519) : fe25519W
  := Eval app_tuple_map in
      app_fe25519W x (Tuple.map (fun v : Z => v : word64)).
Definition wire_digitsWToZ (x : wire_digitsW) : Specific.GF25519.wire_digits
  := Eval app_tuple_map in
      app_wire_digitsW x (Tuple.map (fun v : word64 => v : Z)).
Definition wire_digitsZToW (x : Specific.GF25519.wire_digits) : wire_digitsW
  := Eval app_tuple_map in
      app_wire_digitsW x (Tuple.map (fun v : Z => v : word64)).
Definition fe25519W_word64ize (x : fe25519W) : fe25519W
  := Eval app_tuple_map in
      app_fe25519W x (Tuple.map word64ize).
Definition wire_digitsW_word64ize (x : wire_digitsW) : wire_digitsW
  := Eval app_tuple_map in
      app_wire_digitsW x (Tuple.map word64ize).

(** TODO: Turn this into a lemma to speed up proofs *)
Ltac unfold_is_bounded_in H :=
  unfold is_bounded, wire_digits_is_bounded, is_bounded_gen, fe25519WToZ, wire_digitsWToZ in H;
  cbv [to_list length bounds wire_digit_bounds from_list from_list' map2 on_tuple2 to_list' ListUtil.map2 List.map fold_right List.rev List.app length_fe25519 List.length wire_widths] in H;
  rewrite ?Bool.andb_true_iff in H.

Ltac unfold_is_bounded :=
  unfold is_bounded, wire_digits_is_bounded, is_bounded_gen, fe25519WToZ, wire_digitsWToZ;
  cbv [to_list length bounds wire_digit_bounds from_list from_list' map2 on_tuple2 to_list' ListUtil.map2 List.map fold_right List.rev List.app length_fe25519 List.length wire_widths];
  rewrite ?Bool.andb_true_iff.

Local Transparent bit_width.
Definition Pow2_64 := Eval compute in 2^Z.of_nat bit_width.
Definition unfold_Pow2_64 : 2^Z.of_nat bit_width = Pow2_64 := eq_refl.
Local Opaque bit_width.

Local Ltac prove_lt_bit_width :=
  rewrite unfold_Pow2_64; cbv [Pow2_64]; omega.

Lemma fe25519ZToW_WToZ (x : fe25519W) : fe25519ZToW (fe25519WToZ x) = x.
Proof.
  hnf in x; destruct_head' prod; cbv [fe25519WToZ fe25519ZToW].
  rewrite !ZToWord64_word64ToZ; reflexivity.
Qed.

Lemma fe25519WToZ_ZToW x : is_bounded x = true -> fe25519WToZ (fe25519ZToW x) = x.
Proof.
  hnf in x; destruct_head' prod; cbv [fe25519WToZ fe25519ZToW].
  intro H.
  unfold_is_bounded_in H; destruct_head' and.
  Z.ltb_to_lt.
  rewrite !word64ToZ_ZToWord64 by prove_lt_bit_width.
  reflexivity.
Qed.

Lemma fe25519W_word64ize_id x : fe25519W_word64ize x = x.
Proof.
  hnf in x; destruct_head' prod.
  cbv [fe25519W_word64ize];
    repeat apply f_equal2; apply word64ize_id.
Qed.
Lemma wire_digitsW_word64ize_id x : wire_digitsW_word64ize x = x.
Proof.
  hnf in x; destruct_head' prod.
  cbv [wire_digitsW_word64ize];
    repeat apply f_equal2; apply word64ize_id.
Qed.

Definition uncurry_unop_fe25519W {T} (op : fe25519W -> T)
  := Eval cbv (*-[word64]*) in Tuple.uncurry (n:=length_fe25519) op.
Definition curry_unop_fe25519W {T} op : fe25519W -> T
  := Eval cbv (*-[word64]*) in fun f => app_fe25519W f (Tuple.curry (n:=length_fe25519) op).
Definition uncurry_binop_fe25519W {T} (op : fe25519W -> fe25519W -> T)
  := Eval cbv (*-[word64]*) in uncurry_unop_fe25519W (fun f => uncurry_unop_fe25519W (op f)).
Definition curry_binop_fe25519W {T} op : fe25519W -> fe25519W -> T
  := Eval cbv (*-[word64]*) in appify2 (fun f => curry_unop_fe25519W (curry_unop_fe25519W op f)).

Definition uncurry_unop_wire_digitsW {T} (op : wire_digitsW -> T)
  := Eval cbv (*-[word64]*) in Tuple.uncurry (n:=length wire_widths) op.
Definition curry_unop_wire_digitsW {T} op : wire_digitsW -> T
  := Eval cbv (*-[word64]*) in fun f => app_wire_digitsW f (Tuple.curry (n:=length wire_widths) op).


Definition proj1_fe25519W (x : fe25519) : fe25519W
  := Eval app_tuple_map in
      app_fe25519 x (HList.mapt (fun _ => (@proj_word _ _))).
Coercion proj1_fe25519 (x : fe25519) : Specific.GF25519.fe25519
  := fe25519WToZ (proj1_fe25519W x).

Lemma is_bounded_proj1_fe25519 (x : fe25519) : is_bounded (proj1_fe25519 x) = true.
Proof.
  revert x; refine (app_fe25519_dep _); intro x.
  hnf in x; destruct_head' prod; destruct_head' bounded_word.
  cbv [is_bounded proj1_fe25519 proj1_fe25519W fe25519WToZ to_list length bounds from_list from_list' map2 on_tuple2 to_list' ListUtil.map2 List.map List.rev List.app proj_word length_fe25519 is_bounded_gen].
  apply fold_right_andb_true_iff_fold_right_and_True.
  cbv [fold_right List.map].
  cbv beta in *.
  repeat split; auto using project_is_boundedT.
Qed.

Definition proj1_wire_digitsW (x : wire_digits) : wire_digitsW
  := app_wire_digits x (HList.mapt (fun _ => proj_word)).
Coercion proj1_wire_digits (x : wire_digits) : Specific.GF25519.wire_digits
  := wire_digitsWToZ (proj1_wire_digitsW x).

Lemma is_bounded_proj1_wire_digits (x : wire_digits) : wire_digits_is_bounded (proj1_wire_digits x) = true.
Proof.
  revert x; refine (app_wire_digits_dep _); intro x.
  hnf in x; destruct_head' prod; destruct_head' bounded_word.
  cbv [wire_digits_is_bounded proj1_wire_digits proj1_wire_digitsW wire_digitsWToZ to_list length wire_digit_bounds from_list from_list' map2 on_tuple2 to_list' ListUtil.map2 List.map List.rev List.app proj_word is_bounded_gen wire_widths HList.mapt HList.mapt' app_wire_digits fst snd].
  apply fold_right_andb_true_iff_fold_right_and_True.
  cbv [fold_right List.map].
  cbv beta in *.
  repeat split; auto using project_is_boundedT.
Qed.

Local Ltac make_exist_W' x app_W_dep :=
  let H := fresh in
  revert x; refine (@app_W_dep _ _ _); intros x H;
  let x' := fresh in
  set (x' := x);
  cbv [tuple tuple' length_fe25519 List.length wire_widths] in x;
  destruct_head' prod;
  let rec do_refine v H :=
      first [ let v' := (eval cbv [snd fst] in (snd v)) in
              refine (_, Build_bounded_word v' _);
              [ do_refine (fst v) (proj2 H) | subst x'; abstract exact (proj1 H) ]
            | let v' := (eval cbv [snd fst] in v) in
              refine (Build_bounded_word v' _); subst x'; abstract exact (proj1 H) ] in
  let H' := constr:(proj1 (@fold_right_andb_true_iff_fold_right_and_True _) H) in
  let T := type of H' in
  let T := (eval cbv [id
                        List.fold_right List.map List.length List.app ListUtil.map2 List.rev
                        Tuple.to_list Tuple.to_list' Tuple.from_list Tuple.from_list' Tuple.map2 Tuple.on_tuple2
                        fe25519 bounds fe25519WToZ length_fe25519
                        wire_digits wire_digit_bounds wire_digitsWToZ wire_widths] in T) in
  let H' := constr:(H' : T) in
  let v := (eval unfold x' in x') in
  do_refine v H'.
Local Ltac make_exist'' x exist_W ZToW :=
  let H := fresh in
  intro H; apply (exist_W (ZToW x));
  abstract (
      hnf in x; destruct_head' prod;
      let H' := fresh in
      pose proof H as H';
      unfold_is_bounded_in H;
      destruct_head' and; simpl in *;
      Z.ltb_to_lt;
      rewrite ?word64ToZ_ZToWord64 by prove_lt_bit_width;
      assumption
    ).
Local Ltac make_exist' x app_W_dep exist'' exist_W ZToW :=
  let H := fresh in
  revert x; refine (@app_W_dep _ _ _); intros x H;
  let x' := fresh in
  set (x' := x) in *;
  cbv [tuple tuple' length_fe25519 List.length wire_widths] in x;
  destruct_head' prod;
  let rec do_refine v :=
      first [ let v' := (eval cbv [exist_W ZToW exist'' proj_word Build_bounded_word Build_bounded_word' snd fst] in (proj_word v)) in
              refine (Build_bounded_word v' _); subst x'; abstract exact (word_bounded v)
            | let v' := (eval cbv [exist_W ZToW exist'' proj_word Build_bounded_word Build_bounded_word' snd fst] in (proj_word (snd v))) in
              refine (_, Build_bounded_word v' _);
              [ do_refine (fst v) | subst x'; abstract exact (word_bounded (snd v)) ] ] in
  let v := (eval unfold x' in (exist'' x' H)) in
  do_refine v.

Definition exist_fe25519W' (x : fe25519W) : is_bounded (fe25519WToZ x) = true -> fe25519.
Proof. make_exist_W' x (@app_fe25519W_dep). Defined.
Definition exist_fe25519W (x : fe25519W) : is_bounded (fe25519WToZ x) = true -> fe25519
  := Eval cbv [app_fe25519W_dep exist_fe25519W' fe25519ZToW] in exist_fe25519W' x.
Definition exist_fe25519'' (x : Specific.GF25519.fe25519) : is_bounded x = true -> fe25519.
Proof. make_exist'' x exist_fe25519W fe25519ZToW. Defined.
Definition exist_fe25519' (x : Specific.GF25519.fe25519) : is_bounded x = true -> fe25519.
Proof. make_exist' x (@app_fe25519W_dep) exist_fe25519'' exist_fe25519W fe25519ZToW. Defined.
Definition exist_fe25519 (x : Specific.GF25519.fe25519) : is_bounded x = true -> fe25519
  := Eval cbv [exist_fe25519' exist_fe25519W exist_fe25519' app_fe25519 app_fe25519W_dep] in
      exist_fe25519' x.

Lemma proj1_fe25519_exist_fe25519W x pf : proj1_fe25519 (exist_fe25519W x pf) = fe25519WToZ x.
Proof. now hnf in x; destruct_head' prod. Qed.
Lemma proj1_fe25519W_exist_fe25519 x pf : proj1_fe25519W (exist_fe25519 x pf) = fe25519ZToW x.
Proof. now hnf in x; destruct_head' prod. Qed.
Lemma proj1_fe25519_exist_fe25519 x pf : proj1_fe25519 (exist_fe25519 x pf) = x.
Proof.
  hnf in x; destruct_head' prod.
  cbv [proj1_fe25519 exist_fe25519 proj1_fe25519W fe25519WToZ proj_word Build_bounded_word Build_bounded_word'].
  unfold_is_bounded_in pf.
  destruct_head' and.
  Z.ltb_to_lt.
  rewrite ?word64ToZ_ZToWord64 by prove_lt_bit_width.
  reflexivity.
Qed.

Definition exist_wire_digitsW' (x : wire_digitsW)
  : wire_digits_is_bounded (wire_digitsWToZ x) = true -> wire_digits.
Proof. make_exist_W' x (@app_wire_digitsW_dep). Defined.
Definition exist_wire_digitsW (x : wire_digitsW)
  : wire_digits_is_bounded (wire_digitsWToZ x) = true -> wire_digits
  := Eval cbv [app_wire_digitsW_dep exist_wire_digitsW' wire_digitsZToW] in exist_wire_digitsW' x.
Definition exist_wire_digits'' (x : Specific.GF25519.wire_digits)
  : wire_digits_is_bounded x = true -> wire_digits.
Proof. make_exist'' x exist_wire_digitsW wire_digitsZToW. Defined.
Definition exist_wire_digits' (x : Specific.GF25519.wire_digits)
  : wire_digits_is_bounded x = true -> wire_digits.
Proof. make_exist' x (@app_wire_digitsW_dep) exist_wire_digits'' exist_wire_digitsW wire_digitsZToW. Defined.
Definition exist_wire_digits (x : Specific.GF25519.wire_digits)
  : wire_digits_is_bounded x = true -> wire_digits
  := Eval cbv [exist_wire_digits' exist_wire_digitsW exist_wire_digits' app_wire_digits app_wire_digitsW_dep] in
      exist_wire_digits' x.

Lemma proj1_wire_digits_exist_wire_digitsW x pf : proj1_wire_digits (exist_wire_digitsW x pf) = wire_digitsWToZ x.
Proof. now hnf in x; destruct_head' prod. Qed.
Lemma proj1_wire_digitsW_exist_wire_digits x pf : proj1_wire_digitsW (exist_wire_digits x pf) = wire_digitsZToW x.
Proof. now hnf in x; destruct_head' prod. Qed.
Lemma proj1_wire_digits_exist_wire_digits x pf : proj1_wire_digits (exist_wire_digits x pf) = x.
Proof.
  hnf in x; destruct_head' prod.
  cbv [proj1_wire_digits exist_wire_digits proj1_wire_digitsW wire_digitsWToZ proj_word Build_bounded_word Build_bounded_word' app_wire_digits HList.mapt HList.mapt' length wire_widths fst snd].
  unfold_is_bounded_in pf.
  destruct_head' and.
  Z.ltb_to_lt.
  rewrite ?word64ToZ_ZToWord64 by prove_lt_bit_width.
  reflexivity.
Qed.

Module opt.
  Definition word64ToZ := Eval vm_compute in word64ToZ.
  Definition word64ToN := Eval vm_compute in @wordToN bit_width.
  Definition NToWord64 := Eval vm_compute in NToWord64.
  Definition bit_width := Eval vm_compute in bit_width.
  Definition Zleb := Eval cbv [Z.leb] in Z.leb.
  Definition andb := Eval vm_compute in andb.
  Definition word64ize := Eval vm_compute in word64ize.
End opt.

Local Transparent bit_width.
Local Ltac do_change lem :=
  match lem with
  | context L[andb (?x <=? ?y)%Z (?y <=? ?z)]
    => let x' := (eval vm_compute in x) in
       let z' := (eval vm_compute in z) in
       lazymatch y with
       | word64ToZ (word64ize ?v)
         => let y' := constr:(opt.word64ToZ (opt.word64ize v)) in
            let L' := context L[andb (opt.Zleb x' y') (opt.Zleb y' z')] in
            do_change L'
       end
  | _ => lem
  end.
Definition fe25519_word64ize (x : fe25519) : fe25519.
Proof.
  set (x' := x).
  hnf in x; destruct_head' prod.
  let lem := constr:(exist_fe25519W (fe25519W_word64ize (proj1_fe25519W x'))) in
  let lem := (eval cbv [proj1_fe25519W x' fe25519W_word64ize proj_word exist_fe25519W Build_bounded_word' Build_bounded_word] in lem) in
  let lem := do_change lem in
  refine (lem _);
    change (is_bounded (fe25519WToZ (fe25519W_word64ize (proj1_fe25519W x'))) = true);
    abstract (rewrite fe25519W_word64ize_id; apply is_bounded_proj1_fe25519).
Defined.
Definition wire_digits_word64ize (x : wire_digits) : wire_digits.
Proof.
  set (x' := x).
  hnf in x; destruct_head' prod.
  let lem := constr:(exist_wire_digitsW (wire_digitsW_word64ize (proj1_wire_digitsW x'))) in
  let lem := (eval cbv [proj1_wire_digitsW x' wire_digitsW_word64ize proj_word exist_wire_digitsW Build_bounded_word Build_bounded_word'] in lem) in
  let lem := do_change lem in
  let lem := (eval cbv [word64ize opt.word64ize andb Z.leb Z.compare CompOpp Pos.compare] in lem) in
  refine (lem _);
    change (wire_digits_is_bounded (wire_digitsWToZ (wire_digitsW_word64ize (proj1_wire_digitsW x'))) = true);
    abstract (rewrite wire_digitsW_word64ize_id; apply is_bounded_proj1_wire_digits).
Defined.

Lemma is_bounded_to_nth_default x (H : is_bounded x = true)
  : forall n : nat,
    (n < length limb_widths)%nat
    -> (0 <= nth_default 0 (Tuple.to_list length_fe25519 x) n <=
        snd (b_of (nth_default (-1) limb_widths n)))%Z.
Proof.
  hnf in x; destruct_head' prod.
  unfold_is_bounded_in H; destruct_head' and.
  Z.ltb_to_lt.
  unfold nth_default; simpl.
  intros.
  repeat match goal with
         | [ |- context[nth_error _ ?x] ]
           => is_var x; destruct x; simpl
         end;
    omega.
Qed.

(* END precomputation *)

(* Precompute constants *)

Definition one' := Eval vm_compute in exist_fe25519 Specific.GF25519.one_ eq_refl.
Definition one := Eval cbv [one' fe25519_word64ize word64ize andb opt.word64ToZ opt.word64ize opt.Zleb Z.compare CompOpp Pos.compare Pos.compare_cont] in fe25519_word64ize one'.

Definition zero' := Eval vm_compute in exist_fe25519 Specific.GF25519.zero_ eq_refl.
Definition zero := Eval cbv [zero' fe25519_word64ize word64ize andb opt.word64ToZ opt.word64ize opt.Zleb Z.compare CompOpp Pos.compare Pos.compare_cont] in fe25519_word64ize zero'.

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
  cbv [nth_default Tuple.to_list Tuple.to_list' List.length limb_widths params25519] in H.
  repeat match type of H with
         | context[nth_error (cons _ _) _]
           => let H' := fresh in
              pose proof (H O) as H'; specialize (fun i => H (S i)); simpl @nth_error in H, H';
                cbv beta iota in H'
         end.
  clear H.
  simpl in *.
  cbv [Z.pow_pos Z.mul Pos.mul Pos.iter nth_default nth_error value] in *.
  unfold is_bounded.
  apply fold_right_andb_true_iff_fold_right_and_True.
  cbv [is_bounded proj1_fe25519 to_list length bounds from_list from_list' map2 on_tuple2 to_list' ListUtil.map2 List.map List.rev List.app proj_word fold_right length_fe25519].
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
  rewrite ?word64ToZ_ZToWord64 by prove_lt_bit_width.
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
  rewrite ?word64ToZ_ZToWord64 by prove_lt_bit_width.
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

(** TODO(andreser): Remove me in favor of a GF25519.v definition *)
Definition prefreeze :=
fun '(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9) =>
dlet a := f9 in
dlet a0 := (Z.shiftr a 26 + f8)%Z in
dlet a1 := (Z.shiftr a0 25 + f7)%Z in
dlet a2 := (Z.shiftr a1 26 + f6)%Z in
dlet a3 := (Z.shiftr a2 25 + f5)%Z in
dlet a4 := (Z.shiftr a3 26 + f4)%Z in
dlet a5 := (Z.shiftr a4 25 + f3)%Z in
dlet a6 := (Z.shiftr a5 26 + f2)%Z in
dlet a7 := (Z.shiftr a6 25 + f1)%Z in
dlet a8 := (Z.shiftr a7 26 + f0)%Z in
dlet a9 := (19 * Z.shiftr a8 25 + Z.land a 67108863)%Z in
dlet a10 := (Z.shiftr a9 26 + Z.land a0 33554431)%Z in
dlet a11 := (Z.shiftr a10 25 + Z.land a1 67108863)%Z in
dlet a12 := (Z.shiftr a11 26 + Z.land a2 33554431)%Z in
dlet a13 := (Z.shiftr a12 25 + Z.land a3 67108863)%Z in
dlet a14 := (Z.shiftr a13 26 + Z.land a4 33554431)%Z in
dlet a15 := (Z.shiftr a14 25 + Z.land a5 67108863)%Z in
dlet a16 := (Z.shiftr a15 26 + Z.land a6 33554431)%Z in
dlet a17 := (Z.shiftr a16 25 + Z.land a7 67108863)%Z in
dlet a18 := (Z.shiftr a17 26 + Z.land a8 33554431)%Z in
dlet a19 := (19 * Z.shiftr a18 25 + Z.land a9 67108863)%Z in
dlet a20 := (Z.shiftr a19 26 + Z.land a10 33554431)%Z in
dlet a21 := (Z.shiftr a20 25 + Z.land a11 67108863)%Z in
dlet a22 := (Z.shiftr a21 26 + Z.land a12 33554431)%Z in
dlet a23 := (Z.shiftr a22 25 + Z.land a13 67108863)%Z in
dlet a24 := (Z.shiftr a23 26 + Z.land a14 33554431)%Z in
dlet a25 := (Z.shiftr a24 25 + Z.land a15 67108863)%Z in
dlet a26 := (Z.shiftr a25 26 + Z.land a16 33554431)%Z in
dlet a27 := (Z.shiftr a26 25 + Z.land a17 67108863)%Z in
dlet a28 := (Z.shiftr a27 26 + Z.land a18 33554431)%Z in

((Z.land a28 33554431 )%Z, (Z.land a27 67108863 )%Z,
(Z.land a26 33554431 )%Z, (Z.land a25 67108863 )%Z,
(Z.land a24 33554431 )%Z, (Z.land a23 67108863 )%Z,
(Z.land a22 33554431 )%Z, (Z.land a21 67108863 )%Z,
(Z.land a20 33554431 )%Z, ( Z.land a19 67108863 )%Z).

Axiom postfreeze : GF25519.fe25519 -> GF25519.fe25519.
Axiom freeze_prepost_freeze : forall x, postfreeze (prefreeze x) = GF25519.freeze x.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Definition postfreezeW : fe25519W -> fe25519W.
Proof. admit. Defined.
Axiom postfreezeW_correct_and_bounded : iunop_correct_and_bounded postfreezeW postfreeze.
