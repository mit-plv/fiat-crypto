Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.Specific.GF25519.
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

(* BEGIN precomputation. *)

Local Notation b_of exp := (0, 2^exp + 2^(exp-3))%Z (only parsing). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)
Local Notation Z_of exp := { v : Z | fst (b_of exp) <= v <= snd (b_of exp) }.
Definition bounds : list (Z * Z)
  := Eval compute in
      [b_of 25; b_of 26; b_of 25; b_of 26; b_of 25; b_of 26; b_of 25; b_of 26; b_of 25; b_of 26].

Definition fe25519 :=
  Eval cbv [fst snd] in
    let sanity := eq_refl : length bounds = length limb_widths in
    (Z_of 25 * Z_of 26 * Z_of 25 * Z_of 26 * Z_of 25 * Z_of 26 * Z_of 25 * Z_of 26 * Z_of 25 * Z_of 26)%type.
Definition proj1_fe25519 (x : fe25519) : Specific.GF25519.fe25519
  := let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) := x in
     (proj1_sig x0, proj1_sig x1, proj1_sig x2, proj1_sig x3, proj1_sig x4,
      proj1_sig x5, proj1_sig x6, proj1_sig x7, proj1_sig x8, proj1_sig x9).
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
  cbv [is_bounded proj1_fe25519 to_list length bounds from_list from_list' map2 on_tuple2 to_list' ListUtil.map2 List.map List.rev List.app proj1_sig].
  apply fold_right_andb_true_iff_fold_right_and_True.
  cbv [fold_right List.map].
  cbv beta in *.
  repeat split; rewrite !Bool.andb_true_iff, !Z.leb_le;
    assumption.
Qed.

(* Make small [vm_computable] versions of proofs *)
Definition correct_le_le {l v u} : l <= v <= u -> l <= v <= u.
Proof.
  intro pf; pose proof (proj1 pf) as pf1; pose proof (proj2 pf) as pf2; clear pf;
    split; hnf in *;
      lazymatch goal with
      | [ H : ?x = Gt -> False |- ?x = Gt -> False ]
        => revert H;
             refine match x as y return (y = Gt -> False) -> y = Gt -> False with
                    | Gt => fun f => f
                    | _ => fun _ pf => match pf with
                                       | eq_refl => I
                                       end
                    end
      end.
Defined.

Definition exist_fe25519' (x : Specific.GF25519.fe25519) : is_bounded x = true -> fe25519.
Proof.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) as x := x return is_bounded x = true -> fe25519 in
          fun H => (fun H' => (exist _ x0 _, exist _ x1 _, exist _ x2 _, exist _ x3 _, exist _ x4 _,
                               exist _ x5 _, exist _ x6 _, exist _ x7 _, exist _ x8 _, exist _ x9 _))
                     (let H' := proj1 (@fold_right_andb_true_iff_fold_right_and_True _) H in
                      _));
    [
    | | | | | | | | |
    | clearbody H'; clear H x;
      unfold is_bounded in *;
      cbv [to_list length bounds from_list from_list' map2 on_tuple2 to_list' ListUtil.map2 List.map fold_right List.rev List.app] in H';
      rewrite !Bool.andb_true_iff, !Z.leb_le in H';
      exact H' ];
    destruct_head and; auto.
Defined.

Definition exist_fe25519 (x : Specific.GF25519.fe25519) : is_bounded x = true -> fe25519.
Proof.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) as x := x return is_bounded x = true -> fe25519 in
          fun H => _).
  let v := constr:(exist_fe25519' (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) H) in
  let rec do_refine v :=
      first [ let v' := (eval cbv [exist_fe25519' proj1_sig snd fst] in (proj1_sig v)) in
              refine (exist _ v' (correct_le_le _)); abstract exact (proj2_sig v)
            | let v' := (eval cbv [exist_fe25519' proj1_sig snd fst] in (proj1_sig (snd v))) in
              refine (_, exist _ v' (correct_le_le _));
              [ do_refine (fst v) | abstract exact (proj2_sig (snd v)) ] ] in
  do_refine v.
Defined.

Lemma proj1_fe25519_exist_fe25519 x pf : proj1_fe25519 (exist_fe25519 x pf) = x.
Proof.
  revert pf.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) as x := x return forall pf : is_bounded x = true, proj1_fe25519 (exist_fe25519 x pf) = x in
          fun pf => _).
  reflexivity.
Qed.

(* END precomputation *)

(* Precompute constants *)

Definition one := Eval cbv -[Z.le] in exist_fe25519 Specific.GF25519.one_ eq_refl.

Definition zero := Eval cbv -[Z.le] in exist_fe25519 Specific.GF25519.zero_ eq_refl.

Axiom ExprBinOp : Type.
Axiom ExprUnOp : Type.
Axiom interp_bexpr : ExprBinOp -> Specific.GF25519.fe25519 -> Specific.GF25519.fe25519 -> Specific.GF25519.fe25519.
Axiom interp_uexpr : ExprUnOp -> Specific.GF25519.fe25519 -> Specific.GF25519.fe25519.
Axiom radd : ExprBinOp.
Axiom rsub : ExprBinOp.
Axiom rmul : ExprBinOp.
Axiom ropp : ExprUnOp.
Axiom rfreeze : ExprUnOp.
Axiom radd_correct : forall x y, interp_bexpr radd x y = carry_add x y.
Axiom rsub_correct : forall x y, interp_bexpr rsub x y = carry_sub x y.
Axiom rmul_correct : forall x y, interp_bexpr rmul x y = mul x y.
Axiom ropp_correct : forall x, interp_uexpr ropp x = carry_opp x.
Axiom rfreeze_correct : forall x, interp_uexpr rfreeze x = freeze x.
Local Notation binop_bounded op
  := (forall x y,
         is_bounded x = true
         -> is_bounded y = true
         -> is_bounded (interp_bexpr op x y) = true) (only parsing).
Local Notation unop_bounded op
  := (forall x,
         is_bounded x = true
         -> is_bounded (interp_uexpr op x) = true) (only parsing).
Axiom radd_bounded : binop_bounded radd.
Axiom rsub_bounded : binop_bounded rsub.
Axiom rmul_bounded : binop_bounded rmul.
Axiom ropp_bounded : unop_bounded ropp.
Axiom rfreeze_bounded : unop_bounded rfreeze.

Local Ltac bounded_t clem blem :=
  rewrite <- clem;
  apply blem; apply is_bounded_proj1_fe25519.

Local Ltac define_binop f g op clem blem :=
  refine (exist_fe25519 (op (proj1_fe25519 f) (proj1_fe25519 g)) _);
  abstract bounded_t clem blem.
Local Ltac define_unop f op clem blem :=
  refine (exist_fe25519 (op (proj1_fe25519 f)) _);
  abstract bounded_t clem blem.

Definition add (f g : fe25519) : fe25519.
Proof. define_binop f g Specific.GF25519.carry_add radd_correct radd_bounded. Defined.
Definition sub (f g : fe25519) : fe25519.
Proof. define_binop f g Specific.GF25519.carry_sub rsub_correct rsub_bounded. Defined.
Definition mul (f g : fe25519) : fe25519.
Proof. define_binop f g Specific.GF25519.mul rmul_correct rmul_bounded. Defined.
Definition opp (f : fe25519) : fe25519.
Proof. define_unop f Specific.GF25519.carry_opp ropp_correct ropp_bounded. Defined.
Definition pow (f : fe25519) chain := fold_chain_opt one mul chain [f].
Lemma fold_chain_opt_proj ls id' op' id op chain
      (Hid : id = proj1_fe25519 id')
      (Hop : forall x y, op (proj1_fe25519 x) (proj1_fe25519 y) = proj1_fe25519 (op' x y))
  : fold_chain_opt id op chain (List.map proj1_fe25519 ls)
    = proj1_fe25519 (fold_chain_opt id' op' chain ls).
Proof.
  rewrite !fold_chain_opt_correct.
  revert ls; induction chain as [|x xs IHxs]; intros.
  { destruct ls; simpl; trivial. }
  { destruct x; simpl; unfold Let_In; simpl.
    rewrite <- IHxs; simpl.
    do 2 f_equal.
    rewrite <- Hop, Hid.
    rewrite !map_nth_default_always.
    reflexivity. }
Qed.
Definition inv (f : fe25519) : fe25519.
Proof.
  refine (exist_fe25519 (inv (proj1_fe25519 f)) _).
  abstract (
      rewrite inv_correct; cbv [inv_opt pow_opt]; erewrite (fold_chain_opt_proj [f] one mul);
      [ apply is_bounded_proj1_fe25519 | reflexivity
        | cbv [mul]; intros; rewrite proj1_fe25519_exist_fe25519, mul_correct; reflexivity ]
    ).
Defined.

Definition freeze (f : fe25519) : fe25519.
Proof. define_unop f Specific.GF25519.freeze rfreeze_correct rfreeze_bounded. Defined.

Lemma encode_bounded x : is_bounded (encode x) = true.
Proof.
  pose proof (bounded_encode x).
  generalize dependent (encode x).
  intro t; compute in t; intros.
  destruct_head prod.
  unfold Pow2Base.bounded in H.
  pose proof (H 0%nat); pose proof (H 1%nat); pose proof (H 2%nat);
    pose proof (H 3%nat); pose proof (H 4%nat); pose proof (H 5%nat);
      pose proof (H 6%nat); pose proof (H 7%nat); pose proof (H 8%nat);
        pose proof (H 9%nat); clear H.
  simpl in *.
  cbv [Z.pow_pos Z.mul Pos.mul Pos.iter nth_default nth_error value] in *.
  unfold is_bounded.
  apply fold_right_andb_true_iff_fold_right_and_True.
  cbv [is_bounded proj1_fe25519 to_list length bounds from_list from_list' map2 on_tuple2 to_list' ListUtil.map2 List.map List.rev List.app proj1_sig fold_right].
  repeat split; rewrite !Bool.andb_true_iff, !Z.leb_le; omega.
Qed.

Definition encode (x : F modulus) : fe25519
  := exist_fe25519 (encode x) (encode_bounded x).

Definition div (f g : fe25519) : fe25519
  := exist_fe25519 (div (proj1_fe25519 f) (proj1_fe25519 g)) (encode_bounded _).

Definition eq (f g : fe25519) : Prop := eq (proj1_fe25519 f) (proj1_fe25519 g).

Import Morphisms.

Lemma field25519 : @field fe25519 eq zero one opp add sub mul inv div.
Proof.
  assert (Reflexive eq) by (repeat intro; reflexivity).
  eapply (Field.field_from_redundant_representation
            (fieldF:=Specific.GF25519.carry_field25519)
            (phi':=proj1_fe25519)).
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { cbv [opp]; intros; rewrite proj1_fe25519_exist_fe25519; reflexivity. }
  { cbv [add]; intros; rewrite proj1_fe25519_exist_fe25519; reflexivity. }
  { cbv [sub]; intros; rewrite proj1_fe25519_exist_fe25519; reflexivity. }
  { cbv [mul]; intros; rewrite proj1_fe25519_exist_fe25519; reflexivity. }
  { cbv [inv]; intros; rewrite proj1_fe25519_exist_fe25519; reflexivity. }
  { cbv [div]; intros; rewrite proj1_fe25519_exist_fe25519; reflexivity. }
Qed.

Lemma homomorphism_F25519 :
  @Ring.is_homomorphism
    (F modulus) Logic.eq F.one F.add F.mul
    fe25519 eq one add mul encode.
Proof.
  pose proof homomorphism_carry_F25519 as H.
  destruct H as [ [H0 H1] H2 H3].
  econstructor; [ econstructor | | ];
    cbv [eq encode add mul one]; repeat intro;
      rewrite ?proj1_fe25519_exist_fe25519 in *.
  { rewrite H0; reflexivity. }
  { apply H1; assumption. }
  { rewrite H2; reflexivity. }
  { reflexivity. }
Qed.
