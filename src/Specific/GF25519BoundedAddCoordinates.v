Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.Specific.GF25519.
Require Import Crypto.Specific.GF25519ExtendedAddCoordinates.
Require Import Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Specific.GF25519Reflective.
Require Import Crypto.Specific.GF25519ReflectiveAddCoordinates.
Require Import Bedrock.Word Crypto.Util.WordUtil.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.ModularArithmetic.ModularBaseSystemWord.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.HList.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Algebra.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Local Open Scope Z.


Local Ltac bounded_t opW blem :=
  apply blem; apply is_bounded_proj1_fe25519.

Local Ltac define_binop f g opW blem :=
  refine (exist_fe25519W (opW (proj1_fe25519W f) (proj1_fe25519W g)) _);
  abstract bounded_t opW blem.

Local Opaque Let_In.
Local Opaque Z.add Z.sub Z.mul Z.shiftl Z.shiftr Z.land Z.lor Z.eqb NToWord64.
Local Arguments interp_radd_coordinates / _ _ _ _ _ _ _ _ _.
Definition add_coordinatesW (x0 x1 x2 x3 x4 x5 x6 x7 x8 : fe25519W) : Tuple.tuple fe25519W 4
  := Eval simpl in interp_radd_coordinates x0 x1 x2 x3 x4 x5 x6 x7 x8.

Local Ltac port_correct_and_bounded pre_rewrite opW interp_rop rop_cb :=
  change opW with (interp_rop);
  rewrite pre_rewrite;
  intros; apply rop_cb; assumption.

Lemma add_coordinatesW_correct_and_bounded : i9top_correct_and_bounded 4 add_coordinatesW Reified.AddCoordinates.add_coordinates.
Proof. port_correct_and_bounded interp_radd_coordinates_correct add_coordinatesW interp_radd_coordinates radd_coordinates_correct_and_bounded. Qed.

Local Ltac define_9_4op x0 x1 x2 x3 x4 x5 x6 x7 x8 opW blem :=
  refine (HList.mapt exist_fe25519W
                     (ts:=opW (proj1_fe25519W x0)
                              (proj1_fe25519W x1)
                              (proj1_fe25519W x2)
                              (proj1_fe25519W x3)
                              (proj1_fe25519W x4)
                              (proj1_fe25519W x5)
                              (proj1_fe25519W x6)
                              (proj1_fe25519W x7)
                              (proj1_fe25519W x8)) _);
  abstract (
      rewrite <- (HList.hlist_map (F:=fun x => is_bounded x = true) (f:=fe25519WToZ));
      apply add_coordinatesW_correct_and_bounded; apply is_bounded_proj1_fe25519
    ).
Definition add_coordinates (x0 x1 x2 x3 x4 x5 x6 x7 x8 : fe25519) : Tuple.tuple fe25519 4.
Proof. define_9_4op x0 x1 x2 x3 x4 x5 x6 x7 x8 add_coordinatesW add_coordinatesW_correct_and_bounded. Defined.

Local Ltac op_correct_t op opW_correct_and_bounded :=
  cbv [op];
  rewrite ?HList.map_mapt;
  lazymatch goal with
  | [ |- context[proj1_fe25519 (exist_fe25519W _ _)] ]
    => rewrite proj1_fe25519_exist_fe25519W || setoid_rewrite proj1_fe25519_exist_fe25519W
  | [ |- context[proj1_wire_digits (exist_wire_digitsW _ _)] ]
    => rewrite proj1_wire_digits_exist_wire_digitsW
  | _ => idtac
  end;
  rewrite <- ?HList.map_is_mapt;
  apply opW_correct_and_bounded;
  lazymatch goal with
  | [ |- is_bounded _ = true ]
    => apply is_bounded_proj1_fe25519
  | [ |- wire_digits_is_bounded _ = true ]
    => apply is_bounded_proj1_wire_digits
  end.

Lemma add_coordinates_correct (x0 x1 x2 x3 x4 x5 x6 x7 x8 : fe25519)
  : Tuple.map (n:=4) proj1_fe25519 (add_coordinates x0 x1 x2 x3 x4 x5 x6 x7 x8)
    = Reified.AddCoordinates.add_coordinates (proj1_fe25519 x0)
                                             (proj1_fe25519 x1)
                                             (proj1_fe25519 x2)
                                             (proj1_fe25519 x3)
                                             (proj1_fe25519 x4)
                                             (proj1_fe25519 x5)
                                             (proj1_fe25519 x6)
                                             (proj1_fe25519 x7)
                                             (proj1_fe25519 x8).
Proof. op_correct_t add_coordinates add_coordinatesW_correct_and_bounded. Qed.
