Require Import Coq.ZArith.ZArith.
Require Import Crypto.SpecificGen.GF25519_32.
Require Import Crypto.SpecificGen.GF25519_32BoundedCommon.
Require Import Crypto.SpecificGen.GF25519_32ReflectiveAddCoordinates.
Require Import Crypto.Util.LetIn.
Local Open Scope Z.

Local Ltac bounded_t opW blem :=
  apply blem; apply is_bounded_proj1_fe25519_32.

Local Ltac define_binop f g opW blem :=
  refine (exist_fe25519_32W (opW (proj1_fe25519_32W f) (proj1_fe25519_32W g)) _);
  abstract bounded_t opW blem.

Local Opaque Let_In.
Local Opaque Z.add Z.sub Z.mul Z.shiftl Z.shiftr Z.land Z.lor Z.eqb NToWord64.
Local Arguments interp_radd_coordinates / _ _ _ _ _ _ _ _ _.
Definition add_coordinatesW (x0 x1 x2 x3 x4 x5 x6 x7 x8 : fe25519_32W) : Tuple.tuple fe25519_32W 4
  := Eval simpl in interp_radd_coordinates x0 x1 x2 x3 x4 x5 x6 x7 x8.

Local Ltac port_correct_and_bounded pre_rewrite opW interp_rop rop_cb :=
  change opW with (interp_rop);
  rewrite pre_rewrite;
  intros; apply rop_cb; assumption.

Lemma add_coordinatesW_correct_and_bounded : i9top_correct_and_bounded 4 add_coordinatesW Reified.AddCoordinates.add_coordinates.
Proof. port_correct_and_bounded interp_radd_coordinates_correct add_coordinatesW interp_radd_coordinates radd_coordinates_correct_and_bounded. Qed.

Local Ltac define_9_4op x0 x1 x2 x3 x4 x5 x6 x7 x8 opW blem :=
  refine (let ts := opW (proj1_fe25519_32W x0)
                        (proj1_fe25519_32W x1)
                        (proj1_fe25519_32W x2)
                        (proj1_fe25519_32W x3)
                        (proj1_fe25519_32W x4)
                        (proj1_fe25519_32W x5)
                        (proj1_fe25519_32W x6)
                        (proj1_fe25519_32W x7)
                        (proj1_fe25519_32W x8) in
          HList.mapt exist_fe25519_32W (ts:=ts) _);
  abstract (
      rewrite <- (HList.hlist_map (F:=fun x => is_bounded x = true) (f:=fe25519_32WToZ));
      apply add_coordinatesW_correct_and_bounded; apply is_bounded_proj1_fe25519_32
    ).
Definition add_coordinates (x0 x1 x2 x3 x4 x5 x6 x7 x8 : fe25519_32) : Tuple.tuple fe25519_32 4.
Proof. define_9_4op x0 x1 x2 x3 x4 x5 x6 x7 x8 add_coordinatesW add_coordinatesW_correct_and_bounded. Defined.

Local Ltac op_correct_t op opW_correct_and_bounded :=
  cbv [op];
  rewrite ?HList.map_mapt;
  lazymatch goal with
  | [ |- context[proj1_fe25519_32 (exist_fe25519_32W _ _)] ]
    => rewrite proj1_fe25519_32_exist_fe25519_32W || setoid_rewrite proj1_fe25519_32_exist_fe25519_32W
  | [ |- context[proj1_wire_digits (exist_wire_digitsW _ _)] ]
    => rewrite proj1_wire_digits_exist_wire_digitsW
  | _ => idtac
  end;
  rewrite <- ?HList.map_is_mapt;
  apply opW_correct_and_bounded;
  lazymatch goal with
  | [ |- is_bounded _ = true ]
    => apply is_bounded_proj1_fe25519_32
  | [ |- wire_digits_is_bounded _ = true ]
    => apply is_bounded_proj1_wire_digits
  end.

Lemma add_coordinates_correct (x0 x1 x2 x3 x4 x5 x6 x7 x8 : fe25519_32)
  : Tuple.map (n:=4) proj1_fe25519_32 (add_coordinates x0 x1 x2 x3 x4 x5 x6 x7 x8)
    = Reified.AddCoordinates.add_coordinates (proj1_fe25519_32 x0)
                                             (proj1_fe25519_32 x1)
                                             (proj1_fe25519_32 x2)
                                             (proj1_fe25519_32 x3)
                                             (proj1_fe25519_32 x4)
                                             (proj1_fe25519_32 x5)
                                             (proj1_fe25519_32 x6)
                                             (proj1_fe25519_32 x7)
                                             (proj1_fe25519_32 x8).
Proof. op_correct_t add_coordinates add_coordinatesW_correct_and_bounded. Qed.
