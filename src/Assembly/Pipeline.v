Require Import Crypto.Assembly.PhoasCommon.
Require Import Crypto.Assembly.HL.
Require Import Crypto.Assembly.LL.
Require Import Crypto.Assembly.Compile.
Require Import Crypto.Assembly.Conversions.
Require Import Crypto.Assembly.StringConversion.
Require Import Crypto.Assembly.State.
Require Import Crypto.Util.Notations.

Module GF25519.
  Import ListNotations StateCommon EvalUtil ListState.
  Import HL LL.

  Local Infix ">>" := Z.shiftr.
  Local Infix "&" := (fun x y => Z.land x (Z.of_nat (Z.to_nat y))).
  Local Open Scope Z_scope.
  Require Import Crypto.Spec.ModularArithmetic.
  Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
  Require Import Crypto.Specific.GF25519.
  Require Import Crypto.Experiments.SpecEd25519.

  (* Computing the length first is necessary to make this run in tolerable time on 8.6 *)
  Definition twice_d' := Eval cbv [length params25519 ModularBaseSystemOpt.limb_widths_from_len ModularBaseSystem.encode ModularBaseSystemList.encode PseudoMersenneBaseParams.limb_widths] in ModularBaseSystem.encode(modulus:=q) (d + d)%F.
  Definition twice_d : fe25519 := Eval vm_compute in twice_d'.

  Definition ge25519_add' :=
    Eval cbv beta delta [Extended.add_coordinates fe25519 add mul sub ModularBaseSystemOpt.Let_In twice_d] in
      @Extended.add_coordinates fe25519 add sub mul twice_d.

  Definition ResultType: type.
  Proof.
    let T' := type of (twice_d, twice_d, twice_d, twice_d) in
    let T := eval vm_compute in T' in
    let t := reify_type T in
    exact t.
  Defined.

  (* Too slow for CI

  Definition ge25519_ast P Q : { r: @Expr Z ResultType | ZInterp r = ge25519_add' P Q }.
  Proof.
    refine (
let '((P_X_0, P_X_1, P_X_2, P_X_3, P_X_4, P_X_5, P_X_6, P_X_7, P_X_8, P_X_9), (P_Y_0, P_Y_1, P_Y_2, P_Y_3, P_Y_4, P_Y_5, P_Y_6, P_Y_7, P_Y_8, P_Y_9), (P_Z_0, P_Z_1, P_Z_2, P_Z_3, P_Z_4, P_Z_5, P_Z_6, P_Z_7, P_Z_8, P_Z_9), (P_T_0, P_T_1, P_T_2, P_T_3, P_T_4, P_T_5, P_T_6, P_T_7, P_T_8, P_T_9)) := P in
let '((Q_X_0, Q_X_1, Q_X_2, Q_X_3, Q_X_4, Q_X_5, Q_X_6, Q_X_7, Q_X_8, Q_X_9), (Q_Y_0, Q_Y_1, Q_Y_2, Q_Y_3, Q_Y_4, Q_Y_5, Q_Y_6, Q_Y_7, Q_Y_8, Q_Y_9), (Q_Z_0, Q_Z_1, Q_Z_2, Q_Z_3, Q_Z_4, Q_Z_5, Q_Z_6, Q_Z_7, Q_Z_8, Q_Z_9), (Q_T_0, Q_T_1, Q_T_2, Q_T_3, Q_T_4, Q_T_5, Q_T_6, Q_T_7, Q_T_8, Q_T_9)) := Q in
_).
    repeat match goal with
             [x:?T |- _] =>
             lazymatch T with
             | Z => fail
             | _ => clear x
             end
           end.

    eexists.
    cbv beta delta [ge25519_add'].
    Reify_rhs.
    reflexivity.
  Defined.

  Definition ge25519_result_range := RangeInterp (ZToRange 32 ge25519_ast). *)
End GF25519.
