Require Import Coq.ZArith.BinInt.

Require Import Crypto.Assembly.QhasmCommon.
Require Import Crypto.Assembly.PhoasCommon.
Require Import Crypto.Assembly.HL.
Require Import Crypto.Assembly.LL.
Require Import Crypto.Assembly.Compile.
Require Import Crypto.Assembly.Conversions.
Require Import Crypto.Assembly.StringConversion.
Require Import Crypto.Assembly.State.

Require Import Crypto.Util.Notations.
Require Import Crypto.Util.LetIn.

Module SimpleExample.
  Definition bits: nat := 32.
  Definition width: Width bits := W32.

  Definition hlProg: NAry 1 Z (@HL.expr Z (@LL.arg Z Z) TT) :=
    fun x => HL.Binop OPadd (HL.Const x) (HL.Const 5%Z).

  Definition llProg: NAry 1 Z (@LL.expr Z Z TT) :=
    liftN CompileHL.compile hlProg.

  Definition wordProg: NAry 1 (@CompileLL.WArg bits TT) (@LL.expr _ _ TT) :=
    NArgMap (fun x => Z.of_N (wordToN (LL.interp_arg (t := TT) x))) (
      liftN (LLConversions.convertZToWord bits) llProg).

  Definition qhasmProg := CompileLL.compile (w := width) wordProg.

  Definition qhasmString: option string :=
    Eval cbv in match qhasmProg with
    | Some (p, _) => StringConversion.convertProgram p
    | None => None
    end.

  Section BoundsCheck.
    Definition R := @WordRangeOpt bits.

    Definition rangeProg: NAry 1 R (@LL.expr R R TT) :=
      NArgMap (fun x => getOrElse (Z.of_N (N.pred (Npow2 bits)))
          (option_map Z.of_N (getUpperBoundOpt x))) (
        liftN (LLConversions.convertZToWordRangeOpt bits) llProg).

    Definition rangeValid: NAry 1 R Prop :=
        liftN (LLConversions.check) rangeProg.

    (* Check that our bounds are valid for any Z in 0..2^31 *)
    Lemma rangeValidAny: rangeValid (makeRange 0 (Z.shiftl 1 31))%Z.
    Proof. cbv; intuition. Qed.
  End BoundsCheck.
End SimpleExample.

Module GF25519.
  Require Import Crypto.Spec.ModularArithmetic.
  Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
  Require Import Crypto.ModularArithmetic.ModularBaseSystem.
  Require Import Crypto.Specific.GF25519.

  (* Computing the length first is necessary to make this run in tolerable time on 8.6 *)
  Definition q : Z := (2 ^ 255 - 19)%Z.
  Definition d : F q := (F.opp (F.of_Z q 121665%Z) / (F.of_Z q 121666%Z))%F.

  Definition twice_d' := Eval cbv [length params25519 ModularBaseSystemOpt.limb_widths_from_len ModularBaseSystem.encode ModularBaseSystemList.encode PseudoMersenneBaseParams.limb_widths] in ModularBaseSystem.encode(modulus:=q) (d + d)%F.
  Definition twice_d : fe25519 := Eval vm_compute in twice_d'.

  Definition ge25519_add' :=
    Eval cbv beta delta [Extended.add_coordinates fe25519 add mul sub Let_In twice_d] in
      @Extended.add_coordinates fe25519 add sub mul twice_d.

  Definition ResultType: type.
  Proof.
    let T' := type of (twice_d, twice_d, twice_d, twice_d) in
    let T := eval vm_compute in T' in
    let t := HL.reify_type T in
    exact t.
  Defined.

  Definition ge25519_ast P Q : { r: @HL.expr Z (@interp_type Z) ResultType
                               | HL.interp (E := ZEvaluable) r = ge25519_add' P Q }.
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
  Admitted.

  (* This is too slow for Travis...

    HL.Reify_rhs.
    reflexivity.
  Defined. *)

  Definition bits: nat := 64.
  Definition width: Width bits := W64.

  Definition hlProg': NAry 80 Z (@HL.expr Z (@interp_type Z) ResultType) := fun 
      P_X_0 P_X_1 P_X_2 P_X_3 P_X_4 P_X_5 P_X_6 P_X_7 P_X_8 P_X_9
      P_Y_0 P_Y_1 P_Y_2 P_Y_3 P_Y_4 P_Y_5 P_Y_6 P_Y_7 P_Y_8 P_Y_9
      P_Z_0 P_Z_1 P_Z_2 P_Z_3 P_Z_4 P_Z_5 P_Z_6 P_Z_7 P_Z_8 P_Z_9
      P_T_0 P_T_1 P_T_2 P_T_3 P_T_4 P_T_5 P_T_6 P_T_7 P_T_8 P_T_9
      Q_X_0 Q_X_1 Q_X_2 Q_X_3 Q_X_4 Q_X_5 Q_X_6 Q_X_7 Q_X_8 Q_X_9
      Q_Y_0 Q_Y_1 Q_Y_2 Q_Y_3 Q_Y_4 Q_Y_5 Q_Y_6 Q_Y_7 Q_Y_8 Q_Y_9
      Q_Z_0 Q_Z_1 Q_Z_2 Q_Z_3 Q_Z_4 Q_Z_5 Q_Z_6 Q_Z_7 Q_Z_8 Q_Z_9
      Q_T_0 Q_T_1 Q_T_2 Q_T_3 Q_T_4 Q_T_5 Q_T_6 Q_T_7 Q_T_8 Q_T_9 =>

      let (P, Q) := (
        ((P_X_0, P_X_1, P_X_2, P_X_3, P_X_4, P_X_5, P_X_6, P_X_7, P_X_8, P_X_9),
         (P_Y_0, P_Y_1, P_Y_2, P_Y_3, P_Y_4, P_Y_5, P_Y_6, P_Y_7, P_Y_8, P_Y_9),
         (P_Z_0, P_Z_1, P_Z_2, P_Z_3, P_Z_4, P_Z_5, P_Z_6, P_Z_7, P_Z_8, P_Z_9),
         (P_T_0, P_T_1, P_T_2, P_T_3, P_T_4, P_T_5, P_T_6, P_T_7, P_T_8, P_T_9)),
        ((Q_X_0, Q_X_1, Q_X_2, Q_X_3, Q_X_4, Q_X_5, Q_X_6, Q_X_7, Q_X_8, Q_X_9),
         (Q_Y_0, Q_Y_1, Q_Y_2, Q_Y_3, Q_Y_4, Q_Y_5, Q_Y_6, Q_Y_7, Q_Y_8, Q_Y_9),
         (Q_Z_0, Q_Z_1, Q_Z_2, Q_Z_3, Q_Z_4, Q_Z_5, Q_Z_6, Q_Z_7, Q_Z_8, Q_Z_9),
         (Q_T_0, Q_T_1, Q_T_2, Q_T_3, Q_T_4, Q_T_5, Q_T_6, Q_T_7, Q_T_8, Q_T_9))) in
      proj1_sig (ge25519_ast P Q).

  Definition hlProg: NAry 80 Z (@HL.expr Z (@LL.arg Z Z) ResultType).
    refine (liftN (HLConversions.mapVar _ _) hlProg'); intro t;
      [ refine LL.uninterp_arg | refine LL.interp_arg ].
  Defined.

  Definition llProg: NAry 80 Z (@LL.expr Z Z ResultType) :=
    liftN CompileHL.compile hlProg.

  Definition wordProg: NAry 80 (@CompileLL.WArg bits TT) (@LL.expr _ _ ResultType) :=
    NArgMap (fun x => Z.of_N (wordToN (LL.interp_arg (t := TT) x))) (
      liftN (LLConversions.convertZToWord bits) llProg).

  Definition qhasmProg := CompileLL.compile (w := width) wordProg.

  Definition qhasmString: option string :=
    match qhasmProg with
    | Some (p, _) => StringConversion.convertProgram p
    | None => None
    end.

  Section BoundsCheck.
    Definition R := @WordRangeOpt bits.

    Definition rangeProg: NAry 80 R (@LL.expr R R ResultType) :=
      NArgMap (fun x => getOrElse (Z.of_N (N.pred (Npow2 bits)))
          (option_map Z.of_N (getUpperBoundOpt x))) (
        liftN (LLConversions.convertZToWordRangeOpt bits) llProg).

    Definition rangeValid: NAry 80 R Prop :=
        liftN (LLConversions.check) rangeProg.

    (* TODO: what are our prior ranges on the inputs?
    Lemma rangeValidAny: rangeValid (makeRange 0 (Z.shiftl 1 31))%Z.
    Proof. cbv; intuition. Qed. *)
  End BoundsCheck.
End GF25519.
