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

  Definition ge25519_ast' (P Q: @interp_type Z ResultType) :
      { r: @HL.expr Z (@interp_type Z) ResultType
      | HL.interp (E := ZEvaluable) (t := ResultType) r
        = ge25519_add' P Q }.
  Proof.
    vm_compute in P, Q; repeat
      match goal with
      | [x:?T |- _] =>
        lazymatch T with
        | Z => fail
        | prod _ _ => destruct x
        | _ => clear x
        end
      end.

    eexists.
    cbv beta delta [ge25519_add'].

    let R := HL.rhs_of_goal in
    let X := HL.reify (@interp_type Z) R in idtac;
    transitivity (HL.interp (E := ZEvaluable) (t := ResultType) X);
      [reflexivity|].

    cbv iota beta delta [
          interp_type interp_binop HL.interp
          Z.land ZEvaluable eadd esub emul eshiftr eand].
    reflexivity.
  Defined.

  Definition ge25519_ast (P Q: @interp_type Z ResultType) :=
    proj1_sig (ge25519_ast' P Q).

  Definition bits: nat := 64.
  Definition width: Width bits := W64.

  Definition lift10 {T} (F: (Z*Z*Z*Z*Z*Z*Z*Z*Z*Z) -> T) := fun (a b c d e f g h i j: Z) =>
      F (a, b, c, d, e, f, g, h, i, j).

  Definition hlProg': NAry 80 Z (@HL.expr Z (@interp_type Z) ResultType) :=
    lift10 (fun px => lift10 (fun py => lift10 (fun pz => lift10 (fun pt =>
    lift10 (fun qx => lift10 (fun qy => lift10 (fun qz => lift10 (fun qt =>
    ge25519_ast (px, py, pz, pt) (qx, qy, qz, qt))))))))).

  Definition hlProg: NAry 80 Z (@HL.expr Z (@LL.arg Z Z) ResultType).
    refine (liftN (HLConversions.mapVar _ _) hlProg'); intro t;
      [ refine LL.uninterp_arg | refine LL.interp_arg ].
  Defined.

  Definition llProg: NAry 80 Z (@LL.expr Z Z ResultType) :=
    Eval vm_compute in (liftN CompileHL.compile hlProg).

  (* Don't vm_compute because it'll stack overflow (!!) *)
  Definition wordProg: NAry 80 (@CompileLL.WArg bits TT) (@LL.expr _ _ ResultType) :=
    NArgMap (fun x => Z.of_N (wordToN (LL.interp_arg (t := TT) x))) (
      liftN (LLConversions.convertZToWord bits) llProg).

  Definition qhasmProg :=
    Eval vm_compute in (CompileLL.compile (w := width) wordProg).

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
