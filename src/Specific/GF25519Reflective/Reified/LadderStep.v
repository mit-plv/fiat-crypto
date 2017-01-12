Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Crypto.Specific.GF25519.
Require Export Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Reflection.Eta.
Require Import Crypto.Reflection.EtaInterp.
Require Import Crypto.Reflection.Z.Interpretations64.
Require Crypto.Reflection.Z.Interpretations64.Relations.
Require Import Crypto.Reflection.Z.Interpretations64.RelationsCombinations.
Require Import Crypto.Reflection.Z.Reify.
Require Export Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.InterpWfRel.
Require Import Crypto.Reflection.LinearizeInterp.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Spec.MxDH.
Require Import Crypto.Specific.GF25519Reflective.Common.
Require Import Crypto.Specific.GF25519Reflective.Reified.Add.
Require Import Crypto.Specific.GF25519Reflective.Reified.Sub.
Require Import Crypto.Specific.GF25519Reflective.Reified.Mul.
Require Import Crypto.Specific.GF25519Reflective.Common9_4Op.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.HList.
Require Import Crypto.Util.Tower.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.
Require Import Bedrock.Word.

Definition rladderstepZ' var (T:=_) (a24 x0 : T) P1 P2
  := @MxDH.ladderstep_gen
       _
       (fun x y => LetIn (Pair x y) (invert_Abs (proj1_sig raddZ_sig var)))
       (fun x y => LetIn (Pair x y) (invert_Abs (proj1_sig rsubZ_sig var)))
       (fun x y => LetIn (Pair x y) (invert_Abs (proj1_sig rmulZ_sig var)))
       a24
       _
       (fun x y z w => (x, y, z, w)%expr)
       (fun v f => LetIn v
                         (fun k => f (SmartVarf k)))
       x0
       P1 P2.

Definition rladderstepZ'' : Syntax.Expr _ _ _
  := Linearize
       (ExprEta
          (fun var
           => Abs (fun a24_x0_P1_P2 : interp_flat_type _ (_ * _ * ((_ * _) * (_ * _)))
                   => let '(a24, x0, ((P10, P11), (P20, P21)))
                          := a24_x0_P1_P2 in
                      rladderstepZ'
                        var (SmartVarf a24) (SmartVarf x0)
                        (SmartVarf P10, SmartVarf P11)
                        (SmartVarf P20, SmartVarf P21)))).

Local Notation eta x := (fst x, snd x).

Definition ladderstep_other_assoc {F Fadd Fsub Fmul} a24 (X1:F) (P1 P2:F*F) : F*F*F*F :=
  Eval cbv beta delta [MxDH.ladderstep_gen] in
    @MxDH.ladderstep_gen
      F Fadd Fsub Fmul a24
      (F*F*F*F)
      (fun X3 Y3 Z3 T3 => (X3, Y3, Z3, T3))
      (fun x f => dlet y := x in f y)
      X1 P1 P2.

Definition uncurried_ladderstep
  := fun (a24_x0_P1_P2 : _ * _ * ((_ * _) * (_ * _)))
     => let a24 := fst (fst a24_x0_P1_P2) in
        let x0 := snd (fst a24_x0_P1_P2) in
        let '(P1, P2) := eta (snd a24_x0_P1_P2) in
        let '((P10, P11), (P20, P21)) := (eta P1, eta P2) in
        @ladderstep_other_assoc
          _ add sub mul
          a24 x0 (P10, P11) (P20, P21).

Local Notation rexpr_sigPf T uncurried_op rexprZ x :=
  (Interp interp_op (t:=T) rexprZ x = uncurried_op x)
    (only parsing).
Local Notation rexpr_sigP T uncurried_op rexprZ :=
  (forall x, rexpr_sigPf T uncurried_op rexprZ x)
    (only parsing).
Local Notation rexpr_sig T uncurried_op :=
  { rexprZ | rexpr_sigP T uncurried_op rexprZ }
    (only parsing).

Local Ltac fold_interpf' :=
  let k := (eval unfold interpf, interpf_step in (@interpf base_type interp_base_type op interp_op)) in
  let k' := fresh in
  let H := fresh in
  pose k as k';
  assert (H : @interpf base_type interp_base_type op interp_op = k') by reflexivity;
  change k with k'; clearbody k'; subst k'.

Local Ltac fold_interpf :=
  let k := (eval unfold interpf in (@interpf base_type interp_base_type op interp_op)) in
  let k' := fresh in
  let H := fresh in
  pose k as k';
  assert (H : @interpf base_type interp_base_type op interp_op = k') by reflexivity;
  change k with k'; clearbody k'; subst k';
  fold_interpf'.

Local Ltac repeat_step_interpf :=
  let k := (eval unfold interpf in (@interpf base_type interp_base_type op interp_op)) in
  let k' := fresh in
  let H := fresh in
  pose k as k';
  assert (H : @interpf base_type interp_base_type op interp_op = k') by reflexivity;
  repeat (unfold interpf_step at 1; change k with k' at 1);
  clearbody k'; subst k'.

Lemma rladderstepZ_sigP' : rexpr_sigP _ uncurried_ladderstep rladderstepZ''.
Proof.
  cbv [rladderstepZ''].
  intro x; rewrite InterpLinearize, InterpExprEta.
  cbv [domain interp_flat_type interp_base_type] in x.
  destruct_head' prod.
  cbv [invert_Abs domain codomain Interp interp SmartVarf smart_interp_flat_map fst snd].
  cbv [rladderstepZ' MxDH.ladderstep_gen uncurried_ladderstep SmartVarf smart_interp_flat_map]; simpl @fst; simpl @snd.
  repeat match goal with
         | [ |- appcontext[@proj1_sig ?A ?B ?v] ]
           => let k := fresh "f" in
              let k' := fresh "f" in
              let H := fresh in
              set (k := v);
                set (k' := @proj1_sig A B k);
                pose proof (proj2_sig k) as H;
                change (proj1_sig k) with k' in H;
                clearbody k'; clear k;
                  cbv beta in *
         end.
  cbv [Interp Curry.curry2] in *.
  unfold interpf, interpf_step; fold_interpf.
  cbv [ladderstep_other_assoc interp_flat_type GF25519.fe25519].
  Time
    abstract (
      repeat match goal with
             | [ |- (dlet x := ?y in @?z x) = (dlet x' := ?y' in @?z' x') ]
               => refine ((fun pf0 pf1 => @Proper_Let_In_nd_changebody _ _ Logic.eq _ y y' pf0 z z' pf1)
                            (_ : y = y')
                            (_ : forall x, z x = z' x));
                    cbv beta; intros;
                      [ cbv [Let_In Common.ExprBinOpT] | ]
             end;
        repeat match goal with
               | _ => rewrite !interpf_invert_Abs
               | _ => rewrite_hyp !*
               | _ => progress cbv [interp_base_type]
               | [ |- ?x = ?x ] => reflexivity
               | _ => rewrite <- !surjective_pairing
               end
    ).
Time Defined.
Lemma rladderstepZ_sigP : rexpr_sigP _ uncurried_ladderstep rladderstepZ''.
Proof.
  exact rladderstepZ_sigP'.
Qed.
Definition rladderstepZ_sig
  := exist (fun v => rexpr_sigP _ _ v) rladderstepZ'' rladderstepZ_sigP.

Definition rladderstep_input_bounds
  := (ExprUnOp_bounds, ExprUnOp_bounds,
      ((ExprUnOp_bounds, ExprUnOp_bounds),
       (ExprUnOp_bounds, ExprUnOp_bounds))).

Time Definition rladderstepW := Eval vm_compute in rword_of_Z rladderstepZ_sig.
Lemma rladderstepW_correct_and_bounded_gen : correct_and_bounded_genT rladderstepW rladderstepZ_sig.
Proof. Time rexpr_correct. Time Qed.
Definition rladderstep_output_bounds := Eval vm_compute in compute_bounds rladderstepW rladderstep_input_bounds.

Local Obligation Tactic := intros; vm_compute; constructor.

(*
Program Definition rladderstepW_correct_and_bounded
  := Expr9_4Op_correct_and_bounded
       rladderstepW uncurried_ladderstep rladderstepZ_sig rladderstepW_correct_and_bounded_gen
       _ _.
 *)

Local Open Scope string_scope.
Compute ("Ladderstep", compute_bounds_for_display rladderstepW rladderstep_input_bounds).
Compute ("Ladderstep overflows? ", sanity_compute rladderstepW rladderstep_input_bounds).
Compute ("Ladderstep overflows (error if it does)? ", sanity_check rladderstepW rladderstep_input_bounds).
