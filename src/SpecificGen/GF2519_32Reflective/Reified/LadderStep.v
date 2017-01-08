Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Crypto.SpecificGen.GF2519_32.
Require Export Crypto.SpecificGen.GF2519_32BoundedCommon.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Reflection.Z.Interpretations64.
Require Crypto.Reflection.Z.Interpretations64.Relations.
Require Import Crypto.Reflection.Z.Interpretations64.RelationsCombinations.
Require Import Crypto.Reflection.Z.Reify.
Require Export Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.InterpWfRel.
Require Import Crypto.Reflection.LinearizeInterp.
Require Import Crypto.Reflection.MapInterp.
Require Import Crypto.Reflection.MapInterpWf.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Spec.MxDH.
Require Import Crypto.SpecificGen.GF2519_32Reflective.Reified.Add.
Require Import Crypto.SpecificGen.GF2519_32Reflective.Reified.Sub.
Require Import Crypto.SpecificGen.GF2519_32Reflective.Reified.Mul.
Require Import Crypto.SpecificGen.GF2519_32Reflective.Common9_4Op.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.HList.
Require Import Crypto.Util.Tower.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.
Require Import Bedrock.Word.

(* XXX FIXME: Remove dummy code *)
Definition rladderstepZ' var (T:=_) (dummy0 dummy1 dummy2 a24 x0 : T) P1 P2
  := @MxDH.ladderstep_gen
       _
       (fun x y => ApplyBinOp (proj1_sig raddZ_sig var) x y)
       (fun x y => ApplyBinOp (proj1_sig rsubZ_sig var) x y)
       (fun x y => ApplyBinOp (proj1_sig rmulZ_sig var) x y)
       a24
       _
       (fun x y z w => (UnReturn x, UnReturn y, UnReturn z, UnReturn w)%expr)
       (fun v f => LetIn (UnReturn v)
                         (fun k => f (Return (SmartVarf k))))
       x0
       P1 P2.

Definition rladderstepZ'' : Syntax.Expr _ _ _ _
  := Linearize (fun var
                => apply9
                     (fun A B => SmartAbs (A := A) (B := B))
                     (fun dummy0 dummy1 dummy2 a24 x0 P10 P11 P20 P21
                      => rladderstepZ'
                           var (Return dummy0) (Return dummy1) (Return dummy2)
                           (Return a24) (Return x0)
                           (Return P10, Return P11)
                           (Return P20, Return P21))).

Definition ladderstep (T := _)
  := fun (dummy0 dummy1 dummy2 a24 x0 P10 P11 P20 P21 : T)
     => @MxDH.ladderstep_other_assoc
          _ add sub mul
          a24 x0 (P10, P11) (P20, P21).

Definition uncurried_ladderstep
  := apply9_nd
       (@uncurry_unop_fe2519_32)
       ladderstep.

Local Notation rexpr_sigP T uncurried_op rexprZ :=
  (interp_type_gen_rel_pointwise (fun _ => Logic.eq) (Interp interp_op (t:=T) rexprZ) uncurried_op)
    (only parsing).
Local Notation rexpr_sig T uncurried_op :=
  { rexprZ | rexpr_sigP T uncurried_op rexprZ }
    (only parsing).

Local Ltac repeat_step_interpf :=
  let k := (eval unfold interpf in (@interpf base_type interp_base_type op interp_op)) in
  let k' := fresh in
  let H := fresh in
  pose k as k';
  assert (H : @interpf base_type interp_base_type op interp_op = k') by reflexivity;
  repeat (unfold interpf_step at 1; change k with k' at 1);
  clearbody k'; subst k'.

Lemma interp_helper
      (f : Syntax.Expr base_type interp_base_type op ExprBinOpT)
      (x y : exprArg interp_base_type interp_base_type)
      (f' : GF2519_32.fe2519_32 -> GF2519_32.fe2519_32 -> GF2519_32.fe2519_32)
      (x' y' : GF2519_32.fe2519_32)
      (H : interp_type_gen_rel_pointwise
             (fun _ => Logic.eq)
             (Interp interp_op f) (uncurry_binop_fe2519_32 f'))
      (Hx : interpf interp_op (UnReturn x) = x')
      (Hy : interpf interp_op (UnReturn y) = y')
  : interpf interp_op (UnReturn (ApplyBinOp (f interp_base_type) x y)) = f' x' y'.
Proof.
  cbv [interp_type_gen_rel_pointwise ExprBinOpT uncurry_binop_fe2519_32 interp_flat_type] in H.
  simpl @interp_base_type in *.
  cbv [GF2519_32.fe2519_32] in x', y'.
  destruct_head' prod.
  rewrite <- H; clear H.
  cbv [ExprArgT] in *; simpl in *.
  rewrite Hx, Hy; clear Hx Hy.
  unfold Let_In; simpl.
  cbv [Interp].
  simpl @interp_type.
  change (fun t => interp_base_type t) with interp_base_type in *.
  generalize (f interp_base_type); clear f; intro f.
  cbv [Apply length_fe2519_32 Apply' interp fst snd].
  rewrite <- (UnAbs_eta f).
  repeat match goal with
         | [ |- appcontext[UnAbs ?f ?x] ]
           => generalize (UnAbs f x); clear f;
                let f' := fresh "f" in
                intro f';
                  first [ rewrite <- (UnAbs_eta f')
                        | rewrite <- (UnReturn_eta f') ]
         end.
  reflexivity.
Qed.

Lemma rladderstepZ_sigP : rexpr_sigP Expr9_4OpT uncurried_ladderstep rladderstepZ''.
Proof.
  cbv [rladderstepZ''].
  etransitivity; [ apply Interp_Linearize | ].
  cbv beta iota delta [apply9 apply9_nd interp_type_gen_rel_pointwise Expr9_4OpT SmartArrow ExprArgT rladderstepZ'' uncurried_ladderstep uncurry_unop_fe2519_32 SmartAbs rladderstepZ' exprArg MxDH.ladderstep_gen Interp interp unop_make_args SmartVarf smart_interp_flat_map length_fe2519_32 ladderstep].
  intros; cbv beta zeta.
  unfold UnReturn at 14 15 16 17.
  repeat match goal with
         | [ |- appcontext[@proj1_sig ?A ?B ?v] ]
           => let k := fresh "f" in
              let k' := fresh "f" in
              let H := fresh in
              set (k := v);
                set (k' := @proj1_sig A B k);
                pose proof (proj2_sig k) as H;
                change (proj1_sig k) with k' in H;
                clearbody k'; clear k
         end.
  unfold interpf; repeat_step_interpf.
  unfold interpf at 14 15 16; unfold interpf_step.
  cbv beta iota delta [MxDH.ladderstep_other_assoc].
  repeat match goal with
         | [ |- (dlet x := ?y in @?z x) = (let x' := ?y' in @?z' x') ]
           => refine ((fun pf0 pf1 => @Proper_Let_In_nd_changebody _ _ Logic.eq _ y y' pf0 z z' pf1)
                        (_ : y = y')
                        (_ : forall x, z x = z' x));
                cbv beta; intros
         end;
    repeat match goal with
           | [ |- interpf interp_op (UnReturn (ApplyBinOp _ _ _)) = _ ]
             => apply interp_helper; [ assumption | | ]
           | [ |- interpf interp_op (UnReturn (Return (_, _)%expr)) = (_, _) ]
             => vm_compute; reflexivity
           | [ |- (_, _) = (_, _) ]
             => reflexivity
           | _ => simpl; rewrite <- !surjective_pairing; reflexivity
           end.
Time Qed.

Definition rladderstepZ_sig : rexpr_9_4op_sig ladderstep.
Proof.
  eexists.
  apply rladderstepZ_sigP.
Defined.

Time Definition rladderstepW := Eval vm_compute in rword_of_Z rladderstepZ_sig.
Lemma rladderstepW_correct_and_bounded_gen : correct_and_bounded_genT rladderstepW rladderstepZ_sig.
Proof. Time rexpr_correct. Time Qed.
Definition rladderstep_output_bounds := Eval vm_compute in compute_bounds rladderstepW Expr9Op_bounds.

Local Obligation Tactic := intros; vm_compute; constructor.

Program Definition rladderstepW_correct_and_bounded
  := Expr9_4Op_correct_and_bounded
       rladderstepW ladderstep rladderstepZ_sig rladderstepW_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("Ladderstep", compute_bounds_for_display rladderstepW Expr9Op_bounds).
Compute ("Ladderstep overflows? ", sanity_compute rladderstepW Expr9Op_bounds).
Compute ("Ladderstep overflows (error if it does)? ", sanity_check rladderstepW Expr9Op_bounds).
