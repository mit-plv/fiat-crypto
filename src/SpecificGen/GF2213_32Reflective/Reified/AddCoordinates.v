Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Crypto.SpecificGen.GF2213_32.
Require Export Crypto.SpecificGen.GF2213_32BoundedCommon.
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
Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Require Import Crypto.SpecificGen.GF2213_32Reflective.Reified.Add.
Require Import Crypto.SpecificGen.GF2213_32Reflective.Reified.Sub.
Require Import Crypto.SpecificGen.GF2213_32Reflective.Reified.Mul.
Require Import Crypto.SpecificGen.GF2213_32Reflective.Common9_4Op.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.HList.
Require Import Crypto.Util.Tower.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.
Require Import Bedrock.Word.

Definition radd_coordinatesZ' var twice_d P1 P2
  := @Extended.add_coordinates_gen
       _
       (fun x y => ApplyBinOp (proj1_sig raddZ_sig var) x y)
       (fun x y => ApplyBinOp (proj1_sig rsubZ_sig var) x y)
       (fun x y => ApplyBinOp (proj1_sig rmulZ_sig var) x y)
       twice_d _
       (fun x y z w => (UnReturn x, UnReturn y, UnReturn z, UnReturn w)%expr)
       (fun v f => LetIn (UnReturn v)
                         (fun k => f (Return (SmartVarf k))))
       P1 P2.

Definition radd_coordinatesZ'' : Syntax.Expr _ _ _ _
  := Linearize (fun var
                => apply9
                     (fun A B => SmartAbs (A := A) (B := B))
                     (fun twice_d P10 P11 P12 P13 P20 P21 P22 P23
                      => radd_coordinatesZ'
                           var (Return twice_d)
                           (Return P10, Return P11, Return P12, Return P13)
                           (Return P20, Return P21, Return P22, Return P23))).

Definition add_coordinates
  := fun twice_d P10 P11 P12 P13 P20 P21 P22 P23
     => @Extended.add_coordinates
          _ add sub mul
          twice_d (P10, P11, P12, P13) (P20, P21, P22, P23).

Definition uncurried_add_coordinates
  := apply9_nd
       (@uncurry_unop_fe2213_32)
       add_coordinates.

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
      (f' : GF2213_32.fe2213_32 -> GF2213_32.fe2213_32 -> GF2213_32.fe2213_32)
      (x' y' : GF2213_32.fe2213_32)
      (H : interp_type_gen_rel_pointwise
             (fun _ => Logic.eq)
             (Interp interp_op f) (uncurry_binop_fe2213_32 f'))
      (Hx : interpf interp_op (UnReturn x) = x')
      (Hy : interpf interp_op (UnReturn y) = y')
  : interpf interp_op (UnReturn (ApplyBinOp (f interp_base_type) x y)) = f' x' y'.
Proof.
  cbv [interp_type_gen_rel_pointwise ExprBinOpT uncurry_binop_fe2213_32 interp_flat_type] in H.
  simpl @interp_base_type in *.
  cbv [GF2213_32.fe2213_32] in x', y'.
  destruct_head' prod.
  rewrite <- H; clear H.
  cbv [ExprArgT] in *; simpl in *.
  rewrite Hx, Hy; clear Hx Hy.
  unfold Let_In; simpl.
  cbv [Interp].
  simpl @interp_type.
  change (fun t => interp_base_type t) with interp_base_type in *.
  generalize (f interp_base_type); clear f; intro f.
  cbv [Apply length_fe2213_32 Apply' interp fst snd].
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

Lemma radd_coordinatesZ_sigP : rexpr_sigP Expr9_4OpT uncurried_add_coordinates radd_coordinatesZ''.
Proof.
  cbv [radd_coordinatesZ''].
  etransitivity; [ apply Interp_Linearize | ].
  cbv beta iota delta [apply9 apply9_nd interp_type_gen_rel_pointwise Expr9_4OpT SmartArrow ExprArgT radd_coordinatesZ'' uncurried_add_coordinates uncurry_unop_fe2213_32 SmartAbs radd_coordinatesZ' exprArg Extended.add_coordinates_gen Interp interp unop_make_args SmartVarf smart_interp_flat_map length_fe2213_32 add_coordinates].
  intros.
  unfold UnReturn at 13 14 15 16.
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
  unfold interpf at 13 14 15; unfold interpf_step.
  cbv beta iota delta [Extended.add_coordinates].
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

Definition radd_coordinatesZ_sig : rexpr_9_4op_sig add_coordinates.
Proof.
  eexists.
  apply radd_coordinatesZ_sigP.
Defined.

Time Definition radd_coordinatesW := Eval vm_compute in rword_of_Z radd_coordinatesZ_sig.
Lemma radd_coordinatesW_correct_and_bounded_gen : correct_and_bounded_genT radd_coordinatesW radd_coordinatesZ_sig.
Proof. Time rexpr_correct. Time Qed.
Definition radd_coordinates_output_bounds := Eval vm_compute in compute_bounds radd_coordinatesW Expr9Op_bounds.

Local Obligation Tactic := intros; vm_compute; constructor.

Program Definition radd_coordinatesW_correct_and_bounded
  := Expr9_4Op_correct_and_bounded
       radd_coordinatesW add_coordinates radd_coordinatesZ_sig radd_coordinatesW_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("Add_Coordinates", compute_bounds_for_display radd_coordinatesW ExprAC_bounds).
Compute ("Add_Coordinates overflows? ", sanity_compute radd_coordinatesW ExprAC_bounds).
Compute ("Add_Coordinates overflows (error if it does)? ", sanity_check radd_coordinatesW ExprAC_bounds).
