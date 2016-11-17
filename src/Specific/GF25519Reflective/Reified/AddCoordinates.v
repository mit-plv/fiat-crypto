Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Crypto.Specific.GF25519.
Require Export Crypto.Specific.GF25519BoundedCommon.
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
Require Import Crypto.Specific.GF25519Reflective.Reified.Add.
Require Import Crypto.Specific.GF25519Reflective.Reified.Sub.
Require Import Crypto.Specific.GF25519Reflective.Reified.Mul.
Require Import Crypto.Specific.GF25519Reflective.CommonBinOp.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ZUtil.
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

Definition radd_coordinatesT : type base_type.
Proof.
  match type of radd_coordinatesZ'' with
  | Syntax.Expr _ _ _ ?T => exact T
  end.
Defined.

Local Notation rexpr_sigP T uncurried_op rexprZ :=
  (interp_type_gen_rel_pointwise (fun _ => Logic.eq) (Interp interp_op (t:=T) rexprZ) uncurried_op)
    (only parsing).
Local Notation rexpr_sig T uncurried_op :=
  { rexprZ | rexpr_sigP T uncurried_op rexprZ }
    (only parsing).

Definition uncurried_add_coordinates
  := apply9_nd
       (@uncurry_unop_fe25519)
       (fun twice_d P10 P11 P12 P13 P20 P21 P22 P23
        => @Extended.add_coordinates
             _ add sub mul
             twice_d (P10, P11, P12, P13) (P20, P21, P22, P23)).


Local Ltac fold_interpf_at_1 :=
  let k := (eval unfold interpf in (@interpf base_type interp_base_type op interp_op)) in
  change k with (@interpf base_type interp_base_type op interp_op) at 1.
Local Ltac step_interpf :=
  unfold interpf_step at 1; fold_interpf_at_1.
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
      (f' : GF25519.fe25519 -> GF25519.fe25519 -> GF25519.fe25519)
      (x' y' : GF25519.fe25519)
      (H : interp_type_gen_rel_pointwise
             (fun _ => Logic.eq)
             (Interp interp_op f) (uncurry_binop_fe25519 f'))
      (Hx : interpf interp_op (UnReturn x) = x')
      (Hy : interpf interp_op (UnReturn y) = y')
  : interpf interp_op (UnReturn (ApplyBinOp (f interp_base_type) x y)) = f' x' y'.
Proof.
  cbv [interp_type_gen_rel_pointwise ExprBinOpT uncurry_binop_fe25519 interp_flat_type] in H.
  simpl @interp_base_type in *.
  cbv [GF25519.fe25519] in x', y'.
  destruct_head' prod.
  rewrite <- H; clear H.
  cbv [ExprArgT] in *; simpl in *.
  rewrite Hx, Hy; clear Hx Hy.
  unfold Let_In; simpl.
  cbv [Interp].
  simpl @interp_type.
  change (fun t => interp_base_type t) with interp_base_type in *.
  generalize (f interp_base_type); clear f; intro f.
  cbv [Apply length_fe25519 Apply' interp fst snd].
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

Lemma radd_coordinatesZ_sigP : rexpr_sigP radd_coordinatesT uncurried_add_coordinates radd_coordinatesZ''.
Proof.
  cbv [radd_coordinatesZ''].
  etransitivity; [ apply Interp_Linearize | ].
  cbv beta iota delta [apply9 apply9_nd interp_type_gen_rel_pointwise radd_coordinatesT SmartArrow ExprArgT radd_coordinatesZ'' uncurried_add_coordinates uncurry_unop_fe25519 SmartAbs radd_coordinatesZ' exprArg Extended.add_coordinates_gen Interp interp unop_make_args SmartVarf smart_interp_flat_map length_fe25519].
  intros.
  repeat match goal with
         | [ |- appcontext[@proj1_sig ?A ?B ?v] ]
           => let k := fresh "f" in
              let k' := fresh "f" in
              let H := fresh in
              set (k := v);
                set (k' := @proj1_sig A B k);
                pose proof (proj2_sig k) as H;
                change (proj1_sig k) with k' in H(*;
                cbv [interp_type_gen_rel_pointwise ExprBinOpT uncurry_binop_fe25519] in H*)
         end.
  unfold UnReturn at 13 14 15 16.
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

Definition radd_coordinatesZ_sig : rexpr_sig radd_coordinatesT uncurried_add_coordinates.
Proof.
  eexists.
  apply radd_coordinatesZ_sigP.
Defined.

Local Ltac bounds_from_list ls :=
  lazymatch (eval hnf in ls) with
  | (?x :: nil)%list => constr:(Some {| Bounds.lower := fst x ; Bounds.upper := snd x |})
  | (?x :: ?xs)%list => let bs := bounds_from_list xs in
                        constr:((Some {| Bounds.lower := fst x ; Bounds.upper := snd x |}, bs))
  end.

Local Ltac make_bounds ls :=
  compute;
  let v := bounds_from_list (List.rev ls) in
  let v := (eval compute in v) in
  exact v.

Definition ExprAC_bounds : interp_all_binders_for radd_coordinatesT ZBounds.interp_base_type.
Proof.
  make_bounds ((Tuple.to_list _ bounds)
                 ++ Tuple.to_list _ bounds ++ Tuple.to_list _ bounds ++ Tuple.to_list _ bounds ++ Tuple.to_list _ bounds
                 ++ Tuple.to_list _ bounds ++ Tuple.to_list _ bounds ++ Tuple.to_list _ bounds ++ Tuple.to_list _ bounds)%list.
Defined.

Time Definition radd_coordinatesW := Eval vm_compute in rword_of_Z radd_coordinatesZ_sig.
Lemma radd_coordinatesW_correct_and_bounded_gen : correct_and_bounded_genT radd_coordinatesW radd_coordinatesZ_sig.
Proof. Time rexpr_correct. Time Qed.
Definition radd_coordinates_output_bounds := Eval vm_compute in compute_bounds radd_coordinatesW ExprAC_bounds.
(*Notation i9op_correct_and_bounded irop op
  := (forall x0 x1 x2 x3 x4 x5 x6 x7 x8,
         is_bounded (fe25519WToZ x0) = true
         -> is_bounded (fe25519WToZ x1) = true
         -> is_bounded (fe25519WToZ x2) = true
         -> is_bounded (fe25519WToZ x3) = true
         -> is_bounded (fe25519WToZ x4) = true
         -> is_bounded (fe25519WToZ x5) = true
         -> is_bounded (fe25519WToZ x6) = true
         -> is_bounded (fe25519WToZ x7) = true
         -> is_bounded (fe25519WToZ x8) = true
         -> fe25519WToZ (irop x0 x1 x2 x3 x4 x5 x6 x7 x8) = op (fe25519WToZ x0) (fe25519WToZ x1) (fe25519WToZ x2) (fe25519WToZ x3) (fe25519WToZ x4) (fe25519WToZ x5) (fe25519WToZ x6) (fe25519WToZ x7) (fe25519WToZ x8)
            /\ is_bounded (fe25519WToZ (irop x0 x1 x2 x3 x4 x5 x6 x7 x8)) = true) (only parsing).

Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition radd_coordinatesW_correct_and_bounded
  := ExprBinOp_correct_and_bounded
       radd_coordinatesW add_coordinates radd_coordinatesZ_sig radd_coordinatesW_correct_and_bounded_gen
       _ _.*)

Local Open Scope string_scope.
Compute ("Add_Coordinates", compute_bounds_for_display radd_coordinatesW ExprAC_bounds).
Compute ("Add_Coordinates overflows? ", sanity_compute radd_coordinatesW ExprAC_bounds).
Compute ("Add_Coordinates overflows (error if it does)? ", sanity_check radd_coordinatesW ExprAC_bounds).
