Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Crypto.Specific.GF25519.
Require Import Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Z.Interpretations.
Require Crypto.Reflection.Z.Interpretations.Relations.
Require Import Crypto.Reflection.Z.Interpretations.RelationsCombinations.
Require Import Crypto.Reflection.Z.Reify.
Require Export Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.InterpWfRel.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.MapInterp.
Require Import Crypto.Reflection.MapInterpWf.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

Notation Expr := (Expr base_type Word64.interp_base_type op).

Local Ltac make_type_from uncurried_op :=
  let T := (type of uncurried_op) in
  let T := (eval compute in T) in
  let rT := reify_type T in
  exact rT.

Definition ExprBinOpT : type base_type.
Proof. make_type_from (uncurry_binop_fe25519 carry_add). Defined.
Definition ExprUnOpT : type base_type.
Proof. make_type_from (uncurry_unop_fe25519 carry_opp). Defined.
Definition ExprUnOpFEToZT : type base_type.
Proof. make_type_from (uncurry_unop_fe25519 ge_modulus). Defined.
Definition ExprUnOpWireToFET : type base_type.
Proof. make_type_from (uncurry_unop_wire_digits unpack). Defined.
Definition ExprUnOpFEToWireT : type base_type.
Proof. make_type_from (uncurry_unop_fe25519 pack). Defined.
Definition ExprBinOp : Type := Expr ExprBinOpT.
Definition ExprUnOp : Type := Expr ExprUnOpT.
Definition ExprUnOpFEToZ : Type := Expr ExprUnOpFEToZT.
Definition ExprUnOpWireToFE : Type := Expr ExprUnOpWireToFET.
Definition ExprUnOpFEToWire : Type := Expr ExprUnOpFEToWireT.

Local Ltac bounds_from_list ls :=
  lazymatch (eval hnf in ls) with
  | (?x :: nil)%list => constr:(Some {| ZBounds.lower := fst x ; ZBounds.upper := snd x |})
  | (?x :: ?xs)%list => let bs := bounds_from_list xs in
                        constr:((Some {| ZBounds.lower := fst x ; ZBounds.upper := snd x |}, bs))
  end.

Local Ltac make_bounds ls :=
  compute;
  let v := bounds_from_list (List.rev ls) in
  let v := (eval compute in v) in
  exact v.

Definition ExprBinOp_bounds : interp_all_binders_for ExprBinOpT ZBounds.interp_base_type.
Proof. make_bounds (Tuple.to_list _ bounds ++ Tuple.to_list _ bounds)%list. Defined.
Definition ExprUnOp_bounds : interp_all_binders_for ExprUnOpT ZBounds.interp_base_type.
Proof. make_bounds (Tuple.to_list _ bounds). Defined.
Definition ExprUnOpFEToZ_bounds : interp_all_binders_for ExprUnOpFEToZT ZBounds.interp_base_type.
Proof. make_bounds (Tuple.to_list _ bounds). Defined.
Definition ExprUnOpFEToWire_bounds : interp_all_binders_for ExprUnOpFEToWireT ZBounds.interp_base_type.
Proof. make_bounds (Tuple.to_list _ bounds). Defined.
Definition ExprUnOpWireToFE_bounds : interp_all_binders_for ExprUnOpWireToFET ZBounds.interp_base_type.
Proof. make_bounds (Tuple.to_list _ wire_digit_bounds). Defined.

Definition interp_bexpr : ExprBinOp -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := fun e => curry_binop_fe25519W (Interp (@Word64.interp_op) e).
Definition interp_uexpr : ExprUnOp -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := fun e => curry_unop_fe25519W (Interp (@Word64.interp_op) e).
Definition interp_uexpr_FEToZ : ExprUnOpFEToZ -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.word64
  := fun e => curry_unop_fe25519W (Interp (@Word64.interp_op) e).
Definition interp_uexpr_FEToWire : ExprUnOpFEToWire -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.wire_digitsW
  := fun e => curry_unop_fe25519W (Interp (@Word64.interp_op) e).
Definition interp_uexpr_WireToFE : ExprUnOpWireToFE -> Specific.GF25519BoundedCommon.wire_digitsW -> Specific.GF25519BoundedCommon.fe25519W
  := fun e => curry_unop_wire_digitsW (Interp (@Word64.interp_op) e).

Notation binop_correct_and_bounded rop op
  := (ibinop_correct_and_bounded (interp_bexpr rop) op) (only parsing).
Notation unop_correct_and_bounded rop op
  := (iunop_correct_and_bounded (interp_uexpr rop) op) (only parsing).
Notation unop_FEToZ_correct rop op
  := (iunop_FEToZ_correct (interp_uexpr_FEToZ rop) op) (only parsing).
Notation unop_FEToWire_correct_and_bounded rop op
  := (iunop_FEToWire_correct_and_bounded (interp_uexpr_FEToWire rop) op) (only parsing).
Notation unop_WireToFE_correct_and_bounded rop op
  := (iunop_WireToFE_correct_and_bounded (interp_uexpr_WireToFE rop) op) (only parsing).

Ltac rexpr_cbv :=
  lazymatch goal with
  | [ |- { rexpr | interp_type_gen_rel_pointwise _ (Interp _ (t:=?T) rexpr) (?uncurry ?oper) } ]
    => let operf := head oper in
       let uncurryf := head uncurry in
       try cbv delta [T]; try cbv delta [oper];
       try cbv beta iota delta [uncurryf]
  end;
  cbv beta iota delta [interp_flat_type Z.interp_base_type interp_base_type zero_].

Ltac reify_sig :=
  rexpr_cbv; eexists; Reify_rhs; reflexivity.

Local Notation rexpr_sig T uncurried_op :=
  { rexprZ
  | interp_type_gen_rel_pointwise (fun _ => Logic.eq) (Interp interp_op (t:=T) rexprZ) uncurried_op }
    (only parsing).

Notation rexpr_binop_sig op := (rexpr_sig ExprBinOpT (uncurry_binop_fe25519 op)) (only parsing).
Notation rexpr_unop_sig op := (rexpr_sig ExprUnOpT (uncurry_unop_fe25519 op)) (only parsing).
Notation rexpr_unop_FEToZ_sig op := (rexpr_sig ExprUnOpFEToZT (uncurry_unop_fe25519 op)) (only parsing).
Notation rexpr_unop_FEToWire_sig op := (rexpr_sig ExprUnOpFEToWireT (uncurry_unop_fe25519 op)) (only parsing).
Notation rexpr_unop_WireToFE_sig op := (rexpr_sig ExprUnOpWireToFET (uncurry_unop_wire_digits op)) (only parsing).

Notation correct_and_bounded_genT ropW'v ropZ_sigv
  := (let ropW' := ropW'v in
      let ropZ_sig := ropZ_sigv in
      let ropW := MapInterp (fun _ x => x) ropW' in
      let ropZ := MapInterp Word64.to_Z ropW' in
      let ropBounds := MapInterp ZBounds.of_word64 ropW' in
      let ropBoundedWord64 := MapInterp BoundedWord64.of_word64 ropW' in
      ropZ = proj1_sig ropZ_sig
      /\ interp_type_rel_pointwise2 Relations.related_Z (Interp (@BoundedWord64.interp_op) ropBoundedWord64) (Interp (@Z.interp_op) ropZ)
      /\ interp_type_rel_pointwise2 Relations.related_bounds (Interp (@BoundedWord64.interp_op) ropBoundedWord64) (Interp (@ZBounds.interp_op) ropBounds)
      /\ interp_type_rel_pointwise2 Relations.related_word64 (Interp (@BoundedWord64.interp_op) ropBoundedWord64) (Interp (@Word64.interp_op) ropW))
       (only parsing).

Local Ltac args_to_bounded_helper v :=
  lazymatch v with
  | (?x, ?xs)
    => args_to_bounded_helper x; [ .. | args_to_bounded_helper xs ]
  | ?w
    => try refine (_, _); [ refine {| BoundedWord64.value := w |} | .. ]
  end.

Local Ltac make_args x :=
  let x' := fresh "x'" in
  pose (x : id _) as x';
  cbv [fe25519W wire_digitsW] in x; destruct_head' prod;
  cbv [fst snd] in *;
  simpl @fe25519WToZ in *;
  simpl @wire_digitsWToZ in *;
  let T := fresh in
  evar (T : Type);
  cut T; subst T;
  [ let H := fresh in
    intro H;
    let xv := (eval hnf in x') in
    args_to_bounded_helper xv;
    [ destruct_head' and;
      match goal with
      | [ H : ?T |- _ ] => is_evar T; refine (proj1 H)
      end.. ]
  | repeat match goal with H : is_bounded _ = true |- _ => unfold_is_bounded_in H end;
    repeat match goal with H : wire_digits_is_bounded _ = true |- _ => unfold_is_bounded_in H end;
    destruct_head' and;
    Z.ltb_to_lt;
    repeat first [ eexact I
                 | apply conj;
                   [ repeat apply conj; [ | eassumption | eassumption | ];
                     vm_compute; [ refine (fun x => match x with eq_refl => I end) | reflexivity ]
                   | ] ] ].

Local Ltac app_tuples x y :=
  let tx := type of x in
  lazymatch (eval hnf in tx) with
  | prod _ _ => let xs := app_tuples (snd x) y in
                constr:((fst x, xs))
  | _ => constr:((x, y))
  end.

Class is_evar {T} (x : T) := make_is_evar : True.
Hint Extern 0 (is_evar ?e) => is_evar e; exact I : typeclass_instances.

Definition unop_args_to_bounded (x : fe25519W) (H : is_bounded (fe25519WToZ x) = true)
  : interp_flat_type (fun _ => BoundedWord64.BoundedWord) (all_binders_for ExprUnOpT).
Proof. make_args x. Defined.
Definition unopWireToFE_args_to_bounded (x : wire_digitsW) (H : wire_digits_is_bounded (wire_digitsWToZ x) = true)
  : interp_flat_type (fun _ => BoundedWord64.BoundedWord) (all_binders_for ExprUnOpWireToFET).
Proof. make_args x. Defined.
Definition binop_args_to_bounded (x : fe25519W * fe25519W)
           (H : is_bounded (fe25519WToZ (fst x)) = true)
           (H' : is_bounded (fe25519WToZ (snd x)) = true)
  : interp_flat_type (fun _ => BoundedWord64.BoundedWord) (all_binders_for ExprBinOpT).
Proof.
  let v := app_tuples (unop_args_to_bounded (fst x) H) (unop_args_to_bounded (snd x) H') in
  exact v.
Defined.

Ltac assoc_right_tuple x so_far :=
  let t := type of x in
  lazymatch (eval hnf in t) with
  | prod _ _ => let so_far := assoc_right_tuple (snd x) so_far in
                assoc_right_tuple (fst x) so_far
  | _ => lazymatch so_far with
         | @None => x
         | _ => constr:((x, so_far))
         end
  end.

Local Ltac make_bounds_prop bounds orig_bounds :=
  let bounds' := fresh "bounds'" in
  let bounds_bad := fresh "bounds_bad" in
  rename bounds into bounds_bad;
  let boundsv := assoc_right_tuple bounds_bad (@None) in
  pose boundsv as bounds;
  pose orig_bounds as bounds';
  repeat (refine (match fst bounds' with
                  | Some bounds' => let (l, u) := fst bounds in
                                    let (l', u') := bounds' in
                                    ((l' <=? l) && (u <=? u'))%Z%bool
                  | None => false
                  end && _)%bool;
          destruct bounds' as [_ bounds'], bounds as [_ bounds]);
  try exact (match bounds' with
             | Some bounds' => let (l, u) := bounds in
                               let (l', u') := bounds' in
                               ((l' <=? l) && (u <=? u'))%Z%bool
             | None => false
             end).


Definition unop_bounds_good (bounds : interp_flat_type (fun _ => ZBounds.bounds) (remove_all_binders ExprUnOpT)) : bool.
Proof. make_bounds_prop bounds ExprUnOp_bounds. Defined.
Definition binop_bounds_good (bounds : interp_flat_type (fun _ => ZBounds.bounds) (remove_all_binders ExprBinOpT)) : bool.
Proof. make_bounds_prop bounds ExprUnOp_bounds. Defined.
Definition unopFEToWire_bounds_good (bounds : interp_flat_type (fun _ => ZBounds.bounds) (remove_all_binders ExprUnOpFEToWireT)) : bool.
Proof. make_bounds_prop bounds ExprUnOpWireToFE_bounds. Defined.
Definition unopWireToFE_bounds_good (bounds : interp_flat_type (fun _ => ZBounds.bounds) (remove_all_binders ExprUnOpWireToFET)) : bool.
Proof. make_bounds_prop bounds ExprUnOp_bounds. Defined.
(* TODO FIXME(jgross?, andreser?): Is every function returning a single Z a boolean function? *)
Definition unopFEToZ_bounds_good (bounds : interp_flat_type (fun _ => ZBounds.bounds) (remove_all_binders ExprUnOpFEToZT)) : bool.
Proof.
  refine (let (l, u) := bounds in ((0 <=? l) && (u <=? 1))%Z%bool).
Defined.

(* FIXME TODO(jgross): This is a horrible tactic.  We should unify the
    various kinds of correct and boundedness, and abstract in Gallina
    rather than Ltac *)

Local Ltac t_correct_and_bounded ropZ_sig Hbounds H0 H1 args :=
  let Heq := fresh "Heq" in
  let Hbounds0 := fresh "Hbounds0" in
  let Hbounds1 := fresh "Hbounds1" in
  let Hbounds2 := fresh "Hbounds2" in
  pose proof (proj2_sig ropZ_sig) as Heq;
  cbv [interp_bexpr interp_uexpr interp_uexpr_FEToWire interp_uexpr_FEToZ interp_uexpr_WireToFE
                    curry_binop_fe25519W curry_unop_fe25519W curry_unop_wire_digitsW
                    curry_binop_fe25519 curry_unop_fe25519 curry_unop_wire_digits
                    uncurry_binop_fe25519W uncurry_unop_fe25519W uncurry_unop_wire_digitsW
                    uncurry_binop_fe25519 uncurry_unop_fe25519 uncurry_unop_wire_digits
                    ExprBinOpT ExprUnOpFEToWireT ExprUnOpT ExprUnOpFEToZT ExprUnOpWireToFET
                    interp_type_gen_rel_pointwise interp_type_gen_rel_pointwise] in *;
  cbv zeta in *;
  simpl @fe25519WToZ; simpl @wire_digitsWToZ;
  rewrite <- Heq; clear Heq;
  destruct Hbounds as [Heq Hbounds];
  change interp_op with (@Z.interp_op) in *;
  change interp_base_type with (@Z.interp_base_type) in *;
  rewrite <- Heq; clear Heq;
  destruct Hbounds as [ Hbounds0 [Hbounds1 Hbounds2] ];
  pose proof (fun pf => Relations.uncurry_interp_type_rel_pointwise2_proj_from_option2 Word64.to_Z pf Hbounds2 Hbounds0) as Hbounds_left;
  pose proof (fun pf => Relations.uncurry_interp_type_rel_pointwise2_proj1_from_option2 Relations.related_word64_boundsi' pf Hbounds1 Hbounds2) as Hbounds_right;
  specialize_by repeat first [ progress intros
                             | reflexivity
                             | assumption
                             | progress destruct_head' base_type
                             | progress destruct_head' BoundedWord64.BoundedWord
                             | progress destruct_head' and
                             | progress repeat apply conj ];
  specialize (Hbounds_left args H0);
  specialize (Hbounds_right args H0);
  cbv beta in *;
  lazymatch type of Hbounds_right with
  | match ?e with _ => _ end
    => lazymatch type of H1 with
       | match ?e' with _ => _ end
         => change e' with e in H1; destruct e eqn:?; [ | exfalso; assumption ]
       end
  end;
  repeat match goal with x := _ |- _ => subst x end;
  cbv [id
         binop_args_to_bounded unop_args_to_bounded unopWireToFE_args_to_bounded
         Relations.proj_eq_rel interp_flat_type_rel_pointwise2 SmartVarfMap interp_flat_type smart_interp_flat_map Application.all_binders_for fst snd BoundedWord64.to_word64' BoundedWord64.boundedWordToWord64 BoundedWord64.value Application.ApplyInterpedAll Application.fst_binder Application.snd_binder interp_flat_type_rel_pointwise2_gen_Prop Relations.related_word64_boundsi' Relations.related'_word64_bounds ZBounds.upper ZBounds.lower Application.remove_all_binders Word64.to_Z] in Hbounds_left, Hbounds_right;
  match goal with
  | [ |- fe25519WToZ ?x = _ /\ _ ]
    => destruct x; destruct_head_hnf' prod
  | [ |- wire_digitsWToZ ?x = _ /\ _ ]
    => destruct x; destruct_head_hnf' prod
  | [ |- _ = _ ]
    => exact Hbounds_left
  end;
  change word64ToZ with Word64.word64ToZ in *;
  (split; [ exact Hbounds_left | ]);
  cbv [interp_flat_type] in *;
  cbv [fst snd
           binop_bounds_good unop_bounds_good unopFEToWire_bounds_good unopWireToFE_bounds_good unopFEToZ_bounds_good
           ExprUnOp_bounds ExprBinOp_bounds ExprUnOpFEToWire_bounds ExprUnOpFEToZ_bounds ExprUnOpWireToFE_bounds] in H1;
  destruct_head' ZBounds.bounds;
  unfold_is_bounded_in H1;
  simpl @fe25519WToZ; simpl @wire_digitsWToZ;
  unfold_is_bounded;
  destruct_head' and;
  Z.ltb_to_lt;
  change Word64.word64ToZ with word64ToZ in *;
  repeat apply conj; Z.ltb_to_lt; try omega; try reflexivity.

Local Opaque Interp.
Lemma ExprBinOp_correct_and_bounded
      ropW op (ropZ_sig : rexpr_binop_sig op)
      (Hbounds : correct_and_bounded_genT ropW ropZ_sig)
      (H0 : forall xy
                   (xy := (eta_fe25519W (fst xy), eta_fe25519W (snd xy)))
                   (Hxy : is_bounded (fe25519WToZ (fst xy)) = true
                          /\ is_bounded (fe25519WToZ (snd xy)) = true),
          let Hx := let (Hx, Hy) := Hxy in Hx in
          let Hy := let (Hx, Hy) := Hxy in Hy in
          let args := binop_args_to_bounded xy Hx Hy in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@BoundedWord64.interp_op) (MapInterp BoundedWord64.of_word64 ropW))
                                    (LiftOption.to' (Some args)))
          with
          | Some _ => True
          | None => False
          end)
      (H1 : forall xy
                   (xy := (eta_fe25519W (fst xy), eta_fe25519W (snd xy)))
                   (Hxy : is_bounded (fe25519WToZ (fst xy)) = true
                          /\ is_bounded (fe25519WToZ (snd xy)) = true),
          let Hx := let (Hx, Hy) := Hxy in Hx in
          let Hy := let (Hx, Hy) := Hxy in Hy in
          let args := binop_args_to_bounded (fst xy, snd xy) Hx Hy in
          let x' := SmartVarfMap (fun _ : base_type => BoundedWord64.to_bounds') args in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@ZBounds.interp_op) (MapInterp ZBounds.of_word64 ropW)) (LiftOption.to' (Some x')))
          with
          | Some bounds => binop_bounds_good bounds = true
          | None => False
          end)
  : binop_correct_and_bounded (MapInterp (fun _ x => x) ropW) op.
Proof.
  intros x y Hx Hy.
  pose x as x'; pose y as y'.
  hnf in x, y; destruct_head' prod.
  specialize (H0 (x', y') (conj Hx Hy)).
  specialize (H1 (x', y') (conj Hx Hy)).
  let args := constr:(binop_args_to_bounded (x', y') Hx Hy) in
  t_correct_and_bounded ropZ_sig Hbounds H0 H1 args.
Qed.

Lemma ExprUnOp_correct_and_bounded
      ropW op (ropZ_sig : rexpr_unop_sig op)
      (Hbounds : correct_and_bounded_genT ropW ropZ_sig)
      (H0 : forall x
                   (x := eta_fe25519W x)
                   (Hx : is_bounded (fe25519WToZ x) = true),
          let args := unop_args_to_bounded x Hx in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@BoundedWord64.interp_op) (MapInterp BoundedWord64.of_word64 ropW))
                                    (LiftOption.to' (Some args)))
          with
          | Some _ => True
          | None => False
          end)
      (H1 : forall x
                   (x := eta_fe25519W x)
                   (Hx : is_bounded (fe25519WToZ x) = true),
          let args := unop_args_to_bounded x Hx in
          let x' := SmartVarfMap (fun _ : base_type => BoundedWord64.to_bounds') args in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@ZBounds.interp_op) (MapInterp ZBounds.of_word64 ropW)) (LiftOption.to' (Some x')))
          with
          | Some bounds => unop_bounds_good bounds = true
          | None => False
          end)
  : unop_correct_and_bounded (MapInterp (fun _ x => x) ropW) op.
Proof.
  intros x Hx.
  pose x as x'.
  hnf in x; destruct_head' prod.
  specialize (H0 x' Hx).
  specialize (H1 x' Hx).
  let args := constr:(unop_args_to_bounded x' Hx) in
  t_correct_and_bounded ropZ_sig Hbounds H0 H1 args.
Qed.

Lemma ExprUnOpFEToWire_correct_and_bounded
      ropW op (ropZ_sig : rexpr_unop_FEToWire_sig op)
      (Hbounds : correct_and_bounded_genT ropW ropZ_sig)
      (H0 : forall x
                   (x := eta_fe25519W x)
                   (Hx : is_bounded (fe25519WToZ x) = true),
          let args := unop_args_to_bounded x Hx in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@BoundedWord64.interp_op) (MapInterp BoundedWord64.of_word64 ropW))
                                    (LiftOption.to' (Some args)))
          with
          | Some _ => True
          | None => False
          end)
      (H1 : forall x
                   (x := eta_fe25519W x)
                   (Hx : is_bounded (fe25519WToZ x) = true),
          let args := unop_args_to_bounded x Hx in
          let x' := SmartVarfMap (fun _ : base_type => BoundedWord64.to_bounds') args in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@ZBounds.interp_op) (MapInterp ZBounds.of_word64 ropW)) (LiftOption.to' (Some x')))
          with
          | Some bounds => unopFEToWire_bounds_good bounds = true
          | None => False
          end)
  : unop_FEToWire_correct_and_bounded (MapInterp (fun _ x => x) ropW) op.
Proof.
  intros x Hx.
  pose x as x'.
  hnf in x; destruct_head' prod.
  specialize (H0 x' Hx).
  specialize (H1 x' Hx).
  let args := constr:(unop_args_to_bounded x' Hx) in
  t_correct_and_bounded ropZ_sig Hbounds H0 H1 args.
Qed.

Lemma ExprUnOpWireToFE_correct_and_bounded
      ropW op (ropZ_sig : rexpr_unop_WireToFE_sig op)
      (Hbounds : correct_and_bounded_genT ropW ropZ_sig)
      (H0 : forall x
                   (x := eta_wire_digitsW x)
                   (Hx : wire_digits_is_bounded (wire_digitsWToZ x) = true),
          let args := unopWireToFE_args_to_bounded x Hx in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@BoundedWord64.interp_op) (MapInterp BoundedWord64.of_word64 ropW))
                                    (LiftOption.to' (Some args)))
          with
          | Some _ => True
          | None => False
          end)
      (H1 : forall x
                   (x := eta_wire_digitsW x)
                   (Hx : wire_digits_is_bounded (wire_digitsWToZ x) = true),
          let args := unopWireToFE_args_to_bounded x Hx in
          let x' := SmartVarfMap (fun _ : base_type => BoundedWord64.to_bounds') args in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@ZBounds.interp_op) (MapInterp ZBounds.of_word64 ropW)) (LiftOption.to' (Some x')))
          with
          | Some bounds => unopWireToFE_bounds_good bounds = true
          | None => False
          end)
  : unop_WireToFE_correct_and_bounded (MapInterp (fun _ x => x) ropW) op.
Proof.
  intros x Hx.
  pose x as x'.
  hnf in x; destruct_head' prod.
  specialize (H0 x' Hx).
  specialize (H1 x' Hx).
  let args := constr:(unopWireToFE_args_to_bounded x' Hx) in
  t_correct_and_bounded ropZ_sig Hbounds H0 H1 args.
Qed.

Lemma ExprUnOpFEToZ_correct_and_bounded
      ropW op (ropZ_sig : rexpr_unop_FEToZ_sig op)
      (Hbounds : correct_and_bounded_genT ropW ropZ_sig)
      (H0 : forall x
                   (x := eta_fe25519W x)
                   (Hx : is_bounded (fe25519WToZ x) = true),
          let args := unop_args_to_bounded x Hx in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@BoundedWord64.interp_op) (MapInterp BoundedWord64.of_word64 ropW))
                                    (LiftOption.to' (Some args)))
          with
          | Some _ => True
          | None => False
          end)
      (H1 : forall x
                   (x := eta_fe25519W x)
                   (Hx : is_bounded (fe25519WToZ x) = true),
          let args := unop_args_to_bounded x Hx in
          let x' := SmartVarfMap (fun _ : base_type => BoundedWord64.to_bounds') args in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@ZBounds.interp_op) (MapInterp ZBounds.of_word64 ropW)) (LiftOption.to' (Some x')))
          with
          | Some bounds => unopFEToZ_bounds_good bounds = true
          | None => False
          end)
  : unop_FEToZ_correct (MapInterp (fun _ x => x) ropW) op.
Proof.
  intros x Hx.
  pose x as x'.
  hnf in x; destruct_head' prod.
  specialize (H0 x' Hx).
  specialize (H1 x' Hx).
  let args := constr:(unop_args_to_bounded x' Hx) in
  t_correct_and_bounded ropZ_sig Hbounds H0 H1 args.
Qed.

Ltac rexpr_correct :=
  let ropW' := fresh in
  let ropZ_sig := fresh in
  intros ropW' ropZ_sig;
  let wf_ropW := fresh "wf_ropW" in
  assert (wf_ropW : Wf ropW') by (subst ropW' ropZ_sig; reflect_Wf base_type_eq_semidec_is_dec op_beq_bl);
  cbv zeta; repeat apply conj;
  [ vm_compute; reflexivity
  | apply @InterpRelWf;
    [ | apply @RelWfMapInterp, wf_ropW ].. ];
  auto with interp_related.

Notation rword_of_Z rexprZ_sig := (MapInterp Word64.of_Z (proj1_sig rexprZ_sig)) (only parsing).

Notation compute_bounds opW bounds
  := (ApplyInterpedAll (Interp (@ZBounds.interp_op) (MapInterp (@ZBounds.of_word64) opW)) bounds)
       (only parsing).


Module Export PrettyPrinting.
  Inductive bounds_on := overflow | in_range (lower upper : Z).

  Definition ZBounds_to_bounds_on
    := fun t : base_type
       => match t return ZBounds.interp_base_type t -> match t with TZ => bounds_on end with
          | TZ => fun x => match x with
                           | Some {| ZBounds.lower := l ; ZBounds.upper := u |}
                             => in_range l u
                           | None
                             => overflow
                           end
          end.

  Fixpoint no_overflow {t} : interp_flat_type (fun t => match t with TZ => bounds_on end) t -> bool
    := match t return interp_flat_type (fun t => match t with TZ => bounds_on end) t -> bool with
       | Tbase TZ => fun v => match v with
                              | overflow => false
                              | in_range _ _ => true
                              end
       | Prod x y => fun v => andb (@no_overflow _ (fst v)) (@no_overflow _ (snd v))
       end.

  (** This gives a slightly easier to read version of the bounds *)
  Notation compute_bounds_for_display opW bounds
    := (SmartVarfMap ZBounds_to_bounds_on (compute_bounds opW bounds)) (only parsing).
  Notation sanity_check opW bounds
    := (eq_refl true <: no_overflow (SmartVarfMap ZBounds_to_bounds_on (compute_bounds opW bounds)) = true) (only parsing).
End PrettyPrinting.
