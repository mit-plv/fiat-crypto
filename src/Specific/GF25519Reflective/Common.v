Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Crypto.Specific.GF25519.
Require Export Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Z.Interpretations64.
Require Crypto.Reflection.Z.Interpretations64.Relations.
Require Import Crypto.Reflection.Z.Interpretations64.RelationsCombinations.
Require Import Crypto.Reflection.Z.Reify.
Require Export Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.InterpWfRel.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.MapInterp.
Require Import Crypto.Reflection.MapInterpWf.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Util.Tower.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

Notation Expr := (Expr base_type WordW.interp_base_type op).

Local Ltac make_type_from' T :=
  let T := (eval compute in T) in
  let rT := reify_type T in
  exact rT.
Local Ltac make_type_from uncurried_op :=
  let T := (type of uncurried_op) in
  make_type_from' T.

Definition fe25519T : flat_type base_type.
Proof.
  let T := (eval compute in GF25519.fe25519) in
  let T := reify_flat_type T in
  exact T.
Defined.
Definition Expr_n_OpT (count_out : nat) : flat_type base_type
  := Eval cbv [Syntax.tuple Syntax.tuple' fe25519T] in
      Syntax.tuple fe25519T count_out.
Fixpoint Expr_nm_OpT (count_in count_out : nat) : type base_type
  := match count_in with
     | 0 => Expr_n_OpT count_out
     | S n => SmartArrow base_type fe25519T (Expr_nm_OpT n count_out)
     end.
Definition ExprBinOpT : type base_type := Eval compute in Expr_nm_OpT 2 1.
Definition ExprUnOpT : type base_type := Eval compute in Expr_nm_OpT 1 1.
Definition ExprUnOpFEToZT : type base_type.
Proof. make_type_from (uncurry_unop_fe25519 ge_modulus). Defined.
Definition ExprUnOpWireToFET : type base_type.
Proof. make_type_from (uncurry_unop_wire_digits unpack). Defined.
Definition ExprUnOpFEToWireT : type base_type.
Proof. make_type_from (uncurry_unop_fe25519 pack). Defined.
Definition Expr4OpT : type base_type := Eval compute in Expr_nm_OpT 4 1.
Definition Expr9_4OpT : type base_type := Eval compute in Expr_nm_OpT 9 4.
Definition ExprArgT : flat_type base_type
  := Eval compute in remove_all_binders ExprUnOpT.
Definition ExprArgWireT : flat_type base_type
  := Eval compute in remove_all_binders ExprUnOpFEToWireT.
Definition ExprArgRevT : flat_type base_type
  := Eval compute in all_binders_for ExprUnOpT.
Definition ExprArgWireRevT : flat_type base_type
  := Eval compute in all_binders_for ExprUnOpWireToFET.
Definition ExprZ : Type := Expr (Tbase TZ).
Definition ExprUnOpFEToZ : Type := Expr ExprUnOpFEToZT.
Definition ExprUnOpWireToFE : Type := Expr ExprUnOpWireToFET.
Definition ExprUnOpFEToWire : Type := Expr ExprUnOpFEToWireT.
Definition Expr_nm_Op count_in count_out : Type := Expr (Expr_nm_OpT count_in count_out).
Definition ExprBinOp : Type := Expr ExprBinOpT.
Definition ExprUnOp : Type := Expr ExprUnOpT.
Definition Expr4Op : Type := Expr Expr4OpT.
Definition Expr9_4Op : Type := Expr Expr9_4OpT.
Definition ExprArg : Type := Expr ExprArgT.
Definition ExprArgWire : Type := Expr ExprArgWireT.
Definition ExprArgRev : Type := Expr ExprArgRevT.
Definition ExprArgWireRev : Type := Expr ExprArgWireRevT.
Definition expr_nm_Op count_in count_out interp_base_type var : Type
  := expr base_type interp_base_type op (var:=var) (Expr_nm_OpT count_in count_out).
Definition exprBinOp interp_base_type var : Type := expr base_type interp_base_type op (var:=var) ExprBinOpT.
Definition exprUnOp interp_base_type var : Type := expr base_type interp_base_type op (var:=var) ExprUnOpT.
Definition expr4Op interp_base_type var : Type := expr base_type interp_base_type op (var:=var) Expr4OpT.
Definition expr9_4Op interp_base_type var : Type := expr base_type interp_base_type op (var:=var) Expr9_4OpT.
Definition exprZ interp_base_type var : Type := expr base_type interp_base_type op (var:=var) (Tbase TZ).
Definition exprUnOpFEToZ interp_base_type var : Type := expr base_type interp_base_type op (var:=var) ExprUnOpFEToZT.
Definition exprUnOpWireToFE interp_base_type var : Type := expr base_type interp_base_type op (var:=var) ExprUnOpWireToFET.
Definition exprUnOpFEToWire interp_base_type var : Type := expr base_type interp_base_type op (var:=var) ExprUnOpFEToWireT.
Definition exprArg interp_base_type var : Type := expr base_type interp_base_type op (var:=var) ExprArgT.
Definition exprArgWire interp_base_type var : Type := expr base_type interp_base_type op (var:=var) ExprArgWireT.
Definition exprArgRev interp_base_type var : Type := expr base_type interp_base_type op (var:=var) ExprArgRevT.
Definition exprArgWireRev interp_base_type var : Type := expr base_type interp_base_type op (var:=var) ExprArgWireRevT.

Local Ltac bounds_from_list_cps ls :=
  lazymatch (eval hnf in ls) with
  | (?x :: nil)%list => constr:(fun T (extra : T) => (Some {| Bounds.lower := fst x ; Bounds.upper := snd x |}, extra))
  | (?x :: ?xs)%list => let bs := bounds_from_list_cps xs in
                        constr:(fun T extra => (Some {| Bounds.lower := fst x ; Bounds.upper := snd x |}, bs T extra))
  end.

Local Ltac make_bounds_cps ls :=
  let v := bounds_from_list_cps (List.rev ls) in
  let v := (eval compute in v) in
  pose v.

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

(*Fixpoint Expr_nm_Op_bounds count_in count_out : interp_all_binders_for (Expr_nm_OpT count_in count_out) ZBounds.interp_base_type.
Proof.
  refine match count_in return interp_all_binders_for (Expr_nm_OpT count_in count_out) ZBounds.interp_base_type with
         | 0 => tt
         | S n => let v := Expr_nm_Op_bounds n count_out in
                  _
         end; simpl.
  make_bounds_cps (Tuple.to_list _ bounds).
  pose (p _ v).
  repeat (split; [ exact (fst p0) | ]; destruct p0 as [_ p0]).
  exact p0.
*)
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
Definition Expr4Op_bounds : interp_all_binders_for Expr4OpT ZBounds.interp_base_type.
Proof.
  make_bounds (List.fold_right (@List.app _) nil (List.repeat (Tuple.to_list _ bounds) 4)).
Defined.
Definition Expr9Op_bounds : interp_all_binders_for Expr9_4OpT ZBounds.interp_base_type.
Proof.
  make_bounds (List.fold_right (@List.app _) nil (List.repeat (Tuple.to_list _ bounds) 9)).
Defined.
Definition interp_bexpr : ExprBinOp -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := fun e => curry_binop_fe25519W (Interp (@WordW.interp_op) e).
Definition interp_uexpr : ExprUnOp -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := fun e => curry_unop_fe25519W (Interp (@WordW.interp_op) e).
Definition interp_uexpr_FEToZ : ExprUnOpFEToZ -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.word64
  := fun e => curry_unop_fe25519W (Interp (@WordW.interp_op) e).
Definition interp_uexpr_FEToWire : ExprUnOpFEToWire -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.wire_digitsW
  := fun e => curry_unop_fe25519W (Interp (@WordW.interp_op) e).
Definition interp_uexpr_WireToFE : ExprUnOpWireToFE -> Specific.GF25519BoundedCommon.wire_digitsW -> Specific.GF25519BoundedCommon.fe25519W
  := fun e => curry_unop_wire_digitsW (Interp (@WordW.interp_op) e).
Definition interp_9_4expr : Expr9_4Op
                            -> Specific.GF25519BoundedCommon.fe25519W
                            -> Specific.GF25519BoundedCommon.fe25519W
                            -> Specific.GF25519BoundedCommon.fe25519W
                            -> Specific.GF25519BoundedCommon.fe25519W
                            -> Specific.GF25519BoundedCommon.fe25519W
                            -> Specific.GF25519BoundedCommon.fe25519W
                            -> Specific.GF25519BoundedCommon.fe25519W
                            -> Specific.GF25519BoundedCommon.fe25519W
                            -> Specific.GF25519BoundedCommon.fe25519W
                            -> Tuple.tuple Specific.GF25519BoundedCommon.fe25519W 4
  := fun e => curry_9op_fe25519W (Interp (@WordW.interp_op) e).

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
Notation op9_4_correct_and_bounded rop op
  := (i9top_correct_and_bounded 4 (interp_9_4expr rop) op) (only parsing).

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
Notation rexpr_9_4op_sig op := (rexpr_sig Expr9_4OpT (uncurry_9op_fe25519 op)) (only parsing).

Notation correct_and_bounded_genT ropW'v ropZ_sigv
  := (let ropW' := ropW'v in
      let ropZ_sig := ropZ_sigv in
      let ropW := MapInterp (fun _ x => x) ropW' in
      let ropZ := MapInterp WordW.to_Z ropW' in
      let ropBounds := MapInterp ZBounds.of_wordW ropW' in
      let ropBoundedWordW := MapInterp BoundedWordW.of_wordW ropW' in
      ropZ = proj1_sig ropZ_sig
      /\ interp_type_rel_pointwise2 Relations.related_Z (Interp (@BoundedWordW.interp_op) ropBoundedWordW) (Interp (@Z.interp_op) ropZ)
      /\ interp_type_rel_pointwise2 Relations.related_bounds (Interp (@BoundedWordW.interp_op) ropBoundedWordW) (Interp (@ZBounds.interp_op) ropBounds)
      /\ interp_type_rel_pointwise2 Relations.related_wordW (Interp (@BoundedWordW.interp_op) ropBoundedWordW) (Interp (@WordW.interp_op) ropW))
       (only parsing).

Ltac app_tuples x y :=
  let tx := type of x in
  lazymatch (eval hnf in tx) with
  | prod _ _ => let xs := app_tuples (snd x) y in
                constr:((fst x, xs))
  | _ => constr:((x, y))
  end.

Local Arguments Tuple.map2 : simpl never.
Local Arguments Tuple.map : simpl never.

Fixpoint args_to_bounded_helperT {n}
         (v : Tuple.tuple' WordW.wordW n)
         (bounds : Tuple.tuple' (Z * Z) n)
         (pf : List.fold_right
                 andb true
                 (Tuple.to_list
                    _
                    (Tuple.map2
                       (n:=S n)
                       (fun bounds v =>
                          let '(lower, upper) := bounds in ((lower <=? v)%Z && (v <=? upper)%Z)%bool)
                       bounds
                       (Tuple.map (n:=S n) WordW.wordWToZ v))) = true)
         (res : Type)
         {struct n}
  : Type.
Proof.
  refine (match n return (forall (v : Tuple.tuple' _ n) (bounds : Tuple.tuple' _ n),
                             List.fold_right
                               _ _ (Tuple.to_list
                                      _
                                      (Tuple.map2 (n:=S n) _ bounds (Tuple.map (n:=S n) _ v))) = true
                             -> Type)
          with
          | 0 => fun v' bounds' pf0 => forall pf1 : (0 <= fst bounds' /\ Z.log2 (snd bounds') < Z.of_nat WordW.bit_width)%Z, res
          | S n' => fun v' bounds' pf0 => let t := _ in
                                        forall pf1 : (0 <= fst (snd bounds') /\ Z.log2 (snd (snd bounds')) < Z.of_nat WordW.bit_width)%Z, @args_to_bounded_helperT n' (fst v') (fst bounds') t res
          end v bounds pf).
  { clear -pf0.
    abstract (
        destruct v', bounds'; simpl @fst;
        rewrite Tuple.map_S in pf0;
        simpl in pf0;
        rewrite Tuple.map2_S in pf0;
        simpl @List.fold_right in *;
        rewrite Bool.andb_true_iff in pf0; tauto
      ). }
Defined.

Fixpoint args_to_bounded_helper {n} res
         {struct n}
  : forall v bounds pf, (Tuple.tuple' BoundedWordW.BoundedWord n -> res) -> @args_to_bounded_helperT n v bounds pf res.
Proof.
  refine match n return (forall v bounds pf, (Tuple.tuple' BoundedWordW.BoundedWord n -> res) -> @args_to_bounded_helperT n v bounds pf res) with
         | 0 => fun v bounds pf f pf' => f {| BoundedWord.lower := fst bounds ; BoundedWord.value := v ; BoundedWord.upper := snd bounds |}
         | S n'
           => fun v bounds pf f pf'
              => @args_to_bounded_helper
                   n' res (fst v) (fst bounds) _
                   (fun ts => f (ts, {| BoundedWord.lower := fst (snd bounds) ; BoundedWord.value := snd v ; BoundedWord.upper := snd (snd bounds) |}))
         end.
  { clear -pf pf'.
    unfold Tuple.map2, Tuple.map in pf; simpl in *.
    abstract (
        destruct bounds;
        simpl in *;
        rewrite !Bool.andb_true_iff in pf;
        destruct_head' and;
        Z.ltb_to_lt; auto
      ). }
  { simpl in *.
    clear -pf pf'.
    abstract (
        destruct bounds as [? [? ?] ], v; simpl in *;
        rewrite Tuple.map_S in pf; simpl in pf; rewrite Tuple.map2_S in pf;
        simpl in pf;
        rewrite !Bool.andb_true_iff in pf;
        destruct_head' and;
        Z.ltb_to_lt; auto
      ). }
Defined.

Definition assoc_right''
  := Eval cbv [Tuple.assoc_right' Tuple.rsnoc' fst snd] in @Tuple.assoc_right'.

Definition args_to_bounded {n} v bounds pf
  := Eval cbv [args_to_bounded_helper assoc_right''] in
      @args_to_bounded_helper n _ v bounds pf (@assoc_right'' _ _).

Local Ltac get_len T :=
  match (eval hnf in T) with
  | prod ?A ?B
    => let a := get_len A in
       let b := get_len B in
       (eval compute in (a + b)%nat)
  | _ => constr:(1%nat)
  end.

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

Local Ltac make_args x :=
  let x' := fresh "x'" in
  compute in x |- *;
  let t := match type of x with @expr _ _ _ _ (Tflat _ ?t) => t end in
  let t' := match goal with |- @expr _ _ _ _ (Tflat _ ?t) => t end in
  refine (LetIn (UnReturn x) _);
  let x'' := fresh "x''" in
  intro x'';
  let xv := assoc_right_tuple x'' (@None) in
  refine (SmartVarf (xv : interp_flat_type _ t')).

Definition unop_make_args {interp_base_type var} (x : exprArg interp_base_type var) : exprArgRev interp_base_type var.
Proof. make_args x. Defined.
Definition unop_wire_make_args {interp_base_type var} (x : exprArgWire interp_base_type var) : exprArgWireRev interp_base_type var.
Proof. make_args x. Defined.

Local Ltac args_to_bounded x H :=
  let x' := fresh in
  set (x' := x);
  compute in x;
  let len := (let T := type of x in get_len T) in
  destruct_head' prod;
  let c := constr:(args_to_bounded (n:=pred len) x' _ H) in
  let bounds := lazymatch c with args_to_bounded _ ?bounds _ => bounds end in
  let c := (eval cbv [all_binders_for ExprUnOpT interp_flat_type args_to_bounded bounds pred fst snd] in c) in
  apply c; compute; clear;
  try abstract (
        repeat split;
        solve [ reflexivity
              | refine (fun v => match v with eq_refl => I end) ]
      ).

Definition unop_args_to_bounded (x : fe25519W) (H : is_bounded (fe25519WToZ x) = true)
  : interp_flat_type (fun _ => BoundedWordW.BoundedWord) (all_binders_for ExprUnOpT).
Proof. args_to_bounded x H. Defined.

Definition unopWireToFE_args_to_bounded (x : wire_digitsW) (H : wire_digits_is_bounded (wire_digitsWToZ x) = true)
  : interp_flat_type (fun _ => BoundedWordW.BoundedWord) (all_binders_for ExprUnOpWireToFET).
Proof. args_to_bounded x H. Defined.
Definition binop_args_to_bounded (x : fe25519W * fe25519W)
           (H : is_bounded (fe25519WToZ (fst x)) = true)
           (H' : is_bounded (fe25519WToZ (snd x)) = true)
  : interp_flat_type (fun _ => BoundedWordW.BoundedWord) (all_binders_for ExprBinOpT).
Proof.
  let v := app_tuples (unop_args_to_bounded (fst x) H) (unop_args_to_bounded (snd x) H') in
  exact v.
Defined.
Definition op9_args_to_bounded (x : fe25519W * fe25519W * fe25519W * fe25519W * fe25519W * fe25519W * fe25519W * fe25519W * fe25519W)
           (H0 : is_bounded (fe25519WToZ (fst (fst (fst (fst (fst (fst (fst (fst x))))))))) = true)
           (H1 : is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst (fst (fst x))))))))) = true)
           (H2 : is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst (fst x)))))))) = true)
           (H3 : is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst x))))))) = true)
           (H4 : is_bounded (fe25519WToZ (snd (fst (fst (fst (fst x)))))) = true)
           (H5 : is_bounded (fe25519WToZ (snd (fst (fst (fst x))))) = true)
           (H6 : is_bounded (fe25519WToZ (snd (fst (fst x)))) = true)
           (H7 : is_bounded (fe25519WToZ (snd (fst x))) = true)
           (H8 : is_bounded (fe25519WToZ (snd x)) = true)
  : interp_flat_type (fun _ => BoundedWordW.BoundedWord) (all_binders_for Expr9_4OpT).
Proof.
  let v := constr:(unop_args_to_bounded _ H8) in
  let v := app_tuples (unop_args_to_bounded _ H7) v in
  let v := app_tuples (unop_args_to_bounded _ H6) v in
  let v := app_tuples (unop_args_to_bounded _ H5) v in
  let v := app_tuples (unop_args_to_bounded _ H4) v in
  let v := app_tuples (unop_args_to_bounded _ H3) v in
  let v := app_tuples (unop_args_to_bounded _ H2) v in
  let v := app_tuples (unop_args_to_bounded _ H1) v in
  let v := app_tuples (unop_args_to_bounded _ H0) v in
  exact v.
Defined.

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
Definition op9_4_bounds_good (bounds : interp_flat_type (fun _ => ZBounds.bounds) (remove_all_binders Expr9_4OpT)) : bool.
Proof. make_bounds_prop bounds Expr4Op_bounds. Defined.

Definition ApplyUnOp {interp_base_type var} (f : exprUnOp interp_base_type var) : exprArg interp_base_type var -> exprArg interp_base_type var
  := fun x
     => LetIn (UnReturn (unop_make_args x))
              (fun k => UnReturn (Apply length_fe25519 f k)).
Definition ApplyBinOp {interp_base_type var} (f : exprBinOp interp_base_type var) : exprArg interp_base_type var -> exprArg interp_base_type var -> exprArg interp_base_type var
  := fun x y
     => LetIn (UnReturn (unop_make_args x))
              (fun x'
               => LetIn (UnReturn (unop_make_args y))
                        (fun y'
                         => UnReturn (Apply length_fe25519
                                            (Apply length_fe25519
                                                   f x') y'))).
Definition ApplyUnOpFEToWire {interp_base_type var} (f : exprUnOpFEToWire interp_base_type var) : exprArg interp_base_type var -> exprArgWire interp_base_type var
  := fun x
     => LetIn (UnReturn (unop_make_args x))
              (fun k => UnReturn (Apply length_fe25519 f k)).
Definition ApplyUnOpWireToFE {interp_base_type var} (f : exprUnOpWireToFE interp_base_type var) : exprArgWire interp_base_type var -> exprArg interp_base_type var
  := fun x
     => LetIn (UnReturn (unop_wire_make_args x))
              (fun k => UnReturn (Apply (List.length wire_widths) f k)).
Definition ApplyUnOpFEToZ {interp_base_type var} (f : exprUnOpFEToZ interp_base_type var) : exprArg interp_base_type var -> exprZ interp_base_type var
  := fun x
     => LetIn (UnReturn (unop_make_args x))
              (fun k => UnReturn (Apply length_fe25519 f k)).


(* FIXME TODO(jgross): This is a horrible tactic.  We should unify the
    various kinds of correct and boundedness, and abstract in Gallina
    rather than Ltac *)

Ltac t_correct_and_bounded ropZ_sig Hbounds H0 H1 args :=
  let Heq := fresh "Heq" in
  let Hbounds0 := fresh "Hbounds0" in
  let Hbounds1 := fresh "Hbounds1" in
  let Hbounds2 := fresh "Hbounds2" in
  pose proof (proj2_sig ropZ_sig) as Heq;
  cbv [interp_bexpr interp_uexpr interp_uexpr_FEToWire interp_uexpr_FEToZ interp_uexpr_WireToFE interp_9_4expr
                    curry_binop_fe25519W curry_unop_fe25519W curry_unop_wire_digitsW curry_9op_fe25519W
                    curry_binop_fe25519 curry_unop_fe25519 curry_unop_wire_digits curry_9op_fe25519
                    uncurry_binop_fe25519W uncurry_unop_fe25519W uncurry_unop_wire_digitsW uncurry_9op_fe25519W
                    uncurry_binop_fe25519 uncurry_unop_fe25519 uncurry_unop_wire_digits uncurry_9op_fe25519
                    ExprBinOpT ExprUnOpFEToWireT ExprUnOpT ExprUnOpFEToZT ExprUnOpWireToFET Expr9_4OpT Expr4OpT
                    interp_type_gen_rel_pointwise interp_type_gen_rel_pointwise] in *;
  cbv zeta in *;
  simpl @fe25519WToZ; simpl @wire_digitsWToZ;
  rewrite <- Heq; clear Heq;
  destruct Hbounds as [Heq Hbounds];
  change interp_op with (@Z.interp_op) in *;
  change interp_base_type with (@Z.interp_base_type) in *;
  rewrite <- Heq; clear Heq;
  destruct Hbounds as [ Hbounds0 [Hbounds1 Hbounds2] ];
  pose proof (fun pf => Relations.uncurry_interp_type_rel_pointwise2_proj_from_option2 WordW.to_Z pf Hbounds2 Hbounds0) as Hbounds_left;
  pose proof (fun pf => Relations.uncurry_interp_type_rel_pointwise2_proj1_from_option2 Relations.related_wordW_boundsi' pf Hbounds1 Hbounds2) as Hbounds_right;
  specialize_by repeat first [ progress intros
                             | reflexivity
                             | assumption
                             | progress destruct_head' base_type
                             | progress destruct_head' BoundedWordW.BoundedWord
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
         binop_args_to_bounded unop_args_to_bounded unopWireToFE_args_to_bounded op9_args_to_bounded
         Relations.proj_eq_rel interp_flat_type_rel_pointwise2 SmartVarfMap interp_flat_type smart_interp_flat_map Application.all_binders_for fst snd BoundedWordW.to_wordW' BoundedWordW.boundedWordToWordW BoundedWord.value Application.ApplyInterpedAll Application.fst_binder Application.snd_binder interp_flat_type_rel_pointwise2_gen_Prop Relations.related_wordW_boundsi' Relations.related'_wordW_bounds Bounds.upper Bounds.lower Application.remove_all_binders WordW.to_Z] in Hbounds_left, Hbounds_right;
  lazymatch goal with
  | [ |- fe25519WToZ ?x = _ /\ _ ]
    => generalize dependent x; intros
  | [ |- wire_digitsWToZ ?x = _ /\ _ ]
    => generalize dependent x; intros
  | [ |- ((Tuple.map fe25519WToZ ?x = _) * _)%type ]
    => generalize dependent x; intros
  | [ |- _ = _ ]
    => exact Hbounds_left
  end;
  cbv [interp_type interp_type_gen interp_type_gen_hetero interp_flat_type WordW.interp_base_type remove_all_binders] in *;
  destruct_head' prod;
  change word64ToZ with WordW.wordWToZ in *;
  (split; [ exact Hbounds_left | ]);
  cbv [interp_flat_type] in *;
  cbv [fst snd
           binop_bounds_good unop_bounds_good unopFEToWire_bounds_good unopWireToFE_bounds_good unopFEToZ_bounds_good op9_4_bounds_good
           ExprUnOp_bounds ExprBinOp_bounds ExprUnOpFEToWire_bounds ExprUnOpFEToZ_bounds ExprUnOpWireToFE_bounds Expr9Op_bounds Expr4Op_bounds] in H1;
  destruct_head' ZBounds.bounds;
  unfold_is_bounded_in H1;
  simpl @fe25519WToZ; simpl @wire_digitsWToZ;
  destruct_head' and;
  Z.ltb_to_lt;
  change WordW.wordWToZ with word64ToZ in *;
  cbv [Tuple.map HList.hlist Tuple.on_tuple Tuple.from_list Tuple.from_list' Tuple.to_list Tuple.to_list' List.map HList.hlist' fst snd];
  repeat split; unfold_is_bounded;
  Z.ltb_to_lt;
  try omega; try reflexivity.


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

Notation rword_of_Z rexprZ_sig := (MapInterp WordW.of_Z (proj1_sig rexprZ_sig)) (only parsing).

Definition rword64ize {t} (x : Expr t) : Expr t
  := MapInterp (fun t => match t with TZ => word64ize end) x.

Notation compute_bounds opW bounds
  := (ApplyInterpedAll (Interp (@ZBounds.interp_op) (MapInterp (@ZBounds.of_wordW) opW)) bounds)
       (only parsing).


Module Export PrettyPrinting.
  (* We add [enlargen] to force [bounds_on] to be in [Type] in 8.4 and
     8.5/8.6.  Because [Set] is special and things break if
     [bounds_on] ends up in [Set] for reasons jgross hasn't bothered
     to debug. *)
  Inductive bounds_on := overflow | in_range (lower upper : Z) | enlargen (_ : Set).

  Inductive result := yes | no | borked.

  Definition ZBounds_to_bounds_on
    := fun t : base_type
       => match t return ZBounds.interp_base_type t -> match t with TZ => bounds_on end with
          | TZ => fun x => match x with
                           | Some {| Bounds.lower := l ; Bounds.upper := u |}
                             => in_range l u
                           | None
                             => overflow
                           end
          end.

  Fixpoint does_it_overflow {t} : interp_flat_type (fun t => match t with TZ => bounds_on end) t -> result
    := match t return interp_flat_type (fun t => match t with TZ => bounds_on end) t -> result with
       | Tbase TZ => fun v => match v with
                              | overflow => yes
                              | in_range _ _ => no
                              | enlargen _ => borked
                              end
       | Prod x y => fun v => match @does_it_overflow _ (fst v), @does_it_overflow _ (snd v) with
                              | no, no => no
                              | yes, no | no, yes | yes, yes => yes
                              | borked, _ | _, borked => borked
                              end
       end.

  (** This gives a slightly easier to read version of the bounds *)
  Notation compute_bounds_for_display opW bounds
    := (SmartVarfMap ZBounds_to_bounds_on (compute_bounds opW bounds)) (only parsing).
  Notation sanity_compute opW bounds
    := (does_it_overflow (SmartVarfMap ZBounds_to_bounds_on (compute_bounds opW bounds))) (only parsing).
  Notation sanity_check opW bounds
    := (eq_refl (sanity_compute opW bounds) <: no = no) (only parsing).
End PrettyPrinting.
