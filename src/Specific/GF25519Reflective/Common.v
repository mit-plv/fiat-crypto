Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Crypto.Specific.GF25519.
Require Export Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.Tuple.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.Eta.
Require Import Crypto.Reflection.Z.Interpretations64.
Require Crypto.Reflection.Z.Interpretations64.Relations.
Require Import Crypto.Reflection.Z.Interpretations64.RelationsCombinations.
Require Import Crypto.Reflection.Z.Reify.
Require Export Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Equality.
Require Import Crypto.Reflection.InterpWfRel.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Util.Curry.
Require Import Crypto.Util.Tower.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Notations.

Notation Expr := (Expr base_type op).

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
Definition Expr_nm_OpT (count_in count_out : nat) : type base_type
  := Eval cbv [Syntax.tuple Syntax.tuple' fe25519T Expr_n_OpT] in
      Arrow (Syntax.tuple fe25519T count_in) (Expr_n_OpT count_out).
Definition ExprBinOpT : type base_type := Eval compute in Expr_nm_OpT 2 1.
Definition ExprUnOpT : type base_type := Eval compute in Expr_nm_OpT 1 1.
Definition ExprUnOpFEToZT : type base_type.
Proof. make_type_from ge_modulus. Defined.
Definition ExprUnOpWireToFET : type base_type.
Proof. make_type_from unpack. Defined.
Definition ExprUnOpFEToWireT : type base_type.
Proof. make_type_from pack. Defined.
Definition Expr4OpT : type base_type := Eval compute in Expr_nm_OpT 4 1.
Definition Expr9_4OpT : type base_type := Eval compute in Expr_nm_OpT 9 4.
Definition ExprArgT : flat_type base_type
  := Eval compute in domain ExprUnOpT.
Definition ExprArgWireT : flat_type base_type
  := Eval compute in domain ExprUnOpWireToFET.
Definition ExprZ : Type := Expr (Arrow Unit (Tbase TZ)).
Definition ExprUnOpFEToZ : Type := Expr ExprUnOpFEToZT.
Definition ExprUnOpWireToFE : Type := Expr ExprUnOpWireToFET.
Definition ExprUnOpFEToWire : Type := Expr ExprUnOpFEToWireT.
Definition Expr_nm_Op count_in count_out : Type := Expr (Expr_nm_OpT count_in count_out).
Definition ExprBinOp : Type := Expr ExprBinOpT.
Definition ExprUnOp : Type := Expr ExprUnOpT.
Definition Expr4Op : Type := Expr Expr4OpT.
Definition Expr9_4Op : Type := Expr Expr9_4OpT.
Definition ExprArg : Type := Expr (Arrow Unit ExprArgT).
Definition ExprArgWire : Type := Expr (Arrow Unit ExprArgWireT).
Definition expr_nm_Op count_in count_out var : Type
  := expr base_type op (var:=var) (Expr_nm_OpT count_in count_out).
Definition exprBinOp var : Type := expr base_type op (var:=var) ExprBinOpT.
Definition exprUnOp var : Type := expr base_type op (var:=var) ExprUnOpT.
Definition expr4Op var : Type := expr base_type op (var:=var) Expr4OpT.
Definition expr9_4Op var : Type := expr base_type op (var:=var) Expr9_4OpT.
Definition exprZ var : Type := expr base_type op (var:=var) (Arrow Unit (Tbase TZ)).
Definition exprUnOpFEToZ var : Type := expr base_type op (var:=var) ExprUnOpFEToZT.
Definition exprUnOpWireToFE var : Type := expr base_type op (var:=var) ExprUnOpWireToFET.
Definition exprUnOpFEToWire var : Type := expr base_type op (var:=var) ExprUnOpFEToWireT.
Definition exprArg var : Type := expr base_type op (var:=var) (Arrow Unit ExprArgT).
Definition exprArgWire var : Type := expr base_type op (var:=var) (Arrow Unit ExprArgWireT).

Definition make_bound (x : Z * Z) : ZBounds.t
  := Some {| Bounds.lower := fst x ; Bounds.upper := snd x |}.

Fixpoint Expr_nm_Op_bounds count_in count_out {struct count_in} : interp_flat_type ZBounds.interp_base_type (domain (Expr_nm_OpT count_in count_out))
  := match count_in return interp_flat_type _ (domain (Expr_nm_OpT count_in count_out)) with
     | 0 => tt
     | S n
       => let b := (Tuple.map make_bound bounds) in
          let bs := Expr_nm_Op_bounds n count_out in
          match n return interp_flat_type _ (domain (Expr_nm_OpT n _)) -> interp_flat_type _ (domain (Expr_nm_OpT (S n) _)) with
          | 0 => fun _ => b
          | S n' => fun bs => (bs, b)
          end bs
     end.
Definition ExprBinOp_bounds : interp_flat_type ZBounds.interp_base_type (domain ExprBinOpT)
  := Eval compute in Expr_nm_Op_bounds 2 1.
Definition ExprUnOp_bounds : interp_flat_type ZBounds.interp_base_type (domain ExprUnOpT)
  := Eval compute in Expr_nm_Op_bounds 1 1.
Definition ExprUnOpFEToZ_bounds : interp_flat_type ZBounds.interp_base_type (domain ExprUnOpFEToZT)
  := Eval compute in Expr_nm_Op_bounds 1 1.
Definition ExprUnOpFEToWire_bounds : interp_flat_type ZBounds.interp_base_type (domain ExprUnOpFEToWireT)
  := Eval compute in Expr_nm_Op_bounds 1 1.
Definition Expr4Op_bounds : interp_flat_type ZBounds.interp_base_type (domain Expr4OpT)
  := Eval compute in Expr_nm_Op_bounds 4 1.
Definition Expr9Op_bounds : interp_flat_type ZBounds.interp_base_type (domain Expr9_4OpT)
  := Eval compute in Expr_nm_Op_bounds 9 4.
Definition ExprUnOpWireToFE_bounds : interp_flat_type ZBounds.interp_base_type (domain ExprUnOpWireToFET)
  := Tuple.map make_bound wire_digit_bounds.

Definition interp_bexpr : ExprBinOp -> Specific.GF25519BoundedCommon.fe25519W * Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := fun e => interp_flat_type_eta (Interp (@WordW.interp_op) e).
Definition interp_uexpr : ExprUnOp -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := fun e => interp_flat_type_eta (Interp (@WordW.interp_op) e).
Definition interp_uexpr_FEToZ : ExprUnOpFEToZ -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.word64
  := fun e => interp_flat_type_eta (Interp (@WordW.interp_op) e).
Definition interp_uexpr_FEToWire : ExprUnOpFEToWire -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.wire_digitsW
  := fun e => interp_flat_type_eta (Interp (@WordW.interp_op) e).
Definition interp_uexpr_WireToFE : ExprUnOpWireToFE -> Specific.GF25519BoundedCommon.wire_digitsW -> Specific.GF25519BoundedCommon.fe25519W
  := fun e => interp_flat_type_eta (Interp (@WordW.interp_op) e).
Definition interp_9_4expr : Expr9_4Op
                            -> Tuple.tuple Specific.GF25519BoundedCommon.fe25519W 9
                            -> Tuple.tuple Specific.GF25519BoundedCommon.fe25519W 4
  := fun e => interp_flat_type_eta (Interp (@WordW.interp_op) e).

Notation binop_correct_and_bounded rop op
  := (ibinop_correct_and_bounded (interp_bexpr rop) (curry2 op)) (only parsing).
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
  | [ |- { rexpr | forall x, Interp _ (t:=?T) rexpr x = ?uncurry ?oper x } ]
    => let operf := head oper in
       let uncurryf := head uncurry in
       try cbv delta [T]; try cbv delta [oper];
       try cbv beta iota delta [uncurryf]
  | [ |- { rexpr | forall x, Interp _ (t:=?T) rexpr x = ?oper x } ]
    => let operf := head oper in
       try cbv delta [T]; try cbv delta [oper]
  end;
  cbv beta iota delta [interp_flat_type interp_base_type zero_ GF25519.fe25519 GF25519.wire_digits].

Ltac reify_sig :=
  rexpr_cbv; eexists; Reify_rhs; reflexivity.

Local Notation rexpr_sig T uncurried_op :=
  { rexprZ
  | forall x, Interp interp_op (t:=T) rexprZ x = uncurried_op x }
    (only parsing).

Notation rexpr_binop_sig op := (rexpr_sig ExprBinOpT (curry2 op)) (only parsing).
Notation rexpr_unop_sig op := (rexpr_sig ExprUnOpT op) (only parsing).
Notation rexpr_unop_FEToZ_sig op := (rexpr_sig ExprUnOpFEToZT op) (only parsing).
Notation rexpr_unop_FEToWire_sig op := (rexpr_sig ExprUnOpFEToWireT op) (only parsing).
Notation rexpr_unop_WireToFE_sig op := (rexpr_sig ExprUnOpWireToFET op) (only parsing).
Notation rexpr_9_4op_sig op := (rexpr_sig Expr9_4OpT op) (only parsing).

Notation correct_and_bounded_genT ropW'v ropZ_sigv
  := (let ropW' := ropW'v in
      let ropZ_sig := ropZ_sigv in
      ropW' = proj1_sig ropZ_sig
      /\ interp_type_rel_pointwise Relations.related_Z (Interp (@BoundedWordW.interp_op) ropW') (Interp (@Z.interp_op) ropW')
      /\ interp_type_rel_pointwise Relations.related_bounds (Interp (@BoundedWordW.interp_op) ropW') (Interp (@ZBounds.interp_op) ropW')
      /\ interp_type_rel_pointwise Relations.related_wordW (Interp (@BoundedWordW.interp_op) ropW') (Interp (@WordW.interp_op) ropW'))
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
(*
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
*)

Definition assoc_right''
  := Eval cbv [Tuple.assoc_right' Tuple.rsnoc' fst snd] in @Tuple.assoc_right'.
(*
Definition args_to_bounded {n} v bounds pf
  := Eval cbv [args_to_bounded_helper assoc_right''] in
      @args_to_bounded_helper n _ v bounds pf (@assoc_right'' _ _).
*)
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

(*
Local Ltac make_args x :=
  let x' := fresh "x'" in
  compute in x |- *;
  let t := match type of x with @expr _ _ _ (Tflat ?t) => t end in
  let t' := match goal with |- @expr _ _ _ (Tflat ?t) => t end in
  refine (LetIn (invert_Return x) _);
  let x'' := fresh "x''" in
  intro x'';
  let xv := assoc_right_tuple x'' (@None) in
  refine (SmartVarf (xv : interp_flat_type _ t')).

Local Ltac args_to_bounded x H :=
  let x' := fresh in
  set (x' := x);
  compute in x;
  let len := (let T := type of x in get_len T) in
  destruct_head' prod;
  let c := constr:(args_to_bounded (n:=pred len) x' _ H) in
  let bounds := lazymatch c with args_to_bounded _ ?bounds _ => bounds end in
  let c := (eval cbv [domain ExprUnOpT interp_flat_type args_to_bounded bounds pred fst snd] in c) in
  apply c; compute; clear;
  try abstract (
        repeat split;
        solve [ reflexivity
              | refine (fun v => match v with eq_refl => I end) ]
      ).
 *)

Section gen.
  Definition bounds_are_good_gen
             {n : nat} (bounds : Tuple.tuple (Z * Z) n)
    := let res :=
           Tuple.map (fun bs => let '(lower, upper) := bs in ((0 <=? lower)%Z && (Z.log2 upper <? Z.of_nat WordW.bit_width)%Z)%bool) bounds
       in
       List.fold_right andb true (Tuple.to_list n res).
  Definition unop_args_to_bounded'
             (bs : Z * Z)
             (Hbs : bounds_are_good_gen (n:=1) bs = true)
             (x : word64)
             (H : is_bounded_gen (Tuple.map (fun v : word64 => (v : Z)) (n:=1) x) bs = true)
    : BoundedWordW.BoundedWord.
  Proof.
    refine {| BoundedWord.lower := fst bs ; BoundedWord.value := x ; BoundedWord.upper := snd bs |}.
    unfold bounds_are_good_gen, is_bounded_gen, Tuple.map, Tuple.map2 in *; simpl in *.
    abstract (
        destruct bs; Bool.split_andb; Z.ltb_to_lt; simpl;
        repeat apply conj; assumption
      ).
  Defined.
  Fixpoint n_op_args_to_bounded'
           n
    : forall (bs : Tuple.tuple' (Z * Z) n)
             (Hbs : bounds_are_good_gen (n:=S n) bs = true)
             (x : Tuple.tuple' word64 n)
             (H : is_bounded_gen (Tuple.eta_tuple (Tuple.map (n:=S n) (fun v : word64 => v : Z)) x) bs = true),
      interp_flat_type (fun _ => BoundedWordW.BoundedWord) (Syntax.tuple' (Tbase TZ) n).
  Proof.
    destruct n as [|n']; simpl in *.
    { exact unop_args_to_bounded'. }
    { refine (fun bs Hbs x H
              => (@n_op_args_to_bounded' n' (fst bs) _ (fst x) _,
                  @unop_args_to_bounded' (snd bs) _ (snd x) _));
        clear n_op_args_to_bounded';
        simpl in *;
        [ clear x H | clear Hbs | clear x H | clear Hbs ];
        unfold bounds_are_good_gen, is_bounded_gen in *;
        abstract (
            repeat first [ progress simpl in *
                         | assumption
                         | reflexivity
                         | progress Bool.split_andb
                         | progress destruct_head prod
                         | match goal with
                           | [ H : _ |- _ ] => progress rewrite ?Tuple.map_S, ?Tuple.map2_S, ?Tuple.strip_eta_tuple'_dep in H
                           end
                         | progress rewrite ?Tuple.map_S, ?Tuple.map2_S, ?Tuple.strip_eta_tuple'_dep
                         | progress break_match_hyps
                         | rewrite Bool.andb_true_iff; apply conj
                         | unfold Tuple.map, Tuple.map', Tuple.map2; simpl; rewrite Bool.andb_true_iff; apply conj ]
          ). }
  Defined.

  Definition n_op_args_to_bounded
             n
    : forall (bs : Tuple.tuple (Z * Z) n)
             (Hbs : bounds_are_good_gen bs = true)
             (x : Tuple.tuple word64 n)
             (H : is_bounded_gen (Tuple.eta_tuple (Tuple.map (fun v : word64 => v : Z)) x) bs = true),
      interp_flat_type (fun _ => BoundedWordW.BoundedWord) (Syntax.tuple (Tbase TZ) n)
    := match n with
       | 0 => fun _ _ _ _ => tt
       | S n' => @n_op_args_to_bounded' n'
       end.

  Fixpoint nm_op_args_to_bounded' n m
           (bs : Tuple.tuple (Z * Z) m)
           (Hbs : bounds_are_good_gen bs = true)
    : forall (x : interp_flat_type (fun _ => Tuple.tuple word64 m) (Syntax.tuple' (Tbase TZ) n))
             (H : SmartVarfPropMap (fun _ x => is_bounded_gen (Tuple.eta_tuple (Tuple.map (fun v : word64 => v : Z)) x) bs = true)
                                   x),
      interp_flat_type (fun _ => BoundedWordW.BoundedWord) (Syntax.tuple' (Syntax.tuple (Tbase TZ) m) n)
    := match n with
       | 0 => @n_op_args_to_bounded m bs Hbs
       | S n' => fun x H
                 => (@nm_op_args_to_bounded' n' m bs Hbs (fst x) (proj1 H),
                     @n_op_args_to_bounded m bs Hbs (snd x) (proj2 H))
       end.
  Definition nm_op_args_to_bounded n m
           (bs : Tuple.tuple (Z * Z) m)
           (Hbs : bounds_are_good_gen bs = true)
    : forall (x : interp_flat_type (fun _ => Tuple.tuple word64 m) (Syntax.tuple (Tbase TZ) n))
             (H : SmartVarfPropMap (fun _ x => is_bounded_gen (Tuple.eta_tuple (Tuple.map (fun v : word64 => v : Z)) x) bs = true)
                                   x),
      interp_flat_type (fun _ => BoundedWordW.BoundedWord) (Syntax.tuple (Syntax.tuple (Tbase TZ) m) n)
    := match n with
       | 0 => fun _ _ => tt
       | S n' => @nm_op_args_to_bounded' n' m bs Hbs
       end.
End gen.

Local Ltac get_inner_len T :=
  lazymatch T with
  | (?T * _)%type => get_inner_len T
  | ?T => get_len T
  end.
Local Ltac get_outer_len T :=
  lazymatch T with
  | (?A * ?B)%type => let a := get_outer_len A in
                      let b := get_outer_len B in
                      (eval compute in (a + b)%nat)
  | ?T => constr:(1%nat)
  end.
Local Ltac args_to_bounded x H :=
  let t := type of x in
  let m := get_inner_len t in
  let n := get_outer_len t in
  let H := constr:(fun Hbs => @nm_op_args_to_bounded n m _ Hbs x H) in
  let H := (eval cbv beta in (H eq_refl)) in
  exact H.

Definition binop_args_to_bounded (x : fe25519W * fe25519W)
           (H : is_bounded (fe25519WToZ (fst x)) = true)
           (H' : is_bounded (fe25519WToZ (snd x)) = true)
  : interp_flat_type (fun _ => BoundedWordW.BoundedWord) (domain ExprBinOpT).
Proof. args_to_bounded x (conj H H'). Defined.
Definition unop_args_to_bounded (x : fe25519W) (H : is_bounded (fe25519WToZ x) = true)
  : interp_flat_type (fun _ => BoundedWordW.BoundedWord) (domain ExprUnOpT).
Proof. args_to_bounded x H. Defined.
Definition unopWireToFE_args_to_bounded (x : wire_digitsW) (H : wire_digits_is_bounded (wire_digitsWToZ x) = true)
  : interp_flat_type (fun _ => BoundedWordW.BoundedWord) (domain ExprUnOpWireToFET).
Proof. args_to_bounded x H. Defined.
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
  : interp_flat_type (fun _ => BoundedWordW.BoundedWord) (domain Expr9_4OpT).
Proof. args_to_bounded x (conj (conj (conj (conj (conj (conj (conj (conj H0 H1) H2) H3) H4) H5) H6) H7) H8). Defined.
Local Ltac make_bounds_prop' bounds bounds' :=
  first [ refine (andb _ _);
          [ destruct bounds' as [bounds' _], bounds as [bounds _]
          | destruct bounds' as [_ bounds'], bounds as [_ bounds] ];
          try make_bounds_prop' bounds bounds'
        | exact (match bounds' with
                 | Some bounds' => let (l, u) := bounds in
                                   let (l', u') := bounds' in
                                   ((l' <=? l) && (u <=? u'))%Z%bool
                 | None => false
                 end) ].
Local Ltac make_bounds_prop bounds orig_bounds :=
  let bounds' := fresh "bounds'" in
  pose orig_bounds as bounds';
  make_bounds_prop' bounds bounds'.
Definition unop_bounds_good (bounds : interp_flat_type (fun _ => ZBounds.bounds) (codomain ExprUnOpT)) : bool.
Proof. make_bounds_prop bounds ExprUnOp_bounds. Defined.
Definition binop_bounds_good (bounds : interp_flat_type (fun _ => ZBounds.bounds) (codomain ExprBinOpT)) : bool.
Proof. make_bounds_prop bounds ExprUnOp_bounds. Defined.
Definition unopFEToWire_bounds_good (bounds : interp_flat_type (fun _ => ZBounds.bounds) (codomain ExprUnOpFEToWireT)) : bool.
Proof. make_bounds_prop bounds ExprUnOpWireToFE_bounds. Defined.
Definition unopWireToFE_bounds_good (bounds : interp_flat_type (fun _ => ZBounds.bounds) (codomain ExprUnOpWireToFET)) : bool.
Proof. make_bounds_prop bounds ExprUnOp_bounds. Defined.
(* TODO FIXME(jgross?, andreser?): Is every function returning a single Z a boolean function? *)
Definition unopFEToZ_bounds_good (bounds : interp_flat_type (fun _ => ZBounds.bounds) (codomain ExprUnOpFEToZT)) : bool.
Proof.
  refine (let (l, u) := bounds in ((0 <=? l) && (u <=? 1))%Z%bool).
Defined.
Definition op9_4_bounds_good (bounds : interp_flat_type (fun _ => ZBounds.bounds) (codomain Expr9_4OpT)) : bool.
Proof. make_bounds_prop bounds Expr4Op_bounds. Defined.
(*Definition ApplyUnOp {var} (f : exprUnOp var) : exprArg var -> exprArg var
  := fun x
     => LetIn (invert_Return (unop_make_args x))
              (fun k => invert_Return (Apply length_fe25519 f k)).
Definition ApplyBinOp {var} (f : exprBinOp var) : exprArg var -> exprArg var -> exprArg var
  := fun x y
     => LetIn (invert_Return (unop_make_args x))
              (fun x'
               => LetIn (invert_Return (unop_make_args y))
                        (fun y'
                         => invert_Return (Apply length_fe25519
                                            (Apply length_fe25519
                                                   f x') y'))).
Definition ApplyUnOpFEToWire {var} (f : exprUnOpFEToWire var) : exprArg var -> exprArgWire var
  := fun x
     => LetIn (invert_Return (unop_make_args x))
              (fun k => invert_Return (Apply length_fe25519 f k)).
Definition ApplyUnOpWireToFE {var} (f : exprUnOpWireToFE var) : exprArgWire var -> exprArg var
  := fun x
     => LetIn (invert_Return (unop_wire_make_args x))
              (fun k => invert_Return (Apply (List.length wire_widths) f k)).
Definition ApplyUnOpFEToZ {var} (f : exprUnOpFEToZ var) : exprArg var -> exprZ var
  := fun x
     => LetIn (invert_Return (unop_make_args x))
              (fun k => invert_Return (Apply length_fe25519 f k)).
*)

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
                    interp_flat_type_eta interp_flat_type_eta_gen
                    curry_binop_fe25519W curry_unop_fe25519W curry_unop_wire_digitsW curry_9op_fe25519W
                    curry_binop_fe25519 curry_unop_fe25519 curry_unop_wire_digits curry_9op_fe25519
                    uncurry_binop_fe25519W uncurry_unop_fe25519W uncurry_unop_wire_digitsW uncurry_9op_fe25519W
                    uncurry_binop_fe25519 uncurry_unop_fe25519 uncurry_unop_wire_digits uncurry_9op_fe25519
                    ExprBinOpT ExprUnOpFEToWireT ExprUnOpT ExprUnOpFEToZT ExprUnOpWireToFET Expr9_4OpT Expr4OpT] in *;
  cbv zeta in *;
  simpl @fe25519WToZ; simpl @wire_digitsWToZ;
  rewrite <- Heq; clear Heq;
  destruct Hbounds as [Heq Hbounds];
  change interp_op with (@Z.interp_op) in *;
  change interp_base_type with (@Z.interp_base_type) in *;
  change word64 with WordW.wordW in *;
  rewrite <- Heq; clear Heq;
  destruct Hbounds as [ Hbounds0 [Hbounds1 Hbounds2] ];
  pose proof (fun pf => Relations.uncurry_interp_type_rel_pointwise_proj_from_option2 WordW.to_Z pf Hbounds2 Hbounds0) as Hbounds_left;
  pose proof (fun pf => Relations.uncurry_interp_type_rel_pointwise_proj1_from_option2 Relations.related_wordW_boundsi' pf Hbounds1 Hbounds2) as Hbounds_right;
  specialize_by repeat first [ progress intros
                             | progress unfold RelationClasses.Reflexive
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
         Tuple.map Tuple.map' Tuple.on_tuple Tuple.to_list Tuple.to_list' List.map Tuple.from_list Tuple.from_list
         Relations.proj_eq_rel SmartVarfMap interp_flat_type smart_interp_flat_map domain fst snd BoundedWordW.to_wordW' BoundedWordW.boundedWordToWordW BoundedWord.value Relations.related_wordW_boundsi' Relations.related'_wordW_bounds Bounds.upper Bounds.lower codomain WordW.to_Z nm_op_args_to_bounded nm_op_args_to_bounded' n_op_args_to_bounded n_op_args_to_bounded' unop_args_to_bounded' Relations.interp_flat_type_rel_pointwise Relations.interp_flat_type_rel_pointwise_gen_Prop] in Hbounds_left, Hbounds_right;
  simpl @fst in Hbounds_left, Hbounds_right; simpl @snd in Hbounds_left, Hbounds_right;
  simpl @interp_flat_type in *;
  (let v := (eval unfold WordW.interp_base_type in (WordW.interp_base_type TZ)) in
   change (WordW.interp_base_type TZ) with v in *);
  cbv beta iota zeta in *;
  lazymatch goal with
  | [ |- fe25519WToZ ?x = _ /\ _ ]
    => generalize dependent x; intros
  | [ |- wire_digitsWToZ ?x = _ /\ _ ]
    => generalize dependent x; intros
  | [ |- (Tuple.map fe25519WToZ ?x = _) /\ _ ]
    => generalize dependent x; intros
  | [ |- ((Tuple.map fe25519WToZ ?x = _) * _)%type ]
    => generalize dependent x; intros
  | [ |- _ = _ ]
    => exact Hbounds_left
  end;
  cbv [interp_type interp_type_gen interp_type_gen_hetero interp_flat_type WordW.interp_base_type codomain] in *;
  destruct_head' prod;
  change word64ToZ with WordW.wordWToZ in *;
  (split; [ exact Hbounds_left | ]);
  cbv [interp_flat_type] in *;
  cbv [fst snd
           Tuple.map Tuple.map' Tuple.on_tuple Tuple.to_list Tuple.to_list' List.map Tuple.from_list Tuple.from_list Tuple.from_list'
           make_bound
           Datatypes.length wire_widths wire_digit_bounds PseudoMersenneBaseParams.limb_widths bounds
           binop_bounds_good unop_bounds_good unopFEToWire_bounds_good unopWireToFE_bounds_good unopFEToZ_bounds_good op9_4_bounds_good
           ExprUnOp_bounds ExprBinOp_bounds ExprUnOpFEToWire_bounds ExprUnOpFEToZ_bounds ExprUnOpWireToFE_bounds Expr9Op_bounds Expr4Op_bounds] in H1;
  destruct_head' ZBounds.bounds;
  unfold_is_bounded_in H1;
  simpl @fe25519WToZ; simpl @wire_digitsWToZ;
  destruct_head' and;
  Z.ltb_to_lt;
  change WordW.wordWToZ with word64ToZ in *;
  cbv [Tuple.map Tuple.map' HList.hlist Tuple.on_tuple Tuple.from_list Tuple.from_list' Tuple.to_list Tuple.to_list' List.map HList.hlist' fst snd fe25519WToZ HList.hlistP HList.hlistP'];
  cbv [WordW.bit_width BitSize64.bit_width Z.of_nat Pos.of_succ_nat Pos.succ] in *;
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
  | apply @InterpWf;
    [ | apply wf_ropW ].. ];
  auto with interp_related.

Notation rword_of_Z rexprZ_sig := (proj1_sig rexprZ_sig) (only parsing).

Notation compute_bounds opW bounds
  := (Interp (@ZBounds.interp_op) opW bounds)
       (only parsing).

Notation rexpr_wfT e := (Wf.Wf e) (only parsing).

Ltac prove_rexpr_wfT
  := reflect_Wf Equality.base_type_eq_semidec_is_dec Equality.op_beq_bl.

Module Export PrettyPrinting.
  (* We add [enlargen] to force [bounds_on] to be in [Type] in 8.4 and
     8.5/8.6.  Because [Set] is special and things break if
     [bounds_on] ends up in [Set] for reasons jgross hasn't bothered
     to debug. *)
  Inductive bounds_on := overflow | in_range (lower upper : Z) | enlargen (_ : Set).

  Inductive result := yes | no | borked.

  Definition ZBounds_to_bounds_on
    := fun (t : base_type) (x : ZBounds.interp_base_type t)
       => match x with
          | Some {| Bounds.lower := l ; Bounds.upper := u |}
            => in_range l u
          | None
            => overflow
          end.

  Fixpoint does_it_overflow {t} : interp_flat_type (fun t : base_type => bounds_on) t -> result
    := match t return interp_flat_type _ t -> result with
       | Tbase _ => fun v => match v with
                             | overflow => yes
                             | in_range _ _ => no
                             | enlargen _ => borked
                             end
       | Unit => fun _ => no
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
