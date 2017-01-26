(** * PHOAS Representation of Gallina which allows exact denotation *)
Require Import Coq.Strings.String.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.InterpProofs.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

(** We parameterize the language over a type of basic type codes (for
    things like [Z], [word], [bool]), as well as a type of n-ary
    operations returning one value, and n-ary operations returning two
    values. *)
Local Open Scope ctype_scope.
Section language.
  Context (base_type_code : Type).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).

  Section expr_param.
    Context (interp_base_type : base_type_code -> Type).
    Context (op : flat_type (* input tuple *) -> flat_type (* output type *) -> Type).
    Local Notation interp_type := (interp_type interp_base_type).
    Local Notation interp_flat_type_gen := interp_flat_type.
    Local Notation interp_flat_type := (interp_flat_type interp_base_type).
    Section expr.
      Context {var : flat_type -> Type}.

      (** N.B. [Let] destructures pairs *)
      Inductive exprf : flat_type -> Type :=
      | Const {t : flat_type} : interp_flat_type t -> exprf t
      | Var {t} : var t -> exprf t
      | Op {t1 tR} : op t1 tR -> exprf t1 -> exprf tR
      | LetIn : forall {tx}, exprf tx -> forall {tC}, (var tx -> exprf tC) -> exprf tC
      | Pair : forall {t1}, exprf t1 -> forall {t2}, exprf t2 -> exprf (Prod t1 t2)
      | MatchPair : forall {t1 t2}, exprf (Prod t1 t2) -> forall {tC}, (var t1 -> var t2 -> exprf tC) -> exprf tC.
      Inductive expr : type -> Type :=
      | Return {t} : exprf t -> expr t
      | Abs {src dst} : (var (Tbase src) -> expr dst) -> expr (Arrow src dst).
      Global Coercion Return : exprf >-> expr.
    End expr.

    Definition Expr (t : type) := forall var, @expr var t.

    Section interp.
      Context (interp_op : forall src dst, op src dst -> interp_flat_type src -> interp_flat_type dst).

      Fixpoint interpf {t} (e : @exprf interp_flat_type t) : interp_flat_type t
        := match e in exprf t return interp_flat_type t with
           | Const _ x => x
           | Var _ x => x
           | Op _ _ op args => @interp_op _ _ op (@interpf _ args)
           | LetIn _ ex _ eC => let x := @interpf _ ex in @interpf _ (eC x)
           | Pair _ ex _ ey => (@interpf _ ex, @interpf _ ey)
           | MatchPair _ _ ex _ eC => match @interpf _ ex with pair x y => @interpf _ (eC x y) end
           end.
      Fixpoint interp {t} (e : @expr interp_flat_type t) : interp_type t
        := match e in expr t return interp_type t with
           | Return _ x => interpf x
           | Abs _ _ f => fun x => @interp _ (f x)
           end.

      Definition Interp {t} (E : Expr t) : interp_type t := interp (E _).
    End interp.

    Section compile.
      Context {var : base_type_code -> Type}
              (make_const : forall t, interp_base_type t -> op Unit (Tbase t)).

      Fixpoint SmartConst (t : flat_type) : interp_flat_type t -> Syntax.exprf base_type_code op (var:=var) t
        := match t return interp_flat_type t -> Syntax.exprf _ _ t with
           | Unit => fun _ => TT
           | Tbase _ => fun v => Syntax.Op (make_const _ v) TT
           | Prod _ _ => fun v => Syntax.Pair (@SmartConst _ (fst v))
                                              (@SmartConst _ (snd v))
           end.

      Fixpoint compilef {t} (e : @exprf (interp_flat_type_gen var) t) : @Syntax.exprf base_type_code op var t
        := match e in exprf t return @Syntax.exprf _ _ _ t with
           | Const _ x => @SmartConst _ x
           | Var _ x => SmartMap.SmartVarf x
           | Op _ _ op args => Syntax.Op op (@compilef _ args)
           | LetIn _ ex _ eC => Syntax.LetIn (@compilef _ ex) (fun x => @compilef _ (eC x))
           | Pair _ ex _ ey => Syntax.Pair (@compilef _ ex) (@compilef _ ey)
           | MatchPair _ _ ex _ eC => Syntax.LetIn (@compilef _ ex) (fun xy => @compilef _ (eC (fst xy) (snd xy)))
           end.

      Fixpoint compile {t} (e : @expr (interp_flat_type_gen var) t) : @Syntax.expr base_type_code op var t
        := match e in expr t return @Syntax.expr _ _ _ t with
           | Return _ x => Syntax.Return (compilef x)
           | Abs a _ f => Syntax.Abs (fun x : var a => @compile _ (f x))
           end.
    End compile.

    Definition Compile
               (make_const : forall t, interp_base_type t -> op Unit (Tbase t))
               {t} (e : Expr t) : Syntax.Expr base_type_code op t
      := fun var => compile make_const (e _).

    Section compile_correct.
      Context (make_const : forall t, interp_base_type t -> op Unit (Tbase t))
              (interp_op : forall src dst, op src dst -> interp_flat_type src -> interp_flat_type dst)
              (make_const_correct : forall T v, interp_op Unit (Tbase T) (make_const T v) tt = v).

      Lemma SmartConst_correct t v
        : Syntax.interpf interp_op (SmartConst make_const t v) = v.
      Proof.
        induction t; try destruct v; simpl in *; congruence.
      Qed.

      Lemma compilef_correct {t} (e : @exprf interp_flat_type t)
      : Syntax.interpf interp_op (compilef make_const e) = interpf interp_op e.
      Proof.
        induction e;
          repeat match goal with
                 | _ => reflexivity
                 | _ => progress unfold LetIn.Let_In
                 | _ => progress simpl in *
                 | _ => rewrite interpf_SmartVarf
                 | _ => rewrite SmartConst_correct
                 | _ => rewrite <- surjective_pairing
                 | _ => progress rewrite_hyp *
                 | [ |- context[let (x, y) := ?v in _] ]
                   => rewrite (surjective_pairing v); cbv beta iota
                 end.
      Qed.

      Lemma Compile_correct {t} (e : @Expr t)
      : interp_type_gen_rel_pointwise (fun _ => @eq _)
                                      (Syntax.Interp interp_op (Compile make_const e))
                                      (Interp interp_op e).
      Proof.
        unfold Interp, Compile, Syntax.Interp; simpl.
        pose (e interp_flat_type) as E.
        repeat match goal with |- context[e ?f] => change (e f) with E end.
        clearbody E; clear e.
        induction E.
        { apply compilef_correct. }
        { simpl; auto. }
      Qed.

      Lemma Compile_flat_correct {t : flat_type} (e : @Expr t)
      : Syntax.Interp interp_op (Compile make_const e) = Interp interp_op e.
      Proof. exact (@Compile_correct t e). Qed.
    End compile_correct.
  End expr_param.
End language.

Global Arguments Const {_ _ _ _ _} _.
Global Arguments Var {_ _ _ _ _} _.
Global Arguments Op {_ _ _ _ _ _} _ _.
Global Arguments LetIn {_ _ _ _ _} _ {_} _.
Global Arguments MatchPair {_ _ _ _ _ _} _ {_} _.
Global Arguments Pair {_ _ _ _ _} _ {_} _.
Global Arguments Return {_ _ _ _ _} _.
Global Arguments Abs {_ _ _ _ _ _} _.
Global Arguments Compile {_ _ _} make_const {t} _ _.
