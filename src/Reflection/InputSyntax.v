(** * PHOAS Representation of Gallina which allows exact denotation *)
Require Import Coq.Strings.String.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.ExprInversion.
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
  Inductive type := Tflat (A : flat_type) | Arrow (A : flat_type) (B : type).

  Section expr_param.
    Context (interp_base_type : base_type_code -> Type).
    Context (op : flat_type (* input tuple *) -> flat_type (* output type *) -> Type).
    Local Notation interp_flat_type_gen := interp_flat_type.
    Local Notation interp_flat_type := (interp_flat_type interp_base_type).

    Fixpoint interp_type (t : type) :=
      match t with
      | Tflat A => interp_flat_type A
      | Arrow A B => (interp_flat_type A -> interp_type B)%type
      end.

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
      | Return {T} : exprf T -> expr (Tflat T)
      | Abs {src dst} : (var src -> expr dst) -> expr (Arrow src dst).

      Definition Fst {t1 t2} (v : exprf (Prod t1 t2)) : exprf t1 := MatchPair v (fun x y => Var x).
      Definition Snd {t1 t2} (v : exprf (Prod t1 t2)) : exprf t2 := MatchPair v (fun x y => Var y).
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
           | Return _ v => interpf v
           | Abs _ _ f => fun x => @interp _ (f x)
           end.

      Definition Interp {t} (E : Expr t) : interp_type t := interp (E _).
    End interp.

    Section compile.
      Context {var : base_type_code -> Type}
              (make_const : forall t, interp_base_type t -> op Unit (Tbase t)).

      Fixpoint compilet (t : type) : Syntax.type base_type_code
        := Syntax.Arrow
             match t with
             | Tflat T => Unit
             | Arrow A (Tflat B) => A
             | Arrow A B
               => A * domain (compilet B)
             end%ctype
             match t with
             | Tflat T => T
             | Arrow A B => codomain (compilet B)
             end.

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

      (* ugh, so much manual annotation *)
      Fixpoint compile {t} (e : @expr (interp_flat_type_gen var) t) : @Syntax.expr base_type_code op var (compilet t)
        := match e in expr t return @Syntax.expr _ _ _ (compilet t) with
           | Return _ v => Syntax.Abs (fun _ => compilef v)
           | Abs src dst f
             => let res := fun x => @compile _ (f x) in
                match dst
                      return (_ -> Syntax.expr _ _ (compilet dst))
                             -> Syntax.expr _ _ (compilet (Arrow src dst))
                with
                | Tflat T
                  => fun resf => Syntax.Abs (fun x => invert_Abs (resf x) tt)
                | Arrow A B as dst'
                  => match compilet dst' as cdst
                           return (_ -> Syntax.expr _ _ cdst)
                                  -> Syntax.expr _ _ (Syntax.Arrow
                                                        (_ * domain cdst)
                                                        (codomain cdst))
                     with
                     | Syntax.Arrow A' B'
                       => fun resf => Syntax.Abs (fun x : interp_flat_type_gen var (_ * _)
                                                  => invert_Abs (resf (fst x)) (snd x))
                     end
                end res
               end.
    End compile.

    Definition Compile
               (make_const : forall t, interp_base_type t -> op Unit (Tbase t))
               {t} (e : Expr t) : Syntax.Expr base_type_code op (compilet t)
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

      Lemma compile_flat_correct {T} (e : expr (Tflat T))
      : forall x, Syntax.interp interp_op (compile make_const e) x = interp interp_op e.
      Proof.
        intros []; simpl.
        let G := match goal with |- ?G => G end in
        let G := match (eval pattern T, e in G) with ?G _ _ => G end in
        refine match e in expr t return match t return expr t -> _ with
                                        | Tflat T => G T
                                        | _ => fun _ => True
                                        end e
               with
               | Return _ _ => _
               | Abs _ _ _ => I
               end; simpl.
        apply compilef_correct.
      Qed.

      Lemma Compile_flat_correct_flat {T} (e : Expr (Tflat T))
        : forall x, Syntax.Interp interp_op (Compile make_const e) x = Interp interp_op e.
      Proof. apply compile_flat_correct. Qed.

      Lemma Compile_correct {src dst} (e : @Expr (Arrow src (Tflat dst)))
      : forall x, Syntax.Interp interp_op (Compile make_const e) x = Interp interp_op e x.
      Proof.
        unfold Interp, Compile, Syntax.Interp; simpl.
        pose (e interp_flat_type) as E.
        repeat match goal with |- context[e ?f] => change (e f) with E end.
        clearbody E; clear e.
        let G := match goal with |- ?G => G end in
        let G := match (eval pattern src, dst, E in G) with ?G _ _ _ => G end in
        refine match E in expr t return match t return expr t -> _ with
                                        | Arrow src (Tflat dst) => G src dst
                                        | _ => fun _ => True
                                        end E
               with
               | Abs src dst e
                 => match dst
                          return (forall e : _ -> expr dst,
                                     match dst return expr (Arrow src dst) -> _ with
                                     | Tflat dst => G src dst
                                     | _ => fun _ => True
                                     end (Abs e))
                    with
                    | Tflat _
                      => fun e0 x
                         => _
                    | Arrow _ _ => fun _ => I
                    end e
               | Return _ _ => I
               end; simpl.
        refine match e0 x as e0x in expr t
                     return match t return expr t -> _ with
                            | Tflat _
                              => fun e0x
                                 => Syntax.interpf _ (invert_Abs (compile _ e0x) _)
                                    = interp _ e0x
                            | _ => fun _ => True
                            end e0x
               with
               | Abs _ _ _ => I
               | Return _ _ => _
               end; simpl.
        apply compilef_correct.
      Qed.
    End compile_correct.
  End expr_param.
End language.

Global Arguments Arrow {_} _ _.
Global Arguments Tflat {_} _.
Global Arguments Const {_ _ _ _ _} _.
Global Arguments Var {_ _ _ _ _} _.
Global Arguments Op {_ _ _ _ _ _} _ _.
Global Arguments LetIn {_ _ _ _ _} _ {_} _.
Global Arguments MatchPair {_ _ _ _ _ _} _ {_} _.
Global Arguments Fst {_ _ _ _ _ _} _.
Global Arguments Snd {_ _ _ _ _ _} _.
Global Arguments Pair {_ _ _ _ _} _ {_} _.
Global Arguments Return {_ _ _ _ _} _.
Global Arguments Abs {_ _ _ _ _ _} _.
Global Arguments Compile {_ _ _} make_const {t} _ _.
