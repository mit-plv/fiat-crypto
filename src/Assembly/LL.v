Require Import Crypto.Assembly.PhoasCommon.
Require Import Crypto.Util.LetIn.

Local Arguments Let_In / _ _ _ _.

Module LL.
  Section Language.
    Context {T: Type}.
    Context {E: Evaluable T}.

    (* A very restricted language where binary operations are restricted
    to returning [T] and must appear in [let] binders, and all pairs
    must be constructed in the return clause.  No matching on pairs is
    allowed *)

    Section expr.
      Context {var: Type}.

      Inductive arg : type -> Type :=
        | Const : @interp_type T TT -> arg TT
        | Var : var -> arg TT
        | Pair : forall {t1 t2}, arg t1 -> arg t2 -> arg (Prod t1 t2).

      Inductive expr : type -> Type :=
        | LetBinop : forall {t1 t2 t3}, binop t1 t2 t3 -> arg t1 -> arg t2 ->
            forall {tC}, (arg t3 -> expr tC) -> expr tC
        | Return : forall {t}, arg t -> expr t.
    End expr.

    Definition Expr t := forall var, @expr var t.

    Fixpoint interp_arg' {V t} (f: V -> T) (e: arg t) : interp_type t :=
      match e with
      | Pair _ _ x y => (interp_arg' f x, interp_arg' f y)
      | Const x => x
      | Var x => f x
      end.

    Fixpoint interp_arg {t} (e: arg t) : interp_type t :=
      match e with
      | Pair _ _ x y => (interp_arg x, interp_arg y)
      | Const x => x
      | Var x => x
      end.

    Lemma interp_arg_spec: forall {t} (x: arg t), interp_arg x = interp_arg' id x.
    Proof.
      intros; induction x; unfold id in *; simpl; repeat f_equal;
        first [reflexivity| assumption].
    Qed.

    Fixpoint uninterp_arg {var t} (x: interp_type t) : @arg var t :=
      match t as t' return interp_type t' -> arg t' with
      | Prod t0 t1 => fun x' =>
        match x' with
        | (x0, x1) => Pair (uninterp_arg x0) (uninterp_arg x1)
        end
      | TT => Const
      end x.

    Fixpoint uninterp_arg_as_var {var t} (x: @interp_type var t) : @arg var t :=
      match t as t' return @interp_type var t' -> @arg var t' with
      | Prod t0 t1 => fun x' =>
        match x' with
        | (x0, x1) => Pair (uninterp_arg_as_var x0) (uninterp_arg_as_var x1)
        end
      | TT => Var
      end x.

    Fixpoint interp' {V t} (f: V -> T) (e:expr t) : interp_type t :=
      match e with
      | LetBinop _ _ _ op a b _ eC =>
        let x := interp_binop op (interp_arg' f a) (interp_arg' f b) in interp' f (eC (uninterp_arg x))
      | Return _ a => interp_arg' f a
      end.

    Fixpoint interp {t} (e:expr t) : interp_type t :=
      match e with
      | LetBinop _ _ _ op a b _ eC =>
        dlet x := interp_binop op (interp_arg a) (interp_arg b) in interp (eC (uninterp_arg x))
      | Return _ a => interp_arg a
      end.

    Lemma interp_spec: forall {t} (e: expr t), interp e = interp' id e.
    Proof.
      intros; induction e; unfold id in *; simpl; repeat f_equal;
        try rewrite H; simpl; repeat f_equal;
        rewrite interp_arg_spec; repeat f_equal.
    Qed.
  End Language.

  Transparent interp interp_arg.

  Example example_expr :
    (@interp Z (ZEvaluable (n := 32)) _
      (LetBinop OPadd (Const 7%Z) (Const 8%Z) (fun v => Return v)) = 15)%Z.
  Proof. reflexivity. Qed.

  Section under_lets.
    Context {T: Type}.

    Fixpoint under_lets {t var} (e: @expr T var t) {struct e} :
      forall {tC} (C: @arg T var t -> @expr T var tC), @expr T var tC :=
      match e with
      | LetBinop _ _ _ op a b tC eC => fun tC C => LetBinop op a b (fun v => @under_lets _ _ (eC v) _ C)
      | Return t a => fun _ C => C a
      end.
  End under_lets.

  Lemma under_lets_correct {T} {E: Evaluable T} {t} (e: expr t) {tC}
    (C: arg t -> expr tC)
    (C_Proper : forall a1 a2, interp_arg a1 = interp_arg a2 -> interp (C a1) = interp (C a2)) :
    forall a, interp_arg a = interp e -> interp (under_lets e C) = interp (C a).
  Proof. induction e; repeat (intuition (congruence || eauto); simpl). Qed.

  Section match_arg.
    Context {T : Type}.

    Arguments arg _ _ _ : clear implicits.
    Arguments expr _ _ _ : clear implicits.

    Definition match_arg_Prod {var t1 t2} (a:arg T var (Prod t1 t2)) : (arg T var t1 * arg T var t2) :=
      match a with
      | Pair _ _ a1 a2 => (a1, a2)
      end.

    Global Arguments match_arg_Prod / : simpl nomatch.

    Lemma match_arg_Prod_correct_helper {var t} (a: arg T var t) :
      match t return arg T var t -> Prop with
      | Prod _ _ => fun a => forall a1 a2,
        match_arg_Prod a = (a1, a2) <-> a = Pair a1 a2
      | _ => fun _ => True
      end a.
    Proof.
      unfold match_arg_Prod; destruct a;
        repeat match goal with
        | _ => split
        | _ => intro
        | _ => progress simpl in *
        | _ => break_match
        | _ => intuition congruence
        | H: _ |- _ => eapply (f_equal match_arg_Prod) in H
        end.
    Qed.

    Lemma match_arg_Prod_correct {var t1 t2} (a:arg T var (Prod t1 t2)) (a1:arg T var t1) (a2:arg T var t2) :
      match_arg_Prod a = (a1, a2) <-> a = Pair a1 a2.
    Proof.
      pose proof (match_arg_Prod_correct_helper a) as H; simpl in H; rewrite H; reflexivity.
    Qed.
  End match_arg.

  Lemma interp_arg_uninterp_arg : forall T t (a:interp_type t), @interp_arg T t (uninterp_arg a) = a.
  Proof.
    induction t as [|i0 v0 i1 v1]; simpl; intros; try reflexivity.
    break_match; subst; simpl.
    unfold interp_arg in *.
    simpl; rewrite v0, v1; reflexivity.
  Qed.

  Lemma interp_under_lets {T} {_: Evaluable T} {t: type} {tC: type}
        (e: @expr T T t)
        (C: @arg T T t -> @expr T T tC)
        (C_Proper : forall a1 a2, interp_arg a1 = interp_arg a2 ->
              interp (C a1) = interp (C a2)) :
    interp (under_lets e C) = interp (C (uninterp_arg (interp e))).
  Proof.
    intros; apply under_lets_correct;
    [ assumption
    | rewrite interp_arg_uninterp_arg; reflexivity ].
  Qed.

  Lemma Pair_eq T var t0 t1 x0 x1 x0' x1' : @Pair T var t0 t1 x0 x1 = @Pair T var t0 t1 x0' x1' <-> (x0, x1) = (x0', x1').
  Proof.
    split; intro H; try congruence.
    apply (f_equal match_arg_Prod) in H; assumption.
  Qed.
End LL.
