Require Import ZArith NArith NPeano.
Require Import QhasmCommon.
Require Export Bedrock.Word Bedrock.Nomega.

Delimit Scope nword_scope with w.
Local Open Scope nword_scope.

Notation "& x" := (wordToN x) (at level 30) : nword_scope.
Notation "** x" := (NToWord _ x) (at level 30) : nword_scope.

Section Util.
  Definition convS {n m} (x: word n) (H: n = m): word m.
    refine (eq_rect _ (fun B0 : Set => B0) x _ _).
    abstract (subst; intuition).
  Defined.

  Definition low {k n: nat} (p: (k <= n)%nat) (w: word n): word k.
    refine (split1 k (n - k) (convS w _)); abstract omega.
  Defined.

  Definition high {k n: nat} (p: (k <= n)%nat) (w: word n): word (n - k).
    refine (split2 k (n - k) (convS w _)); abstract omega.
  Defined.

  Definition extend {k n: nat} (p: (k <= n)%nat) (w: word k): word n.
    refine (convS (zext w (n - k)) _); abstract omega.
  Defined.

  Definition shiftr {n} (w: word n) (k: nat): word n.
    refine match (le_dec k n) with
    | left p => extend _ (@high k _ _ w)
    | right _ => wzero n
    end; abstract nomega.
  Defined.

  Definition mask {n} (k: nat) (w: word n): word n :=
    match (le_dec k n) with
    | left p => extend p (low p w)
    | right _ => w
    end.

  Definition Nge_dec (x y: N) :
      {(x >= y)%N} + {(x < y)%N}.
    refine (
      let c := (x ?= y)%N in
      match c as c' return c = c' -> _ with
      | Lt => fun _ => right _
      | _ => fun _ => left _
      end eq_refl); abstract (
        unfold c in *; unfold N.lt, N.ge;
        repeat match goal with
        | [ H: (_ ?= _)%N = _ |- _] =>
          rewrite H; intuition; try inversion H
        | [ H: Eq = _ |- _] => inversion H
        | [ H: Gt = _ |- _] => inversion H
        | [ H: Lt = _ |- _] => inversion H
        end).
  Defined.

  Definition overflows (n: nat) (x: N) := Nge_dec x (Npow2 n).

  Definition ind (b: bool): N := if b then 1%N else 0%N.

  Definition ind' {A B} (b: {A} + {B}): N := if b then 1%N else 0%N.

  Definition break {n} (m: nat) (x: word n): word m * word (n - m).
    refine match (le_dec m n) with
    | left p => (extend _ (low p x), extend _ (@high m n _ x))
    | right p => (extend _ x, extend _ WO)
    end; try abstract intuition.
  Defined.

  Definition addWithCarry {n} (x y: word n) (c: bool): word n :=
    x ^+ y ^+ (natToWord _ (if c then 1 else 0)).

  Definition omap {A B} (x: option A) (f: A -> option B) :=
    match x with | Some y => f y | _ => None end.

  Notation "A <- X ; B" := (omap X (fun A => B)) (at level 70, right associativity).
End Util.

Close Scope nword_scope.