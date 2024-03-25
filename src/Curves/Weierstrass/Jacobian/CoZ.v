Require Import Coq.Classes.Morphisms.

Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Affine Crypto.Curves.Weierstrass.AffineProofs.
Require Import Crypto.Curves.Weierstrass.Jacobian.Jacobian.
Require Import Crypto.Util.Decidable Crypto.Algebra.Field.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Util.Notations Crypto.Util.LetIn.
Require Import Crypto.Util.Sum Crypto.Util.Prod Crypto.Util.Sigma.
Require Import Crypto.Util.FsatzAutoLemmas.
Require Import Coq.PArith.BinPos.

Module Jacobian.
  Section Co_Z.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b:F}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero. Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "-" := Fsub.
    Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x). Local Notation "x ^ 3" := (x^2*x).
    Local Notation "2" := (1+1). Local Notation "4" := (2+2).
    Local Notation "8" := (4+4). Local Notation "27" := (4*4 + 4+4 +1+1+1).
    Local Notation Wpoint := (@W.point F Feq Fadd Fmul a b).
    Context {char_ge_12:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12%positive}
            {discriminant_nonzero:id(4*a*a*a + 27*b*b <> 0)}.

    Local Notation Wopp := (@W.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation Wadd := (@W.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field Feq_dec char_ge_3 a b).
    Local Notation Wzero := (@W.zero F Feq Fadd Fmul a b).
    Local Notation Weq := (@W.eq F Feq Fadd Fmul a b).

    Local Notation point := (@Jacobian.point F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation eq := (@Jacobian.eq F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation opp := (@Jacobian.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation add := (@Jacobian.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field char_ge_3).
    Local Notation double := (@Jacobian.double F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation of_affine := (@Jacobian.of_affine F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation to_affine := (@Jacobian.to_affine F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).

   (* Stolen from Jacobian.v *)
    Ltac prept_step_opt :=
      match goal with
      | [ H : ?T |- ?T ] => exact H
      | [ |- ?x = ?x ] => reflexivity
      | [ H : ?T, H' : ~?T |- _ ] => solve [ exfalso; apply H', H ]
      end.

    Ltac prept_step :=
      match goal with
      | _ => progress prept_step_opt
      | _ => progress intros
      (*| _ => progress specialize_by_assumption*)
      (*| _ => progress specialize_by trivial*)
      | _ => progress cbv [proj1_sig fst snd] in *
      | _ => progress autounfold with points_as_coordinates in *
      | _ => progress destruct_head'_True
      | _ => progress destruct_head'_unit
      | _ => progress destruct_head'_prod
      | _ => progress destruct_head'_sig
      | _ => progress destruct_head'_and
      | _ => progress destruct_head'_sum
      | _ => progress destruct_head'_bool
      | _ => progress destruct_head'_or
      | H: context[@dec ?P ?pf] |- _ => destruct (@dec P pf)
      | |- context[@dec ?P ?pf]      => destruct (@dec P pf)
      | |- ?P => lazymatch type of P with Prop => split end
      end.
    Ltac prept := repeat prept_step.
    Ltac t := prept; trivial; try contradiction; fsatz.

    Definition x_of (P : point) : F :=
      match proj1_sig P with
      | (x, y, z) => x
      end.

    Definition y_of (P : point) : F :=
      match proj1_sig P with
      | (x, y, z) => y
      end.

    Definition z_of (P : point) : F :=
      match proj1_sig P with
      | (x, y, z) => z
      end.

    Create HintDb points_as_coordinates discriminated.
    Hint Unfold Proper respectful Reflexive Symmetric Transitive : points_as_coordinates.
    Hint Unfold Jacobian.point Jacobian.eq W.eq W.point W.coordinates proj1_sig fst snd : points_as_coordinates.
    Hint Unfold x_of y_of z_of : points_as_coordinates.

        Local Ltac clear_neq :=
      repeat match goal with
             | [ H : _ <> _ |- _ ] => clear H
             end.
    Local Ltac clear_eq :=
      repeat match goal with
             | [ H : _ = _ |- _ ] => clear H
             end.
    Local Ltac clear_eq_and_neq :=
      repeat (clear_eq || clear_neq).
    Local Ltac clean_up_speed_up_fsatz :=
      repeat match goal with
             | [ H : forall a : F, _ = _ -> _ = _ |- _ ] => clear H
             | [ H : forall a : F, _ <> _ -> _ = _ |- _ ] => clear H
             | [ H : forall a : F, _ <> _ -> _ <> _ |- _ ] => clear H
             | [ H : forall a b : F, _ = _ |- _ ] => clear H
             | [ H : forall a b : F, _ = _ -> _ = _ |- _ ] => clear H
             | [ H : forall a b : F, _ <> _ -> _ = _ |- _ ] => clear H
             | [ H : forall a b : F, _ <> _ -> _ <> _ |- _ ] => clear H
             | [ H : forall a b : F, _ = _ -> _ <> _ -> _ = _ |- _ ] => clear H
             | [ H : forall a b : F, _ <> _ -> _ <> _ -> _ = _ |- _ ] => clear H
             | [ H : forall a b : F, _ <> _ -> _ <> _ -> _ <> _ |- _ ] => clear H
             | [ H : forall a b c : F, _ |- _ ] => clear H
             | [ H : ?T, H' : ?T |- _ ] => clear H'
             | [ H : ?x = ?x |- _ ] => clear H
             | [ H : ?x <> 0, H' : ?x = 1 |- _ ] => clear H
             | [ H : ?x = 0 |- _ ] => is_var x; clear H x
             | [ H : ?x = 1 |- _ ] => is_var x; clear H x
             | [ H : Finv (?x^3) <> 0, H' : ?x <> 0 |- _ ] => clear H
             end.
    Local Ltac find_and_do_or_prove_by ty by_tac tac :=
      lazymatch goal with
      | [ H' : ty |- _ ]
        => tac H'
      | _
        => assert ty by by_tac
      end.
    Local Ltac find_and_do_or_prove_by_fsatz ty tac :=
      find_and_do_or_prove_by ty ltac:(clear_eq_and_neq; intros; fsatz) tac.
    Local Ltac find_and_do_or_prove_by_fsatz_with_neq ty tac :=
      find_and_do_or_prove_by ty ltac:(clear_neq; intros; fsatz) tac.
    Local Ltac find_and_goal_apply_or_prove_by_fsatz ty :=
      find_and_do_or_prove_by_fsatz ty ltac:(fun H' => apply H').
    Local Ltac find_and_apply_or_prove_by_fsatz H ty :=
      find_and_do_or_prove_by_fsatz ty ltac:(fun H' => apply H' in H).
    Local Ltac find_and_apply_or_prove_by_fsatz2 H0 H1 ty :=
      find_and_do_or_prove_by_fsatz ty ltac:(fun H' => apply H' in H0; [ | exact H1 ]).
    Local Ltac find_and_apply_or_prove_by_fsatz' H ty preapp :=
      find_and_do_or_prove_by_fsatz ty ltac:(fun H' => let H' := preapp H' in apply H' in H).
    Local Ltac speed_up_fsatz_step_on pkg :=
      let goal_if_var_neq_zero (* we want to keep lazymatch below, so we hack backtracking on is_var *)
          := match goal with
             | [ |- ?x <> 0 ] => let test := match goal with _ => is_var x end in
                                 constr:(x <> 0)
             | _ => I
             end in
      lazymatch goal with
      | [ H : False |- _ ] => solve [ exfalso; exact H ]
      | [ H : ?T |- ?T ] => exact H
      | [ H : ?x <> ?x |- _ ] => solve [ exfalso; apply H; reflexivity ]
      | [ H : ?x = ?y, H' : ?x <> ?y |- _ ] => solve [ exfalso; apply H', H ]
      | [ H : ?x = 0 |- ?x * ?y <> 0 ] => exfalso
      | [ H : ?y = 0 |- ?x * ?y <> 0 ] => exfalso
      | [ H : ~?T |- ?T ] => exfalso
      | [ H : ?T |- ~?T ] => exfalso
      | [ H : ?x - ?x = 0 |- _ ] => clear H
      | [ H : ?x * ?y = 0, H' : ?x = 0 |- _ ] => clear H
      | [ H : ?x * ?y = 0, H' : ?y = 0 |- _ ] => clear H
      | [ |- goal_if_var_neq_zero ] => intro
      | [ H : ?x = Fopp ?x |- _ ]
        => F.apply_lemma_in_on pkg H (forall a, a = Fopp a -> a = 0)
      | [ H : ?x <> Fopp ?x |- _ ]
        => F.apply_lemma_in_on pkg H (forall a, a <> Fopp a -> a <> 0)
      | [ H : ?x + ?x = 0 |- _ ]
        => F.apply_lemma_in_on pkg H (forall y, y + y = 0 -> y = 0)
      | [ H : Finv (?x^3) = 0, H' : ?x <> 0 |- _ ]
        => F.apply2_lemma_in_on pkg H H' (forall a, Finv (a^3) = 0 -> a <> 0 -> False)
      | [ H : ?x - ?y = 0, H' : ?y <> ?x |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b, a - b = 0 -> b = a)
      | [ H : ?x - ?y = 0, H' : ?x <> ?y |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b, a - b = 0 -> a = b)
      | [ H : ?x * ?y * ?z <> 0, H' : ?y <> 0 |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b c, a * b * c <> 0 -> a * c <> 0)
      | [ H : ?x * ?y^3 <> 0, H' : ?y <> 0 |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b, a * b <> 0 -> a <> 0)
      | [ H : ?x * ?y^2 <> 0, H' : ?y <> 0 |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b, a * b <> 0 -> a <> 0)
      | [ H : ?x^2 - ?y^2 = ?z |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b c, a^2 - b^2 = c -> (a - b) * (a + b) = c)
      | [ H : ?x + ?y * ?z = 0, H' : ?x <> Fopp (?z * ?y) |- _ ]
        => F.apply2_lemma_in_on pkg H H' (forall a b c, a + b * c = 0 -> a <> Fopp (c * b) -> False)
      | [ H : ?x + ?x <> 0 |- _ ]
        => F.apply_lemma_in_on pkg H (forall a, a + a <> 0 -> a <> 0)
      | [ H : ?x - ?y <> 0, H' : ?y = ?x |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b, a - b <> 0 -> b <> a)
      | [ H : ?x - ?y <> 0, H' : ?x = ?y |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b, a - b <> 0 -> a <> b)
      | [ H : (?x + ?y)^2 - (?x^2 + ?y^2) = 0 |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b, (a + b)^2 - (a^2 + b^2) = 0 -> a * b = 0)
      | [ H : (?x + ?y)^2 - (?x^2 + ?y^2) <> 0 |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b, (a + b)^2 - (a^2 + b^2) <> 0 -> a * b <> 0)
      | [ H : ?x * ?y = 0, H' : ?x <> 0 |- _ ]
        => F.apply2_lemma_in_on pkg H H' (forall a b, a * b = 0 -> a <> 0 -> b = 0)
      | [ H : ?x * ?y = 0, H' : ?y <> 0 |- _ ]
        => F.apply2_lemma_in_on pkg H H' (forall a b, a * b = 0 -> b <> 0 -> a = 0)
      | [ H : ?x * ?y <> 0, H' : ?x <> 0 |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b, a * b <> 0 -> b <> 0)
      | [ H : ?x * ?y <> 0, H' : ?y <> 0 |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b, a * b <> 0 -> a <> 0)
      | [ H : ?x * ?y <> 0, H' : ?x = 0 |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b, a * b <> 0 -> a <> 0)
      | [ H : ?x * ?y <> 0, H' : ?y = 0 |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b, a * b <> 0 -> b <> 0)
      | [ |- (?x + ?y)^2 - (?x^2 + ?y^2) = 0 ]
        => F.goal_apply_lemma_on pkg (forall a b, a * b = 0 -> (a + b)^2 - (a^2 + b^2) = 0)
      | [ |- (?x + ?y)^2 - (?x^2 + ?y^2) <> 0 ]
        => F.goal_apply_lemma_on pkg (forall a b, a * b <> 0 -> (a + b)^2 - (a^2 + b^2) <> 0)
      | [ |- (?x + ?y)^2 - ?x^2 - ?y^2 = 0 ]
        => F.goal_apply_lemma_on pkg (forall a b, a * b = 0 -> (a + b)^2 - a^2 - b^2 = 0)
      | [ |- (?x + ?y)^2 - ?x^2 - ?y^2 <> 0 ]
        => F.goal_apply_lemma_on pkg (forall a b, a * b <> 0 -> (a + b)^2 - a^2 - b^2 <> 0)
      | [ H : (?x + ?y)^2 - (?x^2 + ?y^2) = 0 |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b, (a + b)^2 - (a^2 + b^2) = 0 -> a * b = 0)
      | [ H : (?x + ?y)^2 - (?x^2 + ?y^2) <> 0 |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b, (a + b)^2 - (a^2 + b^2) <> 0 -> a * b <> 0)
      | [ H : (?x + ?y)^2 - ?x^2 - ?y^2 = 0 |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b, (a + b)^2 - a^2 - b^2 = 0 -> a * b = 0)
      | [ H : (?x + ?y)^2 - ?x^2 - ?y^2 <> 0 |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b, (a + b)^2 - a^2 - b^2 <> 0 -> a * b <> 0)
      | [ H : ?x = 0 |- ?x * ?y = 0 ]
        => F.goal_apply_lemma_on pkg (forall a b, a = 0 -> a * b = 0)
      | [ H : ?y = 0 |- ?x * ?y = 0 ]
        => F.goal_apply_lemma_on pkg (forall a b, b = 0 -> a * b = 0)
      | [ H : ?x <> 0 |- ?x * ?y <> 0 ]
        => F.goal_apply_lemma_on pkg (forall a b, a <> 0 -> b <> 0 -> a * b <> 0)
      | [ H : ?y <> 0 |- ?x * ?y <> 0 ]
        => F.goal_apply_lemma_on pkg (forall a b, a <> 0 -> b <> 0 -> a * b <> 0)
      | [ H : ?x <> 0 |- ?x * ?y = 0 ]
        => F.goal_apply_lemma_on pkg (forall a b, b = 0 -> a * b = 0)
      | [ H : ?y <> 0 |- ?x * ?y = 0 ]
        => F.goal_apply_lemma_on pkg (forall a b, a = 0 -> a * b = 0)

      | [ H : ?x - ?y * ?z <> ?w, H' : ?y = 1 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c d, a - b * c <> d -> b = 1 -> a - c <> d) ltac:(fun H'' => constr:(fun Hv => H'' x y z w Hv H'))
      | [ H : ?x - ?y * ?z = ?w, H' : ?y = 1 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c d, a - b * c = d -> b = 1 -> a - c = d) ltac:(fun H'' => constr:(fun Hv => H'' x y z w Hv H'))
      | [ H : ?x - ?y * ?z * ?w <> ?v, H' : ?y = 1 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c d e, a - b * c * d <> e -> b = 1 -> a - c * d <> e) ltac:(fun H'' => constr:(fun Hv => H'' x y z w v Hv H'))
      | [ H : ?x - ?y * ?z * ?w = ?v, H' : ?y = 1 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c d e, a - b * c * d = e -> b = 1 -> a - c * d = e) ltac:(fun H'' => constr:(fun Hv => H'' x y z w v Hv H'))
      | [ H : ?x - ?y * ?z^2 <> ?w, H' : ?z = 1 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c d, a - b * c^2 <> d -> c = 1 -> a - b <> d) ltac:(fun H'' => constr:(fun Hv => H'' x y z w Hv H'))
      | [ H : ?x - ?y * ?z^2 = ?w, H' : ?z = 1 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c d, a - b * c^2 = d -> c = 1 -> a - b = d) ltac:(fun H'' => constr:(fun Hv => H'' x y z w Hv H'))

      | [ H : ?x - ?y + ?z <> ?w, H' : ?y = 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c d, a - b + c <> d -> b = 0 -> a + c <> d) ltac:(fun H'' => constr:(fun Hv => H'' x y z w Hv H'))
      | [ H : ?x - ?y <> ?z, H' : ?y = 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c, a - b <> c -> b = 0 -> a <> c) ltac:(fun H'' => constr:(fun Hv => H'' x y z Hv H'))
      | [ H : ?x * ?y + ?z <> ?w, H' : ?x = 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c d, a * b + c <> d -> a = 0 -> c <> d) ltac:(fun H'' => constr:(fun Hv => H'' x y z w Hv H'))
      | [ H : ?x * ?y + ?z <> ?w, H' : ?y = 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c d, a * b + c <> d -> b = 0 -> c <> d) ltac:(fun H'' => constr:(fun Hv => H'' x y z w Hv H'))
      | [ H : ?x * ?y <> ?z, H' : ?x = 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c, a * b <> c -> a = 0 -> c <> 0) ltac:(fun H'' => constr:(fun Hv => H'' x y z Hv H'))
      | [ H : ?x * ?y <> ?z, H' : ?y = 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c, a * b <> c -> b = 0 -> c <> 0) ltac:(fun H'' => constr:(fun Hv => H'' x y z Hv H'))
      | [ H : Fopp (?x * ?y) <> ?z, H' : ?x = 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c, Fopp (a * b) <> c -> a = 0 -> c <> 0) ltac:(fun H'' => constr:(fun Hv => H'' x y z Hv H'))
      | [ H : Fopp (?x * ?y) <> ?z, H' : ?y = 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c, Fopp (a * b) <> c -> b = 0 -> c <> 0) ltac:(fun H'' => constr:(fun Hv => H'' x y z Hv H'))
      | [ H : ?x * ?y^3 = ?z, H' : ?y = 0 |- _ ]
        => F.apply2_lemma_in_on pkg H H' (forall a b c, a * b^3 = c -> b = 0 -> c = 0)
      | [ H : ?x * ?y = ?z, H' : ?x = 0 |- _ ]
        => F.apply2_lemma_in_on pkg H H' (forall a b c, a * b = c -> a = 0 -> c = 0)
      | [ H : ?x * ?y - ?z <> 0, H' : ?x = 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c, a * b - c <> 0 -> a = 0 -> c <> 0) ltac:(fun H'' => constr:(fun Hv => H'' x y z Hv H'))
      | [ H : ?x * ?y - ?z <> 0, H' : ?y = 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c, a * b - c <> 0 -> b = 0 -> c <> 0) ltac:(fun H'' => constr:(fun Hv => H'' x y z Hv H'))
      | [ H : ?x * ?y - ?z = 0, H' : ?x = 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c, a * b - c = 0 -> a = 0 -> c = 0) ltac:(fun H'' => constr:(fun Hv => H'' x y z Hv H'))
      | [ H : ?x * ?y - ?z = 0, H' : ?y = 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c, a * b - c = 0 -> b = 0 -> c = 0) ltac:(fun H'' => constr:(fun Hv => H'' x y z Hv H'))
      | [ H : ?x - ?y * ?z = 0, H' : ?z = 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c, a - b * c = 0 -> c = 0 -> a = 0) ltac:(fun H'' => constr:(fun Hv => H'' x y z Hv H'))
      | [ H : ?x * (?y * ?y^2) - ?z <> ?w |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b c d, a * (b * b^2) - c <> d -> a * (b^3) - c <> d)
      | [ H : ?x * (?y * ?y^2) - ?z = ?w |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b c d, a * (b * b^2) - c = d -> a * (b^3) - c = d)
      | [ H : ?x - (?y * ?y^2) * ?z <> ?w |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b c d, a - (b * b^2) * c <> d -> a - (b^3) * c <> d)
      | [ H : ?x - (?y * ?y^2) * ?z = ?w |- _ ]
        => F.apply_lemma_in_on pkg H (forall a b c d, a - (b * b^2) * c = d -> a - (b^3) * c = d)
      | [ H : ?x * (?y * ?y^2) = 0, H' : ?y <> 0 |- _ ]
        => F.apply2_lemma_in_on pkg H H' (forall a b, a * (b * b^2) = 0 -> b <> 0 -> a = 0)
      | [ H : ?x * (?y * ?z) = 0, H' : ?z <> 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c, c <> 0 -> a * (b * c) = 0 -> a * b = 0) ltac:(fun lem => constr:(lem x y z H'))
      | [ H : ?x = ?y * ?z, H' : ?y = 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c, a = b * c -> b = 0 -> a = 0) ltac:(fun lem => constr:(fun H => lem x y z H H'))
      | [ H : ?x * ?y + ?z = 0, H' : ?x = 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c, a = 0 -> a * b + c = 0 -> c = 0) ltac:(fun lem => constr:(lem x y z H'))
      | [ H : ?x * (?y * ?y^2) - ?z * ?z^2 * ?w = 0, H' : ?x * ?y^3 + ?w * ?z^3 = 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c d, a * b^3 + d * c^3 = 0 -> a * (b * b^2) - c * c^2 * d = 0 -> a * b^3 = 0) ltac:(fun lem => constr:(lem x y z w H'))
      | [ H : ?x * Finv (?y^2) <> ?z * Finv (?w^2), Hy : ?y <> 0, Hw : ?w <> 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c d, a * Finv (b^2) <> c * Finv (d^2) -> b <> 0 -> d <> 0 -> a * (d^2) <> c * (b^2)) ltac:(fun Hv => constr:(fun H => Hv x y z w H Hy Hw))
      | [ H : ?x * Finv (?y^2) = ?z * Finv (?w^2), Hy : ?y <> 0, Hw : ?w <> 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c d, a * Finv (b^2) = c * Finv (d^2) -> b <> 0 -> d <> 0 -> a * (d^2) = c * (b^2)) ltac:(fun Hv => constr:(fun H => Hv x y z w H Hy Hw))
      | [ H : ?x * Finv (?y^3) = Fopp (?z * Finv (?w^3)), Hy : ?y <> 0, Hw : ?w <> 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c d, a * Finv (b^3) = Fopp (c * Finv (d^3)) -> b <> 0 -> d <> 0 -> a * (d^3) = Fopp (c * (b^3))) ltac:(fun Hv => constr:(fun H => Hv x y z w H Hy Hw))
      | [ H : ?x * Finv (?y^3) <> Fopp (?z * Finv (?w^3)), Hy : ?y <> 0, Hw : ?w <> 0 |- _ ]
        => F.apply_lemma_in_on' pkg H (forall a b c d, a * Finv (b^3) <> Fopp (c * Finv (d^3)) -> b <> 0 -> d <> 0 -> a * (d^3) <> Fopp (c * (b^3))) ltac:(fun Hv => constr:(fun H => Hv x y z w H Hy Hw))
      | [ H : ?x = Fopp (?y * ?z), H' : ?x - ?z * ?y = 0 |- _ ]
        => F.apply2_lemma_in_on pkg H H' (forall a b c, a = Fopp (b * c) -> a - c * b = 0 -> a = 0)
      | [ H : ?x = Fopp (?y * ?z), H' : ?x - ?z * ?y = 0 |- _ ]
        => F.apply2_lemma_in_on pkg H H' (forall a b c, a = Fopp (b * c) -> a - c * b = 0 -> a = 0)
      | [ H : ?x <> Fopp (?y * ?z), H' : ?x - ?z * ?y = 0 |- _ ]
        => F.apply2_lemma_in_on pkg H H' (forall a b c, a <> Fopp (b * c) -> a - c * b = 0 -> a * b * c <> 0)
      | [ H : ?x <> Fopp (?y * ?z), H' : ?x - ?z * ?y = 0 |- _ ]
        => F.apply2_lemma_in_on pkg H H' (forall a b c, a <> Fopp (b * c) -> a - c * b = 0 -> a * b * c <> 0)
      | [ H : ?y^2 = ?c^3 + ?a * ?c * (?x^2)^2 + ?b * (?x^3)^2,
              H' : ?y'^2 = ?c'^3 + ?a * ?c' * (?x'^2)^2 + ?b * (?x'^3)^2,
                   H0 : ?c' * ?x^2 - ?c * ?x'^2 = 0
          |- _ ]
        => F.apply_lemma_in_on' pkg H (forall X Y X' Y' A B C C', Y^2 = C^3 + A * C * (X^2)^2 + B * (X^3)^2 -> Y'^2 = C'^3 + A * C' * (X'^2)^2 + B * (X'^3)^2 -> C' * X^2 - C * X'^2 = 0 -> (Y' * (X^3))^2 - ((X'^3) * Y)^2 = 0) ltac:(fun Hv => constr:(fun H => Hv x y x' y' a b c c' H H' H0))
      | [ H : ?y^2 = ?c^3 + ?a * ?c * (?x^2)^2 + ?b * (?x^3)^2,
              H' : ?y'^2 = ?c'^3 + ?a * ?c' * (?x'^2)^2 + ?b * (?x'^3)^2,
                   H0 : ?c' * ?x^2 = ?c * ?x'^2
          |- _ ]
        => F.apply_lemma_in_on' pkg H (forall X Y X' Y' A B C C', Y^2 = C^3 + A * C * (X^2)^2 + B * (X^3)^2 -> Y'^2 = C'^3 + A * C' * (X'^2)^2 + B * (X'^3)^2 -> C' * X^2 = C * X'^2 -> (Y' * (X^3))^2 - ((X'^3) * Y)^2 = 0) ltac:(fun Hv => constr:(fun H => Hv x y x' y' a b c c' H H' H0))

      | [ H0 : ?x * ?y^3 = ?A * ?B^3,
               H1 : ?x * ?z^3 - ?B^3 * ?D = 0,
                    H2 : ?D * ?C^3 = ?w * ?z^3,
                         H3 : ?A * ?C^3 - ?y^3 * ?w <> 0,
                              Hz : ?z <> 0,
                                   HB : ?B <> 0
          |- _ ]
        => exfalso; revert H0 H1 H2 H3 Hz HB;
           generalize x, y, z, w, A, B, C, D;
           F.goal_exact_lemma_on pkg
      | [ H0 : ?x * ?y^3 = ?A * ?B^3,
               H1 : ?x * ?z^3 - ?B^3 * ?D <> 0,
                    H2 : ?D * ?C^3 = ?w * ?z^3,
                         H3 : ?A * ?C^3 - ?y^3 * ?w = 0,
                              Hy : ?y <> 0,
                                   HC : ?C <> 0
          |- _ ]
        => exfalso; revert H0 H1 H2 H3 Hy HC;
           generalize x, y, z, w, A, B, C, D;
           F.goal_exact_lemma_on pkg
      | [ H0 : ?x * ?y^2 = ?A * ?B^2,
               H1 : ?x * ?z^2 - ?D * ?B^2 = 0,
                    H2 : ?D * ?C^2 = ?w * ?z^2,
                         H3 : ?A * ?C^2 - ?w * ?y^2 <> 0,
                              Hz : ?z <> 0,
                                   HB : ?B <> 0
          |- _ ]
        => exfalso; revert H0 H1 H2 H3 Hz HB;
           generalize x, y, z, w, A, B, C, D;
           F.goal_exact_lemma_on pkg
      | [ H0 : ?A * ?B^2 = ?x * ?y^2,
               H1 : ?x * ?z^2 - ?D * ?B^2 = 0,
                    H2 : ?w * ?z^2 = ?D * ?C^2,
                         H3 : ?A * ?C^2 - ?w * ?y^2 <> 0,
                              Hz : ?z <> 0,
                                   HB : ?B <> 0
          |- _ ]
        => exfalso; revert H0 H1 H2 H3 Hz HB;
           generalize x, y, z, w, A, B, C, D;
           F.goal_exact_lemma_on pkg
      | [ H : ?x <> 0 |- context[Finv (?x^2)] ]
        => F.with_lemma_on pkg (forall a, a <> 0 -> Finv (a^2) = (Finv a)^2) ltac:(fun H' => rewrite !(H' x H))
      | [ H : ?x <> 0 |- context[Finv (?x^3)] ]
        => F.with_lemma_on pkg (forall a, a <> 0 -> Finv (a^3) = (Finv a)^3) ltac:(fun H' => rewrite !(H' x H))
      | [ H : ?x <> 0 |- context[Finv (Finv ?x)] ]
        => F.with_lemma_on pkg (forall a, a <> 0 -> Finv (Finv a) = a) ltac:(fun H' => rewrite !(H' x H))
      | [ |- context[Finv ((?x + ?y)^2 - ?x^2 - ?y^2)] ]
        => F.with_lemma_on pkg (forall a b, (a + b)^2 - a^2 - b^2 = (1+1) * a * b) ltac:(fun H' => rewrite !(H' x y))
      | [ |- context[Finv ((?x + ?y)^2 - (?x^2 + ?y^2))] ]
        => F.with_lemma_on pkg (forall a b, (a + b)^2 - (a^2 + b^2) = (1+1) * a * b) ltac:(fun H' => rewrite !(H' x y))
      | [ |- context[Finv (?x * ?y)] ]
        => F.with_lemma_on
             pkg
             (forall a b, a * b <> 0 -> Finv (a * b) = Finv a * Finv b)
             ltac:(fun H' => rewrite !(H' x y) by (clear_eq; fsatz))
      | _ => idtac
      end.
    Local Ltac speed_up_fsatz :=
      let fld := guess_field in
      let pkg := F.get_package_on fld in
      divisions_to_inverses fld;
      repeat speed_up_fsatz_step_on pkg.
    Local Ltac speed_up_fsatz_check :=
      let fld := guess_field in
      let pkg := F.get_package_on fld in
      speed_up_fsatz_step_on pkg.

    Local Ltac pre_pre_faster_t :=
      prept; try contradiction; speed_up_fsatz.
    Local Ltac pre_faster_t :=
      pre_pre_faster_t; speed_up_fsatz_check; clean_up_speed_up_fsatz.
    Local Ltac faster_t_noclear :=
      pre_faster_t; fsatz.
    Local Ltac faster_t :=
      pre_faster_t;
      try solve [ lazymatch goal with
                  | [ |- _ = _ ] => clear_neq
                  | _ => idtac
                  end;
                  fsatz ].

    Hint Unfold Jacobian.double negb andb : points_as_coordinates.
    Hint Unfold W.eq W.add Jacobian.to_affine Jacobian.of_affine Jacobian.add Jacobian.add_impl Jacobian.opp : points_as_coordinates.

    (* These could go into Jacobian.v *)
    Global Instance Proper_opp : Proper (eq ==> eq) opp. Proof. faster_t_noclear. Qed.

    Lemma of_affine_add P Q
      : eq (of_affine (W.add P Q)) (add (of_affine P) (of_affine Q)).
    Proof. t. Qed.

    Lemma add_opp (P : point) :
      z_of (add P (opp P)) = 0.
    Proof. faster_t_noclear. Qed.

    Lemma add_comm (P Q : point) :
      eq (add P Q) (add Q P).
    Proof. faster_t_noclear. Qed.

    Lemma add_zero_l (P Q : point) (H : z_of P = 0) :
      eq (add P Q) Q.
    Proof. faster_t. Qed.

    Lemma add_zero_r (P Q : point) (H : z_of Q = 0) :
      eq (add P Q) P.
    Proof. faster_t. Qed.

    Lemma add_double (P Q : point) :
      eq P Q ->
      eq (add P Q) (double P).
    Proof. faster_t_noclear. Qed.

    (* This uses assumptions not present in Jacobian.v,
       namely char_ge_12 and discriminant_nonzero. *)
    Lemma add_assoc (P Q R : point) :
      eq (add (add P Q) R) (add P (add Q R)).
    Proof.
      rewrite <- (Jacobian.of_affine_to_affine (add (add _ _) _)).
      rewrite <- (Jacobian.of_affine_to_affine (add _ (add _ _))).
      rewrite (Jacobian.to_affine_add _ R).
      rewrite (Jacobian.to_affine_add P (add Q R)).
      do 2 rewrite of_affine_add.
      rewrite (Jacobian.to_affine_add P Q).
      rewrite (Jacobian.to_affine_add Q R).
      do 2 rewrite <- of_affine_add.
      destruct (@W.commutative_group F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec char_ge_3 char_ge_12 ltac:(cbv [id] in *; fsatz)).
      destruct commutative_group_group. destruct group_monoid.
      destruct monoid_is_associative.
      rewrite associative.
      reflexivity.
    Qed.

    Definition is_point (P : F*F*F) : Prop :=
      let '(X,Y,Z) := P in
      if dec (Z=0) then True else Y^2 = X^3 + a*X*(Z^2)^2 + b*(Z^3)^2.

    Definition co_z (P Q : point) : Prop :=
      z_of P = z_of Q.

    Lemma opp_co_z (P : point) :
      co_z P (opp P).
    Proof. unfold co_z; faster_t. Qed.

    Program Definition make_co_z (P Q : point) (HQaff : z_of Q = 1) : point*point :=
      match proj1_sig P, proj1_sig Q return (F*F*F)*(F*F*F) with
      | (x1, y1, z1), (x2, y2, z2) =>
          let t1 := x2 in
          let t2 := y2 in
          let t3 := z1 in
          let t4 := t3^2 in
          let t1 := t4 * t1 in
          let t2 := t4 * t2 in
          let t2 := t3 * t2 in
          (P, (t1, t2, t3))
      end.
    Next Obligation. Proof. faster_t. Qed.
    Next Obligation. Proof. faster_t. Qed.

    Hint Unfold is_point co_z make_co_z : points_as_coordinates.

    Lemma make_co_z_correct (P Q : point) (HQaff : z_of Q = 1)
      (HPnz : z_of P <> 0) :
      let '(A, B) := make_co_z P Q HQaff in
      eq P A
      /\ eq Q B
      /\ co_z A B.
    Proof. faster_t. Qed.

    (* Scalar Multiplication on Weierstraß Elliptic Curves from Co-Z Arithmetic *)
    (* Goundar, Joye, Miyaji, Rivain, Vanelli *)
    (* Algorithm 19 Co-Z addition with update (register allocation) *)
    (* 6 field registers, 5M, 2S *)
    Program Definition zaddu (P Q : point) (H : co_z P Q) : point * point :=
      match proj1_sig P, proj1_sig Q return (F*F*F)*(F*F*F) with
      | (x1, y1, z1), (x2, y2, z2) =>
          let t1 := x1 in
          let t2 := y1 in
          let t3 := z1 in
          let t4 := x2 in
          let t5 := y2 in
          let t6 := t1 - t4 in
          let t3 := t3 * t6 in
          let t6 := t6^2 in
          let t1 := t1 * t6 in
          let t6 := t6 * t4 in
          let t5 := t2 - t5 in
          let t4 := t5^2 in
          let t4 := t4 - t1 in
          let t4 := t4 - t6 in
          let t6 := t1 - t6 in
          let t2 := t2 * t6 in
          let t6 := t1 - t4 in
          let t5 := t5 * t6 in
          let t5 := t5 - t2 in
          ((t4, t5, t3), (t1, t2, t3))
      end.
    Next Obligation. Proof. faster_t_noclear. Qed.
    Next Obligation. Proof. faster_t. Qed.

    Hint Unfold zaddu : points_as_coordinates.

    (* ZADDU(P, Q) = (P + Q, P) if P <> Q, Q <> -P *)
    Lemma zaddu_correct (P Q : point) (H : co_z P Q)
      (Hneq : x_of P <> x_of Q):
      let '(R1, R2) := zaddu P Q H in
      eq (add P Q) R1 /\ eq P R2 /\ co_z R1 R2.
    Proof. faster_t_noclear. Qed.

    Lemma zaddu_correct_alt (P Q : point) (H : co_z P Q) :
      let '(R1, R2) := zaddu P Q H in
      z_of R1 <> 0 ->
      eq (add P Q) R1 /\ eq P R2 /\ co_z R1 R2.
    Proof.
      generalize (zaddu_correct P Q H).
      rewrite (surjective_pairing (zaddu _ _ _)).
      intros A B. apply A.
      clear -B. t.
    Qed.

    Lemma zaddu_correct0 (P : point) :
      let '(R1, R2) := zaddu P (opp P) (opp_co_z P) in
      z_of R1 = 0 /\ co_z R1 R2.
    Proof. faster_t_noclear. Qed.

    (* Scalar Multiplication on Weierstraß Elliptic Curves from Co-Z Arithmetic *)
    (* Goundar, Joye, Miyaji, Rivain, Vanelli *)
    (* Algorithm 20 Conjugate co-Z addition (register allocation) *)
    (* 7 field registers, 6M, 3S*)
    Program Definition zaddc (P Q : point) (H : co_z P Q) : point * point :=
      match proj1_sig P, proj1_sig Q return (F*F*F)*(F*F*F) with
      | (x1, y1, z1), (x2, y2, z2) =>
          let t1 := x1 in
          let t2 := y1 in
          let t3 := z1 in
          let t4 := x2 in
          let t5 := y2 in
          let t6 := t1 - t4 in
          let t3 := t3 * t6 in
          let t6 := t6^2 in
          let t7 := t1 * t6 in
          let t6 := t6 * t4 in
          let t1 := t2 + t5 in
          let t4 := t1^2 in
          let t4 := t4 - t7 in
          let t4 := t4 - t6 in
          let t1 := t2 - t5 in
          let t1 := t1^2 in
          let t1 := t1 - t7 in
          let t1 := t1 - t6 in
          let t6 := t6 - t7 in
          let t6 := t6 * t2 in
          let t2 := t2 - t5 in
          let t5 := t5 + t5 in
          let t5 := t2 + t5 in
          let t7 := t7 - t4 in
          let t5 := t5 * t7 in
          let t5 := t5 + t6 in
          let t7 := t4 + t7 in
          let t7 := t7 - t1 in
          let t2 := t2 * t7 in
          let t2 := t2 + t6 in
          ((t1, t2, t3), (t4, t5, t3))
      end.
    Next Obligation. Proof. faster_t_noclear. Qed.
    Next Obligation. Proof. faster_t_noclear. Qed.

    Hint Unfold zaddc : points_as_coordinates.
    (* ZADDC(P, Q) = (P + Q, P - Q) if P <> Q, Q <> -P *)
    Lemma zaddc_correct (P Q : point) (H : co_z P Q)
      (Hneq : x_of P <> x_of Q):
      let '(R1, R2) := zaddc P Q H in
      eq (add P Q) R1 /\ eq (add P (opp Q)) R2 /\ co_z R1 R2.
    Proof. faster_t_noclear. Qed.

    Lemma zaddc_correct_alt (P Q : point) (H : co_z P Q) :
      let '(R1, R2) := zaddc P Q H in
      z_of R1 <> 0 ->
      eq (add P Q) R1 /\ eq (add P (opp Q)) R2 /\ co_z R1 R2.
    Proof.
      generalize (zaddc_correct P Q H).
      rewrite (surjective_pairing (zaddc _ _ _)).
      intros A B. apply A.
      clear -B. t.
    Qed.

    Lemma zaddc_correct0 (P : point) :
      let '(R1, R2) := zaddc P (opp P) (opp_co_z P) in
      z_of R1 = 0 /\ co_z R1 R2.
    Proof. faster_t_noclear. Qed.

    (* Scalar Multiplication on Weierstraß Elliptic Curves from Co-Z Arithmetic *)
    (* Goundar, Joye, Miyaji, Rivain, Vanelli *)
    (* Algorithm 21 Co-Z doubling with update (register allocation) *)
    (* 6 field registers, 1M, 5S *)
    Program Definition dblu (P : point) (H: z_of P = 1) : point * point :=
      match proj1_sig P return (F*F*F)*(F*F*F) with
      | (x1, y1, _) =>
          let t0 :=  a in
          let t1 := x1 in
          let t2 := y1 in
          let t3 := t2 + t2 in
          let t2 := t2^2 in
          let t4 := t1 + t2 in
          let t4 := t4^2 in
          let t5 := t1^2 in
          let t4 := t4 - t5 in
          let t2 := t2^2 in
          let t4 := t4 - t2 in
          let t1 := t4 + t4 in
          let t0 := t0 + t5 in
          let t5 := t5 + t5 in
          let t0 := t0 + t5 in
          let t4 := t0^2 in
          let t5 := t1 + t1 in
          let t4 := t4 - t5 in
          let t2 := 8 * t2 in
          let t5 := t1 - t4 in
          let t5 := t5 * t0 in
          let t5 := t5 - t2 in
          ((t4, t5, t3), (t1, t2, t3))
      end.
    Next Obligation. Proof. faster_t. Qed.
    Next Obligation. Proof. faster_t. Qed.

    Hint Unfold dblu : points_as_coordinates.

    (* DBLU(P) = (2P, P) when Z(P) = 1 *)
    Lemma dblu_correct (P : point) (H : z_of P = 1)
      (Hynz : y_of P <> 0) :
      let '(R1, R2) := dblu P H in
      eq (double P) R1 /\ eq P R2 /\ co_z R1 R2.
    Proof. faster_t. Qed.

    Lemma dblu_correct_alt (P : point) (H : z_of P = 1) :
      let '(R1, R2) := dblu P H in
      z_of R1 <> 0 ->
      eq (double P) R1 /\ eq P R2 /\ co_z R1 R2.
    Proof.
      generalize (dblu_correct P H).
      rewrite (surjective_pairing (dblu _ _)).
      intros A B. apply A.
      clear -B. t.
    Qed.

    Lemma dblu_correct0 (P : point) (H : z_of P = 1)
      (Hyz : y_of P = 0) :
      let '(R1, R2) := dblu P H in
      z_of R1 = 0 /\ co_z R1 R2.
    Proof. faster_t. Qed.

    (* Scalar Multiplication on Weierstraß Elliptic Curves from Co-Z Arithmetic *)
    (* Goundar, Joye, Miyaji, Rivain, Vanelli *)
    (* Algorithm 22 Co-Z tripling with update (register allocation) *)
    (* 6M, 7S *)
    Program Definition tplu (P : point) (H : z_of P = 1) : point * point :=
      zaddu (snd (dblu P H)) (fst (dblu P H)) _.
    Next Obligation. faster_t. Qed.

    Hint Unfold tplu : points_as_coordinates.

    Lemma tplu_correct0 (P : point) (H : z_of P = 1) (Hyz : y_of P = 0) :
      let '(R1, R2) := tplu P H in
      z_of R1 = 0 /\ co_z R1 R2.
    Proof. faster_t. Qed.

    Lemma tplu_correct (P : point) (H : z_of P = 1) (Hynz : y_of P <> 0) :
      let '(R1, R2) := tplu P H in
      z_of R1 <> 0 ->
      eq (add (double P) P) R1 /\ eq P R2 /\ co_z R1 R2.
    Proof.
      rewrite (surjective_pairing (tplu P H)).
      unfold co_z, tplu.
      generalize (zaddu_correct_alt (snd (dblu P H)) (fst (dblu P H)) (tplu_obligation_1 P H)).
      destruct (zaddu (snd (dblu P H)) (fst (dblu P H)) (tplu_obligation_1 P H)) as [R1 R2] eqn:Hzaddu.
      intros A B. specialize (A B). destruct A as [A1 [A2 A3] ].
      generalize (dblu_correct P H Hynz).
      rewrite (surjective_pairing (dblu P H)). intros [B1 [B2 B3] ].
      simpl; repeat split; [| |assumption].
      - rewrite B1. rewrite <- A1.
        rewrite B2 at 2. apply add_comm.
      - etransitivity; eauto.
    Qed.

    (* Scalar Multiplication on Weierstraß Elliptic Curves from Co-Z Arithmetic *)
    (* Goundar, Joye, Miyaji, Rivain, Vanelli *)
    (* Co-Z doubling-addition with update (naive version) *)
    (* 11M, 5S *)
    Program Definition zdau_naive (P Q : point) (H : co_z P Q) :=
      zaddc (fst (zaddu P Q H)) (snd (zaddu P Q H)) _.
    Next Obligation. Proof. t. Qed.

    (* ZDAU(P, Q) = (2P + Q, Q) if P <> Q, Q <> -P *)
    Lemma zdau_naive_correct (P Q : point) (H : co_z P Q)
      (Hneq : x_of P <> x_of Q) :
      let '(R1, R2) := zdau_naive P Q H in
      z_of R1 <> 0 ->
      eq (add (double P) Q) R1 /\ eq Q R2 /\ co_z R1 R2.
    Proof.
      destruct (zdau_naive P Q H) as [R1 R2] eqn:HR.
      intros HR1. unfold zdau_naive in HR.
      generalize (zaddc_correct_alt (fst (zaddu P Q H)) (snd (zaddu P Q H)) (zdau_naive_obligation_1 P Q H)). rewrite HR.
      intros A. specialize (A HR1).
      destruct A as (A1 & A2 & A3).
      generalize (zaddu_correct P Q H Hneq).
      rewrite (surjective_pairing (zaddu P Q H)).
      intros (B1 & B2 & B3).
      repeat split; auto.
      - rewrite <- add_double, <- A1, <- B1, <- B2; [|reflexivity].
        rewrite add_assoc, add_comm. reflexivity.
      - rewrite <- A2, <- B1, <- B2.
        rewrite (add_comm P Q).
        rewrite add_assoc. rewrite add_zero_r; [reflexivity|apply add_opp].
    Qed.

    Lemma zdau_naive_correct_alt (P Q : point) (H : co_z P Q)
      (Hneq : x_of P <> x_of Q)
      (Hneq2: x_of (fst (zaddu P Q H)) <> x_of (snd (zaddu P Q H))) :
      let '(R1, R2) := zdau_naive P Q H in
      eq (add (double P) Q) R1 /\ eq Q R2 /\ co_z R1 R2.
    Proof.
      destruct (zdau_naive P Q H) as [R1 R2] eqn:HR.
      unfold zdau_naive in HR.
      generalize (zaddc_correct (fst (zaddu P Q H)) (snd (zaddu P Q H)) (zdau_naive_obligation_1 P Q H) Hneq2). rewrite HR.
      intros (A1 & A2 & A3).
      generalize (zaddu_correct P Q H Hneq).
      rewrite (surjective_pairing (zaddu P Q H)).
      intros (B1 & B2 & B3).
      repeat split; auto.
      - rewrite <- add_double, <- A1, <- B1, <- B2; [|reflexivity].
        rewrite add_assoc, add_comm. reflexivity.
      - rewrite <- A2, <- B1, <- B2.
        rewrite (add_comm P Q).
        rewrite add_assoc. rewrite add_zero_r; [reflexivity|apply add_opp].
    Qed.

    (* Scalar Multiplication on Weierstraß Elliptic Curves from Co-Z Arithmetic *)
    (* Goundar, Joye, Miyaji, Rivain, Vanelli *)
    (* Algorithm 23 Co-Z doubling-addition with update (register allocation) *)
    (* 8 field registers, 9M, 7S (instead of 11M, 5S) *)
    Program Definition zdau (P Q : point) (H : co_z P Q) : point * point :=
      match proj1_sig P, proj1_sig Q return (F*F*F)*(F*F*F) with
      | (x1, y1, z1), (x2, y2, z2) =>
          let t1 := x1 in
          let t2 := y1 in
          let t3 := z1 in
          let t4 := x2 in
          let t5 := y2 in
          let t6 := t1 - t4 in
          let t7 := t6^2 in
          let t1 := t1 * t7 in
          let t4 := t4 * t7 in
          let t5 := t2 - t5 in
          let t8 := t1 - t4 in
          let t2 := t2 * t8 in
          let t2 := t2 + t2 in
          let t8 := t5^2 in
          let t4 := t8 - t4 in
          let t4 := t4 - t1 in
          let t4 := t4 - t1 in
          let t6 := t4 + t6 in
          let t6 := t6^2 in
          let t6 := t6 - t7 in
          let t5 := t5 - t4 in
          let t5 := t5^2 in
          let t5 := t5 - t8 in
          let t5 := t5 - t2 in
          let t7 := t4^2 in
          let t5 := t5 - t7 in
          let t8 := t7 + t7 in
          let t8 := t8 + t8 in
          let t6 := t6 - t7 in
          let t3 := t3 * t6 in
          let t6 := t1 * t8 in
          let t1 := t1 + t4 in
          let t8 := t8 * t1 in
          let t7 := t2 + t5 in
          let t2 := t5 - t2 in
          let t1 := t8 - t6 in
          let t5 := t5 * t1 in
          let t6 := t6 + t8 in
          let t1 := t2^2 in
          let t1 := t1 - t6 in
          let t4 := t8 - t1 in
          let t2 := t2 * t4 in
          let t2 := t2 - t5 in
          let t4 := t7^2 in
          let t4 := t4 - t6 in
          let t8 := t8 - t4 in
          let t7 := t7 * t8 in
          let t5 := t7 - t5 in
          ((t1, t2, t3), (t4, t5, t3))
      end.
    Next Obligation. Proof. faster_t_noclear. Qed.
    Next Obligation. Proof. faster_t_noclear. Qed.

    Hint Unfold zdau : points_as_coordinates.

    Lemma zdau_naive_eq_zdau (P Q : point) (H : co_z P Q) :
      let '(R1, R2) := zdau_naive P Q H in
      let '(S1, S2) := zdau P Q H in
      eq R1 S1 /\ eq R2 S2.
    Proof. faster_t. all: try fsatz. Qed.

    (* Direct proof is intensive, which is why we need the naive implementation *)
    Lemma zdau_correct (P Q : point) (H : co_z P Q)
      (Hneq : x_of P <> x_of Q) :
      let '(R1, R2) := zdau P Q H in
      z_of R1 <> 0 ->
      eq (add (double P) Q) R1 /\ eq Q R2 /\ co_z R1 R2.
    Proof.
      generalize (zdau_naive_correct P Q H Hneq).
      generalize (zdau_naive_eq_zdau P Q H).
      rewrite (surjective_pairing (zdau_naive _ _ _)).
      rewrite (surjective_pairing (zdau _ _ _)).
      intros [A1 A2] X Y.
      assert (Z: forall A B, eq A B -> z_of A <> 0 -> z_of B <> 0) by (clear; intros; faster_t).
      repeat split.
      - rewrite <- A1. apply X. eapply Z; eauto. symmetry; assumption.
      - rewrite <- A2. apply X. eapply Z; eauto. symmetry; assumption.
      - clear -H. t.
    Qed.

    Lemma zdau_correct_alt (P Q : point) (H : co_z P Q)
      (Hneq : x_of P <> x_of Q)
      (Hneq2: x_of (fst (zaddu P Q H)) <> x_of (snd (zaddu P Q H))) :
      let '(R1, R2) := zdau P Q H in
      eq (add (double P) Q) R1 /\ eq Q R2 /\ co_z R1 R2.
    Proof.
      generalize (zdau_naive_correct_alt P Q H Hneq Hneq2).
      generalize (zdau_naive_eq_zdau P Q H).
      rewrite (surjective_pairing (zdau_naive _ _ _)).
      rewrite (surjective_pairing (zdau _ _ _)).
      intros [A1 A2] [A3 [A4 A5] ].
      assert (Z: forall A B, eq A B -> z_of A <> 0 -> z_of B <> 0) by (clear; intros; faster_t).
      repeat split.
      - rewrite <- A1. auto.
      - rewrite <- A2. auto.
      - clear -H. t.
    Qed.

    Lemma zdau_correct0 (P : point) :
      let '(R1, R2) := zdau P (opp P) (opp_co_z P) in
      z_of R1 = 0 /\ co_z R1 R2.
    Proof. faster_t. Qed.
  End Co_Z.
End Jacobian.
