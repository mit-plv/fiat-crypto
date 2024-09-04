Require Import Coq.Classes.Morphisms.

Require Import Crypto.Spec.WeierstrassCurve.
Require Import Curves.Weierstrass.Affine.
Require Import Crypto.Util.Decidable Crypto.Algebra.Field.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Util.Tactics.Beta1.
Require Import Crypto.Util.Notations Crypto.Util.LetIn.
Require Import Crypto.Util.Sum Crypto.Util.Prod Crypto.Util.Sigma.
Require Import Crypto.Util.FsatzAutoLemmas.

Module Jacobian.
  Section Jacobian.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b:F}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "-" := Fsub.
    Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x). Local Notation "x ^ 3" := (x^2*x).
    Local Notation Wpoint := (@W.point F Feq Fadd Fmul a b).

    Definition point : Type := { P : F*F*F | let '(X,Y,Z) := P in
                                             if dec (Z=0) then True else Y^2 = X^3 + a*X*(Z^2)^2 + b*(Z^3)^2 }.
    Definition eq (P Q : point) : Prop :=
      match proj1_sig P, proj1_sig Q with
      | (X1, Y1, Z1), (X2, Y2, Z2) =>
        if dec (Z1 = 0) then Z2 = 0
        else Z2 <> 0 /\ X1*Z2^2 = X2*Z1^2 /\ Y1*Z2^3 = Y2*Z1^3
      end.

    (* These cases are not needed to solve the goal, but handling them early speeds things up considerably *)
    Ltac prept_step_opt :=
      match goal with
      | [ H : ?T |- ?T ] => exact H
      | [ |- ?x = ?x ] => reflexivity
      | [ H : ?T, H' : ~?T |- _ ] => solve [ exfalso; apply H', H ]
      end.

    Ltac lift_let :=
      match goal with
      | H : context G [let x := ?v in @?c x] |- _ =>
          first [is_var v | is_constructor v];
          let cx := beta1 constr:(c v) in
          let G' := context G [cx] in
          change G' in (type of H)
      | H : context G [let x := ?v in @?c x] |- _ =>
          let y := fresh x in
          pose v as y;
          let cx := beta1 constr:(c y) in
          let G' := context G [cx] in
          change G' in (type of H)
      | H := context G [let x := ?v in @?c x] |- _ =>
          first [is_var v | is_constructor v];
          let cx := beta1 constr:(c v) in
          let G' := context G [cx] in
          change G' in (value of H)
      | H := context G [let x := ?v in @?c x] |- _ =>
          let y := fresh x in
          pose v as y;
          let cx := beta1 constr:(c y) in
          let G' := context G [cx] in
          change G' in (value of H)
      | |- context G [let x := ?v in @?c x] =>
          first [is_var v | is_constructor v];
          let cx := beta1 constr:(c v) in
          let G' := context G [cx] in
          change G'
      | |- context G [let x := ?v in @?c x] =>
          let y := fresh x in
          pose v as y;
          let cx := beta1 constr:(c y) in
          let G' := context G [cx] in
          change G'
      end.

    Ltac subst_lets := repeat match goal with x := _ |- _ => subst x end.

    Ltac prept_step :=
      match goal with
      | _ => progress prept_step_opt
      | _ => progress intros
      | _ => lift_let
      (*| _ => progress specialize_by_assumption*)
      (*| _ => progress specialize_by trivial*)
      | _ => progress cbv beta match delta [proj1_sig fst snd] in *
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
    Ltac t := prept; trivial; try contradiction; subst_lets; fsatz.

    Create HintDb points_as_coordinates discriminated.
    Hint Unfold Proper respectful Reflexive Symmetric Transitive : points_as_coordinates.
    Hint Unfold point eq W.eq W.point W.coordinates W.eq W.add W.zero proj1_sig fst snd : points_as_coordinates.

    Global Instance Equivalence_eq : Equivalence eq.
    Proof. t. Qed.

    Definition of_affine_impl (P : F*F + unit) : F*F*F :=
      match  P with
      | inl (x, y) => (x, y, 1)
      | inr _ => (0, 0, 0)
      end.

    Definition of_affine (P : Wpoint) : point. refine (
      exist _ (of_affine_impl (proj1_sig P)) _).
    Proof. abstract (cbv [of_affine_impl]; t). Defined.

    Definition to_affine_impl (P : F*F*F) : F*F+unit :=
      match P return F*F+_ with
      | (X, Y, Z) =>
        if dec (Z = 0) then inr tt
        else inl (X/Z^2, Y/Z^3)
      end.

    Definition to_affine (P:point) : Wpoint. refine (exist _ (
      to_affine_impl (proj1_sig P)) _).
    Proof. abstract (cbv [to_affine_impl]; t). Defined.

    Hint Unfold to_affine_impl to_affine of_affine_impl of_affine : points_as_coordinates.

    Global Instance Proper_of_affine : Proper (W.eq ==> eq) of_affine. Proof. t. Qed.

    Lemma to_affine_of_affine P : W.eq (to_affine (of_affine P)) P.
    Proof. t. Qed.

    Lemma eq_iff P Q : eq P Q <-> W.eq (to_affine P) (to_affine Q). Proof. t. Qed.

    Global Instance Proper_to_affine : Proper (eq ==> W.eq) to_affine.
    Proof. cbv [respectful Proper]; intros. apply eq_iff; trivial. Qed.

    Lemma of_affine_to_affine P : eq (of_affine (to_affine P)) P.
    Proof. apply eq_iff, to_affine_of_affine. Qed.

    Definition iszero (P : point) := snd (proj1_sig P) = 0.

    Hint Unfold iszero : points_as_coordiantes.

    Lemma iszero_iff P : iszero P <-> W.eq (to_affine P) W.zero.
    Proof. cbv [iszero W.zero]; t. Qed.

    Definition opp (P:point) : point. refine (exist _ (
      match proj1_sig P return F*F*F with
      | (X, Y, Z) => (X, Fopp Y, Z)
      end) _).
    Proof. abstract t. Qed.

    (** From http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#doubling-dbl-2007-bl *)
    Definition double_impl (P : F*F*F) : F*F*F :=
      let z := snd P in let x := fst (fst P) in let y := snd (fst P) in
      let xx := x^2 in
      let yy := y^2 in
      let yyyy := yy^2 in
      let zz := z^2 in
      (** [s = 2*((x + yy)^2 - xx - yyyy)] *)
      let s := x + yy in
      let s := s^2 in
      let s := s - xx in
      let s := s - yyyy in
      let s := s + s in
      (** [m = 3*xx + a*zz^2] *)
      let m := zz^2 in
      let m := a * m in
      let m := m + xx in
      let m := m + xx in
      let m := m + xx in
      (** [x_out = m^2 - 2*s] *)
      let x_out := m^2 in
      let x_out := x_out - s in
      let x_out := x_out - s in
      (** [z_out = (y + z)^2 - yy - zz] *)
      let z_out := y + z in
      let z_out := z_out^2 in
      let z_out := z_out - yy in
      let z_out := z_out - zz in
      (** [y_out = m*(s-x_out) - 8*yyyy] *)
      let yyyy := yyyy + yyyy in
      let yyyy := yyyy + yyyy in
      let yyyy := yyyy + yyyy in
      let y_out := s - x_out in
      let y_out := y_out * m in
      let y_out := y_out - yyyy in
      (x_out, y_out, z_out).

    Definition double (P : point) : point. refine (exist _ (
      double_impl (proj1_sig P)) _).
    Proof. abstract (cbv [double_impl]; t). Defined.

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
    (* sanity check to get error messages that would otherwise be gobbled by [repeat] *)
    Local Ltac speed_up_fsatz_check :=
      let fld := guess_field in
      let pkg := F.get_package_on fld in
      speed_up_fsatz_step_on pkg.

    (* Everything this can solve, [t] can also solve, but this does some extra work to go faster *)
    Local Ltac pre_pre_faster_t :=
      prept; try contradiction; speed_up_fsatz.
    Local Ltac pre_faster_t :=
      pre_pre_faster_t; speed_up_fsatz_check; clean_up_speed_up_fsatz.
    Local Ltac faster_t_noclear :=
      pre_faster_t; subst_lets; fsatz.
    Local Ltac faster_t :=
      pre_faster_t;
      try solve [ lazymatch goal with
                  | [ |- _ = _ ] => clear_neq
                  | _ => idtac
                  end;
                  fsatz ].

    Hint Unfold double double_impl to_affine : points_as_coordinates.

    Lemma to_affine_double P : W.eq (to_affine (double P)) (W.add (to_affine P) (to_affine P)).
    Proof. Time faster_t_noclear. Qed.

    Lemma Proper_double : Proper (eq ==> eq) double.
    Proof. intros ???H. apply eq_iff. rewrite 2 to_affine_double, H; reflexivity. Qed.


    Definition add_impl (P Q : F*F*F) (affine_Q : bool) : F*F*F :=
      let z1 := snd P in let z2 := snd Q in let y1 := snd (fst P) in let y2 := snd (fst Q) in let x1 := fst (fst P) in let x2 := fst (fst Q) in
      let u1 := x1*z2^2 in
      let u2 := x2*z1^2 in
      let s1 := y1*z2^3 in
      let s2 := y2*z1^3 in
      let z := z1*z2 in
      let t := u1+u2 in
      let m := if dec (s1+s2 = 0) then u2-u1 else s1+s2 in
      let q := Fopp t*m^2 in
      let r := if dec (s1+s2 = 0) then s2-s1 else t^2-u1*u2 + a*(z^2)^2 in
      let x3 := r^2+q in
      let y3 := Fopp (r*((1+1)*x3+q)+m*(s1+s2)^3)/(1+1) in
      let z3 := m * z in
      if dec (s1+s2 = 0)
      then if dec (u1 = u2) then (0, 0, 0) else (x3, y3, z3)
      else (x3, y3, z3).
    Hint Unfold add_impl : points_as_coordinates.

    Definition add_nz_nz (P Q : point) : point. refine (
      exist _ (add_impl (proj1_sig P) (proj1_sig Q) false) _).
    Proof. abstract faster_t_noclear. Defined.
    Hint Unfold add_nz_nz : points_as_coordinates.

    Hint Unfold W.add' : points_as_coordinates.

    Lemma to_affine_add_nz_nz (P Q : point) (HP : ~ iszero P) (HQ : ~ iszero Q) :
      W.eq (to_affine (add_nz_nz P Q)) (W.add (to_affine P) (to_affine Q)).
    Proof.
      rewrite <-W.add'_correct.
      case P as [((x1&y1)&z1)?], Q as [((x2&y2)&z2)?].
      cbv [iszero] in *; prept.
      par: faster_t_noclear.
    Qed.

    Definition add (P Q : point) : point :=
      if dec (snd (proj1_sig P) = 0) then Q
      else if dec (snd (proj1_sig Q) = 0) then P
      else add_nz_nz P Q.
    Hint Unfold add : points_as_coordinates.

    Lemma to_affine_add (P Q : point) :
      W.eq (to_affine (add P Q)) (W.add (to_affine P) (to_affine Q)).
    Proof.
      cbv [add].
      case dec as [HP|HP]; try (setoid_rewrite iszero_iff in HP; rewrite HP; faster_t).
      case dec as [HQ|HQ]; try (setoid_rewrite iszero_iff in HQ; rewrite HQ; faster_t).
      rewrite to_affine_add_nz_nz by trivial; reflexivity.
    Qed.

    Global Instance Proper_add : Proper (eq ==> eq ==> eq) add.
    Proof. repeat intros ???H. apply eq_iff. rewrite ? to_affine_add; f_equiv; f_equiv; trivial. Qed.

    Definition add_inequal_impl (P Q : F*F*F) (affine_Q : bool) : (F*F*F)*bool :=
      let z1 := snd P in let z2 := snd Q in let y1 := snd (fst P) in let y2 := snd (fst Q) in let x1 := fst (fst P) in let x2 := fst (fst Q) in
      let z1z1 := z1^2 in
      let u2 := x2*z1z1 in
      let z2z2 := if affine_Q then Fone else z2^2 in
      let u1 := if affine_Q then x1 else x1 * z2z2 in
      let h := u2 - u1 in
      let s2 := z1*z1z1 in
      let out_z := h * z1 in
      let out_z := if affine_Q then out_z else out_z * z2 in
      let s2 := s2*y2 in
      let s1 := if affine_Q then y1 else z2*z2z2*y1 in
      let r := s2 - s1 in
      let doubling := if dec (h = 0) then if dec(r = 0) then true else false else false in
      let Hsqr := h^2 in
      let out_x := r^2 in
      let Hcub := Hsqr*h in
      let u2 := u1 * Hsqr in
      let out_x := out_x - Hcub in
      let out_x := out_x - u2 in
      let out_x := out_x - u2 in
      let h := u2 - out_x in
      let s2 := Hcub * s1 in
      let h := h * r in
      let out_y := h - s2 in
      ((out_x, out_y, out_z), doubling).

    Hint Unfold add_inequal_impl : points_as_coordinates.

    Definition add_inequal_nz_nz (P Q : point) (_ : ~ eq P Q) : point. refine (exist _ (
      fst (add_inequal_impl (proj1_sig P) (proj1_sig Q) false)) _).
    Proof. abstract faster_t_noclear. Defined.

    Definition add_affine_inequal_nz_nz (P : point) (Q : Wpoint) (_ : ~ eq P (of_affine Q)) : point. refine (exist _ (
      fst (add_inequal_impl (proj1_sig P) (proj1_sig (of_affine Q)) false)) _).
    Proof. abstract faster_t_noclear. Defined.

    Hint Unfold add_inequal_impl add_inequal_nz_nz add_affine_inequal_nz_nz : points_as_coordinates.

    Lemma snd_add_inequal_impl (P Q : point) (HP : ~ iszero P) (HQ : ~ iszero Q) :
      snd (add_inequal_impl (proj1_sig P) (proj1_sig Q) false) = true :> bool <-> eq P Q.
    Proof.
      case P as [((x1&y1)&z1)?], Q as [((x2&y2)&z2)?].
      split; [|clear HP; clear HQ; t]; cbv [iszero] in *.
      prept; try congruence; try t.
    Qed.

    Lemma to_affine_add_inequal_nz_nz P Q (H : ~ eq P Q)(HP : ~ iszero P) (HQ : ~ iszero Q)  :
      W.eq (to_affine (add_inequal_nz_nz P Q H)) (W.add (to_affine P) (to_affine Q)).
    Proof. 
      case P as [((x1&y1)&z1)?], Q as [((x2&y2)&z2)?].
      cbv [iszero] in *; prept; try apply H; prept.
      par : faster_t_noclear.
    Qed.

    Definition add_inequal (P Q : point) (H : ~ eq P Q) : point :=
      if dec (snd (proj1_sig P) = 0) then Q
      else if dec (snd (proj1_sig Q) = 0) then P
      else add_inequal_nz_nz P Q H.
    Hint Unfold add_inequal : points_as_coordinates.

    Lemma to_affine_add_inequal (P Q : point) H :
      W.eq (to_affine (add_inequal P Q H)) (W.add (to_affine P) (to_affine Q)).
    Proof.
      cbv [add_inequal].
      case dec as [HP|HP]; try (setoid_rewrite iszero_iff in HP; rewrite HP; t).
      case dec as [HQ|HQ]; try (setoid_rewrite iszero_iff in HQ; rewrite HQ; t).
      rewrite to_affine_add_inequal_nz_nz by trivial; reflexivity.
    Qed.

    Lemma add_affine_inequal_nz_nz_correct P Q H H':
      eq (add_affine_inequal_nz_nz  P Q H) (add_inequal_nz_nz P (of_affine Q) H').
    Proof. faster_t. Qed.

    Lemma to_affine_add_affine_inequal_nz_nz P Q H (_ : ~ iszero P) (_ : ~ W.eq Q W.zero) :
      W.eq (to_affine (add_affine_inequal_nz_nz P Q H)) (W.add (to_affine P) Q).
    Proof.
      unshelve rewrite @add_affine_inequal_nz_nz_correct, @to_affine_add_inequal_nz_nz, @to_affine_of_affine;
        trivial; try reflexivity.
      rewrite iszero_iff, to_affine_of_affine; trivial.
    Qed.

    Definition add_affine_inequal (P : point) (Q : Wpoint) (H : ~ eq P _) : point :=
      if dec (snd (proj1_sig P) = 0) then of_affine Q
      else match W.coordinates Q with inr _ => P | _ =>
      add_affine_inequal_nz_nz P Q H end.
    Hint Unfold add_affine_inequal : points_as_coordinates.

    Lemma to_affine_add_affine_inequal P Q H :
      W.eq (to_affine (add_affine_inequal P Q H)) (W.add (to_affine P) Q).
    Proof.
      cbv [add_affine_inequal].
      case dec as [HP|HP]; try (setoid_rewrite iszero_iff in HP; rewrite HP; t).
      case W.coordinates as [|[] ] eqn:E.
      { rewrite to_affine_add_affine_inequal_nz_nz; trivial; try reflexivity.
        cbv [W.eq]; rewrite E; cbv [W.coordinates W.zero]; case p; intuition idtac. }
      eassert (W.eq Q W.zero) as ->. { cbv [W.eq W.zero]. rewrite E. exact I. }
      faster_t.
    Qed.

    (** If [a] is -3, one can substitute a faster implementation of [double]. *)
    Section AEqMinus3.
      Context (a_eq_minus3 : a = Fopp (1+1+1)).
      Definition Fsquare x := x^2.
      Definition Ftriple x := x+x+x.
      Definition Fhalve x := x/(1+1).

      (* Based on "Guide to Elliptic Curve Cryptography" HMV'04 page 90 *)
      Definition double_minus3_impl P :=
        let x := fst (fst P) in let y := snd (fst P) in let z := snd P in
        let D := Fadd y y in
        let tmp := Fsquare z in
        let D := Fsquare D in
        let out_z := Fmul z y in
        let out_z := Fadd out_z out_z in
        let A := Fadd x tmp in
        let tmp := Fsub x tmp in
        let tmp := Ftriple tmp in
        let out_y := Fsquare D in
        let A := Fmul A tmp in
        let D := Fmul D x in
        let out_x := Fsquare A in
        let tmp := Fadd D D in
        let out_x := Fsub out_x tmp in
        let D := Fsub D out_x in
        let D := Fmul D A in
        let out_y := Fhalve out_y in
        let out_y := Fsub D out_y in
        (out_x, out_y, out_z).

      Hint Unfold Fsquare Ftriple Fhalve double_minus3_impl : points_as_coordinates.

      Definition double_minus_3 (P : point) : point. refine (exist _
        (double_minus3_impl (proj1_sig P))
        _).
      Proof. abstract faster_t. Defined.

      Hint Unfold double_minus_3 : points_as_coordinates.

      Lemma double_minus_3_eq_double (P : point) :
        eq (double P) (double_minus_3 P).
      Proof. faster_t. Qed.

      Definition double_minus3_without_halving_impl P :=
        let x := fst (fst P) in let y := snd (fst P) in let z := snd P in
        let delta := z^2 in
        let gamma := y^2 in
        let beta := x * gamma in
        let ftmp := x - delta in
        let ftmp2 := x + delta in
        let tmptmp := ftmp2 + ftmp2 in
        let ftmp2 := ftmp2 + tmptmp in
        let alpha := ftmp * ftmp2 in
        let x_out := alpha^2 in
        let fourbeta := beta + beta in
        let fourbeta := fourbeta + fourbeta in
        let tmptmp := fourbeta + fourbeta in
        let x_out := x_out - tmptmp in
        let delta := gamma + delta in
        let ftmp := y + z in
        let z_out := ftmp^2 in
        let z_out := z_out - delta in
        let y_out := fourbeta - x_out in
        let gamma := gamma + gamma in
        let gamma := gamma^2 in
        let y_out := alpha * y_out in
        let gamma := gamma + gamma in
        let y_out := y_out - gamma in
        (x_out, y_out, z_out).

      Hint Unfold double_minus3_without_halving_impl : points_as_coordinates.

      Definition double_minus3_without_halving (P : point) : point. refine (exist _
        (double_minus3_without_halving_impl (proj1_sig P))
        _).
      Proof. abstract faster_t. Defined.

      Hint Unfold double_minus3_without_halving : points_as_coordinates.

      Lemma double_minus3_without_halving_eq_double (P : point) :
        eq (double_minus3_without_halving P) (double_minus_3 P).
      Proof. abstract faster_t. Qed.
    End AEqMinus3.
  End Jacobian.
End Jacobian.
