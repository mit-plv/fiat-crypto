Require Coq.setoid_ring.Ncring.
Require Coq.setoid_ring.Cring.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.OnSubterms.
Require Import Crypto.Util.Tactics.Revert.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Group Crypto.Algebra.Monoid.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Util.Tactics.DestructHead.
Require Coq.ZArith.ZArith Coq.PArith.PArith.


Section Ring.
  Context {T} {ok : T -> Prop} {eq : T -> T -> Prop}
          {zero one : T}
          {opp : T -> T}
          {add sub mul : T -> T -> T}.

  Record subsetoid_ring :=
    {
      zero_ok : ok zero;
      one_ok : ok one;
      opp_ok : forall x, ok x -> ok (opp x);
      add_ok : forall x y, ok x -> ok y -> ok (add x y);
      sub_ok : forall x y, ok x -> ok y -> ok (sub x y);
      mul_ok : forall x y, ok x -> ok y -> ok (mul x y);
      T_sig := { v : T | ok v };
      eq_sig := fun x y : T_sig => eq (proj1_sig x) (proj1_sig y);
      zero_sig : T_sig := exist _ _ zero_ok;
      one_sig : T_sig := exist _ _ one_ok;
      opp_sig : T_sig -> T_sig
      := fun x => exist _ _ (opp_ok _ (proj2_sig x));
      add_sig : T_sig -> T_sig -> T_sig
      := fun x y => exist _ _ (add_ok _ _ (proj2_sig x) (proj2_sig y));
      sub_sig : T_sig -> T_sig -> T_sig
      := fun x y => exist _ _ (sub_ok _ _ (proj2_sig x) (proj2_sig y));
      mul_sig : T_sig -> T_sig -> T_sig
      := fun x y => exist _ _ (mul_ok _ _ (proj2_sig x) (proj2_sig y));
      subsetoid_ring_is_ring : @ring T_sig eq_sig zero_sig one_sig opp_sig add_sig sub_sig mul_sig
    }.
  Existing Class subsetoid_ring.
  Global Existing Instance subsetoid_ring_is_ring.

  Section trivial_ok.
    Context {R:@ring T eq zero one opp add sub mul}
            (always_ok : forall x, ok x).
    Lemma subsetoid_ring_by_always_ok
      : subsetoid_ring.
    Proof.
      unshelve econstructor; intros; try apply always_ok; [].
      destruct R; clear R.
      repeat match goal with H : _ |- _ => destruct H; [] end.
      hnf in *.
      repeat unshelve econstructor; repeat intro; cbn in *;
        match goal with
        | [ H : _ |- _ ] => eapply H; eassumption
        end.
    Qed.
  End trivial_ok.
End Ring.

Section Homomorphism.
  Context {R OK EQ ZERO ONE OPP ADD SUB MUL} `{RR : @subsetoid_ring R OK EQ ZERO ONE OPP ADD SUB MUL}.
  Context {S ok eq zero one opp add sub mul} `{SS : @subsetoid_ring S ok eq zero one opp add sub mul}.
  Context {phi:R->S}.

  Record is_subsetoid_homomorphism :=
    {
      phi_ok : forall x, OK x -> ok (phi x);
      is_subsetoid_homomorphism_phi_proper
      : forall x y, OK x -> OK y -> EQ x y -> eq (phi x) (phi y);
      subsetoid_homomorphism_add
      : forall a b : R, OK a -> OK b -> eq (phi (ADD a b)) (add (phi a) (phi b));
      subsetoid_homomorphism_mul
      : forall x y : R, OK x -> OK y -> eq (phi (MUL x y)) (mul (phi x) (phi y));
      subsetoid_homomorphism_one
      : eq (phi ONE) one
    }.
  Existing Class is_subsetoid_homomorphism.
End Homomorphism.

Section Isomorphism.
  Context {F OK EQ ZERO ONE OPP ADD SUB MUL} {ringF:@subsetoid_ring F OK EQ ZERO ONE OPP ADD SUB MUL}.
  Context {H} {ok : H -> Prop} {eq : H -> H -> Prop} {zero one : H} {opp : H -> H} {add sub mul : H -> H -> H}.
  Context {phi:F->H} {phi':H->F}.
  Local Infix "=" := EQ. Local Infix "=" := EQ : type_scope.
  Context (OK_respects_EQ : Proper (EQ ==> Basics.flip Basics.impl) OK)
          (ok_respects_eq : Proper (eq ==> Basics.impl) ok)
          (phi_ok : forall x, OK x -> ok (phi x))
          (phi'_ok : forall x, ok x -> OK (phi' x))
          (phi'_phi_id : forall A, OK A -> phi' (phi A) = A)
          (phi'_eq : forall a b, EQ (phi' a) (phi' b) <-> eq a b)
          {phi'_zero : phi' zero = ZERO}
          {phi'_one : phi' one = ONE}
          {phi'_opp : forall a, ok a -> phi' (opp a) = OPP (phi' a)}
          (phi'_add : forall a b, ok a -> ok b -> phi' (add a b) = ADD (phi' a) (phi' b))
          (phi'_sub : forall a b, ok a -> ok b -> phi' (sub a b) = SUB (phi' a) (phi' b))
          (phi'_mul : forall a b, ok a -> ok b -> phi' (mul a b) = MUL (phi' a) (phi' b)).

  Lemma subsetoid_ring_by_isomorphism
    : @subsetoid_ring H ok eq zero one opp add sub mul
      /\ @is_subsetoid_homomorphism F OK EQ ONE ADD MUL H ok eq one add mul phi
      /\ @is_subsetoid_homomorphism H ok eq one add mul F OK EQ ONE ADD MUL phi'.
  Proof.
    let lem := open_constr:(@ring_by_isomorphism
                              _ _ _ _ _ _ _ _ (ringF.(subsetoid_ring_is_ring))
                              { v : H | ok v}
                              _ _ _ _ _ _ _
                              (fun x => exist _ _ (phi_ok _ (proj2_sig x)))
                              (fun x => exist _ _ (phi'_ok _ (proj2_sig x)))) in
    edestruct lem as [Hring [H0 H1] ]; cbv [eq_sig T_sig];
      [ ..
      | repeat apply conj;
        [ unshelve econstructor;
          [ .. | exact Hring ]
        | | ] ];
      cbn; intros; destruct_head'_sig; cbn;
        auto with nocore.
    1-6:(eapply ok_respects_eq; [ eapply phi'_eq, phi'_phi_id | apply phi_ok ]);
      (eapply OK_respects_EQ; [ solve [ eauto with nocore ] | ]);
      solve [ destruct ringF; auto with nocore ].
    1:clear H1.
    2:clear H0.
    all:destruct_head' @is_homomorphism; cbn in *.
    all:destruct_head' @Monoid.is_homomorphism; cbn in *.
    all:unshelve econstructor;
      cbv [Proper respectful eq_sig T_sig] in *; cbn in *.
    all:repeat match goal with
               | [ H : forall a b : sig _, _ |- _ ]
                 => specialize (fun a b apf bpf => H (exist _ a apf) (exist _ b bpf))
               end;
      cbn in *.
    all:eauto with nocore.
  Qed.
End Isomorphism.

Section IsomorphismToTrivial.
  Context {F EQ ZERO ONE OPP ADD SUB MUL} {ringF:@ring F EQ ZERO ONE OPP ADD SUB MUL}.
  Context {H} {ok : H -> Prop} {eq : H -> H -> Prop} {zero one : H} {opp : H -> H} {add sub mul : H -> H -> H}.
  Context {phi:F->H} {phi':H->F}.
  Local Infix "=" := EQ. Local Infix "=" := EQ : type_scope.
  Context (ok_respects_eq : Proper (eq ==> Basics.impl) ok)
          (phi_ok : forall x, ok (phi x))
          (phi'_phi_id : forall A, phi' (phi A) = A)
          (phi'_eq : forall a b, EQ (phi' a) (phi' b) <-> eq a b)
          {phi'_zero : phi' zero = ZERO}
          {phi'_one : phi' one = ONE}
          {phi'_opp : forall a, ok a -> phi' (opp a) = OPP (phi' a)}
          (phi'_add : forall a b, ok a -> ok b -> phi' (add a b) = ADD (phi' a) (phi' b))
          (phi'_sub : forall a b, ok a -> ok b -> phi' (sub a b) = SUB (phi' a) (phi' b))
          (phi'_mul : forall a b, ok a -> ok b -> phi' (mul a b) = MUL (phi' a) (phi' b)).

  Lemma subsetoid_ring_by_ring_isomorphism
        (OK := fun _ => True)
    : @subsetoid_ring H ok eq zero one opp add sub mul
      /\ @is_subsetoid_homomorphism F OK EQ ONE ADD MUL H ok eq one add mul phi
      /\ @is_subsetoid_homomorphism H ok eq one add mul F OK EQ ONE ADD MUL phi'.
  Proof.
    eapply @subsetoid_ring_by_isomorphism;
      [ eapply @subsetoid_ring_by_always_ok; [ eassumption | constructor ]
      | auto with nocore; try solve [ constructor ].. ].
  Qed.
End IsomorphismToTrivial.
