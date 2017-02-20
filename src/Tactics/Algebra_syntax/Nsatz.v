(*** Tactics for manipulating polynomial equations *)
Require Coq.nsatz.Nsatz.
Require Import Coq.Lists.List.

Generalizable All Variables.
Lemma cring_sub_diag_iff {R zero eq sub} `{cring:Cring.Cring (R:=R) (ring0:=zero) (ring_eq:=eq) (sub:=sub)}
  : forall x y, eq (sub x y) zero <-> eq x y.
Proof.
  split;intros Hx.
  { eapply Nsatz.psos_r1b. eapply Hx. }
  { eapply Nsatz.psos_r1. eapply Hx. }
Qed.

Ltac get_goal := lazymatch goal with |- ?g => g end.

Ltac nsatz_equation_implications_to_list eq zero g :=
  lazymatch g with
  | eq ?p zero => constr:(p::nil)
  | eq ?p zero -> ?g => let l := nsatz_equation_implications_to_list eq zero g in constr:(p::l)
  end.

Ltac nsatz_reify_equations eq zero :=
  let g := get_goal in
  let lb := nsatz_equation_implications_to_list eq zero g in
  lazymatch (eval red in (Ncring_tac.list_reifyl (lterm:=lb))) with
    (?variables, ?le) =>
    lazymatch (eval compute in (List.rev le)) with
    | ?reified_goal::?reified_givens => constr:((variables, reified_givens, reified_goal))
    end
  end.

Ltac nsatz_get_free_variables reified_package :=
  lazymatch reified_package with (?fv, _, _) => fv end.

Ltac nsatz_get_reified_givens reified_package :=
  lazymatch reified_package with (_, ?givens, _) => givens end.

Ltac nsatz_get_reified_goal reified_package :=
  lazymatch reified_package with (_, _, ?goal) => goal end.

Require Import Coq.setoid_ring.Ring_polynom.
(* Kludge for 8.4/8.5 compatibility *)
Module Import mynsatz_compute.
  Import Nsatz.
  Global Ltac mynsatz_compute x := nsatz_compute x.
End mynsatz_compute.
Ltac nsatz_compute x := mynsatz_compute x.

Ltac nsatz_compute_to_goal sugar nparams reified_goal power reified_givens :=
  nsatz_compute (PEc sugar :: PEc nparams :: PEpow reified_goal power :: reified_givens).

Ltac nsatz_compute_get_leading_coefficient :=
  lazymatch goal with
    |- Logic.eq ((?a :: _ :: ?b) :: ?c) _ -> _ => a
  end.

Ltac nsatz_compute_get_certificate :=
  lazymatch goal with
    |- Logic.eq ((?a :: _ :: ?b) :: ?c) _ -> _ => constr:((c,b))
  end.

Ltac nsatz_rewrite_and_revert domain :=
  lazymatch type of domain with
  | @Integral_domain.Integral_domain ?F ?zero _ _ _ _ _ ?eq ?Fops ?FRing ?FCring =>
    lazymatch goal with
    | |- eq _ zero => idtac
    | |- eq _ _ => rewrite <-(cring_sub_diag_iff (cring:=FCring))
    end;
    repeat match goal with
           | [H : eq _ zero |- _ ] => revert H
           | [H : eq _ _ |- _ ] => rewrite <-(cring_sub_diag_iff (cring:=FCring)) in H; revert H
           end
  end.

(** As per https://coq.inria.fr/bugs/show_bug.cgi?id=4851, [nsatz]
    cannot handle duplicate hypotheses.  So we clear them. *)
Ltac nsatz_clear_duplicates_for_bug_4851 domain :=
  lazymatch type of domain with
  | @Integral_domain.Integral_domain _ _ _ _ _ _ _ ?eq _ _ _ =>
    repeat match goal with
           | [ H : eq ?x ?y, H' : eq ?x ?y |- _ ] => clear H'
           end
  end.

Ltac nsatz_nonzero :=
  try solve [apply Integral_domain.integral_domain_one_zero
            |apply Integral_domain.integral_domain_minus_one_zero
            |trivial
            |assumption].

Ltac nsatz_domain_sugar_power domain sugar power :=
  let nparams := constr:(BinInt.Zneg BinPos.xH) in (* some symbols can be "parameters", treated as coefficients *)
  lazymatch type of domain with
  | @Integral_domain.Integral_domain ?F ?zero _ _ _ _ _ ?eq ?Fops ?FRing ?FCring =>
    nsatz_clear_duplicates_for_bug_4851 domain;
    nsatz_rewrite_and_revert domain;
    let reified_package := nsatz_reify_equations eq zero in
    let fv := nsatz_get_free_variables reified_package in
    let interp := constr:(@Nsatz.PEevalR _ _ _ _ _ _ _ _ Fops fv) in
    let reified_givens := nsatz_get_reified_givens reified_package in
    let reified_goal := nsatz_get_reified_goal reified_package in
    nsatz_compute_to_goal sugar nparams reified_goal power reified_givens;
    let a := nsatz_compute_get_leading_coefficient in
    let crt := nsatz_compute_get_certificate in
    intros _ (* discard [nsatz_compute] output *); intros;
    apply (fun Haa refl cond => @Integral_domain.Rintegral_domain_pow _ _ _ _ _ _ _ _ _ _ _ domain (interp a) _ (BinNat.N.to_nat power) Haa (@Nsatz.check_correct _ _ _ _ _ _ _ _ _ _ FCring fv reified_givens (PEmul a (PEpow reified_goal power)) crt refl cond));
    [ nsatz_nonzero; cbv iota beta delta [Nsatz.PEevalR PEeval InitialRing.gen_phiZ InitialRing.gen_phiPOS]
    | solve [vm_compute; exact (eq_refl true)] (* exact_no_check (eq_refl true) *)
    | solve [repeat (split; [assumption|]); exact I] ]
  end.

Ltac nsatz_guess_domain :=
  match goal with
  | |- ?eq _ _ => constr:(_:Integral_domain.Integral_domain (ring_eq:=eq))
  | |- not (?eq _ _) =>  constr:(_:Integral_domain.Integral_domain (ring_eq:=eq))
  | [H: ?eq _ _ |- _ ] =>  constr:(_:Integral_domain.Integral_domain (ring_eq:=eq))
  | [H: not (?eq _ _) |- _] =>  constr:(_:Integral_domain.Integral_domain (ring_eq:=eq))
  end.

Ltac nsatz_sugar_power sugar power :=
  let domain := nsatz_guess_domain in
  nsatz_domain_sugar_power domain sugar power.

Ltac nsatz_power power :=
  let power_N := (eval compute in (BinNat.N.of_nat power)) in
  nsatz_sugar_power BinInt.Z0 power_N.

Ltac nsatz := nsatz_power 1%nat.

Tactic Notation "nsatz" := nsatz.
Tactic Notation "nsatz" constr(n) := nsatz_power n.

(** If the goal is of the form [?x <> ?y] and assuming [?x = ?y]
    contradicts any hypothesis of the form [?x' <> ?y'], we turn this
    problem about inequalities into one about equalities and give it
    to [nsatz]. *)
Ltac nsatz_contradict_single_hypothesis domain :=
  lazymatch type of domain with
  | @Integral_domain.Integral_domain _ ?zero ?one _ _ _ _ ?eq ?Fops ?FRing ?FCring =>
    unfold not in *;
    match goal with
    | [ H : eq _ _ -> False |- eq _ _ -> False ]
      => intro; apply H; nsatz
    | [ H : eq _ _ -> False |- False ]
      => apply H; nsatz
    end
  end.

Ltac nsatz_contradict :=
  let domain := nsatz_guess_domain in
  nsatz_contradict_single_hypothesis domain
  || (unfold not;
      intros;
      lazymatch type of domain with
      | @Integral_domain.Integral_domain _ ?zero ?one _ _ _ _ ?eq ?Fops ?FRing ?FCring =>
        assert (eq one zero) as Hbad;
        [nsatz; nsatz_nonzero
        |destruct (Integral_domain.integral_domain_one_zero (Integral_domain:=domain) Hbad)]
      end).
