Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Export Crypto.ModularArithmetic.FField.
Require Import Coq.nsatz.Nsatz.

Ltac FqAsIntegralDomain :=
  lazymatch goal with [H:Znumtheory.prime ?q |- _ ] =>
    pose proof (_:@Integral_domain.Integral_domain (F q) _ _ _ _ _ _ _ _ _ _) as FqIntegralDomain;
    lazymatch type of FqIntegralDomain with @Integral_domain.Integral_domain _ _ _ _ _ _ _ _ ?ringOps ?ringOk ?ringComm =>
      generalize dependent ringComm; intro Cring;
      generalize dependent ringOk; intro Ring;
      generalize dependent ringOps; intro RingOps;
      lazymatch type of RingOps with @Ncring.Ring_ops ?t ?z ?o ?a ?m ?s ?p ?e =>
        generalize dependent e; intro equiv;
        generalize dependent p; intro opp;
        generalize dependent s; intro sub;
        generalize dependent m; intro mul;
        generalize dependent a; intro add;
        generalize dependent o; intro one;
        generalize dependent z; intro zero;
        generalize dependent t; intro R
      end
    end; intros;
    clear q H
  end.

Ltac fixed_equality_to_goal H x y := generalize (psos_r1 x y H); clear H.
Ltac fixed_equalities_to_goal :=
  match goal with
  | H:?x == ?y |- _ => fixed_equality_to_goal H x y
  | H:_ ?x ?y |- _ => fixed_equality_to_goal H x y
  | H:_ _ ?x ?y |- _ => fixed_equality_to_goal H x y
  | H:_ _ _ ?x ?y |- _ => fixed_equality_to_goal H x y
  | H:_ _ _ _ ?x ?y |- _ => fixed_equality_to_goal H x y
  end.
Ltac fixed_nsatz :=
  intros; try apply psos_r1b;
   lazymatch goal with
   | |- @equality ?T _ _ _ => repeat fixed_equalities_to_goal; nsatz_generic 6%N 1%Z (@nil T) (@nil T)
  end.
Ltac F_nsatz := abstract (FqAsIntegralDomain; fixed_nsatz).
