(*
Copyright (c) 2014-2015, Verdi Team
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

1. Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

Ltac subst_max := idtac "VerdiTactics is deprecated in fiat-crypto";
  repeat match goal with
           | [ H : ?X = _ |- _ ]  => subst X
           | [H : _ = ?X |- _] => subst X
         end.

Ltac inv H := idtac "VerdiTactics is deprecated in fiat-crypto"; inversion H; subst_max.
Ltac invc H := idtac "VerdiTactics is deprecated in fiat-crypto"; inv H; clear H.
Ltac invcs H := idtac "VerdiTactics is deprecated in fiat-crypto"; invc H; simpl in *.

Ltac break_if := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ |- context [ if ?X then _ else _ ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
    | [ H : context [ if ?X then _ else _ ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

Ltac break_match_hyp := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

Ltac break_match_goal := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ |- context [ match ?X with _ => _ end ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

Ltac break_match := idtac "VerdiTactics is deprecated in fiat-crypto"; break_match_goal || break_match_hyp.


Ltac break_exists := idtac "VerdiTactics is deprecated in fiat-crypto";
  repeat match goal with
           | [H : exists _, _ |- _ ] => destruct H
         end.

Ltac break_exists_exists := idtac "VerdiTactics is deprecated in fiat-crypto";
  repeat match goal with
           | H:exists _, _ |- _ =>
             let x := fresh "x" in
             destruct H as [x]; exists x
         end.

Ltac break_and := idtac "VerdiTactics is deprecated in fiat-crypto";
  repeat match goal with
           | [H : _ /\ _ |- _ ] => destruct H
         end.

Ltac solve_by_inversion' tac := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [H : _ |- _] => solve [inv H; tac]
  end.

Ltac solve_by_inversion := idtac "VerdiTactics is deprecated in fiat-crypto"; solve_by_inversion' auto.

Ltac apply_fun f H:= idtac "VerdiTactics is deprecated in fiat-crypto";
  match type of H with
    | ?X = ?Y => assert (f X = f Y)
  end.

Ltac conclude H tac := idtac "VerdiTactics is deprecated in fiat-crypto";
  (let H' := fresh in
   match type of H with
     | ?P -> _ => assert P as H' by (tac)
   end; specialize (H H'); clear H').

Ltac concludes := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : ?P -> _ |- _ ] => conclude H auto
  end.

Ltac forward H := idtac "VerdiTactics is deprecated in fiat-crypto";
  let H' := fresh in
   match type of H with
     | ?P -> _ => assert P as H'
   end.

Ltac forwards := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : ?P -> _ |- _ ] => forward H
  end.

Ltac find_contradiction := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : ?X = _, H' : ?X = _ |- _ ] => rewrite H in H'; solve_by_inversion
  end.

Ltac find_rewrite := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : ?X _ _ _ _ = _, H' : ?X _ _ _ _ = _ |- _ ] => rewrite H in H'
    | [ H : ?X = _, H' : ?X = _ |- _ ] => rewrite H in H'
    | [ H : ?X = _, H' : context [ ?X ] |- _ ] => rewrite H in H'
    | [ H : ?X = _ |- context [ ?X ] ] => rewrite H
  end.

Ltac find_rewrite_lem lem := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : _ |- _ ] =>
      rewrite lem in H; [idtac]
  end.

Ltac find_rewrite_lem_by lem t := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : _ |- _ ] =>
      rewrite lem in H by t
  end.

Ltac find_erewrite_lem lem := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : _ |- _] => erewrite lem in H by eauto
  end.

Ltac find_reverse_rewrite := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : _ = ?X _ _ _ _, H' : ?X _ _ _ _ = _ |- _ ] => rewrite <- H in H'
    | [ H : _ = ?X, H' : context [ ?X ] |- _ ] => rewrite <- H in H'
    | [ H : _ = ?X |- context [ ?X ] ] => rewrite <- H
  end.

Ltac find_inversion := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : ?X _ _ _ _ _ _ = ?X _ _ _ _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ _ _ _ = ?X _ _ _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ _ _ = ?X _ _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ _ = ?X _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ = ?X _ _ |- _ ] => invc H
    | [ H : ?X _ = ?X _ |- _ ] => invc H
  end.

Ltac prove_eq := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : ?X ?x1 ?x2 ?x3 = ?X ?y1 ?y2 ?y3 |- _ ] =>
      assert (x1 = y1) by congruence;
        assert (x2 = y2) by congruence;
        assert (x3 = y3) by congruence;
        clear H
    | [ H : ?X ?x1 ?x2 = ?X ?y1 ?y2 |- _ ] =>
      assert (x1 = y1) by congruence;
        assert (x2 = y2) by congruence;
        clear H
    | [ H : ?X ?x1 = ?X ?y1 |- _ ] =>
      assert (x1 = y1) by congruence;
        clear H
  end.

Ltac tuple_inversion := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : (_, _, _, _) = (_, _, _, _) |- _ ] => invc H
    | [ H : (_, _, _) = (_, _, _) |- _ ] => invc H
    | [ H : (_, _) = (_, _) |- _ ] => invc H
  end.

Ltac f_apply H f := idtac "VerdiTactics is deprecated in fiat-crypto";
  match type of H with
    | ?X = ?Y =>
      assert (f X = f Y) by (rewrite H; auto)
  end.

Ltac break_let := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : context [ (let (_,_) := ?X in _) ] |- _ ] => destruct X eqn:?
    | [ |- context [ (let (_,_) := ?X in _) ] ] => destruct X eqn:?
  end.

Ltac break_or_hyp := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : _ \/ _ |- _ ] => invc H
  end.

Ltac copy_apply lem H := idtac "VerdiTactics is deprecated in fiat-crypto";
  let x := fresh in
  pose proof H as x;
    apply lem in x.

Ltac copy_eapply lem H := idtac "VerdiTactics is deprecated in fiat-crypto";
  let x := fresh in
  pose proof H as x;
    eapply lem in x.

Ltac conclude_using tac := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : ?P -> _ |- _ ] => conclude H tac
  end.

Ltac find_higher_order_rewrite := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : _ = _ |- _ ] => rewrite H in *
    | [ H : forall _, _ = _ |- _ ] => rewrite H in *
    | [ H : forall _ _, _ = _ |- _ ] => rewrite H in *
  end.

Ltac find_reverse_higher_order_rewrite := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : _ = _ |- _ ] => rewrite <- H in *
    | [ H : forall _, _ = _ |- _ ] => rewrite <- H in *
    | [ H : forall _ _, _ = _ |- _ ] => rewrite <- H in *
  end.

Ltac clean := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : ?X = ?X |- _ ] => clear H
  end.

Ltac find_apply_hyp_goal := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : _ |- _ ] => solve [apply H]
  end.

Ltac find_copy_apply_lem_hyp lem := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : _ |- _ ] => copy_apply lem H
  end.

Ltac find_apply_hyp_hyp := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : forall _, _ -> _,
        H' : _ |- _ ] =>
      apply H in H'; [idtac]
    | [ H : _ -> _ , H' : _ |- _ ] =>
      apply H in H'; auto; [idtac]
  end.

Ltac find_copy_apply_hyp_hyp := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : forall _, _ -> _,
        H' : _ |- _ ] =>
      copy_apply H H'; [idtac]
    | [ H : _ -> _ , H' : _ |- _ ] =>
      copy_apply H H'; auto; [idtac]
  end.

Ltac find_apply_lem_hyp lem := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : _ |- _ ] => apply lem in H
  end.

Ltac find_eapply_lem_hyp lem := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : _ |- _ ] => eapply lem in H
  end.

Ltac insterU H := idtac "VerdiTactics is deprecated in fiat-crypto";
  match type of H with
    | forall _ : ?T, _ =>
      let x := fresh "x" in
      evar (x : T);
      let x' := (eval unfold x in x) in
        clear x; specialize (H x')
  end.

Ltac find_insterU := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : forall _, _ |- _ ] => insterU H
  end.

Ltac eapply_prop P := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | H : P _ |- _ =>
      eapply H
  end.

Ltac isVar t := idtac "VerdiTactics is deprecated in fiat-crypto";
    match goal with
      | v : _ |- _ =>
        match t with
          | v => idtac
        end
    end.

Ltac remGen t := idtac "VerdiTactics is deprecated in fiat-crypto";
  let x := fresh in
  let H := fresh in
  remember t as x eqn:H;
    generalize dependent H.

Ltac remGenIfNotVar t := idtac "VerdiTactics is deprecated in fiat-crypto"; first [isVar t| remGen t].

Ltac rememberNonVars H := idtac "VerdiTactics is deprecated in fiat-crypto";
  match type of H with
    | _ ?a ?b ?c ?d ?e =>
      remGenIfNotVar a;
      remGenIfNotVar b;
      remGenIfNotVar c;
      remGenIfNotVar d;
      remGenIfNotVar e
    | _ ?a ?b ?c ?d =>
      remGenIfNotVar a;
      remGenIfNotVar b;
      remGenIfNotVar c;
      remGenIfNotVar d
    | _ ?a ?b ?c =>
      remGenIfNotVar a;
      remGenIfNotVar b;
      remGenIfNotVar c
    | _ ?a ?b =>
      remGenIfNotVar a;
      remGenIfNotVar b
    | _ ?a =>
      remGenIfNotVar a
  end.

Ltac generalizeEverythingElse H := idtac "VerdiTactics is deprecated in fiat-crypto";
  repeat match goal with
           | [ x : ?T |- _ ] =>
             first [
                 match H with
                   | x => fail 2
                 end |
                 match type of H with
                   | context [x] => fail 2
                 end |
                 revert x]
         end.

Ltac prep_induction H := idtac "VerdiTactics is deprecated in fiat-crypto";
  rememberNonVars H;
  generalizeEverythingElse H.

Ltac econcludes := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : ?P -> _ |- _ ] => conclude H eauto
  end.

Ltac find_copy_eapply_lem_hyp lem := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : _ |- _ ] => copy_eapply lem H
  end.

Ltac apply_prop_hyp P Q := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
  | [ H : context [ P ], H' : context [ Q ] |- _ ] =>
    apply H in H'
  end.


Ltac eapply_prop_hyp P Q := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
  | [ H : context [ P ], H' : context [ Q ] |- _ ] =>
    eapply H in H'
  end.

Ltac copy_eapply_prop_hyp P Q := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : context [ P ], H' : context [ Q ] |- _ ] =>
      copy_eapply H H'
  end.

Ltac find_false := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | H : _ -> False |- _ => exfalso; apply H
  end.

Ltac injc H := idtac "VerdiTactics is deprecated in fiat-crypto";
  injection H; clear H; intro; subst_max.

Ltac find_injection := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
    | [ H : ?X _ _ _ _ _ _ = ?X _ _ _ _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ _ _ _ = ?X _ _ _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ _ _ = ?X _ _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ _ = ?X _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ = ?X _ _ |- _ ] => injc H
    | [ H : ?X _ = ?X _ |- _ ] => injc H
  end.

Ltac aggresive_rewrite_goal := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with H : _ |- _ => rewrite H end.

Ltac break_exists_name x := idtac "VerdiTactics is deprecated in fiat-crypto";
  match goal with
  | [ H : exists _, _ |- _ ] => destruct H as [x H]
  end.
