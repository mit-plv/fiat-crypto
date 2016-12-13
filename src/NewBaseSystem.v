Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Decidable.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra. Import Ring.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

Module B.
  Section NewBaseSystem.
    Let rep : Type := list (Z * Z).

    Definition eval (p:rep) : Z :=
      fold_right Z.add 0 (map (fun t => (fst t) * (snd t)) p).

    Definition add (p q : rep) : rep := p ++ q.

    Definition opp (p : rep) : rep :=
      map (fun cx => (fst cx, - (snd cx))) p.

    Definition mul (p q:rep) : rep :=
      flat_map (fun t => let '(c, x) := t in
                         map (fun t' => let '(c', x') := t' in
                                        (c * c', x * x')) q) p.

    Definition carry (from next : Z) (p : rep) : rep :=
      let cap := (next / from)%Z in
      flat_map (fun cx => let '(c,x) := cx in
                          if dec (Logic.eq c from)
                          then ((c, x mod cap) :: (next, x / cap) :: nil)%Z
                          else ((c,x) :: nil)) p.

    Definition gather_or_leave b cx gso : rep * Z :=
      if dec (Logic.eq ((fst cx) mod b) 0)%Z
      then (fst gso, Z.add (((fst cx) / b) * (snd cx)) (snd gso)) (* TODO: use a compile-time scaling operation that compile-time checks whether the coefficient is 1 and skips multiplication if so. Maybe use notation scopes for compiletime and runtime. *)
      else (cx :: fst gso, snd gso).

    Definition gather_single (b : Z) (p : rep) : rep * Z :=
      fold_right (gather_or_leave b) (nil,0) p.

    Definition gather' (base:list Z) (p:rep) : (rep * list Z) :=
      fold_right (fun b state =>
                    let gso := gather_single b (fst state) in
                    (fst gso, snd gso::snd state)) (p, nil) base.
    Definition gather b p := snd (gather' b p).


  (*
    Let base := (1::10::100::1000::10000::100000::1000000::10000000::nil)%Z.
    Axiom f0 f1 f2 f3 : R.
    Axiom g0 g1 g2 g3 : R.
    Let f_ := f0::f1::f2::f3::nil.
    Let g_ := g0::g1::g2::g3::nil.

    Let f := Eval compute in (combine base f_).
    Let g := Eval compute in (combine base g_).

    Local Infix "*" := ZRmul.
    Compute gather base (mul f g).
  *)

    Section Proofs.

    Lemma eval_nil : eval nil = 0. Proof. reflexivity. Qed.
    Lemma eval_cons p q : eval (p::q) = (fst p) * (snd p) + eval q. Proof. reflexivity. Qed.
    Lemma eval_app p q: eval (p++q) = eval p + eval q.
    Proof.
      induction p; intros; [rewrite ?app_nil_l, ?eval_nil, ?left_identity; reflexivity|].
      rewrite <-!app_comm_cons, !eval_cons, IHp; auto using associative.
    Qed.
    
    Lemma add_correct p q : eval (add p q) = eval p + eval q.
    Proof.
      induction p; simpl; rewrite ?eval_nil, ?eval_cons, ?left_identity, ?IHp, ?associative; reflexivity.
    Qed.

    Lemma opp_correct p : eval (opp p) = - (eval p).
    Proof.
      induction p; simpl; rewrite ?eval_nil, ?eval_cons; [reflexivity|].
      simpl fst; simpl snd. rewrite IHp. ring.
    Qed.

    Lemma mul_single a q : eval (mul (a :: nil) q) = fst a * snd a * eval q.
    Proof.
      induction q; intros; simpl mul; destruct_head prod;
        rewrite ?eval_nil, ?eval_cons, ?app_nil_r, ?mul_0_r in *; try reflexivity.
      simpl. rewrite IHq, left_distributive. ring. 
    Qed.
    
    Lemma mul_correct' a p q :
      eval (mul (a :: p) q) = eval (mul (a :: nil) q) + eval (mul p q).
    Proof.
      intros; simpl mul; rewrite ?eval_nil, ?eval_cons, ?app_nil_r, <-?eval_app. reflexivity.
    Qed.

    Lemma mul_correct p q : eval (mul p q) = eval p * eval q.
    Proof.
      induction p; [destruct q; simpl; rewrite ?eval_nil, ?mul_0_l; reflexivity |].
      rewrite mul_correct', mul_single, eval_cons, IHp; ring.
    Qed.

    Lemma carry_correct from next: from <> 0 ->
                                   next mod from = 0 ->
                                   next / from <> 0 ->
                                   forall p,
                                      eval (carry from next p) = eval p.
    Proof.
      induction p; [reflexivity|]; intros; simpl carry; destruct_head prod.
      break_match; subst; rewrite !eval_app, ?eval_cons, ?eval_nil;
        rewrite IHp; [|ring].
      simpl fst; simpl snd; ring_simplify.
      match goal with |- ?a + ?b + ?x = ?c + ?x =>
                      replace (a + b) with c; [ring|] end.
      match goal with |- _ * ?x = _ * (?x mod ?y) + _ * (?x / ?y) =>
                      rewrite (Z.div_mod x y) at 1 by auto end.
      rewrite Z.mul_add_distr_l, !Z.mul_assoc.
      rewrite <-Z_div_exact_full_2 by assumption. ring.
    Qed.

    Lemma gather_single_all p : Logic.eq (fst (gather_single 1%Z p)) nil.
    Proof.
      induction p; [solve [trivial]|]; simpl gather_single.
      unfold gather_or_leave; rewrite Z.mod_1_r, IHp.
      break_match; [reflexivity|congruence].
    Qed.

    Lemma gather_all base' p : Logic.eq (fst (gather' (1%Z::base') p)) nil.
    Proof. unfold gather'; simpl fst; setoid_rewrite gather_single_all; reflexivity. Qed.

    Lemma gather_single_correct b (b_nonzero : b <> 0%Z) p :
      eval (fst (gather_single b p)) + (b * snd (gather_single b p)) = eval p.
    Proof.
      induction p; simpl; [rewrite ?eval_nil; ring|].
      cbv [gather_or_leave]; destruct_head' prod; break_match; try congruence; simpl;
        rewrite !eval_cons; simpl; rewrite <-IHp; simpl fst in *; [|ring].
      rewrite Z.mul_add_distr_l, !Z.mul_assoc, <-Zdiv.Z_div_exact_full_2;
        auto; ring.
    Qed.

    Lemma gather'_correct base : forall p, (forall b, In b base -> b <> 0%Z) ->
      eval (fst (gather' base p)) + eval (combine base (snd (gather' base p))) = eval p.
    Proof.
      induction base; intros; simpl; [rewrite eval_nil; auto using right_identity|].
      setoid_rewrite eval_cons. rewrite associative, gather_single_correct; auto using in_cons, in_eq.
    Qed.

    Lemma gather_correct base p : (forall b, In b base -> b <> 0%Z) ->
      eval (combine (1%Z::base) (gather (1%Z::base) p)) = eval p.
    Proof.
      intros. etransitivity; [|eapply gather'_correct; eassumption].
      simpl; setoid_rewrite eval_cons.
      rewrite <-gather_single_correct with (p := fst (gather' base p)) (b := 1%Z) by congruence.
      rewrite gather_single_all, eval_nil. simpl fst; simpl snd. ring.
    Qed.

    End Proofs.

    Section Ring.

    Definition eq (p q : rep) : Prop := eval p = eval q.

    Definition zero : rep := nil.

    Definition one : rep := ((1,1) :: nil).

    Definition sub (p q : rep) : rep := add p (opp q).

    Lemma sub_correct p q : eval (sub p q) = eval p - eval q.
    Proof. cbv [sub]. rewrite add_correct, opp_correct. ring. Qed.

    Lemma is_ring : @Algebra.ring rep eq zero one opp add sub mul.
    Proof.
      cbv [eq]; eapply (isomorphism_to_subring_ring (ringR := ring_Z) (phi := eval)).
      Grab Existential Variables.
      + reflexivity.
      + reflexivity.
      + apply mul_correct.
      + apply sub_correct.
      + apply add_correct.
      + apply opp_correct.
      + tauto.
      + repeat intro. rewrite !mul_correct. congruence.
      + repeat intro. rewrite !sub_correct. congruence.
      + repeat intro. rewrite !add_correct. congruence.
      + repeat intro. rewrite !opp_correct. congruence.
      + intros; apply Z.eq_dec.
      + econstructor; repeat intro; congruence.
    Qed.
    End Ring.
    
  End NewBaseSystem.
End B.