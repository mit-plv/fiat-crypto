Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Decidable.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra. Import Ring.
Require Import Coq.ZArith.BinInt.

Module B.
  Section NewBaseSystem.
    Context {R Req Rzero Rone Ropp Radd Rmul Rsub}
            {ZRmul : Z -> R -> R} {ZRmul_0_r:forall b, ZRmul b Rzero = Rzero}
            {ZRmul_Zmul_Rmul : forall x y a b, ZRmul (x * y)%Z (Rmul a b) = Rmul (ZRmul x a) (ZRmul y b)}
            {ZRmul_distr_add_l : forall x a b, ZRmul x (Radd a b) = Radd (ZRmul x a) (ZRmul x b)}
            {ZRmul_ZRmul : forall x y a, ZRmul x (ZRmul y a) = ZRmul (x * y)%Z a}
            {Rring:@Algebra.ring R Req Rzero Rone Ropp Radd Rsub Rmul}.
    Local Infix "=" := Req : type_scope.
    Local Infix "*" := Rmul.
    Local Infix "+" := Radd.

    Let coef := Z.
    Let rep : Type := list (coef * R).

    Definition evalterm (t:coef*R) : R :=
      let '(c, x) := t in ZRmul c x.

    Definition eval (p:rep) : R :=
      fold_right Radd Rzero (map evalterm p).

    Lemma eval_nil : eval nil = Rzero. Proof. reflexivity. Qed.
    Lemma eval_cons p q : eval (p::q) = evalterm p + eval q. Proof. reflexivity. Qed.
    Lemma eval_app p q: eval (p++q) = eval p + eval q.
    Proof.
      induction p; intros; [rewrite ?app_nil_l, ?eval_nil, ?left_identity; reflexivity|].
      rewrite <-!app_comm_cons, !eval_cons, IHp; auto using associative.
    Qed.

    Definition mul (p q:rep) : rep :=
      flat_map (fun t => let '(c, x) := t in
                         map (fun t' => let '(c', x') := t' in
                                        (Z.mul c c', Rmul x x')) q) p.

    Lemma mul_single a q : eval (mul (a :: nil) q) = evalterm a * eval q.
    Proof.
      induction q; intros; simpl mul; destruct_head prod;
        rewrite ?eval_nil, ?eval_cons, ?app_nil_r, ?mul_0_r in *; try reflexivity.
      match goal with |- eval (?x :: ?y) = _ => rewrite (eval_cons x y) end.
      simpl evalterm; rewrite IHq, left_distributive, ZRmul_Zmul_Rmul. reflexivity.
    Qed.
    
    Lemma mul_correct' a p q :
      eval (mul (a :: p) q) = eval (mul (a :: nil) q) + eval (mul p q).
    Proof.
      intros; simpl mul; rewrite ?eval_nil, ?eval_cons, ?app_nil_r, <-?eval_app. reflexivity.
    Qed.

    Lemma mul_correct p q : eval (mul p q) = Rmul (eval p) (eval q).
    Proof.
      induction p; [destruct q; simpl; rewrite ?eval_nil, ?mul_0_l; reflexivity |].
      rewrite mul_correct', mul_single, eval_cons, IHp, right_distributive; reflexivity.
    Qed.

    Definition gather_or_leave b cx gso : rep * R :=
      if dec (Logic.eq ((fst cx) mod b) 0)%Z
      then (fst gso, ZRmul ((fst cx) / b) (snd cx) + snd gso) (* TODO: use a compile-time scaling operation that compile-time checks whether the coefficient is 1 and skips multiplication if so. Maybe use notation scopes for compiletime and runtime. *)
      else (cx :: fst gso, snd gso).

    Definition gather_single (b : Z) (p : rep) : rep * R :=
      fold_right (gather_or_leave b) (nil,Rzero) p.

    Definition gather' (base:list Z) (p:rep) : (rep * list R) :=
      fold_right (fun b state =>
                    let gso := gather_single b (fst state) in
                    (fst gso, snd gso::snd state)) (p, nil) base.
    Definition gather b p := snd (gather' b p).

    Lemma gather_single_all p : Logic.eq (fst (gather_single 1%Z p)) nil.
    Proof.
      induction p; [solve [trivial]|]; simpl gather_single.
      unfold gather_or_leave; rewrite Z.mod_1_r, IHp.
      break_match; [reflexivity|congruence].
    Qed.

    Lemma gather_all base' p : Logic.eq (fst (gather' (1%Z::base') p)) nil.
    Proof. unfold gather'; simpl fst; setoid_rewrite gather_single_all; reflexivity. Qed.

    Lemma gather_single_correct b (b_nonzero : b <> 0%Z) p :
      Radd (eval (fst (gather_single b p))) (ZRmul b (snd (gather_single b p))) = eval p.
    Proof.
      induction p; simpl; [rewrite ?eval_nil, ?left_identity, ?ZRmul_0_r;reflexivity|].
      cbv [gather_or_leave]; destruct_head' prod; break_match; try congruence; simpl;
        rewrite !eval_cons; simpl; rewrite <-IHp; simpl fst in *.
      { rewrite ZRmul_distr_add_l, ZRmul_ZRmul, <-Zdiv.Z_div_exact_full_2 by auto.
        rewrite !associative; apply Group.cancel_right, commutative. }
      { setoid_rewrite eval_cons; rewrite associative; reflexivity. }
    Qed.

    Lemma gather'_correct base : forall p, (forall b, In b base -> b <> 0%Z) ->
      eval (fst (gather' base p)) + eval (combine base (snd (gather' base p))) = eval p.
    Proof.
      induction base; intros; simpl; [rewrite eval_nil; auto using right_identity|].
      setoid_rewrite eval_cons; cbv [evalterm]; rewrite associative.
      rewrite gather_single_correct; auto using in_cons, in_eq.
    Qed.

    Lemma gather_correct base p : (forall b, In b base -> b <> 0%Z) ->
      eval (combine (1%Z::base) (gather (1%Z::base) p)) = eval p.
    Proof.
      intros. etransitivity; [|eapply gather'_correct; eassumption].
      simpl; setoid_rewrite eval_cons; cbv [evalterm].
      rewrite <-gather_single_correct with (p := fst (gather' base p)) (b := 1%Z) by congruence.
      rewrite gather_single_all, eval_nil, left_identity.
      reflexivity.
    Qed.

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

End NewBaseSystem.