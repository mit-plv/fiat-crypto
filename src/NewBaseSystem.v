Require Import Crypto.Util.Tactics.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.Decidable.
Require Import Psatz.
Require Import Coq.omega.Omega.

Require Import Coq.ZArith.BinIntDef. Local Open Scope Z_scope.
Require Import Crypto.Algebra. Import Algebra.Ring.

Require Coq.Lists.List. Local Notation list := List.list.
Require Crypto.Util.Tuple. Local Notation tuple := Tuple.tuple.

Import ZArith. (* for ring *)

    (* TODO: move *)
    Lemma fst_pair {A B} (a:A) (b:B) : fst (a,b) = a. reflexivity. Qed.
    Lemma snd_pair {A B} (a:A) (b:B) : snd (a,b) = b. reflexivity. Qed.

    Program Definition add_to_nth {n} i x : tuple Z n -> tuple Z n :=
      Tuple.on_tuple (ListUtil.update_nth i (Z.add x)) _.
    Next Obligation. apply ListUtil.length_update_nth. Defined.

    Lemma combine_update_nth_r {A B} (ls:list A) (rs:list B) i f :
      List.combine ls (ListUtil.update_nth i f rs) =
      ListUtil.update_nth i (fun p => (fst p, f (snd p))) (List.combine ls rs).
    Admitted.
    Lemma update_nth_id {T} i (xs:list T) : ListUtil.update_nth i id xs = xs.
    Admitted.
    Lemma map_fst_combine {A B} (xs:list A) (ys:list B) : List.map fst (List.combine xs ys) = List.firstn (length ys) xs.
    Admitted.
    Lemma nth_default_seq_inbouns d s n i (H:(i < n)%nat) :
      List.nth_default d (List.seq s n) i = (s+i)%nat.
    Proof.
      progress cbv [List.nth_default].
      rewrite ListUtil.nth_error_seq.
      VerdiTactics.break_if; solve [ trivial | omega ].
    Qed.

Module B.
  Section NewBaseSystem.
    Let limb := (Z*Z)%type. (* position coefficient and run-time value *)
    Definition eval (p:list limb) : Z :=
      List.fold_right Z.add 0%Z (List.map (fun t => fst t * snd t) p).
    
    Lemma eval_nil : eval nil = 0. Proof. reflexivity. Qed.
    Lemma eval_cons p q : eval (p::q) = (fst p) * (snd p) + eval q. Proof. reflexivity. Qed.
    Lemma eval_app p q: eval (p++q) = eval p + eval q.
    Proof. induction p; simpl eval; rewrite ?eval_nil, ?eval_cons; nsatz. Qed.

    Definition mul (p q:list limb) : list limb :=
      List.flat_map (fun t => List.map (fun t' => (fst t * fst t', snd t * snd t')) q) p.
    Lemma eval_map_mul a x q : eval (List.map (fun t => (a * fst t, x * snd t)) q) = a * x * eval q.
    Proof. induction q; simpl List.map;
             rewrite ?eval_nil, ?eval_cons, ?fst_pair, ?snd_pair; nsatz. Qed.
    Lemma mul_correct p q : eval (mul p q) = eval p * eval q.
    Proof. induction p; simpl mul;
             rewrite ?eval_nil, ?eval_cons, ?eval_app, ?eval_map_mul; nsatz. Qed.

    Section Positional.
      Context (weight : nat -> Z) (* [weight i] is the weight of position [i] *)
              (weight_0 : weight 0%nat = 1%Z)
              (weight_nonzero : forall i, weight i <> 0).

      Definition eval_positional {n:nat} (xs:tuple Z n) : Z :=
        eval (List.combine (List.map weight (List.seq 0 n)) (Tuple.to_list n xs)).

      Lemma eval_positional_add_to_nth {n} (i:nat) (H:(i<n)%nat) (x:Z) (xs:tuple Z n) :
        eval_positional (add_to_nth i x xs) = weight i * x + eval_positional xs.
      Proof.
        cbv [eval_positional add_to_nth Tuple.on_tuple]; rewrite !Tuple.to_list_from_list.
        rewrite combine_update_nth_r at 1.
        rewrite <-(update_nth_id i (List.combine _ _)) at 2.
        rewrite <-!(ListUtil.splice_nth_equiv_update_nth_update _ _ (weight 0, 0)) by (autorewrite with distr_length; lia); progress cbv [ListUtil.splice_nth id].
        repeat match goal with
        | |- context[?w] => progress (replace w with (weight i); [ring|])
        | _ => progress rewrite ?eval_app, ?eval_cons, ?fst_pair, ?snd_pair, <-?ListUtil.map_nth_default_always, ?map_fst_combine, ?List.firstn_all2, ?ListUtil.map_nth_default_always, ?nth_default_seq_inbouns by (autorewrite with distr_length; lia)
        | _ => reflexivity
        end.
      Qed.

      Fixpoint place (t:limb) (i:nat) : nat * Z :=
        if dec (fst t mod weight i = 0)
        then (i, fst t / weight i * snd t)
        else match i with S i' => place t i' | O => (O, fst t * snd t) end.

      Lemma place_in_range (t:limb) (n:nat) : (fst (place t n) < S n)%nat.
      Proof. induction n; simpl; VerdiTactics.break_match; simpl; omega. Qed.

      Lemma eval_place t i :
        weight (fst (place t i)) * snd (place t i) = fst t * snd t.
      Proof. induction i; simpl place; VerdiTactics.break_match;
               try match goal with H:_ |- _ => pose proof (Z_div_exact_full_2 _ _ (weight_nonzero _) H) end;
               rewrite ?weight_0, ?Z.div_1_r, ?fst_pair, ?snd_pair; nsatz. Qed.

      Definition place_all {n} (init:tuple Z n) (p:list limb) :=
        List.fold_right (fun t => let p := place t (pred n) in add_to_nth (fst p) (snd p)) init p.
      Lemma eval_positional_place_all {n} p (init:tuple Z n) (n_nonzero:n<>O) :
        eval_positional (place_all init p) = eval p + eval_positional init.
      Proof. induction p; simpl; try pose proof place_in_range a (pred n);
               rewrite ?eval_positional_add_to_nth by omega;
               rewrite ?eval_cons, ?eval_place; try nsatz. Qed.

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

    Lemma add_correct p q : eval (add p q) = eval p + eval q. Proof. apply eval_app. Qed.

    Lemma opp_correct p : eval (opp p) = - (eval p).
    Proof.
      induction p; simpl opp;
        rewrite ?eval_nil, ?eval_cons, ?fst_pair, ?snd_pair, ?IHp; ring.
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

    Section Split.
      
    Definition split coef p : rep * rep :=
      fold_right (fun cx state =>
                    if dec (fst cx < coef)
                    then (cx :: fst state, snd state)
                    else (fst state, (fst cx / coef, snd cx) :: snd state))
                 (nil, nil) p.

    Lemma split_correct coef p : coef <> 0 ->
      (forall cx, In cx p -> fst cx < coef \/ (fst cx) mod coef = 0) ->
      eval (fst (split coef p)) + coef * eval (snd (split coef p)) = eval p.
    Proof.
      induction p; intros; simpl; rewrite ?eval_nil, ?eval_cons; [ring|].
      break_match; repeat (simpl fst; simpl snd; rewrite ?eval_cons);
        rewrite <-IHp; auto using associative, in_cons.
      ring_simplify.
      rewrite <-Z_div_exact_full_2 by (auto;
        match goal with H : forall cx, _ -> _ \/ _ |- _ =>
                      destruct (H a); auto using in_eq; congruence
        end).
      destruct (split coef p); destruct a; simpl fst; simpl snd.
      ring.
    Qed.

    End Split.

  End NewBaseSystem.
End B.