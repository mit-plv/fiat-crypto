Require Import Crypto.Util.Tactics Crypto.Util.Decidable.

Require Import ZArith Nsatz Psatz Coq.omega.Omega.
Require Import Coq.ZArith.BinIntDef. Local Open Scope Z_scope.

Require Coq.Lists.List. Local Notation list := List.list.
Require Crypto.Util.Tuple. Local Notation tuple := Tuple.tuple.

    (* TODO: move *)
    Lemma fst_pair {A B} (a:A) (b:B) : fst (a,b) = a. reflexivity. Qed.
    Lemma snd_pair {A B} (a:A) (b:B) : snd (a,b) = b. reflexivity. Qed.

    (* TODO: move to ListUtil *)
    Lemma update_nth_id {T} i (xs:list T) : ListUtil.update_nth i id xs = xs.
    Proof.
      revert xs; induction i; destruct xs; simpl; solve [ trivial | congruence ].
    Qed.

    Lemma map_fst_combine {A B} (xs:list A) (ys:list B) : List.map fst (List.combine xs ys) = List.firstn (length ys) xs.
    Proof.
      revert xs; induction ys; destruct xs; simpl; solve [ trivial | congruence ].
    Qed.

    Lemma map_snd_combine {A B} (xs:list A) (ys:list B) : List.map snd (List.combine xs ys) = List.firstn (length xs) ys.
    Proof.
      revert xs; induction ys; destruct xs; simpl; solve [ trivial | congruence ].
    Qed.

    Lemma nth_default_seq_inbouns d s n i (H:(i < n)%nat) :
      List.nth_default d (List.seq s n) i = (s+i)%nat.
    Proof.
      progress cbv [List.nth_default].
      rewrite ListUtil.nth_error_seq.
      break_match; solve [ trivial | omega ].
    Qed.

Delimit Scope runtime_scope with RT.
Definition runtime_mul := Z.mul. Global Infix "*" := runtime_mul : runtime_scope.
Definition runtime_add := Z.add. Global Infix "+" := runtime_add : runtime_scope. 

Module B.
  Let limb := (Z*Z)%type. (* position coefficient and run-time value *)
  Definition eval (p:list limb) : Z :=
    List.fold_right Z.add 0%Z (List.map (fun t => fst t * snd t) p).
  
  Lemma eval_nil : eval nil = 0. Proof. reflexivity. Qed.
  Lemma eval_cons p q : eval (p::q) = (fst p) * (snd p) + eval q. Proof. reflexivity. Qed.
  Lemma eval_app p q: eval (p++q) = eval p + eval q.
  Proof. induction p; simpl eval; rewrite ?eval_nil, ?eval_cons; nsatz. Qed.

  Definition mul (p q:list limb) : list limb :=
    List.flat_map (fun t => List.map (fun t' => (fst t * fst t', (snd t * snd t')%RT)) q) p.
  Lemma eval_map_mul a x q : eval (List.map (fun t => (a * fst t, x * snd t)) q) = a * x * eval q.
  Proof. induction q; simpl List.map;
           rewrite ?eval_nil, ?eval_cons, ?fst_pair, ?snd_pair; nsatz. Qed.
  Lemma eval_mul p q : eval (mul p q) = eval p * eval q.
  Proof. induction p; simpl mul;
           rewrite ?eval_nil, ?eval_cons, ?eval_app, ?eval_map_mul; nsatz. Qed.

  Section GeneralizedMersenneReduction.
    Fixpoint split (s:Z) (xs:list limb) : list limb * list limb :=
      match xs with
      | nil => (nil, nil)
      | cons x xs' =>
        let sxs' := split s xs' in
        if dec (fst x mod s = 0)
        then (fst sxs',          cons (fst x / s, snd x) (snd sxs'))
        else (cons x (fst sxs'), snd sxs')
      end.

    Lemma eval_split s p (s_nonzero:s<>0) :
      eval (fst (split s p)) + s * eval (snd (split s p)) = eval p.
    Proof. induction p;
             repeat match goal with
                    | H:_ |- _ => unique pose proof (Z_div_exact_full_2 _ _ s_nonzero H)
                    | _ => progress rewrite ?split_cons, ?eval_cons, ?fst_pair, ?snd_pair
                    | _ => progress simpl split
                    | _ => progress break_match
                    | _ => nsatz
                    end. Qed.

    Definition reduce (s:Z) (c:list limb) (p:list limb) : list limb :=
      let ab := split s p in fst ab ++ mul c (snd ab).

    Lemma reduction_rule a b s c (modulus_nonzero:s-c<>0) :
      (a + s * b) mod (s - c) = (a + c * b) mod (s - c).
    Proof. replace (a + s * b) with ((a + c*b) + b*(s-c)) by nsatz.
           rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod; trivial. Qed.

    Lemma eval_reduce s c p (s_nonzero:s<>0) (modulus_nonzero:s-eval c<>0) :
      eval (reduce s c p) mod (s - eval c) = eval p mod (s - eval c).
    Proof. cbv [reduce].
           rewrite eval_app, eval_mul, <-reduction_rule, eval_split; trivial. Qed.
  End GeneralizedMersenneReduction.

  Section Positional.
    Context (weight : nat -> Z) (* [weight i] is the weight of position [i] *)
            (weight_0 : weight 0%nat = 1%Z)
            (weight_nonzero : forall i, weight i <> 0).

    Definition from_positional {n:nat} (xs:tuple Z n) : list limb :=
      List.combine (List.map weight (List.seq 0 n)) (Tuple.to_list n xs).

    Program Definition add_to_nth {n} i x : tuple Z n -> tuple Z n :=
      Tuple.on_tuple (ListUtil.update_nth i (runtime_add x)) _.
    Next Obligation. apply ListUtil.length_update_nth. Defined.

    Lemma eval_positional_add_to_nth {n} (i:nat) (H:(i<n)%nat) (x:Z) (xs:tuple Z n) :
      eval (from_positional (add_to_nth i x xs)) = weight i * x + eval (from_positional xs).
    Proof.
      cbv [from_positional add_to_nth Tuple.on_tuple]; rewrite !Tuple.to_list_from_list.
      rewrite ListUtil.combine_update_nth_r at 1.
      rewrite <-(update_nth_id i (List.combine _ _)) at 2.
      rewrite <-!(ListUtil.splice_nth_equiv_update_nth_update _ _ (weight 0, 0)) by (autorewrite with distr_length; lia); progress cbv [ListUtil.splice_nth id].
      repeat match goal with
             | |- context[?w] => progress (replace w with (weight i); [ring|])
             | _ => progress rewrite ?eval_app, ?eval_cons, ?fst_pair, ?snd_pair, <-?ListUtil.map_nth_default_always, ?map_fst_combine, ?List.firstn_all2, ?ListUtil.map_nth_default_always, ?nth_default_seq_inbouns, ?(eq_refl:runtime_add=Z.add) by (autorewrite with distr_length; lia)
             | _ => reflexivity
             end.
    Qed.

    Fixpoint place (t:limb) (i:nat) : nat * Z :=
      if dec (fst t mod weight i = 0)
      then (i, let c := fst t / weight i in (c * snd t)%RT)
      else match i with S i' => place t i' | O => (O, fst t * snd t)%RT end.

    Lemma place_in_range (t:limb) (n:nat) : (fst (place t n) < S n)%nat.
    Proof. induction n; simpl; break_match; simpl; omega. Qed.

    Lemma eval_place t i :
      weight (fst (place t i)) * snd (place t i) = fst t * snd t.
    Proof. induction i; simpl place; break_match;
             try match goal with H:_ |- _ => pose proof (Z_div_exact_full_2 _ _ (weight_nonzero _) H) end;
             rewrite ?weight_0, ?Z.div_1_r, ?fst_pair, ?snd_pair; nsatz. Qed.

    Definition to_positional {n} (init:tuple Z n) (p:list limb) :=
      List.fold_right (fun t => let p := place t (pred n) in add_to_nth (fst p) (snd p)) init p.
    Lemma eval_from_positional_to_positional {n} p (init:tuple Z n) (n_nonzero:n<>O) :
      eval (from_positional (to_positional init p)) = eval p + eval (from_positional init).
    Proof. induction p; simpl; try pose proof place_in_range a (pred n);
             rewrite ?eval_positional_add_to_nth by omega;
             rewrite ?eval_cons, ?eval_place; try nsatz. Qed.
  End Positional.
End B.

Local Coercion Z.of_nat : nat >-> Z.
Import Coq.Lists.List.ListNotations. Local Open Scope list_scope.
Program Definition zeros n : tuple Z n := Tuple.from_list n (List.map (fun _ => 0) (List.seq 0 n)) _.
Next Obligation. rewrite List.map_length, List.seq_length; reflexivity. Qed.

Goal let base10 i := 10^i in forall f0 f1 f2 f3 g0 g1 g2 g3 : Z, False. intros.
  let t := constr:(B.to_positional base10 (zeros 7)
                                   (B.mul
                                      (B.from_positional base10 (Tuple.from_list _ [f0;f1;f2;f3] eq_refl))
                                      (B.from_positional base10 (Tuple.from_list _ [g0;g1;g2;g3] eq_refl)))) in
  let t := (eval cbv -[runtime_mul runtime_add] in t) in
  let t := (eval cbv [runtime_mul runtime_add] in t) in
  remember t eqn:Heqt; rewrite !Z.mul_1_l, !Z.add_0_r, !Z.add_assoc in Heqt.
Abort.

Goal let base2_51 i := 2 ^ (51 * i) in forall f0 f1 f2 f3 f4 g0 g1 g2 g3 g4 : Z, False. intros.
  let t := constr:(B.to_positional base2_51 (zeros 5)
                                   (B.reduce (2^255) [(1,19)] 
                                   (B.mul
                                      (B.from_positional base2_51 (Tuple.from_list _ [f0;f1;f2;f3;f4] eq_refl))
                                      (B.from_positional base2_51 (Tuple.from_list _ [g0;g1;g2;g3;g4] eq_refl))))) in
  let t := (eval cbv -[runtime_mul runtime_add] in t) in
  let t := (eval cbv [runtime_mul runtime_add] in t) in
  remember t eqn:Heqt; rewrite !Z.mul_1_l, !Z.add_0_r, !Z.add_assoc, !Z.mul_assoc in Heqt.
Abort.


Goal let base2_25_5 i := 2 ^ (25 * (i / 2) + 26 * (i - i / 2)) in forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9: Z, False. intros.
  let t := constr:(B.to_positional base2_25_5 (zeros 10)
                                   (B.reduce (2^255) [(1,19)] 
                                   (B.mul
                                      (B.from_positional base2_25_5 (Tuple.from_list _ [f0;f1;f2;f3;f4;f5;f6;f7;f8;f9] eq_refl))
                                      (B.from_positional base2_25_5 (Tuple.from_list _ [g0;g1;g2;g3;g4;g5;g6;g7;g8;g9] eq_refl))))) in
  let t := (eval cbv -[runtime_mul runtime_add] in t) in
  let t := (eval cbv [runtime_mul runtime_add] in t) in
  remember t eqn:Heqt; rewrite !Z.mul_1_l, !Z.add_0_r, !Z.add_assoc, !Z.mul_assoc in Heqt.
Abort.

Goal let base2_56 i := 2 ^ (56 * i) in forall f0 f1 f2 f3 f4 f5 f6 f7 g0 g1 g2 g3 g4 g5 g6 g7: Z, False. intros.
  let t := constr:(B.to_positional base2_56 (zeros 8)
                                   (B.reduce (2^448) [(2^224,1);(1,-1)] 
                                   (B.reduce (2^448) [(2^224,1);(1,-1)] 
                                   (B.mul
                                      (B.from_positional base2_56 (Tuple.from_list _ [f0;f1;f2;f3;f4;f5;f6;f7] eq_refl))
                                      (B.from_positional base2_56 (Tuple.from_list _ [g0;g1;g2;g3;g4;g5;g6;g7] eq_refl)))))) in
  let t := (eval cbv -[runtime_mul runtime_add] in t) in
  let t := (eval cbv [runtime_mul runtime_add] in t) in
  remember t eqn:Heqt; rewrite !Z.mul_1_l, !Z.add_0_r, !Z.add_assoc, !Z.mul_assoc, !Z.mul_opp_l, !Z.add_opp_r in Heqt.
Abort.