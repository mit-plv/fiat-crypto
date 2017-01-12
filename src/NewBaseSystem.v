Require Import Crypto.Util.Tactics Crypto.Util.Decidable Crypto.Util.LetIn.

Require Import ZArith Nsatz Psatz Coq.omega.Omega.
Require Import Coq.ZArith.BinIntDef. Local Open Scope Z_scope.
Require Import Crypto.Util.ZUtil.

Require Coq.Lists.List. Local Notation list := List.list.
Require Crypto.Util.Tuple. Local Notation tuple := Tuple.tuple.

    (* TODO: move *)
    Lemma fst_pair {A B} (a:A) (b:B) : fst (a,b) = a. reflexivity. Qed.
    Lemma snd_pair {A B} (a:A) (b:B) : snd (a,b) = b. reflexivity. Qed.
    Create HintDb cancel_pair discriminated. Hint Rewrite @fst_pair @snd_pair : cancel_pair.

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
      break_innermost_match; solve [ trivial | omega ].
    Qed.
    
    Lemma mod_add_mul_full a b c k m : m <> 0 -> c mod m = k mod m -> 
                                    (a + b * c) mod m = (a + b * k) mod m.
    Proof.
      intros; rewrite Z.add_mod, Z.mul_mod by auto.
      match goal with H : _ mod _ = _ mod _ |- _ => rewrite H end.
      rewrite <-Z.mul_mod, <-Z.add_mod by auto; reflexivity.
    Qed.

Delimit Scope runtime_scope with RT.
Definition runtime_mul := Z.mul. Global Infix "*" := runtime_mul : runtime_scope.
Definition runtime_add := Z.add. Global Infix "+" := runtime_add : runtime_scope. 

Module B.
  Let limb := (Z*Z)%type. (* position coefficient and run-time value *)
  Module Associational.
    Definition eval (p:list limb) : Z :=
      List.fold_right Z.add 0%Z (List.map (fun t => fst t * snd t) p).
    
    Lemma eval_nil : eval nil = 0. Proof. reflexivity. Qed.
    Lemma eval_cons p q : eval (p::q) = (fst p) * (snd p) + eval q. Proof. reflexivity. Qed.
    Lemma eval_app p q: eval (p++q) = eval p + eval q.
    Proof. induction p; simpl eval; rewrite ?eval_nil, ?eval_cons; nsatz. Qed.
    Create HintDb push_eval discriminated. Hint Rewrite eval_nil eval_cons eval_app : push_eval.

    Definition mul (p q:list limb) : list limb :=
      List.flat_map (fun t => List.map (fun t' => (fst t * fst t', (snd t * snd t')%RT)) q) p.
    Lemma eval_map_mul a x q : eval (List.map (fun t => (a * fst t, x * snd t)) q) = a * x * eval q.
    Proof. induction q; simpl List.map; autorewrite with push_eval cancel_pair; nsatz. Qed.
    Hint Rewrite eval_map_mul : push_eval.
    Lemma eval_mul p q : eval (mul p q) = eval p * eval q.
    Proof. induction p; simpl mul; autorewrite with push_eval cancel_pair; try nsatz. Qed.
    Hint Rewrite eval_mul : push_eval.

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
                    | _ => progress simpl split
                    | _ => progress autorewrite with push_eval cancel_pair
                    | _ => progress break_match
                    | H:_ |- _ => unique pose proof (Z_div_exact_full_2 _ _ s_nonzero H)
                    end; nsatz. Qed.

    Definition reduce (s:Z) (c:list limb) (p:list limb) : list limb :=
      let ab := split s p in fst ab ++ mul c (snd ab).

    Lemma reduction_rule a b s c (modulus_nonzero:s-c<>0) :
      (a + s * b) mod (s - c) = (a + c * b) mod (s - c).
    Proof. replace (a + s * b) with ((a + c*b) + b*(s-c)) by nsatz.
           rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod; trivial. Qed.

    Lemma eval_reduce s c p (s_nonzero:s<>0) (modulus_nonzero:s-eval c<>0) :
      eval (reduce s c p) mod (s - eval c) = eval p mod (s - eval c).
    Proof. cbv [reduce]. rewrite eval_app, eval_mul, <-reduction_rule, eval_split; trivial. Qed.

    Definition carry (w fw:Z) : list limb -> list limb :=
      List.flat_map (fun t => if dec (fst t = w)
                              then cons (w*fw, snd t / fw) (cons (w, snd t mod fw) nil)
                              else cons t nil).
    Lemma eval_carry w fw p (fw_nonzero:fw<>0) : eval (carry w fw p) = eval p.
    Proof. induction p; simpl carry; repeat break_match; autorewrite with push_eval cancel_pair;
             try pose proof (Z.div_mod (snd a) _ fw_nonzero); nsatz.
    Qed. Hint Rewrite eval_carry eval_reduce : push_eval.
  End Associational.

  Module Positional.
    Section Positional.
      Import Associational.
      Context (weight : nat -> Z) (* [weight i] is the weight of position [i] *)
              (weight_0 : weight 0%nat = 1%Z)
              (weight_nonzero : forall i, weight i <> 0).

      (** Converting from positional to associational *)

      Definition to_associational {n:nat} (xs:tuple Z n) : list limb :=
        List.combine (List.map weight (List.seq 0 n)) (Tuple.to_list n xs).
      Definition eval {n} x := Associational.eval (@to_associational n x).
      Lemma eval_to_associational {n} x : Associational.eval (@to_associational n x) = eval x.
      Proof. reflexivity. Qed.

      (** Converting from associational to positional *)

      Program Definition zeros n : tuple Z n := Tuple.from_list n (List.map (fun _ => 0) (List.seq 0 n)) _.
      Next Obligation. autorewrite with distr_length; reflexivity. Qed.
      Lemma eval_zeros n : eval (zeros n) = 0.
      Proof. cbv [eval Associational.eval to_associational zeros]; rewrite Tuple.to_list_from_list.
             generalize dependent (List.seq 0 n); intro xs; induction xs; simpl; nsatz. Qed.

      Program Definition add_to_nth {n} i x : tuple Z n -> tuple Z n :=
        Tuple.on_tuple (ListUtil.update_nth i (runtime_add x)) _.
      Next Obligation. apply ListUtil.length_update_nth. Defined.
      Lemma eval_add_to_nth {n} (i:nat) (H:(i<n)%nat) (x:Z) (xs:tuple Z n) :
        eval (add_to_nth i x xs) = weight i * x + eval xs.
      Proof.
        cbv [eval to_associational add_to_nth Tuple.on_tuple runtime_add]; rewrite !Tuple.to_list_from_list.
        rewrite ListUtil.combine_update_nth_r at 1.
        rewrite <-(update_nth_id i (List.combine _ _)) at 2.
        rewrite <-!(ListUtil.splice_nth_equiv_update_nth_update _ _ (weight 0, 0)); cbv [ListUtil.splice_nth id];
          repeat match goal with
                 | _ => progress (apply Zminus_eq; ring_simplify)
                 | _ => progress autorewrite with push_eval cancel_pair distr_length
                 | _ => progress rewrite <-?ListUtil.map_nth_default_always, ?map_fst_combine, ?List.firstn_all2, ?ListUtil.map_nth_default_always, ?nth_default_seq_inbouns, ?plus_O_n
                 end; trivial; lia. Qed. Hint Rewrite @eval_add_to_nth eval_zeros : push_eval.

      Fixpoint place (t:limb) (i:nat) : nat * Z :=
        if dec (fst t mod weight i = 0)
        then (i, let c := fst t / weight i in (c * snd t)%RT)
        else match i with S i' => place t i' | O => (O, fst t * snd t)%RT end.
      Lemma place_in_range (t:limb) (n:nat) : (fst (place t n) < S n)%nat.
      Proof. induction n; simpl; break_match; simpl; omega. Qed.
      Lemma weight_place t i : weight (fst (place t i)) * snd (place t i) = fst t * snd t.
      Proof. induction i; simpl place; break_match; autorewrite with cancel_pair;
               try find_apply_lem_hyp Z_div_exact_full_2; nsatz || auto. Qed.

      Definition from_associational n (p:list limb) :=
        List.fold_right (fun t => let p := place t (pred n) in add_to_nth (fst p) (snd p)) (zeros n) p.
      Lemma eval_from_associational {n} p (n_nonzero:n<>O) :
        eval (from_associational n p) = Associational.eval p.

      Proof. induction p; simpl; try pose proof place_in_range a (pred n);
               autorewrite with push_eval; rewrite ?weight_place; nsatz || omega.
      Qed. Hint Rewrite @eval_from_associational : push_eval.

      (** Carrying *)

      Definition carry_allowed (i j:nat) : Prop := weight i mod weight j = 0 /\ weight j / weight i <> 0.
      Definition carry_from_to {n} (i j:nat) (p:tuple Z n) : tuple Z n :=
        from_associational n (carry (weight i) (weight j / weight i) (to_associational p)).
      Lemma eval_carry_from_to {n} (n_nonzero:n<>O) i j (H:carry_allowed i j) (p:tuple Z n) :
        eval (carry_from_to i j p) = eval p.
      Proof. cbv [carry_from_to carry_allowed] in *;
                destruct_head and; autorewrite with push_eval; trivial. Qed.

      Definition carry_pick_dst n (i:nat) : nat :=
        match List.find (fun j => if dec (carry_allowed i j) then true else false) (List.skipn i (List.seq (S O) (S n)) with
        | None => i
        | Some j => j
        end.
      Lemma carry_allowed_refl (i:nat) : carry_allowed i i.
      Proof. cbv [carry_allowed]; rewrite Z.mod_same, Z.div_same by trivial; omega. Qed.
      Lemma carry_allowed_pick_dst (n i:nat) : carry_allowed i (carry_pick_dst n i).
      Proof. induction i; cbv [carry_pick_dst];
               repeat match goal with
                      | _ => progress break_match
                      | _ => progress destruct_head and
                      | H:_ |- _ => apply List.find_some in H
                      | _ => solve [trivial using carry_allowed_refl | discriminate ]
                      end. Qed.

      Definition carry {n} (i:nat) (p:tuple Z n) := carry_from_to i (carry_pick_dst n i) p.
      Lemma eval_carry {n} (n_nonzero:n<>O) (i:nat) (p:tuple Z n) : eval (carry i p) = eval p.
      Proof. cbv [carry]. rewrite ?eval_carry_from_to; auto using carry_allowed_pick_dst. Qed.
      Hint Rewrite @eval_carry_from_to @eval_carry : push_eval.
    End Positional.
  End Positional.
End B.

Section Karatsuba.
  Context {T : Type} (eval : T -> Z)
          (sub : T -> T -> T)
          (eval_sub : forall x y, eval (sub x y) = eval x - eval y)
          (mul : T -> T -> T)
          (eval_mul : forall x y, eval (mul x y) = eval x * eval y)
          (add : T -> T -> T)
          (eval_add : forall x y, eval (add x y) = eval x + eval y)
          (scmul : Z -> T -> T)
          (eval_scmul : forall c x, eval (scmul c x) = c * eval x)
          (split : Z -> T -> T * T)
          (eval_split : forall s x, s <> 0 -> eval (fst (split s x)) + s * (eval (snd (split s x))) = eval x)
  .

  Definition karatsuba_mul s (x y : T) : T :=
      let xab := split s x in
      let yab := split s y in
      let xy0 := mul (fst xab) (fst yab) in
      let xy2 := mul (snd xab) (snd yab) in
      let xy1 := sub (mul (add (fst xab) (snd xab)) (add (fst yab) (snd yab))) (add xy2 xy0) in
      add (add (scmul (s^2) xy2) (scmul s xy1)) xy0.

  Lemma eval_karatsuba_mul s x y (s_nonzero:s <> 0) :
    eval (karatsuba_mul s x y) = eval x * eval y.
  Proof. cbv [karatsuba_mul]; repeat rewrite ?eval_sub, ?eval_mul, ?eval_add, ?eval_scmul.
         rewrite <-(eval_split s x), <-(eval_split s y) by assumption; ring. Qed.


  Definition goldilocks_mul s (xs ys : T) : T :=
    let a_b := split s xs in
    let c_d := split s ys in
    let ac := mul (fst a_b) (fst c_d) in
    (add (add ac (mul (snd a_b) (snd c_d)))
         (scmul s (sub (mul (add (fst a_b) (snd a_b)) (add (fst c_d) (snd c_d))) ac))).

  Local Existing Instances Z.equiv_modulo_Reflexive RelationClasses.eq_Reflexive Z.equiv_modulo_Symmetric Z.equiv_modulo_Transitive Z.mul_mod_Proper Z.add_mod_Proper Z.modulo_equiv_modulo_Proper.

  Lemma goldilocks_mul_correct (p : Z) (p_nonzero : p <> 0) s (s_nonzero : s <> 0) (s2_modp : (s^2) mod p = (s+1) mod p) xs ys :
    (eval (goldilocks_mul s xs ys)) mod p = (eval xs * eval ys) mod p.
  Proof. cbv [goldilocks_mul]; Zmod_to_equiv_modulo.
    repeat rewrite ?eval_mul, ?eval_add, ?eval_sub, ?eval_scmul, <-?(eval_split s xs), <-?(eval_split s ys) by assumption; ring_simplify.
    setoid_rewrite s2_modp.
    apply f_equal2; nsatz. Qed.
End Karatsuba.

Local Coercion Z.of_nat : nat >-> Z.
Import Coq.Lists.List.ListNotations. Local Open Scope list_scope.
Import B.

Goal let base10 i := 10^i in forall f0 f1 f2 f3 g0 g1 g2 g3 : Z, False. intros.
  let t := constr:(Positional.from_associational base10 7
                                   (Associational.mul
                                      (Positional.to_associational base10 (Tuple.from_list _ [f0;f1;f2;f3] eq_refl))
                                      (Positional.to_associational base10 (Tuple.from_list _ [g0;g1;g2;g3] eq_refl)))) in
  let t := (eval cbv -[runtime_mul runtime_add] in t) in
  let t := (eval cbv [runtime_mul runtime_add] in t) in
  remember t eqn:Heqt; rewrite !Z.mul_1_l, !Z.add_0_r, !Z.add_assoc in Heqt.
Abort.

Goal let base2_51 i := 2 ^ (51 * i) in forall f0 f1 f2 f3 f4 g0 g1 g2 g3 g4 : Z, False. intros.
  let t := constr:(Positional.from_associational base2_51 5
                                   (Associational.reduce (2^255) [(1,19)] 
                                   (Associational.mul
                                      (Positional.to_associational base2_51 (Tuple.from_list _ [f0;f1;f2;f3;f4] eq_refl))
                                      (Positional.to_associational base2_51 (Tuple.from_list _ [g0;g1;g2;g3;g4] eq_refl))))) in
  let t := (eval cbv -[runtime_mul runtime_add] in t) in
  let t := (eval cbv [runtime_mul runtime_add] in t) in
  remember t eqn:Heqt; rewrite !Z.mul_1_l, !Z.add_0_r, !Z.add_assoc, !Z.mul_assoc in Heqt.
Abort.


Goal let base2_25_5 i := 2 ^ (25 * (i / 2) + 26 * (i - i / 2)) in forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9: Z, False. intros.
  let t := constr:(Positional.from_associational base2_25_5 10
                                   (Associational.reduce (2^255) [(1,19)] 
                                   (Associational.mul
                                      (Positional.to_associational base2_25_5 (Tuple.from_list _ [f0;f1;f2;f3;f4;f5;f6;f7;f8;f9] eq_refl))
                                      (Positional.to_associational base2_25_5 (Tuple.from_list _ [g0;g1;g2;g3;g4;g5;g6;g7;g8;g9] eq_refl))))) in
  let t := (eval cbv -[runtime_mul runtime_add] in t) in
  let t := (eval cbv [runtime_mul runtime_add] in t) in
  remember t eqn:Heqt; rewrite !Z.mul_1_l, !Z.add_0_r, !Z.add_assoc, !Z.mul_assoc in Heqt.
Abort.

Goal let base2_56 i := 2 ^ (56 * i) in forall f0 f1 f2 f3 f4 f5 f6 f7 g0 g1 g2 g3 g4 g5 g6 g7: Z, False. intros.
  let t := constr:(Positional.from_associational base2_56 8
                                   (Associational.reduce (2^448) [(2^224,1);(1,-1)] 
                                   (Associational.reduce (2^448) [(2^224,1);(1,-1)] 
                                   (Associational.mul
                                      (Positional.to_associational base2_56 (Tuple.from_list _ [f0;f1;f2;f3;f4;f5;f6;f7] eq_refl))
                                      (Positional.to_associational base2_56 (Tuple.from_list _ [g0;g1;g2;g3;g4;g5;g6;g7] eq_refl)))))) in
  let t := (eval cbv -[runtime_mul runtime_add] in t) in
  let t := (eval cbv [runtime_mul runtime_add] in t) in
  remember t eqn:Heqt; rewrite !Z.mul_1_l, !Z.add_0_r, !Z.add_assoc, !Z.mul_assoc, !Z.mul_opp_l, !Z.add_opp_r in Heqt.
Abort.

Require Import Crypto.Algebra. (* TODO: move ring_simplify_subterms_in_all to a different file? *)
Goal let base2_25_5 i := 2 ^ (25 * (i / 2) + 26 * (i - i / 2)) in forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9: Z, False. intros.
  let t := constr:(Positional.from_associational base2_25_5 10
                                   (Associational.reduce (2^255) [(1,19)] 
                                   (karatsuba_mul (fun x y => x ++ (List.map (fun t => (fst t, (-1 * snd t)%RT)) y)) Associational.mul (@List.app _) (fun x => List.map (fun t => (x * fst t, snd t))) Associational.split (2^102)
                                      (Positional.to_associational base2_25_5 (Tuple.from_list _ [f0;f1;f2;f3;f4;f5;f6;f7;f8;f9] eq_refl))
                                      (Positional.to_associational base2_25_5 (Tuple.from_list _ [g0;g1;g2;g3;g4;g5;g6;g7;g8;g9] eq_refl))))) in
  let t := (eval cbv -[runtime_mul runtime_add] in t) in
  let t := (eval cbv [runtime_mul runtime_add] in t) in
  remember t eqn:Heqt; change (Zneg xH) with (Z.opp 1) in Heqt; (* TODO : make this a lemma *)
    ring_simplify_subterms_in_all.
Abort.

Goal let base2_56 i := 2 ^ (56 * i) in forall f0 f1 f2 f3 f4 f5 f6 f7 g0 g1 g2 g3 g4 g5 g6 g7: Z, False. intros.
  let t := constr:(Positional.from_associational base2_56 8
                                   (Associational.reduce (2^448) [(2^224,1);(1,-1)]
                                   (Associational.reduce (2^448) [(2^224,1);(1,-1)]
                                   (goldilocks_mul (fun x y => x ++ (List.map (fun t => (fst t, (-1 * snd t)%RT)) y)) Associational.mul (@List.app _) (fun x => List.map (fun t => (x * fst t, snd t))) Associational.split (2^224)
                                      (Positional.to_associational base2_56 (Tuple.from_list _ [f0;f1;f2;f3;f4;f5;f6;f7] eq_refl))
                                      (Positional.to_associational base2_56 (Tuple.from_list _ [g0;g1;g2;g3;g4;g5;g6;g7] eq_refl)))))) in
  let t := (eval cbv -[runtime_mul runtime_add] in t) in
  let t := (eval cbv [runtime_mul runtime_add] in t) in
  remember t eqn:Heqt; rewrite !Z.mul_1_l, !Z.add_0_r, !Z.add_assoc, !Z.mul_assoc, !Z.mul_opp_l, !Z.add_opp_r, !Z.sub_opp_r in Heqt.
Abort.