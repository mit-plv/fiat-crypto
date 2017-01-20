Require Import Crypto.Util.Tactics Crypto.Util.Decidable Crypto.Util.LetIn.

Require Import ZArith Nsatz Psatz Coq.omega.Omega.
Require Import Coq.ZArith.BinIntDef. Local Open Scope Z_scope.
Require Import Crypto.Util.ZUtil Crypto.Util.ListUtil.

Require Coq.Lists.List. Local Notation list := List.list.
Require Crypto.Util.Tuple. Local Notation tuple := Tuple.tuple.
Require Import Recdef.

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

    Fixpoint remove_first {A} (dec:forall x y:A, {x = y} + {x<>y}) (x:A) (ls:list A)
      := match ls with
         | nil => nil
         | (a :: ls')%list =>
           if (dec x a) then ls' else (a :: remove_first dec x ls')%list
         end.

    Lemma length_remove_first_In {A} dec (x:A) ls:
      List.In x ls -> length (remove_first dec x ls) = (length ls - 1)%nat.
    Proof.
      induction ls; simpl remove_first; intros; [reflexivity|].
      break_if; simpl length; try omega.
      destruct H; try congruence. rewrite IHls by assumption.
      assert (length ls > 0)%nat by (destruct ls; simpl in *; omega).
      omega.
    Qed.

    Lemma length_remove_first_notIn {A} dec (x:A) ls:
      ~List.In x ls -> length (remove_first dec x ls) = length ls.
    Proof.
      induction ls; simpl remove_first; intros; [reflexivity|].
      break_if; simpl length.
      { simpl in H. intuition. congruence. }
      { rewrite IHls; auto using List.in_cons. }
    Qed.
    
    Definition find_remove_first {A dec} (f:A -> bool) ls : (option A) * list A
      := match List.find (fun a => f a) ls with
         | None => (None, ls)
         | Some a => (Some a, remove_first dec a ls)
         end.

    Lemma length_find_remove_first {A dec} (f:A -> bool) ls :
      length (snd (@find_remove_first _ dec f ls)) =
        match (fst (@find_remove_first _ dec f ls)) with
        | None => length ls
        | Some _ => (length ls - 1)%nat
        end.
    Proof.
      cbv [find_remove_first]; repeat break_match; try discriminate;
        rewrite ?fst_pair, ?snd_pair in *; auto.
      apply length_remove_first_In.
      apply List.find_some in Heqo; tauto.
    Qed.

    Lemma to_nat_neg : forall x, x < 0 -> Z.to_nat x = 0%nat.
    Proof. destruct x; try reflexivity; intros. pose proof (Pos2Z.is_pos p). omega. Qed.

    Lemma remove_first_cons {A dec} x (ls:list A) :
      remove_first dec x (x::ls) = ls.
    Proof. cbv [remove_first]. break_if;  congruence. Qed.
    
    Lemma remove_first_correct {A dec} x (ls:list A) :
      List.In x ls ->
      exists hd tl, (hd ++ tl)%list = remove_first dec x ls
                    /\ (hd ++ x :: tl)%list = ls.
    Proof.
      induction ls; intros; [exfalso; auto|].
      cbv [remove_first].
      break_if.
      { exists nil; exists ls.
        subst; rewrite !List.app_nil_l.
        tauto. }
      { destruct IHls as [hd [tl IHls]];[destruct H; congruence||assumption|].
        exists (a::hd)%list. exists tl.
        rewrite <-!List.app_comm_cons.
        destruct IHls as [Hrf Hls].
        rewrite Hrf, Hls.
        tauto. }
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

    Section Saturated.
      Context {word_max : Z} {word_max_pos : 1 < word_max}
              {add : Z -> Z -> Z * Z}
              {add_correct : forall x y, fst (add x y) + word_max * snd (add x y) = x + y}
              {end_wt:Z} {end_wt_pos : 0 < end_wt}
      .
      
      Definition has_same_wt (cx:limb) := fun a:limb => if dec (fst cx = fst a) then true else false.

      Lemma find_remove_first_same_wt cx cx' p p':
        @find_remove_first limb dec_eq_prod (has_same_wt cx) p = (Some cx', p') ->
        fst cx * (snd cx + snd cx') + eval p' = fst cx * snd cx + eval p.
      Proof.
        cbv [find_remove_first].
        break_match; intros; try discriminate.
        destruct (List.find_some _ _ Heqo) as [HIn Hwt].
        destruct (@remove_first_correct limb dec_eq_prod _ _ HIn) as [hd [tl [Hrf Hp]]].
        inversion H. subst.
        rewrite <-Hrf; autorewrite with push_eval.
        cbv [has_same_wt] in Hwt; break_if; try discriminate.
        nsatz.
      Qed.

      Fixpoint compact_no_carry' (acc p:list limb) : list limb :=
        match p with
        | nil => acc
        | (cx::tl)%list =>
          match (@find_remove_first limb dec_eq_prod (has_same_wt cx) acc) with
          | (None,_) => compact_no_carry' (cx::acc)%list tl
          | (Some l,acc') => compact_no_carry' ((fst cx, snd cx + snd l)::acc')%list tl
          end
        end.
      Definition compact_no_carry := compact_no_carry' nil.
      Lemma eval_compact_no_carry' p: forall acc,
        eval (compact_no_carry' acc p) = eval acc + eval p.
      Proof.
        induction p; simpl;
        repeat match goal with
               | |- _ => break_match
               | |- _ => progress (intros;subst)
               | |- _ => progress autorewrite with push_eval in *
               | |- _ => progress rewrite ?@fst_pair, ?@snd_pair in *
               | |- _ => rewrite IHp
               | H : find_remove_first _ _ = _ |- _ => apply find_remove_first_same_wt in H
                                                                                          | |- _ => nsatz
               end.
      Qed.
      Lemma eval_compact_no_carry p: eval (compact_no_carry p) = eval p.
      Proof. cbv [compact_no_carry]. rewrite eval_compact_no_carry'. reflexivity. Qed. Hint Rewrite eval_compact_no_carry : push_eval.
      
      Function add_and_carry (cx:limb) (acc p:list limb)
               {measure (fun cx => Z.to_nat (end_wt - fst cx)) cx}
        : list limb * list limb * limb :=
        if dec (fst cx <= 0) then (acc,p,cx) (* never happens *) else 
        if dec (fst cx >= end_wt) then (acc, p, cx) else
          match (@find_remove_first limb dec_eq_prod (has_same_wt cx) p) with
          | (None,_) => add_and_carry (fst cx * word_max, 0) (cx :: acc)%list p
          | (Some cx',p') =>
            let '(sum, carry) := add (snd cx) (snd cx') in
            let new_list := ((fst cx, sum) :: p')%list in
            let new_limb := (fst cx * word_max, carry) in
            add_and_carry new_limb acc new_list
          end.
      Proof.
        { intros; simpl.
          destruct (Z_lt_dec end_wt (fst cx*word_max)).
          { rewrite to_nat_neg by omega.
            change 0%nat with (Z.to_nat 0).
            apply Z2Nat.inj_lt; omega. }
          { apply Z2Nat.inj_lt; try omega.
            apply Z.sub_lt_mono_l.
            apply Z.le_lt_trans with (m := fst cx * 1); try omega.
            apply Z.mul_lt_mono_pos_l; auto; omega.
        } }
        { intros; simpl.
          destruct (Z_lt_dec end_wt (fst cx*word_max)).
          { rewrite to_nat_neg by omega.
            change 0%nat with (Z.to_nat 0).
            apply Z2Nat.inj_lt; omega. }
          { apply Z2Nat.inj_lt; try omega.
            apply Z.sub_lt_mono_l.
            apply Z.le_lt_trans with (m := fst cx * 1); try omega.
            apply Z.mul_lt_mono_pos_l; auto; omega.
        } }
      Defined.

      Lemma length_add_and_carry cx acc p: length (snd (fst (add_and_carry cx acc p))) = length p.
      Proof.
        functional induction (add_and_carry cx acc p); try reflexivity.
        { rewrite IHp0. reflexivity. }
        { rewrite IHp0. simpl length.
          let A := fresh "H" in
          lazymatch goal with H : @find_remove_first ?T ?dec ?f ?l = (_,_) |- _ =>
                              pose proof (@length_find_remove_first T dec f l) as A;
                                rewrite H in A; simpl in A
          end.
          assert (length p > 0)%nat by (destruct p; (discriminate || simpl; omega)).
          omega. }
      Qed.

      Lemma eval_add_and_carry cx acc p :
        eval (fst (fst (add_and_carry cx acc p))) + eval (snd (fst (add_and_carry cx acc p))) + eval (snd (add_and_carry cx acc p)::nil)%list = eval (cx::p)%list + eval acc.
      Proof.
        functional induction (add_and_carry cx acc p);
          autorewrite with push_eval in *;
          rewrite ?@fst_pair, ?@snd_pair in *.
        { ring. }
        { omega. }
        { rewrite IHp0. ring. }
        { rewrite IHp0. clear IHp0.
          let A := fresh H in
          lazymatch goal with H : add ?x ?y = _ |- _ =>
                          pose proof (add_correct x y) as A;
                            rewrite H in A
          end.
          lazymatch goal with H : find_remove_first _ _ = _ |- _ =>
                              apply find_remove_first_same_wt in H end.
          
          rewrite ?@fst_pair, ?@snd_pair in *.
          nsatz.
        }
      Qed.

      Function compact_rows' (end_carry:list limb) (acc p:list limb)
               {measure length p}: list limb :=
        match p with
        | nil => (acc ++ end_carry)%list
        | (cx :: p')%list =>
          let '(new_acc, new_list, new_end_carry) := add_and_carry cx nil p' in
          compact_rows' (compact_no_carry (new_end_carry :: end_carry)) (compact_no_carry (new_acc ++ acc))%list new_list
        end.
      Proof.
        intros. subst. simpl length.
        let A := fresh "H" in
        lazymatch goal with H : add_and_carry ?l ?acc ?p = _ |- _ =>
                            pose proof (@length_add_and_carry l acc p) as A;
                              rewrite H in A
        end.
        rewrite ?@fst_pair, ?@snd_pair in *. omega.
      Defined.

      Definition compact_rows (p:list limb) : list limb :=
        compact_rows' nil nil p.

      Lemma eval_compact_rows' end_carry acc p :
        eval (compact_rows' end_carry acc p) = eval p + eval acc + eval end_carry.
      Proof.
        functional induction (compact_rows' end_carry acc p);
          autorewrite with push_eval in *.
        { reflexivity. }
        { rewrite IHl.
          let A := fresh "H" in
          lazymatch goal with H : add_and_carry ?x ?y ?z = _ |- _ =>
                          pose proof (eval_add_and_carry x y z) as A;
                            rewrite H in A
          end.
          rewrite ?@fst_pair, ?snd_pair in *.
          autorewrite with push_eval in *.
          nsatz. }
      Qed.

      Lemma eval_compact_rows p : eval (compact_rows p) = eval p.
      Proof. cbv [compact_rows]; rewrite eval_compact_rows'; autorewrite with push_eval; ring. Qed.

    End Saturated.
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

      Definition carry (index:nat) (p:list limb) : list limb :=
        Associational.carry (weight index) (weight (S index) / weight index) p.
      Lemma eval_carry i p : weight (S i) / weight i <> 0 ->
        Associational.eval (carry i p) = Associational.eval p.
      Proof. cbv [carry]; intros; auto using eval_carry. Qed.
      Hint Rewrite @eval_carry : push_eval.
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