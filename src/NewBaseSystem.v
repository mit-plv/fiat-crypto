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
    
    Fixpoint find_remove_first' {A} (f : A->bool) (acc ls:list A) : (option A) * list A :=
      (match ls with
      | nil => (None, acc)
      | x :: tl =>
        if f x then (Some x, acc ++ tl) else find_remove_first' f (acc ++ x::nil) tl
      end)%list.
    
    Definition find_remove_first {A} (f:A -> bool) ls : (option A) * list A :=
      find_remove_first' f nil ls.

    Lemma length_find_remove_first' {A} (f:A -> bool) ls : forall acc,
      length (snd (@find_remove_first' _ f acc ls)) =
        match (fst (@find_remove_first' _ f acc ls)) with
        | None => length (acc ++ ls)
        | Some _ => (length (acc ++ ls) - 1)%nat
        end.
    Proof.
      induction ls; intros; simpl find_remove_first';
        repeat match goal with
               | |- _ => break_match; try discriminate
               | |- _ => progress (rewrite ?@fst_pair, ?@snd_pair in * )
               | |- _ => progress distr_length
               | |- _ => rewrite IHls
               end.
    Qed.

    Lemma length_find_remove_first {A} (f:A -> bool) ls :
      length (snd (find_remove_first f ls)) =
        match (fst (find_remove_first f ls)) with
        | None => length ls
        | Some _ => (length ls - 1)%nat
        end.
    Proof. cbv [find_remove_first]; rewrite length_find_remove_first'; distr_length. Qed.

    Lemma to_nat_neg : forall x, x < 0 -> Z.to_nat x = 0%nat.
    Proof. destruct x; try reflexivity; intros. pose proof (Pos2Z.is_pos p). omega. Qed.

Delimit Scope runtime_scope with RT.
Definition runtime_mul := Z.mul. Global Infix "*" := runtime_mul : runtime_scope.
Definition runtime_add := Z.add. Global Infix "+" := runtime_add : runtime_scope. 
Definition runtime_div := Z.div. Global Infix "/" := runtime_div : runtime_scope. 
Definition runtime_modulo := Z.modulo. Global Infix "mod" := runtime_modulo : runtime_scope.
Definition runtime_fst {A B} := @fst A B.
Definition runtime_snd {A B} := @snd A B.

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

      Lemma find_remove_first'_same_wt cx cx' p: forall acc,
        fst (find_remove_first' (has_same_wt cx) acc p) = Some cx' ->
        fst cx * (snd cx + snd cx') + eval (snd (find_remove_first' (has_same_wt cx) acc p)) = fst cx * snd cx + eval acc + eval p.
      Proof.
        induction p; intros; simpl find_remove_first' in *;
            repeat match goal with
                   | |- _ => progress (autorewrite with push_eval in * )
                   | |- _ => progress (rewrite ?@fst_pair, ?@snd_pair in * )
                   | H : Some _ = Some _ |- _ => progress (inversion H; subst)
                   | |- _ => rewrite IHp by assumption; clear IHp
                   | |- _ => break_if
                   | |- _ => discriminate
                   | H : has_same_wt _ _ = true |- _ => cbv [has_same_wt] in H
                   | |- _ => nsatz
                   end.
      Qed.

      Lemma find_remove_first_same_wt cx cx' p:
        fst (@find_remove_first limb (has_same_wt cx) p) = Some cx' ->
        fst cx * (snd cx + snd cx') + eval (snd (@find_remove_first limb (has_same_wt cx) p)) = fst cx * snd cx + eval p.
      Proof.
        cbv [find_remove_first]; intros.
        rewrite find_remove_first'_same_wt by auto.
        autorewrite with push_eval; ring.
      Qed.

      Fixpoint compact_no_carry' (acc p:list limb) : list limb :=
        match p with
        | nil => acc
        | (cx::tl)%list =>
          let found_ls := (find_remove_first (has_same_wt cx) acc) in
          match (fst found_ls) with
          | None => compact_no_carry' (cx::acc)%list tl
          | Some l => compact_no_carry' ((fst cx, (snd cx + snd l)%RT)::snd found_ls)%list tl
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
               | H : fst (find_remove_first _ _) = _ |- _ => apply find_remove_first_same_wt in H
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
        let found_ls := find_remove_first (has_same_wt cx) p in
          match (fst found_ls) with
          | None => ((cx::acc)%list,p,(end_wt,0))
          | Some cx' =>
            let sum_carry := add (snd cx) (snd cx') in
            let new_list := ((fst cx, (runtime_fst sum_carry)) :: snd found_ls)%list in
            let new_limb := (fst cx * word_max, (runtime_snd sum_carry)) in
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
      Defined.

      Lemma length_add_and_carry cx acc p: length (snd (fst (add_and_carry cx acc p))) = length p.
      Proof.
        functional induction (add_and_carry cx acc p); try reflexivity.
        { rewrite IHp0. simpl length.
          let A := fresh "H" in
          lazymatch goal with H : fst (find_remove_first ?f ?l) = _ |- _ =>
                              pose proof (length_find_remove_first f l) as A;
                                rewrite H in A; rewrite A
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
        { autorewrite with push_eval. ring. }
        { rewrite IHp0. clear IHp0.
          lazymatch goal with |- context[add ?x ?y] =>
                              specialize (add_correct x y) end.
          lazymatch goal with H : fst (find_remove_first _ _) = _ |- _ =>
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
          let acc_list_carry := add_and_carry cx nil p' in
          compact_rows' (compact_no_carry (snd acc_list_carry :: end_carry)) (compact_no_carry (fst (fst acc_list_carry) ++ acc))%list (snd (fst acc_list_carry))
        end.
      Proof. intros. rewrite length_add_and_carry. simpl; omega. Defined.

      Definition compact_rows (p:list limb) : list limb :=
        compact_rows' nil nil p.

      Lemma eval_compact_rows' end_carry acc p :
        eval (compact_rows' end_carry acc p) = eval p + eval acc + eval end_carry.
      Proof.
        functional induction (compact_rows' end_carry acc p);
          autorewrite with push_eval in *.
        { reflexivity. }
        { rewrite IHl; clear IHl.
          lazymatch goal with |- context[add_and_carry ?x ?y ?z] =>
                          pose proof (eval_add_and_carry x y z)
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

Axiom add_get_carry : Z -> Z -> Z * Z.

Lemma lt_1_2_32 : 1 < 2^32. cbv. congruence. Qed.

Require Import Crypto.Algebra. (* TODO: move ring_simplify_subterms_in_all to a different file? *)
Goal let base2_32 i := 2 ^ (32 * i) in forall f0 f1 f2 f3 g0 g1 g2 g3: Z, False. intros.
  let t := constr:(
                                   (@Associational.compact_rows (2^32) lt_1_2_32 add_get_carry (2^256)
                                   (Associational.mul
                                      (Positional.to_associational base2_32 (Tuple.from_list _ [f0;f1;f2;f3] eq_refl))
                                      (Positional.to_associational base2_32 (Tuple.from_list _ [g0;g1;g2;g3] eq_refl))))) in
  
  let t := (eval cbv -[Associational.compact_rows runtime_mul runtime_add runtime_div runtime_modulo] in t) in
  remember t eqn:Heqt.
  cbv [Associational.compact_rows] in Heqt.
  
  rewrite @Associational.compact_rows'_equation in Heqt;
  rewrite @Associational.add_and_carry_equation in Heqt;
  cbv - [runtime_mul runtime_add runtime_div runtime_modulo Associational.add_and_carry Associational.compact_rows' runtime_fst runtime_snd]  in Heqt.

  repeat match goal with
         | H : _ = Associational.compact_rows' (cons _ _) nil (cons _ _) |- _ => rewrite @Associational.compact_rows'_equation in H
         | H : _ = Associational.compact_rows' (cons _ _) (cons _ _) (cons _ _) |- _ => rewrite @Associational.compact_rows'_equation in H
         | |- _ => progress (rewrite ?@fst_pair, ?@snd_pair in * )
         | H : context [fst (@Associational.add_and_carry ?wm ?wmp ?add ?end_wt ?x ?y ?z)] |- _ => remember (@Associational.add_and_carry wm wmp add end_wt x y z)
         | H : _ = Associational.compact_rows' (Associational.compact_no_carry ?x) _ _ |- _ => remember (Associational.compact_no_carry x)
         | H : _ = Associational.compact_rows' _ (Associational.compact_no_carry ?x) _ |- _ => remember (Associational.compact_no_carry x)
                                                                                                       
         | H : ?x = Associational.add_and_carry _ _ _ |- _ =>
           repeat (
           rewrite @Associational.add_and_carry_equation in H;
             cbv -[runtime_add runtime_mul runtime_div runtime_modulo Associational.add_and_carry runtime_fst runtime_snd] in H); subst x
           | H : ?x = Associational.compact_no_carry _ |- _ =>
             cbv -[runtime_add runtime_mul runtime_div runtime_modulo runtime_fst runtime_snd] in H;
               subst x
         end.
  
  repeat match goal with H : context [runtime_fst (add_get_carry ?x ?y)] |- _ =>
                  let LHS := match type of H with ?LHS = ?RHS => LHS end in
                  let RHS := match type of H with ?LHS = ?RHS => RHS end in
                  let RHSf := match (eval pattern (add_get_carry x y) in RHS) with ?RHSf _ => RHSf end in
                  assert (LHS = (Let_In (add_get_carry x y) RHSf)) by apply H; clear H end.
  cbv [runtime_fst runtime_snd runtime_add runtime_mul] in *.
  ring_simplify_subterms_in_all.
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