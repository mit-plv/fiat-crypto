Require Import Crypto.Util.ListUtil.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Crypto.Tactics.VerdiTactics Coq.omega.Omega.

Section Conversion.
  Context {bit T : Type} {low_bits : T -> nat -> T} {high_bits : T -> nat -> T}
    (* Note : the second argument of [high_bits] is how many low bits should be removed. *)
    {high_bits_zero : forall t, high_bits t 0 = t}.

  Definition has_size t n := low_bits t n = t.

  (* concat takes low bits first, and truncates first argument at third argument number of bits *)
  Context {concat : T -> T -> nat -> T }
    {zero : T} {zero_correct : forall t, low_bits t 0 = zero}
    {concat_has_size : forall n m s t, has_size s n -> has_size t m -> has_size (concat s t n) (n + m)}
    {concat_self_high : forall n t, concat t (high_bits t n) n = t}.

  Definition decode (ws : list nat) (ts : list T) : T :=
    fold_right (fun w_t t' => let '(w,t) := w_t in concat t t' w) zero (combine ws ts).

  (* maximum bits for each digit of input and output lists *)
  Context {src : list nat} {dst : list nat}.
  Local Notation "u $ a" := (decode a u) (at level 30).
  Local Notation "u #t i" := (nth_default zero u i) (at level 30).
  Local Notation "u # i" := (nth_default 0%nat u i) (at level 30).

  Fixpoint distr_bits (caps : list nat) (inp_bits : nat) (inp : T) (acc : list T) : nat * T * list T :=
    match caps with
    | nil => (0, zero, acc)
    | c :: caps' => if Compare_dec.le_dec inp_bits c
                    then (inp_bits, inp, acc)
                    else distr_bits caps' (inp_bits - c) (high_bits inp c) (acc ++ (low_bits inp c) :: nil)
    end.

  Fixpoint convert' us i acc_bits acc out : list T :=
    match i with
    | O => out
    | S i' =>
       let j          := length us - i                   in
       let acc_cap    := dst # length out                in
       let concat_acc := (concat acc (us #t j) acc_bits) in
       if Compare_dec.lt_dec (src # j + acc_bits) acc_cap
       then (* everything fits in accumulator *)
         convert' us i' (src # j + acc_bits) concat_acc out
       else (* accumulator is full *)
         let '(acc_bits', acc', out') :=
           distr_bits
               (skipn (S (length out)) dst) (* caps *)
               (src # j - (acc_cap - acc_bits)) (* inp_bits *)
               (low_bits (us #t j) (acc_cap - acc_bits)) (* inp *)
               nil in
          convert' us i' acc_bits' acc' (out ++ (concat_acc :: out'))
    end.

  Record convert'_state := mkState
    { i : nat;
      acc_bits : nat;
      acc : T;
      out : list T }.

  Definition convert'_update us (st : convert'_state) : convert'_state :=
     match st.(i) with
     | 0 => st
     | S i' =>
         let j          := length us - st.(i)                              in
         let acc_cap    := dst # length st.(out)                           in
         let low_us     := (low_bits (us #t j) (acc_cap - st.(acc_bits)))  in
         let high_us    := (high_bits (us #t j) (acc_cap - st.(acc_bits))) in
         let concat_acc := (concat st.(acc) low_us st.(acc_bits))          in
         if Compare_dec.lt_dec (src # j + st.(acc_bits)) acc_cap
         then mkState i' (src # j + st.(acc_bits)) concat_acc st.(out)
         else let d :=
           distr_bits
             (skipn (S (length st.(out))) dst)
             (src # j - (acc_cap - st.(acc_bits)))
             high_us nil in
         mkState i' ((fst (fst d))) (snd (fst d)) (st.(out) ++ (concat_acc :: (snd d)))
     end.

  Definition sum_firstn_nat ls n := fold_right Nat.add 0 (firstn n ls).

  Definition convert'_invariant us (st : convert'_state) :=
    let out_bits := sum_firstn_nat dst (length st.(out)) in
    st.(out) $ dst = low_bits (us $ src) out_bits
    /\ st.(acc) = low_bits (high_bits (us $ src) out_bits) st.(acc_bits)
    /\ sum_firstn_nat src (length us - st.(i)) = out_bits + st.(acc_bits)
    /\ (acc_bits st) <= dst # (length st.(out))
    /\ st.(i) <= length us.

  Lemma distr_bits_step :  forall c caps' inp_bits inp acc,
    distr_bits (c :: caps') inp_bits inp acc =
      if Compare_dec.le_dec inp_bits c
      then (inp_bits, inp, acc)
      else distr_bits caps' (inp_bits - c) (high_bits inp c) (acc ++ (low_bits inp c) :: nil).
  Proof.
    reflexivity.
  Qed.

  Ltac distr_bits_cases := cbv zeta; intros;
    match goal with |- appcontext [distr_bits ?caps ?inp_bits ?inp ?acc] =>
      revert inp_bits inp acc; induction caps as [|c caps]; intros;
      [ cbv [snd distr_bits]; auto
      | rewrite distr_bits_step;
        destruct (le_dec inp_bits c);
        [ cbv [fst snd]; auto
        | ]]
    end.

  Lemma distr_bits_length_acc : forall caps inp_bits inp acc,
    let abits_acc_out := distr_bits caps inp_bits inp acc in
    length acc <= length (snd abits_acc_out).
  Proof.
    distr_bits_cases.
    etransitivity; [ | apply IHcaps ].
    distr_length.
  Qed.

  Lemma distr_bits_acc_bits : forall caps inp_bits inp acc,
    let abits_acc_out := distr_bits caps inp_bits inp acc in
    fst (fst abits_acc_out) <= caps # (length (snd abits_acc_out) - length acc).
  Proof.
    intros; subst abits_acc_out.
    revert inp_bits inp acc0; induction caps; intros.
    + cbv [fst snd distr_bits]; rewrite nth_default_nil; auto.
    + rewrite distr_bits_step.
      destruct (le_dec inp_bits a).
      - cbv [fst snd]. rewrite Nat.sub_diag, nth_default_cons; assumption.
      - etransitivity; [ apply IHcaps | ].
        distr_length.
        match goal with |- caps # (?a - (?b + 1)) <= _ # (?a - ?b) =>
          replace (a - b) with (S (a - (b + 1))) by 
            (assert (b < a) by (eapply Nat.lt_le_trans;
               [ | apply distr_bits_length_acc]; distr_length); omega) end.
        rewrite nth_default_cons_S. auto.
  Qed.

  Lemma distr_bits_inp_bits : forall caps inp_bits inp acc,
    let abits_acc_out := distr_bits caps inp_bits inp acc in
    sum_firstn_nat caps (length (snd abits_acc_out)) + fst (fst abits_acc_out) = inp_bits.
  Admitted.

  Lemma distr_bits_spec_acc_out : forall caps inp_bits inp,
    let abits_acc_out := distr_bits caps inp_bits inp nil in
    (snd abits_acc_out ++ (snd (fst abits_acc_out)) :: nil) $ caps = inp.
  Admitted.

  Lemma distr_bits_acc : forall caps inp_bits inp,
    let abits_acc_out := distr_bits caps inp_bits inp nil in
    (snd (fst abits_acc_out)) = high_bits inp (sum_firstn_nat caps (length (snd abits_acc_out))) .
  Admitted.

  Lemma distr_bits_out : forall caps inp_bits inp,
    let abits_acc_out := distr_bits caps inp_bits inp nil in
    snd abits_acc_out $ caps = low_bits inp (sum_firstn_nat caps (length (snd abits_acc_out))).
  Admitted.

  Lemma decode_app : forall xs ys a,
    (xs ++ ys) $ a = concat (xs $ a) (ys $ (skipn (length xs) a)) (sum_firstn_nat a (length xs)).
  Admitted.

  Lemma concat_low_bits_add : forall x n m,
    low_bits x (n + m) = concat (low_bits x n) (low_bits (high_bits x n) m) n.
  Admitted.

  Lemma sum_firstn_nat_split : forall xs n m,
    sum_firstn_nat xs (n + m) = sum_firstn_nat xs n + (sum_firstn_nat (skipn n xs) m).
  Admitted.

  Lemma concat_low_equiv : forall a b c n, low_bits a n = low_bits b n ->
    concat a c n = concat b c n.
  Proof.
  Admitted.

  Lemma low_low : forall x n m, 
    low_bits (low_bits x n) m = low_bits x (min n m).
  Admitted.

  Lemma high_high : forall x n m, 
    high_bits (high_bits x n) m = high_bits x (n + m).
  Admitted.

  Lemma high_low : forall x n m, 
    high_bits (low_bits x (m + n)) m = low_bits (high_bits x m) n.
  Admitted.

  Lemma low_high_low_high : forall a l1 l2 h1 h2,
    low_bits (high_bits (low_bits (high_bits a h1) l1) h2) l2 =
     high_bits (low_bits a (h1 + Init.Nat.min l1 (h2 + l2))) (h1 + h2).
  Proof.
    intros.
    rewrite <-high_low, low_low, <-high_low, high_high.
    reflexivity.
  Qed.

  Lemma sum_firstn_nat_succ : forall a n,
    sum_firstn_nat a (S n) = nth_default 0 a n + sum_firstn_nat a n.
  Admitted.

  Lemma nth_default_skipn : forall a n m,
    (skipn n a) # m = nth_default 0 a (n + m).
  Admitted.

  Lemma sum_firstn_nat_skipn_succ : forall a n m,
    sum_firstn_nat (skipn n a) (S m) =
    nth_default 0 a n + sum_firstn_nat (skipn (S n) a) m.
  Admitted.

  Lemma tl_skipn : forall {A} (ls : list A) n,
    tl (skipn n ls) = skipn (S n) ls.
  Admitted.

  Lemma concat_zero_bits : forall a b, concat a b 0 = b.
  Proof.
    intros.
    rewrite <-(concat_self_high 0 b) at 2.
    rewrite high_bits_zero; apply concat_low_equiv.
    congruence.
  Qed.

  Lemma decode_cons : forall x0 xs bs,
    (x0 :: xs) $ bs = concat x0 (xs $ tl bs) (bs # 0).
  Proof.
    cbv [decode]; intros; destruct bs; try reflexivity.
    cbv [fold_right tl combine].
    rewrite nth_default_nil, concat_zero_bits.
    reflexivity.
  Qed.

  Lemma digit_select : forall a us i,
    us #t i = low_bits (high_bits (us $ a) (sum_firstn_nat a i)) (a # i).
  Admitted.

  Ltac remember_distr_bits := try (
    let H0 := fresh "H" in
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    let H3 := fresh "H" in
    match goal with |- appcontext[distr_bits ?a ?b ?c _] =>
      remember (distr_bits a b c nil) end;
    match goal with Heq : _ = distr_bits ?a ?b ?c nil |- _ =>
      pose proof (distr_bits_inp_bits a b c nil) as H0; 
      pose proof (distr_bits_acc_bits a b c nil) as H1;
      pose proof (distr_bits_out a b c) as H2;
      pose proof (distr_bits_acc a b c) as H3;
      cbv zeta in H0, H1, H2, H3; rewrite <-Heq in H0, H1, H2, H3
    end).

  Lemma convert'_invariant_holds : forall us st,
    (forall i, has_size (us #t i) (src # i)) ->
    convert'_invariant us st ->
    convert'_invariant us (convert'_update us st).
  Proof.
    cbv [convert'_invariant convert'_update]; intros ? ? ? IHconvert'.
    destruct st.
    cbv [out acc i acc_bits] in *.
    destruct IHconvert' as [IHout [IHacc [IHi [IHacc_bits IHlength]]]].
    destruct i0; auto.
    break_if; repeat (split; try assumption; distr_length; try omega);
      remember_distr_bits.
    + rewrite digit_select with (a := src).
      rewrite low_low, Min.min_l, IHacc by omega.
      rewrite Nat.add_comm, concat_low_bits_add, high_high, IHi.
      reflexivity.
    + replace (length us - i0) with (S (length us - S i0)) by omega.
      rewrite sum_firstn_nat_succ, IHi. omega.
    + rewrite decode_app, sum_firstn_nat_split, IHout, concat_low_bits_add. f_equal.
      rewrite decode_cons, tl_skipn, sum_firstn_nat_skipn_succ, nth_default_skipn, Nat.add_0_r.
      rewrite digit_select with (a := src).
      rewrite IHi, concat_low_bits_add. f_equal.
      - rewrite low_low, Min.min_r, IHacc by omega.
        replace (dst # length out0)
          with (acc_bits0 + (dst # length out0 - acc_bits0)) at 2 by omega.
        rewrite concat_low_bits_add, high_high.
        reflexivity.
      - etransitivity; [ eassumption | ].
        rewrite digit_select with (a := src).
        rewrite IHi, high_high, low_high_low_high.
        match goal with |- appcontext [?b + ?a + (?c - ?a)] =>
          replace (b + a + (c - a)) with (b + c) by omega end.
        rewrite Min.min_r by omega.
        rewrite <-high_low.
        do 2 f_equal.
        rewrite <-!Nat.add_assoc.
        f_equal.
        omega.
  + etransitivity; [ eassumption | ].
    rewrite digit_select with (a := src).
    repeat rewrite high_high, <-high_low.
    rewrite IHi.
    rewrite sum_firstn_nat_split, sum_firstn_nat_skipn_succ.
    do 2 (f_equal; try omega).
  + rewrite sum_firstn_nat_split, sum_firstn_nat_skipn_succ.
    rewrite <-!Nat.add_assoc.
    subst p.
    rewrite distr_bits_inp_bits.
    replace (length us - i0) with (S (length us - S i0)) by omega.
    rewrite sum_firstn_nat_succ, IHi. omega.
  + etransitivity; [ eassumption | apply Nat.eq_le_incl ].
    distr_length; rewrite Nat.sub_0_r.
    rewrite nth_default_skipn.
    f_equal. omega.
  Qed.

End Conversion.