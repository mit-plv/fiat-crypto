Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.

Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.

Module BaseConversion.
  Import Positional.
  Section BaseConversion.
    Context (sw dw : nat -> Z) (* source/destination weight functions *)
            {swprops : @weight_properties sw}
            {dwprops : @weight_properties dw}.

    Definition convert_bases (sn dn : nat) (p : list Z) : list Z :=
      let p' := Positional.from_associational dw dn (Positional.to_associational sw sn p) in
      chained_carries_no_reduce dw dn p' (seq 0 (pred dn)).

    Lemma eval_convert_bases sn dn p :
      (dn <> 0%nat) -> length p = sn ->
      eval dw dn (convert_bases sn dn p) = eval sw sn p.
    Proof using dwprops.
      cbv [convert_bases]; intros.
      rewrite eval_chained_carries_no_reduce by auto with zarith.
      rewrite eval_from_associational; auto with zarith.
    Qed.

    Lemma length_convert_bases sn dn p
      : length (convert_bases sn dn p) = dn.
    Proof using Type.
      cbv [convert_bases]; now repeat autorewrite with distr_length.
    Qed.
    Hint Rewrite length_convert_bases : distr_length.

    Lemma convert_bases_partitions sn dn p
          (dw_unique : forall i j : nat, (i <= dn)%nat -> (j <= dn)%nat -> dw i = dw j -> i = j)
          (p_bounded : 0 <= eval sw sn p < dw dn)
      : convert_bases sn dn p = Partition.partition dw dn (eval sw sn p).
    Proof using dwprops.
      apply list_elementwise_eq; intro i.
      destruct (lt_dec i dn); [ | now rewrite !nth_error_length_error by distr_length ].
      erewrite !(@nth_error_Some_nth_default _ _ 0) by (break_match; distr_length).
      apply f_equal.
      cbv [convert_bases Partition.partition].
      unshelve erewrite map_nth_default, nth_default_chained_carries_no_reduce_pred;
        repeat first [ progress autorewrite with distr_length push_eval
                     | rewrite eval_from_associational, eval_to_associational
                     | rewrite nth_default_seq_inbounds
                     | apply dwprops
                     | destruct dwprops; now auto with zarith ].
    Qed.

    Hint Rewrite
         @Rows.eval_from_associational
         @Associational.eval_carry
         @Associational.eval_mul
         @Positional.eval_to_associational
         Associational.eval_carryterm
         @eval_convert_bases using solve [auto with zarith] : push_eval.

    Ltac push_eval := intros; autorewrite with push_eval; auto with zarith.

    (* convert from positional in one weight to the other, then to associational *)
    Definition to_associational n m p : list (Z * Z) :=
      let p' := convert_bases n m p in
      Positional.to_associational dw m p'.

    (* TODO : move to Associational? *)
    Section reorder.
      Definition reordering_carry (w fw : Z) (p : list (Z * Z)) :=
        fold_right (fun t acc =>
                      let r := Associational.carryterm w fw t in
                      if fst t =? w then acc ++ r else r ++ acc) nil p.

      Lemma eval_reordering_carry w fw p (_:fw<>0):
        Associational.eval (reordering_carry w fw p) = Associational.eval p.
      Proof using Type.
        cbv [reordering_carry]. induction p; [reflexivity |].
        autorewrite with push_fold_right. break_match; push_eval.
      Qed.
    End reorder.
    Hint Rewrite eval_reordering_carry using solve [auto with zarith] : push_eval.

    (* carry at specified indices in dw, then use Rows.flatten to convert to Positional with sw *)
    Definition from_associational idxs n (p : list (Z * Z)) : list Z :=
      (* important not to use Positional.carry here; we don't want to accumulate yet *)
      let p' := fold_right (fun i acc => reordering_carry (dw i) (dw (S i) / dw i) acc) (Associational.bind_snd p) (rev idxs) in
      fst (Rows.flatten sw n (Rows.from_associational sw n p')).

    Lemma eval_carries p idxs :
      Associational.eval (fold_right (fun i acc => reordering_carry (dw i) (dw (S i) / dw i) acc) p idxs) =
      Associational.eval p.
    Proof using dwprops. apply fold_right_invariant; push_eval. Qed.
    Hint Rewrite eval_carries: push_eval.

    Lemma eval_to_associational n m p :
      m <> 0%nat -> length p = n ->
      Associational.eval (to_associational n m p) = Positional.eval sw n p.
    Proof using dwprops. cbv [to_associational]; push_eval. Qed.
    Hint Rewrite eval_to_associational using solve [push_eval; distr_length] : push_eval.

    Lemma eval_from_associational idxs n p :
      n <> 0%nat -> 0 <= Associational.eval p < sw n ->
      Positional.eval sw n (from_associational idxs n p) = Associational.eval p.
    Proof using dwprops swprops.
      cbv [from_associational]; intros.
      rewrite Rows.flatten_mod by eauto using Rows.length_from_associational.
      rewrite Associational.bind_snd_correct.
      push_eval.
    Qed.
    Hint Rewrite eval_from_associational using solve [push_eval; distr_length] : push_eval.

    Lemma from_associational_partitions n idxs p  (_:n<>0%nat):
      from_associational idxs n p = Partition.partition sw n (Associational.eval p).
    Proof using dwprops swprops.
      intros. cbv [from_associational].
      rewrite Rows.flatten_correct with (n:=n) by eauto using Rows.length_from_associational.
      rewrite Associational.bind_snd_correct.
      push_eval.
    Qed.

    Derive from_associational_inlined
           SuchThat (forall idxs n p,
                        from_associational_inlined idxs n p = from_associational idxs n p)
           As from_associational_inlined_correct.
    Proof.
      intros.
      cbv beta iota delta [from_associational reordering_carry Associational.carryterm].
      cbv beta iota delta [Let_In]. (* inlines all shifts/lands from carryterm *)
      cbv beta iota delta [from_associational Rows.from_associational Columns.from_associational].
      cbv beta iota delta [Let_In]. (* inlines the shifts from place *)
      subst from_associational_inlined; reflexivity.
    Qed.

    Derive to_associational_inlined
           SuchThat (forall n m p,
                        to_associational_inlined n m p = to_associational n m p)
           As to_associational_inlined_correct.
    Proof.
      intros.
      cbv beta iota delta [ to_associational convert_bases
                                             Positional.to_associational
                                             Positional.from_associational
                                             chained_carries_no_reduce
                                             carry
                                             Associational.carry
                                             Associational.carryterm
                          ].
      cbv beta iota delta [Let_In].
      subst to_associational_inlined; reflexivity.
    Qed.

    (* carry chain that aligns terms in the intermediate weight with the final weight *)
    Definition aligned_carries (log_dw_sw nout : nat)
      := (map (fun i => ((log_dw_sw * (i + 1)) - 1))%nat (seq 0 nout)).

    Section mul_converted.
      Definition mul_converted
              n1 n2 (* lengths in original format *)
              m1 m2 (* lengths in converted format *)
              (n3 : nat) (* final length *)
              (idxs : list nat) (* carries to do -- this helps preemptively line up weights *)
              (p1 p2 : list Z) :=
        let p1_a := to_associational n1 m1 p1 in
        let p2_a := to_associational n2 m2 p2 in
        let p3_a := Associational.mul p1_a p2_a in
        from_associational idxs n3 p3_a.

      Lemma eval_mul_converted n1 n2 m1 m2 n3 idxs p1 p2 (_:n3<>0%nat) (_:m1<>0%nat) (_:m2<>0%nat):
        length p1 = n1 -> length p2 = n2 ->
        0 <= (Positional.eval sw n1 p1 * Positional.eval sw n2 p2) < sw n3 ->
        Positional.eval sw n3 (mul_converted n1 n2 m1 m2 n3 idxs p1 p2) = (Positional.eval sw n1 p1) * (Positional.eval sw n2 p2).
      Proof using dwprops swprops. cbv [mul_converted]; push_eval. Qed.
      Hint Rewrite eval_mul_converted : push_eval.

      Lemma mul_converted_partitions n1 n2 m1 m2 n3 idxs p1 p2  (_:n3<>0%nat) (_:m1<>0%nat) (_:m2<>0%nat):
        length p1 = n1 -> length p2 = n2 ->
        mul_converted n1 n2 m1 m2 n3 idxs p1 p2 = Partition.partition sw n3 (Positional.eval sw n1 p1 * Positional.eval sw n2 p2).
      Proof using dwprops swprops.
        intros; cbv [mul_converted].
        rewrite from_associational_partitions by auto. push_eval.
      Qed.
    End mul_converted.
  End BaseConversion.
  Hint Rewrite length_convert_bases : distr_length.

  (* multiply two (n*k)-bit numbers by converting them to n k-bit limbs each, multiplying, then converting back *)
  Section widemul.
    Context (log2base : Z) (log2base_pos : 0 < log2base).
    Context (m n : nat) (m_nz : m <> 0%nat) (n_nz : n <> 0%nat) (n_le_log2base : Z.of_nat n <= log2base).
    Let dw : nat -> Z := weight (log2base / Z.of_nat n) 1.
    Let sw : nat -> Z := weight log2base 1.
    Let mn := (m * n)%nat.
    Let nout := (m * 2)%nat.

    Local Lemma mn_nonzero : mn <> 0%nat. Proof. subst mn. apply Nat.neq_mul_0. auto. Qed.
    Local Hint Resolve mn_nonzero : core.
    Local Lemma nout_nonzero : nout <> 0%nat.  Proof. subst nout. apply Nat.neq_mul_0. auto. Qed.
    Local Hint Resolve nout_nonzero : core.
    Local Lemma base_bounds : 0 < 1 <= log2base. Proof using log2base_pos. clear -log2base_pos; auto with zarith. Qed.
    Local Lemma dbase_bounds : 0 < 1 <= log2base / Z.of_nat n. Proof using n_nz n_le_log2base. clear -n_nz n_le_log2base; auto with zarith. Qed.
    Let dwprops : @weight_properties dw := wprops (log2base / Z.of_nat n) 1 dbase_bounds.
    Let swprops : @weight_properties sw := wprops log2base 1 base_bounds.
    Local Notation deval := (Positional.eval dw).
    Local Notation seval := (Positional.eval sw).

    Definition widemul a b := mul_converted sw dw m m mn mn nout (aligned_carries n nout) a b.

    Lemma widemul_correct a b :
      length a = m ->
      length b = m ->
      widemul a b = Partition.partition sw nout (seval m a * seval m b).
    Proof. apply mul_converted_partitions; auto with zarith. Qed.

    Derive widemul_inlined
           SuchThat (forall a b,
                        length a = m ->
                        length b = m ->
                        widemul_inlined a b = Partition.partition sw nout (seval m a * seval m b))
           As widemul_inlined_correct.
    Proof.
      intros.
      rewrite <-widemul_correct by auto.
      cbv beta iota delta [widemul mul_converted].
      rewrite <-to_associational_inlined_correct with (p:=a).
      rewrite <-to_associational_inlined_correct with (p:=b).
      rewrite <-from_associational_inlined_correct.
      subst widemul_inlined; reflexivity.
    Qed.

    Derive widemul_inlined_reverse
           SuchThat (forall a b,
                        length a = m ->
                        length b = m ->
                        widemul_inlined_reverse a b = Partition.partition sw nout (seval m a * seval m b))
           As widemul_inlined_reverse_correct.
    Proof.
      intros.
      rewrite <-widemul_inlined_correct by assumption.
      cbv [widemul_inlined].
      match goal with |- _ = from_associational_inlined sw dw ?idxs ?n ?p =>
                      transitivity (from_associational_inlined sw dw idxs n (rev p));
                        [ | transitivity (from_associational sw dw idxs n p); [ | reflexivity ] ](* reverse to make addc chains line up *)
      end.
      { subst widemul_inlined_reverse; reflexivity. }
      { rewrite from_associational_inlined_correct by auto.
        cbv [from_associational].
        rewrite !Rows.flatten_correct by eauto using Rows.length_from_associational.
        rewrite !Rows.eval_from_associational by auto.
        f_equal.
        rewrite !eval_carries, !Associational.bind_snd_correct, !Associational.eval_rev by auto.
        reflexivity. }
    Qed.
  End widemul.
End BaseConversion.
