Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.Definitions.

Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.

Module BaseConversion.
  Import Positional.
  Section BaseConversion.
    Context (sw dw : nat -> Z) (* source/destination weight functions *)
            {swprops : @weight_properties sw}
            {dwprops : @weight_properties dw}.

    Definition convert_bases (sn dn : nat) (p : list Z) : list Z :=
      let p_assoc := Positional.to_associational sw sn p in
      let p_cols := Columns.from_associational dw dn p_assoc in
      (* reverse is not needed for correctness, but this way has better
         performance because we add the small numbers first *)
      let p_cols := Columns.reverse p_cols in
      let p_flattened := Columns.flatten dw Z.add_split p_cols in
      let r := fst p_flattened in
      let carry := (snd p_flattened * (dw dn / dw (pred dn))) in
      let r := add_to_nth (pred dn) carry r in
      r.

    Hint Rewrite @Columns.length_from_associational
         @Columns.length_flatten @Columns.length_reverse
      : distr_length.
    Hint Rewrite @Columns.eval_from_associational
         @Columns.eval_reverse @Positional.eval_to_associational
         using (auto; solve [distr_length])
      : push_eval.

    Lemma eval_convert_bases sn dn p :
      (dn <> 0%nat) -> length p = sn ->
      eval dw dn (convert_bases sn dn p) = eval sw sn p.
    Proof using dwprops.
      cbv [convert_bases]; intros.
      rewrite eval_add_to_nth by distr_length.
      rewrite Columns.flatten_mod by (auto; distr_length).
      erewrite Columns.flatten_div by (auto; distr_length).
      distr_length.
      autorewrite with push_eval.
      match goal with
      | |- context [?a * (?b * (?c / ?a))] =>
        replace (a * (b * (c / a))) with (a * (c / a) * b) by Lia.lia
      end.
      rewrite <-Weight.weight_div_mod by (auto; Lia.lia).
      pose proof (weight_positive dwprops dn).
      rewrite <-Z.div_mod; auto; Lia.lia.
    Qed.

    Lemma length_convert_bases sn dn p
      : length (convert_bases sn dn p) = dn.
    Proof using Type.
      cbv [convert_bases]; now repeat autorewrite with distr_length.
    Qed.
    Hint Rewrite length_convert_bases : distr_length.

    Lemma convert_bases_partitions sn dn p
          (dw_unique : forall i j : nat, (i <= dn)%nat -> (j <= dn)%nat -> dw i = dw j -> i = j)
          (dn_pos : dn <> 0%nat)
          (p_bounded : 0 <= eval sw sn p < dw dn)
      : convert_bases sn dn p = Partition.partition dw dn (eval sw sn p).
    Proof using dwprops.
      cbv [convert_bases].
      erewrite Columns.flatten_div by (auto; distr_length).
      distr_length.
      erewrite Columns.flatten_correct by (auto; distr_length).
      distr_length.
      autorewrite with push_eval.
      rewrite Z.div_small by Lia.lia.
      autorewrite with zsimplify_fast.
      rewrite add_to_nth_zero. reflexivity.
    Qed.

    Hint Rewrite
         @Rows.eval_from_associational
         @Associational.eval_carry
         @Associational.eval_mul
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
      cbv beta iota delta [ to_associational convert_bases ].
      cbv beta iota delta [ Columns.from_associational ].
      cbv beta iota delta [Let_In]. (* inlines dlets from Columns.from_associaitonal  *)
      cbv beta iota delta [ Columns.flatten Columns.flatten_step
                                            Columns.flatten_column ].
      cbv beta iota delta [Let_In]. (* inlines dlets from Columns.flatten  *)
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

Section base_conversion_mod_ops.
  Import Positional.
  Import BaseConversion.
  Local Coercion Z.of_nat : nat >-> Z.
  (* Design constraints:
     - inputs must be [Z] (b/c reification does not support Q)
     - internal structure must not match on the arguments (b/c reification does not support [positive]) *)
  Context (src_limbwidth_num src_limbwidth_den : Z)
          (src_limbwidth_good : 0 < src_limbwidth_den <= src_limbwidth_num)
          (dst_limbwidth_num dst_limbwidth_den : Z)
          (dst_limbwidth_good : 0 < dst_limbwidth_den <= dst_limbwidth_num)
          (src_n : nat)
          (dst_n : nat)
          (bitwidth : Z)
          (Hsrc_n_nz : src_n <> 0%nat)
          (Hdst_n_nz : dst_n <> 0%nat).
  Local Notation src_weight := (@weight src_limbwidth_num src_limbwidth_den).
  Local Notation dst_weight := (@weight dst_limbwidth_num dst_limbwidth_den).

  Local Notation src_wprops := (@wprops src_limbwidth_num src_limbwidth_den src_limbwidth_good).
  Local Notation dst_wprops := (@wprops dst_limbwidth_num dst_limbwidth_den dst_limbwidth_good).

  Local Notation src_wunique := (@weight_unique src_limbwidth_num src_limbwidth_den src_limbwidth_good).
  Local Notation dst_wunique := (@weight_unique dst_limbwidth_num dst_limbwidth_den dst_limbwidth_good).

  Local Hint Immediate (src_wprops) : core.
  Local Hint Immediate (src_wunique) : core.
  Local Hint Immediate (weight_0 src_wprops) : core.
  Local Hint Immediate (weight_positive src_wprops) : core.
  Local Hint Immediate (weight_multiples src_wprops) : core.
  Local Hint Immediate (weight_divides src_wprops) : core.
  Local Hint Immediate (dst_wprops) : core.
  Local Hint Immediate (dst_wunique) : core.
  Local Hint Immediate (weight_0 dst_wprops) : core.
  Local Hint Immediate (weight_positive dst_wprops) : core.
  Local Hint Immediate (weight_multiples dst_wprops) : core.
  Local Hint Immediate (weight_divides dst_wprops) : core.

  Definition convert_bases (v : list Z)
    := BaseConversion.convert_bases src_weight dst_weight src_n dst_n v.

  Definition convert_basesmod (f : list Z) : list Z
    := convert_bases f.

  Lemma eval_convert_bases
    : forall (f : list Z)
        (Hf : length f = src_n),
      eval dst_weight dst_n (convert_bases f) = eval src_weight src_n f.
  Proof using Hdst_n_nz src_limbwidth_good dst_limbwidth_good.
    generalize src_wprops dst_wprops; clear -Hdst_n_nz.
    intros.
    cbv [convert_bases].
    rewrite BaseConversion.eval_convert_bases by auto.
    reflexivity.
  Qed.

  Lemma convert_bases_partitions
    : forall (f : list Z)
             (Hf_small : 0 <= eval src_weight src_n f < dst_weight dst_n),
      convert_bases f = Partition.partition dst_weight dst_n (Positional.eval src_weight src_n f).
  Proof using dst_limbwidth_good Hdst_n_nz.
    clear -dst_limbwidth_good Hdst_n_nz.
    intros; cbv [convert_bases].
    apply BaseConversion.convert_bases_partitions; eauto.
  Qed.

  Lemma eval_convert_basesmod
    : forall (f : list Z)
             (Hf : length f = src_n),
      eval dst_weight dst_n (convert_basesmod f) = eval src_weight src_n f.
  Proof using Hdst_n_nz src_limbwidth_good dst_limbwidth_good. apply eval_convert_bases. Qed.

  Lemma convert_basesmod_partitions
    : forall (f : list Z)
             (Hf_small : 0 <= eval src_weight src_n f < dst_weight dst_n),
      convert_basesmod f = Partition.partition dst_weight dst_n (Positional.eval src_weight src_n f).
  Proof using dst_limbwidth_good Hdst_n_nz. apply convert_bases_partitions. Qed.

  Lemma eval_convert_basesmod_and_partitions
    : forall (f : list Z)
             (Hf : length f = src_n)
             (Hf_small : 0 <= eval src_weight src_n f < dst_weight dst_n),
      eval dst_weight dst_n (convert_basesmod f) = eval src_weight src_n f
      /\ convert_basesmod f = Partition.partition dst_weight dst_n (Positional.eval src_weight src_n f).
  Proof using src_limbwidth_good dst_limbwidth_good Hdst_n_nz.
    now (split; [ apply eval_convert_basesmod | apply convert_bases_partitions ]).
  Qed.
End base_conversion_mod_ops.
Hint Rewrite eval_convert_basesmod eval_convert_bases : push_eval.
