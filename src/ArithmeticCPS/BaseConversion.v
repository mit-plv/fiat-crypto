Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Crypto.ArithmeticCPS.Core.
Require Import Crypto.ArithmeticCPS.ModOps.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.ArithmeticCPS.Saturated.
Require Import Crypto.Util.CPSUtil.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.

Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.
Import CPSBindNotations.
Local Open Scope cps_scope.

Module BaseConversion (Import RT : Runtime).
  Module Import Deps.
    Module Export Positional := Positional RT.
    Module Rows := Rows RT.
    Module Export Saturated.
      Module Associational := ArithmeticCPS.Saturated.Associational RT.
    End Saturated.
    Module Export Core.
      Module Associational := ArithmeticCPS.Core.Associational RT.
    End Core.
  End Deps.
  Section BaseConversion.
    Context (sw dw : nat -> Z) (* source/destination weight functions *).

    Definition convert_bases_cps (sn dn : nat) (p : list Z) : ~> list Z :=
      (p' <- Positional.from_associational_cps dw dn (Positional.to_associational sw sn p);
      chained_carries_no_reduce_cps dw dn p' (seq 0 (pred dn))).

    Definition to_associational_cps n m p : ~> list (Z * Z) :=
      (p' <- convert_bases_cps n m p;
         return (Positional.to_associational dw m p')).

    (* TODO : move to Associational? *)
    Section reorder.
      Definition reordering_carry_cps (w fw : Z) (p : list (Z * Z)) : ~> _ :=
        fun T => fold_right_cps2 (fun t acc =>
                      r <- Associational.carryterm_cps w fw t;
                        return (if fst t =? w then acc ++ r else r ++ acc)) nil p.
    End reorder.

    (* carry at specified indices in dw, then use Rows.flatten to convert to Positional with sw *)
    Definition from_associational_cps idxs n (p : list (Z * Z)) : ~> list Z :=
      (* important not to use Positional.carry here; we don't want to accumulate yet *)
      (p' <- Associational.bind_snd_cps p;
         p' <- (fun T => fold_right_cps2 (fun i acc => reordering_carry_cps (dw i) (dw (S i) / dw i) acc) p' (rev idxs));
         p' <- Rows.from_associational_cps sw n p';
         p' <- Rows.flatten_cps sw n p';
       return (fst p')).

(*    Derive from_associational_inlined
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
*)
    (* carry chain that aligns terms in the intermediate weight with the final weight *)
    Definition aligned_carries (log_dw_sw nout : nat)
      := (map (fun i => ((log_dw_sw * (i + 1)) - 1))%nat (seq 0 nout)).

    Section mul_converted.
  (*    Definition mul_converted
              n1 n2 (* lengths in original format *)
              m1 m2 (* lengths in converted format *)
              (n3 : nat) (* final length *)
              (idxs : list nat) (* carries to do -- this helps preemptively line up weights *)
              (p1 p2 : list Z) :=
        let p1_a := to_associational n1 m1 p1 in
        let p2_a := to_associational n2 m2 p2 in
        let p3_a := Associational.mul p1_a p2_a in
        from_associational idxs n3 p3_a.
*)
    End mul_converted.
  End BaseConversion.

  (* multiply two (n*k)-bit numbers by converting them to n k-bit limbs each, multiplying, then converting back *)
  Section widemul.
    Context (log2base : Z) (log2base_pos : 0 < log2base).
    Context (m n : nat) (m_nz : m <> 0%nat) (n_nz : n <> 0%nat) (n_le_log2base : Z.of_nat n <= log2base).
    Let dw : nat -> Z := weight (log2base / Z.of_nat n) 1.
    Let sw : nat -> Z := weight log2base 1.
    Let mn := (m * n)%nat.
    Let nout := (m * 2)%nat.

    (*Definition widemul a b := mul_converted sw dw m m mn mn nout (aligned_carries n nout) a b.*)

(*    Derive widemul_inlined
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
    Qed.*)
  End widemul.
End BaseConversion.
