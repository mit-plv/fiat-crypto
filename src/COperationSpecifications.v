(** * C Operation Specifications *)
(** The specifications for the various operations to be synthesized. *)
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.BaseConversion.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.UniquePose.
Local Open Scope Z_scope. Local Open Scope bool_scope.

(** These Imports are only needed for the ring proof *)
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Algebra.SubsetoidRing.

Local Notation is_bounded_by0 r v
:= ((lower r%zrange <=? v) && (v <=? upper r%zrange)).
Local Notation is_bounded_by2 r v
  := (let '(v1, v2) := v in is_bounded_by0 (fst r) v1 && is_bounded_by0 (snd r) v2).
Local Notation is_bounded_by0o r
  := (match r with Some r' => fun v' => is_bounded_by0 r' v' | None => fun _ => true end).
Local Notation is_bounded_by bounds ls
  := (fold_andb_map (fun r v'' => is_bounded_by0o r v'') bounds ls).

Section list_Z_bounded.
  Definition list_Z_bounded_by
             (bounds : list (option zrange))
             (v : list Z)
    := is_bounded_by bounds v = true.

  Lemma length_list_Z_bounded_by bounds ls
    : list_Z_bounded_by bounds ls -> length ls = length bounds.
  Proof using Type.
    intro H.
    apply fold_andb_map_length in H; congruence.
  Qed.

  Lemma eval_list_Z_bounded_by wt n' bounds bounds' f
        (H : list_Z_bounded_by bounds f)
        (Hb : bounds = List.map (@Some _) bounds')
        (Hblen : length bounds' = n')
        (Hwt : forall i, List.In i (seq 0 n') -> 0 <= wt i)
    : Positional.eval wt n' (List.map lower bounds') <= Positional.eval wt n' f <= Positional.eval wt n' (List.map upper bounds').
  Proof using Type.
    setoid_rewrite in_seq in Hwt.
    subst bounds.
    pose proof H as H'; apply fold_andb_map_length in H'.
    revert dependent bounds'; intro bounds'.
    revert dependent f; intro f.
    rewrite <- (List.rev_involutive bounds'), <- (List.rev_involutive f);
      generalize (List.rev bounds') (List.rev f); clear bounds' f; intros bounds f; revert bounds f.
    induction n' as [|n IHn], bounds as [|b bounds], f as [|f fs]; intros;
      cbn [length rev map] in *; distr_length.
    { rewrite !map_app in *; cbn [map] in *.
      erewrite !Positional.eval_snoc by (distr_length; eauto).
      cbv [list_Z_bounded_by] in *.
      specialize_by (intros; auto with omega).
      specialize (Hwt n); specialize_by omega.
      repeat first [ progress Bool.split_andb
                   | rewrite Nat.add_1_r in *
                   | rewrite fold_andb_map_snoc in *
                   | rewrite Nat.succ_inj_wd in *
                   | progress Z.ltb_to_lt
                   | progress cbn [In seq] in *
                   | match goal with
                     | [ H : length _ = ?v |- _ ] => rewrite H in *
                     | [ H : ?v = length _ |- _ ] => rewrite <- H in *
                     end ].
      split; apply Z.add_le_mono; try apply IHn; auto; distr_length; nia. }
  Qed.
End list_Z_bounded.

Ltac pose_proof_length_list_Z_bounded_by :=
  repeat match goal with
         | [ H : list_Z_bounded_by _ _ |- _ ] => unique pose proof (length_list_Z_bounded_by _ _ H)
         end.

Module Primitives.
  Definition mulx_correct s
             (mulx : Z -> Z -> Z * Z)
    := forall x y,
    is_bounded_by0 r[0~>2^s-1] x = true
    -> is_bounded_by0 r[0~>2^s-1] y = true
    -> mulx x y = ((x * y) mod 2^s, (x * y) / 2^s)
       /\ is_bounded_by2 (r[0~>2^s-1], r[0~>2^s-1]) (mulx x y) = true.

  Definition addcarryx_correct s
             (addcarryx : Z -> Z -> Z -> Z * Z)
    := forall c x y,
      is_bounded_by0 r[0~>1] c = true
      -> is_bounded_by0 r[0~>2^s-1] x = true
      -> is_bounded_by0 r[0~>2^s-1] y = true
      -> addcarryx c x y = ((c + x + y) mod 2^s, (c + x + y) / 2^s)
         /\ is_bounded_by2 (r[0~>2^s-1], r[0~>1]) (addcarryx c x y) = true.

  Definition subborrowx_correct s
             (subborrowx : Z -> Z -> Z -> Z * Z)
    := forall b x y,
      is_bounded_by0 r[0~>1] b = true
      -> is_bounded_by0 r[0~>2^s-1] x = true
      -> is_bounded_by0 r[0~>2^s-1] y = true
      -> subborrowx b x y = ((-b + x + -y) mod 2^s, -((-b + x + -y) / 2^s))
         /\ is_bounded_by2 (r[0~>2^s-1], r[0~>1]) (subborrowx b x y) = true.

  Definition cmovznz_correct s
             (cmovznz : Z -> Z -> Z -> Z)
    := forall cond z nz,
      is_bounded_by0 r[0~>1] cond = true
      -> is_bounded_by0 r[0~>2^s-1] z = true
      -> is_bounded_by0 r[0~>2^s-1] nz = true
      -> cmovznz cond z nz = (if Decidable.dec (cond = 0) then z else nz)
         /\ is_bounded_by0 r[0~>2^s-1] (cmovznz cond z nz) = true.
End Primitives.

Module selectznz.
  Section __.
    Context (wt : nat -> Z)
            (n : nat)
            (saturated_bounds : list (option zrange))
            (length_saturated_bounds : length saturated_bounds = n).
    Local Notation eval := (Positional.eval wt n).

    Definition selectznz_correct
               (selectznz : Z -> list Z -> list Z -> list Z)
      := forall cond x y,
        is_bounded_by0 r[0~>1] cond = true
        -> list_Z_bounded_by saturated_bounds x
        -> list_Z_bounded_by saturated_bounds y
        -> eval (selectznz cond x y) = (if Decidable.dec (cond = 0) then eval x else eval y)
           /\ list_Z_bounded_by saturated_bounds (selectznz cond x y).
  End __.
End selectznz.


Module BaseConversion.
  Section __.
    Context (src_wt dst_wt : nat -> Z)
            (src_n dst_n : nat)
            (inbounds : list (option zrange))
            (length_inbounds : length inbounds = src_n).
    Local Notation src_eval := (Positional.eval src_wt src_n).
    Local Notation dst_eval := (Positional.eval dst_wt dst_n).

    Definition convert_bases_correct
               (convert_bases : list Z -> list Z)
      := forall x,
        list_Z_bounded_by inbounds x
        -> convert_bases x = Partition.partition dst_wt dst_n (src_eval x).
  End __.
End BaseConversion.

Module Solinas.
  (** re-export [selectznz_correct] and the primitives.  We
      semi-arbitrarily choose to allow [Solinas.selectznz_correct] to
      exist, but have the full name of the primitive operations start
      with [Primitives.] *)
  Export Primitives.
  Include selectznz.

  Section __.
    Context (wt : nat -> Z)
            (n : nat)
            (n_bytes : nat)
            (m : Z)
            (s : Z) (* only for prime_bytes *)
            (tight_bounds : list (option zrange))
            (length_tight_bounds : length tight_bounds = n)
            (loose_bounds : list (option zrange))
            (length_loose_bounds : length loose_bounds = n)
            (saturated_bounds : list (option zrange))
            (length_saturated_bounds : length saturated_bounds = n)
            (m_pos : 0 < m).
    Local Notation eval := (Positional.eval wt n).
    Local Notation bytes_eval := (Positional.eval (weight 8 1) n_bytes).

    Let prime_bytes_upperbound_list : list Z
      := Positional.encode_no_reduce (weight 8 1) n_bytes (s-1).
    Let prime_bytes_bounds : list (option zrange)
      := List.map (fun v => Some r[0 ~> v]%zrange) prime_bytes_upperbound_list.
    Let prime_bound : zrange
      := r[0~>(m - 1)]%zrange.

    Definition from_bytes_correct
               (from_bytes : list Z -> list Z)
      := forall x,
        list_Z_bounded_by prime_bytes_bounds x
        -> eval (from_bytes x) mod m = bytes_eval x mod m
           /\ list_Z_bounded_by tight_bounds (from_bytes x).

    Definition to_bytes_correct
               (to_bytes : list Z -> list Z)
      := forall x,
        list_Z_bounded_by tight_bounds x
        -> to_bytes x = Partition.partition (weight 8 1) n_bytes (eval x mod m).

    Definition carry_mul_correct
               (carry_mul : list Z -> list Z -> list Z)
      := forall x y,
        list_Z_bounded_by loose_bounds x
        -> list_Z_bounded_by loose_bounds y
        -> eval (carry_mul x y) mod m = (Z.mul (eval x) (eval y)) mod m
           /\ list_Z_bounded_by tight_bounds (carry_mul x y).

    Definition carry_square_correct
               (carry_square : list Z -> list Z)
      := forall x,
        list_Z_bounded_by loose_bounds x
        -> eval (carry_square x) mod m = (eval x * eval x) mod m
           /\ list_Z_bounded_by tight_bounds (carry_square x).

    Definition carry_scmul_const_correct
               (a : Z)
               (carry_scmul_const : list Z -> list Z)
      := forall x,
        list_Z_bounded_by loose_bounds x
        -> eval (carry_scmul_const x) mod m = (a * eval x) mod m
           /\ list_Z_bounded_by tight_bounds (carry_scmul_const x).

    Definition add_correct
               (add : list Z -> list Z -> list Z)
      := forall x y,
        list_Z_bounded_by tight_bounds x
        -> list_Z_bounded_by tight_bounds y
        -> eval (add x y) mod m = (Z.add (eval x) (eval y)) mod m
           /\ list_Z_bounded_by loose_bounds (add x y).

    Definition sub_correct
               (sub : list Z -> list Z -> list Z)
      := forall x y,
        list_Z_bounded_by tight_bounds x
        -> list_Z_bounded_by tight_bounds y
        -> eval (sub x y) mod m = (Z.sub (eval x) (eval y)) mod m
           /\ list_Z_bounded_by loose_bounds (sub x y).

    Definition opp_correct
               (opp : list Z -> list Z)
      := forall x,
        list_Z_bounded_by tight_bounds x
        -> eval (opp x) mod m = (Z.opp (eval x)) mod m
           /\ list_Z_bounded_by loose_bounds (opp x).

    Definition carry_correct
               (carry : list Z -> list Z)
      := forall x,
        list_Z_bounded_by loose_bounds x
        -> eval (carry x) mod m = (eval x) mod m
           /\ list_Z_bounded_by tight_bounds (carry x).

    Definition zero_correct
               (zero : list Z)
      := eval zero mod m = 0
         /\ list_Z_bounded_by tight_bounds zero.

    Definition one_correct
               (one : list Z)
      := eval one mod m = 1 mod m
         /\ list_Z_bounded_by tight_bounds one.

    Definition encode_correct
               (encode : Z -> list Z)
      := forall x,
        is_bounded_by0 prime_bound x = true
        -> eval (encode x) mod m = x mod m
           /\ list_Z_bounded_by tight_bounds (encode x).

    Section ring.
      Context carry_mul (Hcarry_mul : carry_mul_correct carry_mul)
              add       (Hadd       :       add_correct add)
              sub       (Hsub       :       sub_correct sub)
              opp       (Hopp       :       opp_correct opp)
              carry     (Hcarry     :     carry_correct carry)
              encode    (Hencode    :    encode_correct encode)
              zero      (Hzero      :      zero_correct zero)
              one       (Hone       :       one_correct one)
              (Hrelax : forall x, list_Z_bounded_by tight_bounds x -> list_Z_bounded_by loose_bounds x).

      Let m' := Z.to_pos m.

      Local Notation T := (list Z) (only parsing).
      Local Notation encoded_ok ls
        := (is_bounded_by tight_bounds ls = true) (only parsing).
      Local Notation encoded_okf := (fun ls => encoded_ok ls) (only parsing).

      Definition Fdecode (v : T) : F m'
        := F.of_Z m' (eval v).
      Definition T_eq (x y : T)
        := Fdecode x = Fdecode y.

      Definition encodedT := sig encoded_okf.

      Definition ring_mul (x y : T) : T := carry_mul x y.
      Definition ring_add (x y : T) : T := carry (add x y).
      Definition ring_sub (x y : T) : T := carry (sub x y).
      Definition ring_opp (x : T) : T := carry (opp x).
      Definition ring_encode (x : F m') : T := encode (F.to_Z x).

      Definition GoodT : Prop
        := @subsetoid_ring
             (list Z) encoded_okf T_eq
             zero one ring_opp ring_add ring_sub ring_mul
           /\ @is_subsetoid_homomorphism
                (F m') (fun _ => True) eq 1%F F.add F.mul
                (list Z) encoded_okf T_eq one ring_add ring_mul ring_encode
           /\ @is_subsetoid_homomorphism
                (list Z) encoded_okf T_eq one ring_add ring_mul
                (F m') (fun _ => True) eq 1%F F.add F.mul
                Fdecode.

      Hint Rewrite ->@F.to_Z_add : push_FtoZ.
      Hint Rewrite ->@F.to_Z_mul : push_FtoZ.
      Hint Rewrite ->@F.to_Z_opp : push_FtoZ.
      Hint Rewrite ->@F.to_Z_of_Z : push_FtoZ.

      Lemma Fm_bounded_alt (x : F m')
        : is_bounded_by0 prime_bound (F.to_Z x) = true.
      Proof using m_pos.
        clear -m_pos.
        destruct x as [x H]; cbn [F.to_Z proj1_sig].
        pose proof (Z.mod_pos_bound x (Z.pos m')).
        subst m'; rewrite Z2Pos.id in * by lia.
        cbv [prime_bound lower upper].
        rewrite Bool.andb_true_iff; split; Z.ltb_to_lt; lia.
      Qed.

      Lemma Good : GoodT.
      Proof.
        split_and; simpl in *.
        repeat match goal with
               | [ H : context[andb _ true] |- _ ] => setoid_rewrite andb_true_r in H
               end.
        all: cbv [carry_mul_correct add_correct sub_correct opp_correct carry_correct encode_correct zero_correct one_correct] in *; split_and.
        eapply subsetoid_ring_by_ring_isomorphism;
          cbv [ring_opp ring_add ring_sub ring_mul ring_encode F.sub list_Z_bounded_by Fdecode m' F.one] in *; auto.
        all: repeat first [ progress intros
                          | reflexivity
                          | progress autorewrite with push_FtoZ
                          | rewrite Z2Pos.id
                          | apply Fm_bounded_alt
                          | match goal with
                            | [ |- _ = _ :> F _ ] => apply F.eq_to_Z_iff
                            | [ |- _ mod _ = F.to_Z ?x ]
                              => etransitivity; [ | apply (F.mod_to_Z x) ]
                            | [ H : _ |- _ ] => apply H; clear H
                            | [ H : context[eval (?f _) mod ?m = _] |- context[eval (?f _) mod ?m] ]
                              => rewrite H
                            | [ H : context[eval (?f _ _) mod ?m = _] |- context[eval (?f _ _) mod ?m] ]
                              => rewrite H
                            end
                          | progress (push_Zmod; pull_Zmod); try (f_equal; lia) ].
      Qed.
    End ring.
  End __.
End Solinas.

Module SaturatedSolinas.
  Section __.
    Context (wt : nat -> Z)
            (n : nat)
            (m : Z)
            (saturated_bounds : list (option zrange))
            (length_saturated_bounds : length saturated_bounds = n).
    Local Notation eval := (Positional.eval wt n).

    Definition mul_correct
               (mul : list Z -> list Z -> list Z * Z)
      := forall x y,
        list_Z_bounded_by saturated_bounds x
        -> list_Z_bounded_by saturated_bounds y
        -> (eval (fst (mul x y)) + wt n * snd (mul x y)) mod m
           = (eval x * eval y) mod m
           /\ ((let '(v, c) := mul x y in
                (is_bounded_by saturated_bounds v)
                  && true(*Should be: is_bounded_by0 r[0~>0] c, but bounds analysis is not good enough*))
               = true).
  End __.
End SaturatedSolinas.

Module WordByWordMontgomery.
  Import Arithmetic.WordByWordMontgomery.
  Local Coercion Z.of_nat : nat >-> Z.
  Section __.
    Context (bitwidth : Z)
            (n : nat)
            (n_bytes : nat)
            (m r' : Z)
            (s : Z) (* only for prime_bytes *)
            (bounds : list (option zrange))
            (length_bounds : length bounds = n)
            (valid : list Z -> Prop)
            (bytes_valid : list Z -> Prop)
            (m_pos : 0 < m)
            (from_montgomery : list Z -> list Z)
            (* saturated_bounds is only for selectznz *)
            (saturated_bounds : list (option zrange))
            (length_saturated_bounds : length saturated_bounds = n).
    Local Notation eval := (@WordByWordMontgomery.eval bitwidth n).
    Local Notation bytes_eval := (Positional.eval (weight 8 1) n_bytes).
    Let prime_bound : zrange
      := r[0~>(m - 1)]%zrange.

    Definition from_montgomery_correct
      := forall v,
        valid v
        -> eval (from_montgomery v) mod m = (eval v * r'^n) mod m
           /\ valid (from_montgomery v).

    Definition mul_correct
               (mul : list Z -> list Z -> list Z)
      := forall a b,
        valid a
        -> valid b
        -> eval (from_montgomery (mul a b)) mod m = (Z.mul (eval (from_montgomery a)) (eval (from_montgomery b))) mod m
           /\ valid (mul a b).

    Definition add_correct
               (add : list Z -> list Z -> list Z)
      := forall a b,
        valid a
        -> valid b
        -> eval (from_montgomery (add a b)) mod m = (Z.add (eval (from_montgomery a)) (eval (from_montgomery b))) mod m
           /\ valid (add a b).

    Definition sub_correct
               (sub : list Z -> list Z -> list Z)
      := forall a b,
        valid a
        -> valid b
        -> eval (from_montgomery (sub a b)) mod m = (Z.sub (eval (from_montgomery a)) (eval (from_montgomery b))) mod m
           /\ valid (sub a b).

    Definition opp_correct
               (opp : list Z -> list Z)
      := forall a,
        valid a
        -> eval (from_montgomery (opp a)) mod m = (Z.opp (eval (from_montgomery a))) mod m
           /\ valid (opp a).

    Definition square_correct
               (square : list Z -> list Z)
      := forall a,
        valid a
        -> eval (from_montgomery (square a)) mod m = (eval (from_montgomery a) * eval (from_montgomery a)) mod m
           /\ valid (square a).

    Definition zero_correct
               (zero : list Z)
      := eval (from_montgomery zero) mod m = 0
         /\ valid zero.

    Definition one_correct
               (one : list Z)
      := eval (from_montgomery one) mod m = 1 mod m
         /\ valid one.

    Definition encode_correct
               (encode : Z -> list Z)
      := forall x,
        is_bounded_by0 prime_bound x = true
        -> eval (from_montgomery (encode x)) mod m = x mod m
           /\ valid (encode x).

    Definition nonzero_correct
               (nonzero : list Z -> Z)
      := forall x,
        valid x
        -> (nonzero x = 0) <-> (eval (from_montgomery x) mod m = 0).

    Definition to_bytes_correct
               (to_bytes : list Z -> list Z)
      := forall x,
        valid x
        -> to_bytes x = Partition.partition (weight 8 1) n_bytes (eval x mod m).

    Definition from_bytes_correct
               (from_bytes : list Z -> list Z)
      := forall x,
        bytes_valid x
        -> eval (from_bytes x) mod m = bytes_eval x mod m
           /\ valid (from_bytes x).

    Definition selectznz_correct
               (selectznz : Z -> list Z -> list Z -> list Z)
      : Prop
      := selectznz.selectznz_correct
           (UniformWeight.uweight bitwidth)
           n
           saturated_bounds
           selectznz.

    Section ring.
      Context mul     (Hmul     :     mul_correct mul)
              add     (Hadd     :     add_correct add)
              sub     (Hsub     :     sub_correct sub)
              opp     (Hopp     :     opp_correct opp)
              encode  (Hencode  :  encode_correct encode)
              zero    (Hzero    :    zero_correct zero)
              one     (Hone     :     one_correct one).

      Let m' := Z.to_pos m.

      Local Notation T := (list Z) (only parsing).
      Local Notation encoded_ok ls
        := (valid ls) (only parsing).
      Local Notation encoded_okf := (fun ls => encoded_ok ls) (only parsing).

      Definition Fdecode (v : T) : F m'
        := F.of_Z m' (eval (from_montgomery v)).
      Definition T_eq (x y : T)
        := Fdecode x = Fdecode y.

      Definition encodedT := sig encoded_okf.

      Definition ring_mul (x y : T) : T := mul x y.
      Definition ring_add (x y : T) : T := add x y.
      Definition ring_sub (x y : T) : T := sub x y.
      Definition ring_opp (x : T) : T := opp x.
      Definition ring_encode (x : F m') : T := encode (F.to_Z x).

      Definition GoodT : Prop
        := @subsetoid_ring
             (list Z) encoded_okf T_eq
             zero one ring_opp ring_add ring_sub ring_mul
           /\ @is_subsetoid_homomorphism
                (F m') (fun _ => True) eq 1%F F.add F.mul
                (list Z) encoded_okf T_eq one ring_add ring_mul ring_encode
           /\ @is_subsetoid_homomorphism
                (list Z) encoded_okf T_eq one ring_add ring_mul
                (F m') (fun _ => True) eq 1%F F.add F.mul
                Fdecode.

      Hint Rewrite ->@F.to_Z_add : push_FtoZ.
      Hint Rewrite ->@F.to_Z_mul : push_FtoZ.
      Hint Rewrite ->@F.to_Z_opp : push_FtoZ.
      Hint Rewrite ->@F.to_Z_of_Z : push_FtoZ.

      Lemma Fm_bounded_alt (x : F m')
        : is_bounded_by0 prime_bound (F.to_Z x) = true.
      Proof using m_pos.
        clear -m_pos.
        destruct x as [x H]; cbn [F.to_Z proj1_sig].
        pose proof (Z.mod_pos_bound x (Z.pos m')).
        subst m'; rewrite Z2Pos.id in * by lia.
        cbv [prime_bound lower upper].
        rewrite Bool.andb_true_iff; split; Z.ltb_to_lt; lia.
      Qed.

      Lemma Good : GoodT.
      Proof.
        split_and; simpl in *.
        repeat match goal with
               | [ H : context[andb _ true] |- _ ] => setoid_rewrite andb_true_r in H
               end.
        all: cbv [mul_correct add_correct sub_correct opp_correct encode_correct zero_correct one_correct] in *; split_and.
        eapply subsetoid_ring_by_ring_isomorphism;
          cbv [ring_opp ring_add ring_sub ring_mul ring_encode F.sub list_Z_bounded_by Fdecode m' F.one] in *; auto.
        all: repeat first [ progress intros
                          | reflexivity
                          | progress autorewrite with push_FtoZ
                          | rewrite Z2Pos.id
                          | apply Fm_bounded_alt
                          | match goal with
                            | [ |- _ = _ :> F _ ] => apply F.eq_to_Z_iff
                            | [ |- _ mod _ = F.to_Z ?x ]
                              => etransitivity; [ | apply (F.mod_to_Z x) ]
                            | [ H : _ |- _ ] => apply H; clear H
                            | [ H : context[eval (?f _) mod ?m = _] |- context[eval (?f _) mod ?m] ]
                              => rewrite H
                            | [ H : context[eval (?f _ _) mod ?m = _] |- context[eval (?f _ _) mod ?m] ]
                              => rewrite H
                            end
                          | progress (push_Zmod; pull_Zmod); try (f_equal; lia) ].
      Qed.
    End ring.
  End __.
End WordByWordMontgomery.

Module BarrettReduction.
  Section __.
    Context (k M : Z).

    Definition barrett_red_correct
               (barrett_red : Z -> Z -> Z)
      := forall xLow xHigh,
        0 <= xLow < 2 ^ k
        -> 0 <= xHigh < M
        -> barrett_red xLow xHigh = (xLow + 2 ^ k * xHigh) mod M.
  End __.
End BarrettReduction.

Module MontgomeryReduction.
  Section __.
    Context (N R R' : Z).

    Definition montred_correct
               (mont_red : Z -> Z -> Z)
      := forall lo hi,
        0 <= lo < R
        -> 0 <= hi < R
        -> 0 <= lo + R * hi < R * N
        -> mont_red lo hi = ((lo + R * hi) * R') mod N.
  End __.
End MontgomeryReduction.
