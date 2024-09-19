From Coq Require Import List.
From Coq Require Import Lia.
From Coq Require Import ZArith.
From Coq Require Import QArith_base Qround.
From Coq Require Import Qabs.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ListUtil.FoldBool.
Require Crypto.TAPSort.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope bool_scope.

Import Associational Positional.

Section encode_distributed.
  Context weight
          (n : nat)
          (s : Z)
          (c : list (Z * Z))
          {wprops : @weight_properties weight}.

  Local Notation eval := (eval weight) (only parsing).

  (** Sometimes we want to ensure that each limb of our encoded
        number [x] is larger than the corresponding limb of a given
        bound [minvalues].  We can ensure this by encoding [x -
        minvalues] in a way that ensures each limb is non-negative,
        and then adding back [minvalues].  We extend [minvalues] with
        zeros for convenience, so we don't need a proof that [length
        minvalues = n] for the proofs about [encode_distributed]. *)
  Definition encode_distributed (minvalues : list Z) (x : Z) : list Z
    := let minvalues := List.firstn n (minvalues ++ List.repeat 0 n) in
       (add weight n)
         (Partition.partition weight n ((x - Positional.eval weight n minvalues) mod (s - Associational.eval c)))
         minvalues.

  Lemma eval_encode_distributed minvalues x
    : 0 < s - Associational.eval c <= weight n
      -> eval n (encode_distributed minvalues x) mod (s - Associational.eval c)
         = x mod (s - Associational.eval c).
  Proof using wprops.
    intros; cbv [encode_distributed]; rewrite eval_add, Partition.eval_partition by (auto; distr_length).
    assert (forall x, x mod (s - Associational.eval c) < s - Associational.eval c) by auto with zarith.
    rewrite (Z.mod_small (_ mod (s - _)) (weight _)) by now eauto using Z.lt_le_trans with zarith.
    pull_Zmod; now autorewrite with zsimplify_fast.
  Qed.
  Hint Rewrite eval_encode_distributed : push_eval.
  Lemma length_encode_distributed minvalues x
    : length (encode_distributed minvalues x) = n.
  Proof using Type. cbv [encode_distributed]; repeat distr_length. Qed.
  Hint Rewrite length_encode_distributed : distr_length.
  Lemma nth_default_encode_distributed_bounded_eq'
        (** We add an extra hypothesis that is too bulky to prove *)
        (Hadd : forall x y, length x = n -> length y = n -> add weight n x y = List.map2 Z.add x y)
        minvalues x i d
    : nth_default d (encode_distributed minvalues x) i
      = if Decidable.dec (i < n)%nat
        then (((x - Positional.eval weight n (firstn n (minvalues ++ repeat 0 n)))
                 mod (s - Associational.eval c)) mod weight (S i))
               / weight i
             + nth_default 0 minvalues i
        else d.
  Proof using wprops.
    cbv [encode_distributed].
    rewrite Hadd by repeat distr_length.
    rewrite nth_default_map2 with (d1:=0) (d2:=0);
      autorewrite with push_nth_default distr_length.
    autorewrite with natsimplify.
    break_innermost_match; try lia.
    now rewrite nth_default_out_of_bounds by lia.
  Qed.
  Lemma nth_default_encode_distributed_bounded'
        (** We add an extra hypothesis that is too bulky to prove *)
        (Hadd : forall x y, length x = n -> length y = n -> add weight n x y = List.map2 Z.add x y)
        minvalues x i d' d
        (Hmin : (i < length minvalues)%nat)
        (Hn : (i < n)%nat)
    : nth_default d' minvalues i <= nth_default d (encode_distributed minvalues x) i.
  Proof using wprops.
    rewrite (nth_default_in_bounds 0 d) by repeat distr_length.
    rewrite (nth_default_in_bounds 0 d') by lia.
    rewrite nth_default_encode_distributed_bounded_eq' by auto.
    break_innermost_match; try lia.
    match goal with |- ?x <= ?y + ?x => cut (0 <= y); [ lia | ] end.
    auto with zarith.
  Qed.
  (** We would like to prove this general lemma, but since we're using
      [Positional.add] rather than [List.map2 Z.add], it's kind-of
      annoying to prove, so we skip it. *)
  Lemma nth_default_encode_distributed_bounded
        minvalues x i d' d
        (Hmin : (i < length minvalues)%nat)
        (Hn : (i < n)%nat)
    : nth_default d' minvalues i <= nth_default d (encode_distributed minvalues x) i.
  Proof using wprops.
    apply nth_default_encode_distributed_bounded'; auto.
  Abort.
End encode_distributed.
#[global]
Hint Rewrite @eval_encode_distributed using solve [auto; lia] : push_eval.
#[global]
Hint Rewrite @length_encode_distributed : distr_length.

Notation limbwidth n s c := (inject_Z (Z.log2_up (s - Associational.eval c)) / inject_Z (Z.of_nat n))%Q.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

(** The fraction by which to multiply upper bounds *)
Class tight_upperbound_fraction_opt := tight_upperbound_fraction : Q.
#[global]
Typeclasses Opaque tight_upperbound_fraction_opt.

Local Notation is_tighter_than0 x y
  := ((lower y <=? lower x) && (upper x <=? upper y)).
Local Notation is_tighter_than0oo r1 r2
  := (match r1, r2 with _, None => true | None, Some _ => false | Some r1', Some r2' => is_tighter_than0 r1' r2' end).
Local Notation is_tighter_than ls1 ls2
  := (fold_andb_map (fun x y => is_tighter_than0oo x y) ls1 ls2).

Section __.
  Context {tight_upperbound_fraction : tight_upperbound_fraction_opt}
          (n : nat)
          (s : Z)
          (c : list (Z * Z))
          (machine_wordsize : Z).
  Let limbwidth := (limbwidth n s c).
  Local Notation weight := (weight (Qnum limbwidth) (Qden limbwidth)).
  Context (Hn_nz : n <> 0%nat)
          (Hs_n : Z.of_nat n <= Z.log2_up (s - Associational.eval c))
          (Hs_nz : s <> 0)
          (Hs_c_nz : s - Associational.eval c <> 0)
          (Hs_c_bounded : 0 < s - Associational.eval c <= weight n).

  Lemma limbwidth_good : 0 < Qden limbwidth <= Qnum limbwidth.
  Proof using Hn_nz Hs_n.
    clear -Hn_nz Hs_n.
    cbv [limbwidth Qnum Qden Qdiv inject_Z Qmult Qinv].
    destruct n; cbn [Z.of_nat]; lia.
  Qed.
  Let wprops := wprops _ _ limbwidth_good.
  Local Hint Resolve wprops : core.
  (** Translating from https://github.com/mit-plv/fiat-crypto/blob/c60b1d2556a72c37f4bc7444204e9ddc0791ce4f/src/Specific/solinas64_2e448m2e224m1_8limbs/CurveParameters.v#L11-L35
<<
if len(p) > 2:
    # do interleaved carry chains, starting at where the taps are
    starts = [(int(t[1] / (num_bits(p) / sz)) - 1) % sz for t in p[1:]]
    chain2 = []
    for n in range(1,sz):
        for j in starts:
            chain2.append((j + n) % sz)
    chain2 = remove_duplicates(chain2)
    chain3 = list(map(lambda x:(x+1)%sz,starts))
    carry_chains = [starts,chain2,chain3]
else:
    carry_chains = "default"
>> *)
  (* p is [(value, weight)]; c is [(weight, value)] *)
  Let p := [(s / 2^Z.log2 s, Z.log2 s)] ++ TAPSort.sort (List.map (fun '(w, v) => (-v, Z.log2 w)) c).
  Definition carry_chains : list nat
    := if (2 <? List.length p)%nat
       then (* do interleaved carry chains, starting at where the taps are *)
         let starts := List.map (fun '((v, w) : Z * Z) => (Qfloor (w / limbwidth) - 1) mod n) (tl p) in
         let chain2 := flat_map
                         (fun n' : nat
                          => List.map (fun j => (j + n') mod n) starts)
                         (List.seq 1 (pred n)) in
         let chain2 := remove_duplicates Z.eqb chain2 in
         let chain3 := List.map (fun x => (x + 1) mod n) starts in
         List.map Z.to_nat (starts ++ chain2 ++ chain3)
       else (List.seq 0 n ++ [0; 1])%list%nat.

  Definition default_tight_upperbound_fraction : Q := 1%Q.
  Definition coef := 2. (* for balance in sub *)
  Definition prime_upperbound_list : list Z
    := Partition.partition weight n (2 ^ Z.log2_up (s - Associational.eval c) - 1).
  (** We take the absolute value mostly to make proofs easy *)
  Definition tight_upperbounds : list Z
    := List.map
         (fun v : Z => Qceiling (Qabs (tight_upperbound_fraction * (v+1))))
         prime_upperbound_list.

  (** We compute loose bounds based on how much headspace we have in
      each limb, and treat separately the maximum number of additions
      and subtractions that we guarantee *)
  (** Allow enough space to do two additions in a row w/o carrying *)
  Definition headspace_add_count : nat := 2.
  (** Allow enough space to do one subtraction w/o carrying *)
  Definition headspace_sub_count : nat := 1.

  (** readjust such that forall i, minvalues[i] <= B[i]
      Algorithm:
        B = encode (s - c)
        B = map(Z.mul coef, B)
        for i from 0 .. nlimbs-2:
            if B[i] < tight_upperbounds[i]:
               // need to find the lowest number we can add, confined to highest bits only
               d = tight_upperbounds[i] - B[i]
               x = d / fw[i]
               if d mod fw[i] != 0:
                  x += 1 // round up
               B[i] += x * fw[i]
               B[i+1] -= x
   *)
  Definition distribute_balance_step (minvalues : list Z) (i : nat) (B : list Z) :=
    let Bi := nth_default 0 B i in
    let Mi := nth_default 0 minvalues i in
    if (Bi <? Mi)
    then
      let fw := weight (S i) / weight i in
      let x := ((Mi - Bi) / fw) + Z.b2z (negb ((Mi - Bi) mod fw =? 0)) in
      let zero := [(weight i, x * fw); (weight (S i), -x)] in
      let Ba := to_associational weight n B ++ zero in
      let B := from_associational weight n Ba in
      B
    else B.

  Definition distribute_balance minvalues B :=
    fold_right (distribute_balance_step minvalues) B (rev (seq 0 (n-1))).

  Definition balance : list Z
    := let B := encode weight n s c (s - Associational.eval c) in
       let B := scmul weight n coef B in
       distribute_balance tight_upperbounds B.

  Definition loose_upperbounds : list Z
    := List.map
         (fun '(v, bal) => v + Z.max (headspace_add_count * v)
                                     (headspace_sub_count * bal))
         (List.combine tight_upperbounds balance).

  Definition tight_bounds : list (option zrange)
    := List.map (fun u => Some r[0~>u]%zrange) tight_upperbounds.
  Definition loose_bounds : list (option zrange)
    := List.map (fun u => Some r[0~>u]%zrange) loose_upperbounds.

  Lemma length_distribute_balance_step minvalues i B
    : List.length B = n ->
      List.length (distribute_balance_step minvalues i B) = n.
  Proof using Type.
    clear; cbv [distribute_balance_step]; break_innermost_match; now autorewrite with distr_length.
  Qed.
  Hint Rewrite length_distribute_balance_step : distr_length.

  Lemma length_distribute_balance minvalues B
    : List.length B = n ->
      List.length (distribute_balance minvalues B) = n.
  Proof using Type.
    clear -limbwidth p; cbv [distribute_balance]; intros.
    apply fold_right_invariant; intros; auto; now autorewrite with distr_length.
  Qed.
  Hint Rewrite length_distribute_balance : distr_length.

  Lemma length_balance : List.length balance = n.
  Proof using Type. cbv [balance]; now repeat autorewrite with distr_length. Qed.
  Hint Rewrite length_balance : distr_length.

  Lemma length_prime_upperbound_list : List.length prime_upperbound_list = n.
  Proof using Type. cbv [prime_upperbound_list]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_prime_upperbound_list : distr_length.

  Lemma length_tight_upperbounds : List.length tight_upperbounds = n.
  Proof using Type. cbv [tight_upperbounds]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_tight_upperbounds : distr_length.

  Lemma length_loose_upperbounds : List.length loose_upperbounds = n.
  Proof using Type. cbv [loose_upperbounds]; now autorewrite with distr_length natsimplify. Qed.
  Hint Rewrite length_loose_upperbounds : distr_length.

  Lemma length_tight_bounds : List.length tight_bounds = n.
  Proof using Type. cbv [tight_bounds]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_tight_bounds : distr_length.
  Lemma length_loose_bounds : List.length loose_bounds = n.
  Proof using Type. generalize length_loose_upperbounds; clear; cbv [loose_bounds]; autorewrite with distr_length natsimplify; lia. Qed.
  Hint Rewrite length_loose_bounds : distr_length.

  Lemma tight_bounds_tighter : is_tighter_than tight_bounds loose_bounds = true.
  Proof using Type.
    cbv [tight_bounds loose_bounds tight_upperbounds loose_upperbounds].
    rewrite !combine_map_l, !fold_andb_map_map, !fold_andb_map_map1, fold_andb_map_iff.
    cbn [lower upper].
    autorewrite with distr_length natsimplify.
    split; [ reflexivity | ].
    intro; rewrite In_nth_error_iff; intros [n' H].
    rewrite !nth_error_combine in H.
    break_innermost_match_hyps; inversion_option; subst; cbn [fst snd].
    rewrite !Bool.andb_true_iff; split; [ reflexivity | Z.ltb_to_lt ].
    let x := lazymatch goal with |- ?x <= _ => x end in
    rewrite <- (Z.add_0_r x) at 1; apply Zplus_le_compat_l.
    etransitivity; [ | apply Z.le_max_l ].
    cbv [Qceiling Qmult Qfloor Qnum Qden Qopp inject_Z Qabs]; case tight_upperbound_fraction; intros; clear.
    Z.div_mod_to_quot_rem; nia.
  Qed.

  Lemma eval_distribute_balance_step minvalues i x :
    eval weight n (distribute_balance_step minvalues i x)
    = eval weight n x.
  Proof using Hs_nz Hs_c_nz Hs_n Hn_nz.
    clear -Hs_nz Hs_c_nz Hs_n Hn_nz wprops.
    cbv [distribute_balance_step].
    break_innermost_match; [ | lia ].
    rewrite eval_from_associational by auto with zarith.
    autorewrite with push_eval. cbn [fst snd].
    rewrite eval_to_associational by auto.
    ring_simplify.
    do 2 match goal with
         | |- context [?a * ?b * (?c / ?a)] =>
           replace (a * b * (c / a)) with (a * (c / a) * b) by lia;
             rewrite (Z.mul_div_eq_full c a) by auto with zarith
         end.
    rewrite weight_multiples by auto. lia.
  Qed.

  Lemma eval_distribute_balance minvalues x :
    eval weight n (distribute_balance minvalues x)
    = eval weight n x.
  Proof using Hs_nz Hs_c_nz Hs_n Hn_nz.
    clear -p Hs_nz Hs_c_nz Hs_n Hn_nz wprops.
    cbv [distribute_balance].
    apply fold_right_invariant; [ reflexivity | ].
    intros; rewrite eval_distribute_balance_step; auto.
  Qed.

  Lemma eval_balance : eval weight n balance mod (s - Associational.eval c) = 0.
  Proof using Hs_nz Hs_c_nz Hs_n Hn_nz.
    clear -p Hs_nz Hs_c_nz Hs_n Hn_nz wprops.
    cbv [balance]. rewrite eval_distribute_balance.
    repeat first [ rewrite Z_mod_same_full
                 | rewrite eval_scmul by auto
                 | rewrite eval_encode by auto with zarith
                 | reflexivity
                 | progress (pull_Zmod; autorewrite with zsimplify_fast; push_Zmod) ].
  Qed.

  (*
  Lemma nth_default_balance_bounded' i d' d
        (** We add an extra hypothesis that is too bulky to prove *)
        (Hadd : forall x y, length x = n -> length y = n -> Positional.add weight n x y = List.map2 Z.add x y)
    : (i < n)%nat ->
      coef * nth_default d' tight_upperbounds i <= nth_default d balance i.
  Proof using wprops.
    generalize length_tight_upperbounds.
    clear -wprops Hadd.
    intros; etransitivity; [ | eapply nth_default_encode_distributed_bounded'; auto ]; auto.
    { rewrite map_nth_default_always; reflexivity. }
    { distr_length. }
  Qed.
  (** We would like to prove this general lemma, but since we're using
      [Positional.add] rather than [List.map2 Z.add], it's kind-of
      annoying to prove, so we skip it. *)
  Lemma nth_default_balance_bounded i d' d
    : (i < n)%nat ->
      coef * nth_default d' tight_upperbounds i <= nth_default d balance i.
  Proof using wprops.
    apply nth_default_balance_bounded'; auto.
  Abort.
   *)

  (** check if the suggested number of limbs will overflow
      double-width registers when adding partial products after a
      multiplication and then doing solinas reduction *)
  Definition overflow_free : bool
    := let v := squaremod weight s c n loose_upperbounds in
       forallb (fun k => Z.log2 k <? 2 * machine_wordsize) v.

  Definition is_goldilocks : bool
    := match c with
       | (w, v) :: _
         => (s =? 2^Z.log2 s)
              && (w =? 2^Z.log2 w)
              && (Z.log2 s =? 2 * Z.log2 w)
       | nil => false
       end.
End __.
#[global]
Hint Rewrite @length_distribute_balance @length_distribute_balance_step @length_balance @length_prime_upperbound_list @length_tight_upperbounds @length_loose_upperbounds @length_tight_bounds @length_loose_bounds : distr_length.

Inductive MaybeLimbCount := NumLimbs (n : nat) | Auto (idx : nat).

Section ___.
  Context {tight_upperbound_fraction : tight_upperbound_fraction_opt}
          (s : Z)
          (c : list (Z * Z))
          (machine_wordsize : Z).
  (** given a parsed prime, pick out all plausible numbers of (unsaturated) limbs *)
  (** an unsaturated implementation will necessarily need at least as many limbs
      as a saturated one, so search starting there *)
  Let num_bits_p := Z.log2_up s.
  Let nlimbs_saturated := Z.to_nat (Qceiling (num_bits_p / machine_wordsize)).
  Let min_limbs := nlimbs_saturated.
  (* don't search past 2x as many limbs as saturated representation; that's just wasteful *)
  Let result := filter (fun n => overflow_free n s c machine_wordsize) (seq min_limbs min_limbs).
  Definition get_possible_limbs : list nat
    := result.

  Definition get_num_limbs (n : MaybeLimbCount) : option nat
    := match n with
       | NumLimbs n => Some n
       | Auto idx => nth_error get_possible_limbs idx
       end.
End ___.
