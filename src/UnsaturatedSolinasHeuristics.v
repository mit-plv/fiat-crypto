Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Import Coq.QArith.Qabs.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ListUtil.FoldBool.
Require Crypto.TAPSort.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope bool_scope.

Import Associational Positional.

Notation limbwidth n s c := (inject_Z (Z.log2_up (s - Associational.eval c)) / inject_Z (Z.of_nat n))%Q.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

(** The fraction by which to multiply upper bounds *)
Class tight_upperbound_fraction_opt := tight_upperbound_fraction : Q.
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

  Definition default_tight_upperbound_fraction : Q := (11/10)%Q.
  Definition coef := 2. (* for balance in sub *)
  Definition prime_upperbound_list : list Z
    := encode_no_reduce (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
  (** We take the absolute value mostly to make proofs easy *)
  Definition tight_upperbounds : list Z
    := List.map
         (fun v : Z => Qceiling (Qabs (tight_upperbound_fraction * v)))
         prime_upperbound_list.

  (** We compute loose bounds based on how much headspace we have in
      each limb, and treat separately the maximum number of additions
      and subtractions that we guarantee *)
  (** Allow enough space to do two additions in a row w/o carrying *)
  Definition headspace_add_count : nat := 2.
  (** Allow enough space to do one subtraction w/o carrying *)
  Definition headspace_sub_count : nat := 1.

  Definition loose_upperbounds : list Z
    := List.map
         (fun '(v, bal) => v + Z.max (headspace_add_count * v)
                                     (headspace_sub_count * bal))
         (List.combine tight_upperbounds (balance (weight (Qnum limbwidth) (Qden limbwidth)) n s c coef)).

  Definition tight_bounds : list (option zrange)
    := List.map (fun u => Some r[0~>u]%zrange) tight_upperbounds.
  Definition loose_bounds : list (option zrange)
    := List.map (fun u => Some r[0~>u]%zrange) loose_upperbounds.

  Lemma tight_bounds_tighter : is_tighter_than tight_bounds loose_bounds = true.
  Proof using Type.
    cbv [tight_bounds loose_bounds tight_upperbounds loose_upperbounds balance scmul].
    rewrite !combine_map_l, !fold_andb_map_map, !fold_andb_map_map1, fold_andb_map_iff.
    cbn [lower upper].
    autorewrite with distr_length.
    split.
    { cbv [prime_upperbound_list].
      now autorewrite with distr_length natsimplify. }
    { intro; rewrite In_nth_error_iff; intros [n' H].
      rewrite !nth_error_combine in H.
      break_innermost_match_hyps; inversion_option; subst; cbn [fst snd].
      rewrite !Bool.andb_true_iff; split; [ reflexivity | Z.ltb_to_lt ].
      let x := lazymatch goal with |- ?x <= _ => x end in
      rewrite <- (Z.add_0_r x) at 1; apply Zplus_le_compat_l.
      etransitivity; [ | apply Z.le_max_l ].
      cbv [Qceiling Qmult Qfloor Qnum Qden Qopp inject_Z Qabs]; case tight_upperbound_fraction; intros; clear.
      Z.div_mod_to_quot_rem; nia. }
  Qed.

  (** check if the suggested number of limbs will overflow
      double-width registers when adding partial products after a
      multiplication and then doing solinas reduction *)
  Definition overflow_free : bool
    := let v := squaremod (weight (Qnum limbwidth) (Qden limbwidth)) s c n loose_upperbounds in
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
