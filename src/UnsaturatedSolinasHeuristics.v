Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Import Coq.QArith.Qabs.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
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
          (machine_wordsize : Z)
          (Hn_nz : n <> 0%nat)
          (Hs_n : Z.of_nat n <= Z.log2_up (s - Associational.eval c))
          (Hs_nz : s <> 0)
          (Hs_c_nz : s - Associational.eval c <> 0).

  Let limbwidth := (limbwidth n s c).
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
    := Partition.partition
         (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
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
      let weight := weight (Qnum limbwidth) (Qden limbwidth) in
      let fw := weight (S i) / weight i in
      let x := ((Mi - Bi) / fw) + Z.b2z (negb ((Mi - Bi) mod fw =? 0)) in
      let zero := [(weight i, x * fw); (weight (S i), -x)] in
      let Ba := to_associational weight n B ++ zero in
      let B := from_associational weight n Ba in
      B
    else B.

  Definition distribute_balance minvalues B :=
    fold_right (distribute_balance_step minvalues) B (rev (seq 0 (n-1))).

  (* distribute balance such that for all limbs i,
     tight_upperbounds[i] <= balance[i] *)
  Definition balance : list Z
      := let weight := weight (Qnum limbwidth) (Qden limbwidth) in
         let B := encode weight n s c (s - Associational.eval c) in
         let B := scmul weight n coef B in
         distribute_balance tight_upperbounds B.

  Lemma balance_length : length balance = n.
  Proof.
    cbv [balance scmul distribute_balance distribute_balance_step].
    apply fold_right_invariant; intros;
      break_innermost_match;
      now autorewrite with distr_length.
  Qed.
  Hint Rewrite balance_length : distr_length.

  (* reduce_balance needs to be enough such that +c doesn't underflow

     put -c in positional, look for negative terms
     if c is all-positive, then min(-c) will be positive

     most negative number that could be added (if min(-c) negative):
          max(tight_upperbounds)^2 * min(-c)

     ...but it can only occur at one position. try to rethink...

     - convert tight_upperbounds to associational
     - multiply by itself, call split
     - compute c * hi, convert to positional = max to be subtracted

     0 <= bal[i] + c_hi[i]
     -c_hi[i] <= bal[i]

     if c_hi[i] is negative, this means 0 < bal, so we do need balance
     if c_hi[i] is positive, this is satisfied by bal=0

     see if it works with 0; if not, try higher values
     TODO: is there a good way to guess the values?
   *)
  Definition max_reduce_add_term : list Z :=
    let weight := weight (Qnum limbwidth) (Qden limbwidth) in
    (* first, compute maximum values post-multiplication *)
    let max_values := to_associational weight n tight_upperbounds in
    let max_postmul := Associational.mul max_values max_values in
    (* next, get high part and multiply by c *)
    let c_hi := Associational.mul c (snd (split s max_postmul)) in
    from_associational weight n c_hi.

  (* negates the max_reduce_add_term and zeroes out negative coefficients; we
     always want balance limbs to be nonnegative *)
  Definition reduce_balance_lower_bounds :=
    let weight := weight (Qnum limbwidth) (Qden limbwidth) in
    List.map (Z.max 0) (scmul weight n (-1) max_reduce_add_term).

  (* Compute the reduce balance coefficient; we divide the evaluation of balance
     lower bounds by the modulus (using a ceiling division) to see the minimum
     coefficient needed so that balance can possibly obey its lower bounds *)
  Definition reduce_balance_coef :=
    let weight := weight (Qnum limbwidth) (Qden limbwidth) in
    ZMicromega.ceiling
      (eval weight n reduce_balance_lower_bounds) (s - Associational.eval c).

  Definition reduce_balance :=
    let weight := weight (Qnum limbwidth) (Qden limbwidth) in
    let M := encode weight n s c (s - Associational.eval c) in
    let balance := scmul weight n reduce_balance_coef M in
    @distribute_balance reduce_balance_lower_bounds balance.

  Definition loose_upperbounds : list Z
    := List.map
         (fun '(v, bal) => v + Z.max (headspace_add_count * v)
                                     (headspace_sub_count * bal))
         (List.combine tight_upperbounds balance).

  Definition tight_bounds : list (option zrange)
    := List.map (fun u => Some r[0~>u]%zrange) tight_upperbounds.
  Definition loose_bounds : list (option zrange)
    := List.map (fun u => Some r[0~>u]%zrange) loose_upperbounds.

  Lemma tight_bounds_tighter : is_tighter_than tight_bounds loose_bounds = true.
  Proof using Type.
    cbv [tight_bounds loose_bounds tight_upperbounds loose_upperbounds].
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

  (* TODO: shouldn't this be in Positional? *)
  Lemma eval_scmul weight {weight_props : @weight_properties weight} k x :
    eval weight n (scmul weight n k x) = k * eval weight n x.
  Proof.
    cbv [scmul].
    rewrite eval_from_associational by auto with zarith.
    autorewrite with push_eval. cbn [fst snd].
    rewrite eval_to_associational by auto. lia.
  Qed.

  Lemma eval_distribute_balance_step minvalues i x :
    eval (weight (Qnum limbwidth) (QDen limbwidth)) n
         (distribute_balance_step minvalues i x)
    = eval (weight (Qnum limbwidth) (QDen limbwidth)) n x.
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
             rewrite (Modulo.Z.mul_div_eq_full c a) by auto with zarith
         end.
    rewrite weight_multiples by auto. lia.
  Qed.

  Lemma eval_distribute_balance minvalues x :
    eval (weight (Qnum limbwidth) (QDen limbwidth))
         n (distribute_balance minvalues x)
    = eval (weight (Qnum limbwidth) (QDen limbwidth)) n x.
  Proof using Hs_nz Hs_c_nz Hs_n Hn_nz.
    clear -p Hs_nz Hs_c_nz Hs_n Hn_nz wprops.
    cbv [distribute_balance].
    apply fold_right_invariant; [ reflexivity | ].
    intros; rewrite eval_distribute_balance_step; auto.
  Qed.

  Lemma eval_balance : eval (weight (Qnum limbwidth) (Qden limbwidth)) n balance mod (s - Associational.eval c) = 0.
  Proof using Hs_nz Hs_c_nz Hs_n Hn_nz.
    clear -p Hs_nz Hs_c_nz Hs_n Hn_nz wprops.
    cbv [balance]. rewrite eval_distribute_balance.
    repeat first [ rewrite Z_mod_same_full
                 | rewrite eval_scmul by auto
                 | rewrite eval_encode by auto with zarith
                 | reflexivity
                 | progress (pull_Zmod; autorewrite with zsimplify_fast; push_Zmod) ].
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
(*
Require Import Crypto.Util.Strings.Show.
Require Import Coq.Strings.String.
Open Scope string_scope.
Existing Instance PowersOfTwo.show_Z.
(* Or: *)
(*
Existing Instance Hex.show_Z.
*)

Class params := { n : nat; s : Z; c : list (Z * Z) }.

Inductive prime := p224_32 | p224_64 | p256_32 | p256_64.

Definition get_params (m : prime) : params :=
  match m with
  | p224_64 => {| n := 4; s := 2^224; c := [(2^96,1);(1,-1)] |}
  | p256_64 => {| n := 6; s := 2^256; c := [(2^224,1); (2^192,-1); (2^96,-1);(1,1)] |}
  | p224_32 => {| n := 8; s := 2^224; c := [(2^96,1);(1,-1)] |}
  | p256_32 => {| n := 12; s := 2^256; c := [(2^224,1); (2^192,-1); (2^96,-1);(1,1)] |}
  end.

Definition m := p256_64.
Instance p : params := get_params m.

Definition weight :=
  weight (Qnum (limbwidth n s c)) (QDen (limbwidth n s c)).

About reduce_balance.
Compute (@reduce_balance 1 n s c).
Compute show false (eval weight n (@reduce_balance 1 n s c)).
Compute show false (eval weight n (@reduce_balance 1 n s c) / (s - Associational.eval c)).
*)
