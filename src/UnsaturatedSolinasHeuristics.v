Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZRange.
Require Crypto.TAPSort.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope bool_scope.

Import Associational Positional.

Notation limbwidth n s c := (inject_Z (Z.log2_up (s - Associational.eval c)) / inject_Z (Z.of_nat n))%Q.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Section __.
  Context (n : nat)
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

  Definition tight_upperbound_fraction : Q := (11/10)%Q.
  Definition loose_upperbound_extra_multiplicand : Z := 3.
  Definition prime_upperbound_list : list Z
    := encode_no_reduce (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
  Definition tight_upperbounds : list Z
    := List.map
         (fun v : Z => Qceiling (tight_upperbound_fraction * v))
         prime_upperbound_list.

  Definition loose_upperbounds : list Z
    := List.map
         (fun v : Z => loose_upperbound_extra_multiplicand * v)
         tight_upperbounds.

  Definition tight_bounds : list (option zrange)
    := List.map (fun u => Some r[0~>u]%zrange) tight_upperbounds.
  Definition loose_bounds : list (option zrange)
    := List.map (fun u => Some r[0~>u]%zrange) loose_upperbounds.

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
  Context (s : Z)
          (c : list (Z * Z))
          (machine_wordsize : Z).
  (** given a parsed prime, pick out all plausible numbers of (unsaturated) limbs *)
  (** we want to leave enough bits unused to do a full solinas
      reduction without carrying; the number of bits necessary is the
      sum of the bits in the negative coefficients of p (other than
      the most significant digit), i.e., in the positive coefficients
      of c *)
  Let num_bits_p := Z.log2_up s.
  Let unused_bits := sum (map (fun t => Z.log2_up (fst t)) c).
  Let min_limbs := Z.to_nat (Qceiling (num_bits_p / (machine_wordsize - unused_bits))).
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
