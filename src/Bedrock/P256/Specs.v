Require Import coqutil.Datatypes.List Coq.Lists.List.
From bedrock2 Require Import Syntax NotationsCustomEntry.

From coqutil Require Import LittleEndianList.

Import BinInt.
Local Open Scope Z_scope.

Module Import List.
  Import Lists.List ListNotations PeanoNat micromega.Lia.
  Local Open Scope nat_scope.

  Lemma cons_hd_tl [A] (a : A) l : l <> nil -> hd a l :: tl l = l.
  Proof. case l; cbn; congruence. Qed.

  Lemma tl_chunk [A : Type] (k : nat) (Hk : k <> 0%nat) (bs : list A) :
    tl (List.chunk k bs) = List.chunk k (List.skipn k bs).
  Proof.
    rewrite <-(Nat.mul_1_l k) at 3. rewrite <-List.skipn_chunk by trivial.
    case List.chunk; trivial.
  Qed.

  Lemma firstn_le_split n m z : List.firstn n (le_split m z) = le_split (Nat.min n m) z.
  Proof.
    apply nth_error_ext; intros i.
    case (Nat.ltb_spec i (Nat.min n m)) as [].
    { rewrite nth_error_le_split, nth_error_firstn by trivial.
      case Nat.ltb_spec; intros; rewrite ?nth_error_le_split; trivial; lia. }
    rewrite 2(proj2 (nth_error_None _ _)); trivial;
      rewrite ?firstn_length, ?length_le_split; trivial.
  Qed.

  (* TODO: move *)
  Lemma le_split_0_l z : le_split 0 z = nil.
  Proof. trivial. Qed.

  (* TODO: move *)
  Lemma le_split_0_r n : le_split n 0 = List.repeat Byte.x00 n.
  Proof.
    induction n; trivial.
    cbn [List.repeat]; unfold le_split; eapply f_equal2; auto.
  Qed.
End List.

Module Z.
  Notation to_bytes := le_split.
  Notation of_bytes := le_combine.
  Definition of_bigendian bs := le_combine (List.rev bs).
  Definition to_bigendian n z := List.rev (le_split n z).

  Lemma testbit_high a n : 0 <= a < 2^n -> Z.testbit a n = false.
  Proof.
    case n as [|p|p]; intros.
    { assert (a = 0) as ->; trivial; Lia.lia. }
    { erewrite <-(Z.mod_small a), Z.mod_pow2_bits_high; try eassumption; eauto using Zorder.Zle_0_pos, Z.le_refl. }
    { trivial. }
  Qed.
End Z.

Module Import NotationsCustomEntry.
Infix ".+"   := (expr.op bopname.add)  (in custom bedrock_expr at level 6, left associativity, only parsing).
End NotationsCustomEntry.

From Coq Require Import BinInt BinNat Init.Byte.
From Crypto Require Import PrimeFieldTheorems ModInv.

Lemma le_combine_app bs1 bs2 :
  le_combine (bs1 ++ bs2) = le_combine bs1 + 2^(Z.of_nat (Datatypes.length bs1)*8) * le_combine bs2.
Proof.
  rewrite le_combine_app, Z.shiftl_mul_pow2, Z.mul_comm by Lia.lia.
  rewrite <-Zbitwise.Z.add_lor_land; enough (Z.land _ _ = 0) as -> by Lia.lia.
  rewrite <-(List.firstn_all bs1), le_combine_firstn, List.firstn_length, PeanoNat.Nat.min_id.
  rewrite Z.mul_comm, <-(Z.mul_comm (le_combine _)).
  apply Z.bits_inj'; intros i H; rewrite Z.land_spec, Z.mul_pow2_bits, Z.testbit_mod_pow2, Z.testbit_0_l
    by auto with zarith.
  case Z.ltb_spec; intros; trivial.
  case (Z.ltb_spec i (Z.of_nat (length bs1) * 8)); intros.
  { rewrite (Z.testbit_neg_r _ (*workaround:*)(_ - _)) by Lia.lia. apply Bool.andb_false_r. }
  { rewrite ?Z.testbit_neg_r by Lia.lia; trivial. }
Qed.

Module F.
  Import micromega.Lia.
  Definition eqb {m} (x y : F m) := if F.eq_dec x y then true else false.
  Lemma eqb_eq {m} (x y : F m) : eqb x y = true <-> x = y.
  Proof. cbv [eqb]; case F.eq_dec; intuition congruence. Qed.

  Lemma zero_iff_to_Z : forall {m : positive} (x : F m), x = 0%F :> F m <-> F.to_Z x = 0%Z.
  Proof.
     split; intros; subst; try apply F.to_Z_0; [].
     apply F.eq_to_Z_iff. rewrite F.to_Z_0. assumption.
  Qed.

  Lemma pow_0_iff (p : positive) (Hp : Znumtheory.prime p) (x : F p) n (Hn : n <> 0%N) : F.pow x n = 0%F <-> x = 0%F.
  Proof.
    revert Hn ;induction n using N.peano_ind; try contradiction.
    intros _; split; cycle 1; intros; subst; rewrite ?F.pow_0_l; trivial; try lia.
    rewrite F.pow_succ_r in H; eapply Hierarchy.zero_product_zero_factor in H; destruct H; trivial.
    case (N.eqb_spec n 0) as [->|]; rewrite ?F.pow_0_r in *.
    { apply eq_sym in H; apply Hierarchy.zero_neq_one in H; case H. }
    eapply IHn; eauto.
  Qed.

  Lemma to_Z_sub {m} (x y : F m) : F.to_Z (x - y) = Z.modulo (F.to_Z x - F.to_Z y) m.
  Proof.
    cbv [F.sub].
    rewrite F.to_Z_add, F.to_Z_opp, Zdiv.Zplus_mod_idemp_r; trivial.
  Qed.
End F.

Module Byte.
  Import Byte.
  Local Coercion byte.unsigned : byte >-> Z.
  Definition xor (a b : byte) := byte.of_Z (Z.lor a b).

  Lemma xor_0_l  x : xor x00 x = x.
  Proof.
    cbv [xor].
    apply byte.unsigned_inj.
    rewrite byte.unsigned_of_Z, Z.lor_0_l, byte.wrap_unsigned; trivial.
  Qed.

  Import Lists.List micromega.Lia.
  Lemma map_xor_0_l bs l (H : (length bs <= l)%nat) : map (uncurry Byte.xor) (combine (repeat (Byte.x00) l) bs) = bs.
  Proof.
    revert dependent l.
    induction bs, l; cbn in *; try lia; trivial; [intros Hl].
    rewrite xor_0_l, IHbs; trivial; lia.
  Qed.
End Byte.

Local Coercion F.to_Z : F >-> Z.

Require Import Curves.Weierstrass.P256.

Module Import coord. (* bytes in montgomery form *)
  Notation coord := (F p256).
  Definition R : F p256 := F.of_Z _ (2^256).
  Coercion to_bytes (x : coord) : list byte := Z.to_bytes 32 (x * R)%F.
  Lemma length_coord (x : coord) : length x = 32%nat.
  Proof. apply length_le_split. Qed.

  Lemma zero_iff (x : coord) : (x = 0 <-> x*R = 0)%F.
  Proof.
    split; intuition (subst; trivial).
    eapply Field.is_mul_nonzero_nonzero in H; case H as [?|H]; trivial.
    apply (f_equal F.to_Z) in H. cbv in H. inversion H.
  Qed.
End coord.

From Crypto.Curves Require Import Jacobian.
Import Coq.Lists.List.

Module Import point.
  Notation point := (@Jacobian.point coord eq F.zero F.add F.mul P256.a P256.b _).
  Notation add :=
    (@Jacobian.add coord eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div P256.a P256.b _ _ _).
  Coercion to_bytes (p : point) :=
    let p := proj1_sig p in
    to_bytes (fst (fst p)) ++ to_bytes (snd (fst p)) ++ to_bytes (snd p).
  Lemma length_point (x : point) : length x = 96%nat.
  Proof. cbv [to_bytes]. rewrite ?app_length, ?length_coord; reflexivity. Qed.

  Definition iszero (P : point) :=
    if Decidable.dec (Jacobian.iszero P) then true else false.
End point.

From Coq Require Import String List. Local Open Scope string_scope. Local Open Scope list_scope.
From bedrock2 Require Import ProgramLogic WeakestPrecondition.
Import ProgramLogic.Coercions.
From coqutil Require Import Word.Interface OfListWord Separation SeparationLogic.
From coqutil Require Import letexists.


From bedrock2 Require Import ListIndexNotations.
Local Open Scope list_index_scope.

From bedrock2 Require Import SepAutoArray.
From coqutil Require Import symmetry.
Import PeanoNat Lia.
Import Tactics.
Require Import UniquePose.

Require Import Crypto.Spec.WeierstrassCurve.
Require Curves.Weierstrass.AffineProofs.
From bedrock2 Require ToCString.
From coqutil Require Macros.WithBaseName.

Local Notation "xs $@ a" := (map.of_list_word_at a xs)
  (at level 10, format "xs $@ a").
Local Notation "$ n" := (match word.of_Z n return word with w => w end) (only parsing, at level 9, format "$ n").
Local Notation "p .+ n" := (word.add p (word.of_Z n)) (only parsing, at level 50, format "p .+ n", left associativity).
Local Unset Printing Coercions.

Local Open Scope Z_scope.
Local Open Scope bool_scope.
Import micromega.Lia Word.Properties.

Section WithSemantics.
Context {width} {BW : Bitwidth.Bitwidth width} {word : word.word width}.
Context {locals : Interface.map.map string word}.
Context {mem : Interface.map.map word byte}.
Context {ext_spec : Semantics.ExtSpec}.


#[export] Instance spec_of_br_declassify : spec_of "br_declassify" :=
  fnspec! "br_declassify" a ~> a',
  { requires t m := True;
    ensures t' m' := t' = t /\ m' = m /\ a' = a }.

#[export] Instance spec_of_value_barrier : spec_of "br_value_barrier" :=
  fnspec! "br_value_barrier" a ~> a',
  { requires t m := True;
    ensures t' m' := t' = t /\ m' = m /\ a' = a }.

#[export] Instance spec_of_br_broadcast_odd : spec_of "br_broadcast_odd" :=
  fnspec! "br_broadcast_odd" x ~> y,
  { requires t m := True;
    ensures t' m' := t' = t /\ m' = m /\ y = word.broadcast (Z.odd x) }.

#[export] Instance spec_of_br_broadcast_negative : spec_of "br_broadcast_negative" :=
  fnspec! "br_broadcast_negative" x ~> y,
  { requires t m := True;
    ensures t' m' := t' = t /\ m' = m /\ y = word.broadcast (word.lts x (word.of_Z 0)) }.

#[export] Instance spec_of_br_broadcast_nonzero : spec_of "br_broadcast_nonzero" :=
  fnspec! "br_broadcast_nonzero" x ~> y,
  { requires t m := True;
    ensures t' m' := t' = t /\ m' = m /\ y = word.broadcast (negb (Z.eqb x 0)) }.

#[export] Instance spec_of_p256_coord_nonzero : spec_of "p256_coord_nonzero" :=
  fnspec! "p256_coord_nonzero" p_x / (x : coord) ~> nz,
  { requires t m := m =*> x$@p_x;
    ensures t' m' := t' = t /\ m' = m /\ nz = word.broadcast (negb (F.eqb x 0)) }.

#[export] Instance spec_of_fiat_p256_point_iszero : spec_of "p256_point_iszero" :=
  fnspec! "p256_point_iszero" p_P / (P : point) ~> nz,
  { requires t m := m =*> P$@p_P;
    ensures t' m' := t' = t /\ m' = m /\ nz = word.broadcast (point.iszero P) }.

#[export] Instance spec_of_p256_point_set_zero : spec_of "p256_point_set_zero" :=
  fnspec! "p256_point_set_zero" p_out / out R,
  { requires t m := m =* out$@p_out * R /\ length out = 96%nat;
    ensures t' m' := t' = t /\ m' =* (Jacobian.of_affine W.zero)$@p_out * R }.

#[export] Instance spec_of_p256_coord_add : spec_of "p256_coord_add" :=
  fnspec! "p256_coord_add" p_out p_x p_y / out (x y : coord) R,
  { requires t m := m =*> x$@p_x /\ m =*> y$@p_y /\ m =* out$@p_out * R /\ length out = length x;
    ensures t' m := let r : coord := F.add x y in t' = t /\ m =* r$@p_out * R }.

#[export] Instance spec_of_p256_coord_sub : spec_of "p256_coord_sub" :=
  fnspec! "p256_coord_sub" p_out p_x p_y / out (x y : coord) R,
  { requires t m := m =*> x$@p_x /\ m =*> y$@p_y /\ m =* out$@p_out * R /\ length out = length x;
    ensures t' m := let r : coord := F.sub x y in t' = t /\ m =* r$@p_out * R }.

#[export] Instance spec_of_p256_coord_halve : spec_of "p256_coord_halve" :=
  fnspec! "p256_coord_halve" p_out p_x / out (x : coord) R,
  { requires t m := m =*> x$@p_x /\ m =* out$@p_out * R /\ length out = length x;
    ensures t' m := let r : coord := F.div x (F.add F.one F.one) in t' = t /\ m =* r$@p_out * R }.

#[export] Instance spec_of_p256_coord_mul : spec_of "p256_coord_mul" :=
  fnspec! "p256_coord_mul" p_out p_x p_y / out (x y : coord) R,
  { requires t m := m =*> x$@p_x /\ m =*> y$@p_y /\ m =* out$@p_out * R /\ length out = length x;
    ensures t' m := let r : coord := F.mul x y in t' = t /\ m =* r$@p_out * R }.

#[export] Instance spec_of_p256_coord_sqr : spec_of "p256_coord_sqr" :=
  fnspec! "p256_coord_sqr" p_out p_x / out (x : coord) R,
  { requires t m := m =*> x$@p_x /\ m =* out$@p_out * R /\ length out = length x;
    ensures t' m := let r : coord := F.pow x 2 in t' = t /\ m =* r$@p_out * R }.

#[export] Instance spec_of_p256_point_add_nz_nz_neq : spec_of "p256_point_add_nz_nz_neq" :=
  fnspec! "p256_point_add_nz_nz_neq" p_out p_P p_Q / out (P Q : point) R ~> ok,
  { requires t m := m =* out$@p_out * P$@p_P * Q$@p_Q * R /\ length out = length P;
    ensures t' m := t' = t /\ exists out,
    m =* out$@p_out * P$@p_P * Q$@p_Q * R /\ length out = length P /\ (
        ~ Jacobian.iszero P -> ~ Jacobian.iszero Q ->
        (ok <> word.of_Z 0 /\ exists pfPneqQ, out = (Jacobian.add_inequal_nz_nz P Q pfPneqQ : point)) \/
        (ok = word.of_Z 0) /\ Jacobian.eq P Q)
  }%sep.

#[export] Instance spec_of_br_memset : spec_of "br_memset" :=
  fnspec! "br_memset" (p_d v n : word) / d R,
  { requires t m := m =* d$@p_d * R /\ length d = n :> Z;
    ensures t' m := t' = t /\ let out := repeat (Byte.byte.of_Z v) (Z.to_nat n) in m =* out$@p_d * R }.

#[export] Instance spec_of_br_memcxor : spec_of "br_memcxor" :=
  fnspec! "br_memcxor" (p_d p_s n mask : word) / (d s : list byte) R,
  { requires t m := m =* d$@p_d * s$@p_s * R /\ length d = n :> Z /\ length s = n :> Z;
    ensures t' m := t' = t /\
    exists out, length out = n :> Z /\
    m =* out$@p_d * s$@p_s * R /\
    (mask = word.of_Z 0 -> out = d) /\
    (mask = word.of_Z (-1) -> out = map (uncurry Byte.xor) (combine d s))
    }.

#[export] Instance spec_of_p256_point_double : spec_of "p256_point_double" :=
  fnspec! "p256_point_double" p_out p_P / out (P : point) R,
  { requires t m := m =* out$@p_out * P$@p_P * R /\ length out = length P;
    ensures t' m := t' = t /\
      let out : point := Jacobian.double_minus_3 eq_refl P in
      m =* out$@p_out * P$@p_P * R
  }%sep.

#[export] Instance spec_of_p256_point_add_vartime_if_doubling : spec_of "p256_point_add_vartime_if_doubling" :=
  fnspec! "p256_point_add_vartime_if_doubling" p_out p_P p_Q / out (P Q : point),
  { requires t m := m =* out$@p_out * P$@p_P * Q$@p_Q /\ length out = length P;
    ensures t' m := t' = t /\ exists out : point,
      m =* out$@p_out * P$@p_P * Q$@p_Q /\ Jacobian.eq out (Jacobian.add P Q)
  }%sep.

#[export] Instance spec_of_p256_point_add_affine_nz_nz_neq : spec_of "p256_point_add_affine_nz_nz_neq" :=
  fnspec! "p256_point_add_affine_nz_nz_neq" p_x / (x : coord) ~> nz,
  { requires t m := m =*> x$@p_x;
    ensures t' m' := t' = t /\ m' = m /\ nz = word.of_Z 0 <-> x = F.zero }.

#[export] Instance spec_of_br_cmov : spec_of "br_cmov" :=
  fnspec! "br_cmov" (c vnz vz : word) ~> r,
  { requires t m := c < 2;
    ensures t' m' := t' = t /\ m' = m /\ r = if Z.eqb c 0 then vz else vnz }.

(* Internal intermediate functions for field arithmetic: *)

#[export] Instance spec_of_u256_shr : spec_of "u256_shr" :=
  fnspec! "u256_shr" p_out p_x n / out (x : Z) R,
  { requires t m := m =*> (le_split 32 x)$@p_x /\ m =* out$@p_out * R /\ length out = 32%nat /\
    0 <= x < 2^256 /\ word.unsigned n < width;
    ensures t' m := let r : Z := x/2^n in
          t' = t /\ m =* (le_split 32 r)$@p_out * R }.

Definition spec_of_p256_coord_sub_nonmont : spec_of "p256_coord_sub" :=
  fnspec! "p256_coord_sub" p_out p_x p_y / out (x y : F p256) R,
  { requires t m := m =*> (le_split 32 x)$@p_x /\ m =*> (le_split 32 y)$@p_y /\ m =* out$@p_out * R /\ length out = 32%nat;
    ensures t' m := t' = t /\ m =* (le_split 32 (x-y)%F)$@p_out * R }.

#[export] Instance spec_of_p256_coord_set_minushalf_conditional : spec_of "u256_set_p256_minushalf_conditional" :=
  fnspec! "u256_set_p256_minushalf_conditional" p_out mask / b out R,
  { requires t m := m =* out$@p_out * R /\ length out = 32%nat /\ mask = word.broadcast b;
    ensures t' m := exists r : F p256,
      t' = t /\ m =* (le_split 32 r)$@p_out * R /\ (r = if b then F.opp (1/(1+1)) else F.zero)
  }.

End WithSemantics.

From bedrock2 Require Import BasicC64Semantics.
From bedrock2Examples Require shrd full_sub full_add full_mul memmove memcpy.
#[export] Existing Instance shrd.spec_of_shrd.
#[export] Instance spec_of_memmove : spec_of "memmove". apply memmove.spec_of_memmove. Defined.
#[export] Hint Mode Interface.map.map - - : typeclass_instances.
#[export] Hint Mode word.word - : typeclass_instances.

Goal spec_of "p256_coord_nonzero". exact _. all : fail. Abort.

Module word.
  Lemma signed_opp_nowrap (x : word) : word.signed x <> -2^63 -> word.signed (word.opp x) = - word.signed x.
  Proof.
    pose proof word.signed_range x.
    rewrite word.signed_opp.
    rewrite word.swrap_as_div_mod.
    PreOmega.Z.div_mod_to_equations; lia.
  Qed.

  Lemma nz_signed (x : word) : word.signed x <> 0 <-> word.unsigned x <> 0.
  Proof.
    rewrite word.signed_eq_swrap_unsigned.
    rewrite word.swrap_as_div_mod.
    intuition ZnWords.ZnWords.
  Qed.

  Lemma and_m1_l (x : word) : word.and (word.opp (word.of_Z (1))) x = x.
  Proof.
    apply word.unsigned_inj.
    rewrite word.unsigned_and_nowrap, word.unsigned_opp_nowrap, Z.sub_1_r, <-Z.ones_equiv.
    2: { rewrite word.unsigned_of_Z_1; inversion 1. }
    rewrite Z.land_comm, Z.land_ones, word.wrap_unsigned; trivial; blia.
  Qed.
End word.
