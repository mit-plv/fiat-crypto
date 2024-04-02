From Coq Require Import ZArith Lia. Local Open Scope Z_scope.

Module Z.
  Lemma testbit_pow2 n i (H : 0 <= n) : Z.testbit (2^n) i = Z.eqb i n.
  Proof.
    rewrite <-(Z.mul_1_l (2^n)), Z.mul_pow2_bits by trivial.
    case (Z.eqb_spec i n) as [->|]; rewrite ?Z.sub_diag; trivial.
    case (Z.ltb_spec (i-n) 0) as []; rewrite ?Z.testbit_neg_r by lia; trivial.
    eapply Z.bits_above_log2; cbn; lia.
  Qed.
End Z.

Local Ltac t := 
  try (eapply Z.bits_inj'; intros i Hi);
  repeat match goal with
  | _ => progress subst
  | _ => solve [trivial | lia]
  | _ => progress rewrite
       ?Z.sub_simpl_r,
       ?Z.testbit_0_l, ?Z.testbit_neg_r, ?Z.testbit_pow2, ?Z.testbit_ones,
       ?Z.lor_spec, ?Z.land_spec, ?Z.lxor_spec, ?Z.ldiff_spec,
       ?Z.testbit_mod_pow2, ?Z.shiftl_spec, ?Z.shiftl_spec_low, ?Z.shiftr_spec
       by lia
  | _ => progress rewrite
      ?Bool.andb_false_r, ?Bool.andb_true_r,
      ?Bool.andb_false_l, ?Bool.andb_true_l,
      ?Bool.orb_false_r, ?Bool.orb_true_r,
      ?Bool.orb_false_l, ?Bool.orb_true_l,
      ?Bool.xorb_false_r, ?Bool.xorb_true_r,
      ?Bool.xorb_false_l, ?Bool.xorb_true_l,
      ?Bool.negb_involutive
  | |- _ => progress cbn [negb]
  | |- context [Z.leb ?x ?y] => destruct (Z.leb_spec x y) as []
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) as []
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y) as []
  end.

Require Import Crypto.Spec.Curve25519.

Lemma mod8_clamp' k : clamp k mod 8 = 0.
Proof. cbv [clamp]. Z.div_mod_to_equations. lia. Qed.

Lemma clamp_range k : 2^254 <= clamp k < 2^255.
Proof. cbv [clamp]. Z.div_mod_to_equations. lia. Qed.

Definition clamp' k := Z.lor (Z.ldiff k (Z.ones 3) mod 2^255) (2^254).

Lemma clamp'_correct k : clamp' k = Curve25519.clamp k.
Proof.
  cbv [Curve25519.clamp clamp']; change 8 with (2^3).
  rewrite Z.mul_comm, <-Z.shiftl_mul_pow2, <-Z.shiftr_div_pow2, ?Z.add_nocarry_lxor; try lia; t.
Qed.


From Coq Require Import ZArith Lia.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Byte.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Import Syntax Syntax.Coercions NotationsCustomEntry.
Import ListNotations.

Definition clamp := func! (sk) {
  store1(sk, load1(sk) & $248);
  store1(sk+$31, (load1(sk+$31) & $127) | $64)
}.

From coqutil Require Import Word.Interface Word.Naive.
From coqutil Require Import SortedListWord.
From coqutil Require Import symmetry.
Require Import bedrock2.FE310CSemantics.
Local Existing Instances SortedListString.map SortedListWord.map coqutil.Word.Naive.word.

From coqutil Require Import LittleEndianList.
Require Import bedrock2.Syntax bedrock2.WeakestPrecondition bedrock2.Map.SeparationLogic.
Import Coq.Lists.List. (* TODO: SeparationLogic should not override skipn  and etc *)
From bedrock2 Require Import ProgramLogic. Import ProgramLogic.Coercions.
Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).
Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").
Import Byte Word.Properties.
Local Coercion byte.unsigned : byte >-> Z.
Local Arguments le_combine !_.

Global Instance spec_of_clamp : spec_of "clamp" :=
  fnspec! "clamp" sk / (s : list Byte.byte) (R : _ -> Prop),
  { requires t m := m =* s$@sk ⋆ R /\ length s = 32%nat;
    ensures t' m := t=t' /\ m=* (le_split 32 (Curve25519.clamp (le_combine s)))$@sk ⋆ R }.

Lemma clamp_correct : program_logic_goal_for_function! clamp.
Proof.
  straightline; repeat straightline_cleanup.

  do 1 try destruct s as [|?b s]; try (cbn [length] in *; congruence).
  cbn [Array.array] in *; cbn [length] in *.
  repeat straightline.

  rewrite <-(firstn_skipn 30 s) in H1 |- *.
  seprewrite_in @Array.bytearray_append H1; rewrite ?app_length, ?firstn_length_le in * by lia.
  rewrite <-!Properties.word.add_assoc, <-!Properties.word.ring_morph_add  in *; simpl Z.add in *.

  assert (length (skipn 30 s) = 1)%nat by (rewrite skipn_length; lia). 
  assert (length (firstn 30 s) = 30)%nat by (rewrite firstn_length; lia). 
  destruct (skipn 30 s) as [|b31 [] ] eqn:? in *; try (cbn [length] in *; congruence).
  cbn [Array.array] in *.

  repeat straightline.
  
  eassert (Hrw : Lift1Prop.iff1 (ptsto a (Byte.byte.of_Z v0)) ([Byte.byte.of_Z v0]$@a)) by (cbn [Array.array]; cancel).
  repeat seprewrite_in Hrw H4.
  repeat seprewrite_in (symmetry! @Array.array_cons) H4.
  seprewrite_in @Array.bytearray_index_merge H4.
  { cbn [length]; rewrite ?app_length, ?length_firstn, ?Properties.word.unsigned_of_Z_nowrap; try lia. }

  eassert (le_split _ _ = _) as ->; [|ecancel_assumption].
  clear -H0 Heql0.

  eapply le_combine_inj; rewrite ?le_combine_split.
  { repeat (cbn [length]; rewrite ?length_le_split, ?app_length, ?firstn_length). lia. }

  rewrite <-clamp'_correct.

  repeat (cbn [le_combine]; rewrite ?le_combine_app, ?le_combine_firstn).

  subst v v0.

  cbn [length]; rewrite ?firstn_length_le by lia.
  simpl Z.mul at 1 2.
  rewrite ?byte.unsigned_of_Z; cbv [byte.wrap].
  repeat rewrite ?word.unsigned_and_nowrap, ?word.unsigned_or_nowrap.

  pose proof byte.unsigned_range b.
  pose proof byte.unsigned_range b31.
  rewrite ?word.unsigned_of_Z_nowrap; try lia.
  cbv [clamp'].

  rewrite <-(byte.wrap_unsigned b);
  rewrite <-(byte.wrap_unsigned b31);
  cbv [byte.wrap].
  change 127 with (Z.ones 7).
  change 64 with (2^6).
  change 248 with (Z.ldiff (Z.ones 8) (Z.ones 3)).
  change (31%nat * 8) with 248 in *.

  t.

  f_equal; lia.
Qed.
