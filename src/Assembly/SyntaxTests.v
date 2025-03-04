From Coq Require Import ZArith.
From Coq Require Import NArith.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Derive.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Listable.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Assembly.Syntax.
Require Crypto.Util.Tuple.
Require Crypto.Util.OptionList.
Import ListNotations.

Local Open Scope list_scope.

Local Set Implicit Arguments.
Local Set Primitive Projections.

Local Coercion N.of_nat : nat >-> N.

Lemma reg_of_index_and_shift_and_bitcount_opt_of_index_and_shift_and_bitcount_of_reg : forall r : REG, reg_of_index_and_shift_and_bitcount_opt (index_and_shift_and_bitcount_of_reg r) = Some r.
Proof. destruct r; vm_compute; try reflexivity. Defined.

Lemma reg_of_index_and_shift_and_bitcount_of_index_and_shift_and_bitcount_of_reg : forall r : REG, reg_of_index_and_shift_and_bitcount (index_and_shift_and_bitcount_of_reg r) = r.
Proof. destruct r; vm_compute; reflexivity. Defined.

Lemma reg_index_widest_register_of : forall r : REG, reg_index (widest_register_of r) = reg_index r.
Proof. destruct r; reflexivity. Defined.

Lemma reg_index_widest_register_of_index_opt : forall index : N, (N.to_nat index <? List.length widest_registers) = true -> option_map reg_index (widest_register_of_index_opt index) = Some index.
Proof.
  intros index; cbv [widest_register_of_index_opt].
  rewrite <- (N2Nat.id index), Nat2N.id; generalize (N.to_nat index); clear index; intro index.
  vm_compute List.map.
  vm_compute List.length.
  cbv [Nat.ltb]; cbn [Nat.leb].
  repeat lazymatch goal with
  | [ |- false = true -> _ ] => discriminate
  | [ |- (?index <=? _) = true -> _ ] =>
      is_var index; destruct index; [ reflexivity | cbn [Nat.leb] ]
  end.
Qed.

Lemma widest_register_of_index_opt_Some_length_iff : forall index : N, (exists r, widest_register_of_index_opt index = Some r) <-> (N.to_nat index <? List.length widest_registers) = true.
Proof.
  intros index; cbv [widest_register_of_index_opt].
  rewrite <- (N2Nat.id index), Nat2N.id; generalize (N.to_nat index); clear index; intro index.
  vm_compute List.map.
  vm_compute List.length.
  cbv [Nat.ltb]; cbn [Nat.leb].
  repeat lazymatch goal with
  | [ |- (exists r, nth_error nil ?index = Some _) <-> _ ] => is_var index; destruct index; cbn [nth_error]
  | [ |- _ <-> false = true ] => split; [ | discriminate ]
  | [ |- _ <-> true = true ] => repeat esplit
  | [ |- _ <-> (?index <=? _) = true ] =>
      is_var index; destruct index; cbn [Nat.leb nth_error]
  end.
  all: intros [? H]; discriminate.
Qed.

Lemma reg_index_widest_register_of_index : forall index : N, (N.to_nat index <? List.length widest_registers) = true -> reg_index (widest_register_of_index index) = index.
Proof.
  intros index H; cbv [widest_register_of_index].
  apply reg_index_widest_register_of_index_opt in H.
  destruct widest_register_of_index_opt; cbv [option_map] in *; inversion H; subst.
  reflexivity.
Qed.

Lemma reg_index_overlapping_registers : forall r r' n, nth_error (overlapping_registers r) n = Some r' -> reg_index r' = reg_index r.
Proof.
  intros r r' n; destruct r.
  all: vm_compute overlapping_registers.
  all: repeat lazymatch goal with
  | [ |- nth_error (_ :: _) ?v = Some _ -> _ ] => is_var v; destruct v; cbn [nth_error]
  | [ |- nth_error [] ?v = Some _ -> _ ] => is_var v; destruct v; cbn [nth_error]
  | [ |- Some _ = Some _ -> _ ] => let H := fresh in intro H; inversion H
  | [ |- None = Some _ -> _ ] => let H := fresh in intro H; inversion H
  end.
  all: subst; reflexivity.
Qed.

Lemma reg_of_index_and_shift_and_bitcount_of_reg r
  : reg_of_index_and_shift_and_bitcount (index_and_shift_and_bitcount_of_reg r) = r.
Proof. destruct r; vm_compute; reflexivity. Qed.

Lemma widest_register_of_index_opt_correct
  : forall n r, widest_register_of_index_opt n = Some r ->
      reg_index r = n
       /\ forall r', reg_index r' = n -> r = r' \/ (reg_size r' < reg_size r)%N.
Proof.
  intros n r H.
  epose proof (proj1 (widest_register_of_index_opt_Some_length_iff _) (ex_intro _ _ H)) as H'.
  pose proof H' as H''.
  apply reg_index_widest_register_of_index_opt in H''.
  rewrite H in H''; cbn in H''; inversion H''; subst.
  split; [ reflexivity | ].
  destruct r, r'.
  all: vm_compute; try (constructor; reflexivity); try discriminate.
Qed.

Lemma widest_register_of_index_correct
  : forall n,
    (~exists r, reg_index r = n)
    \/ (let r := widest_register_of_index n in reg_index r = n
       /\ forall r', reg_index r' = n -> r = r' \/ (reg_size r' < reg_size r)%N).
Proof.
  intro n; pose proof (widest_register_of_index_opt_correct n) as H.
  cbv [widest_register_of_index].
  destruct (widest_register_of_index_opt n) as [r |] eqn:H'; [ right; apply H; reflexivity | left ].
  intros [ [] H'' ]; subst; cbv in H'.
  all: inversion H'.
Qed.

Lemma reg_of_index_and_shift_and_bitcount_opt_correct v r
  : reg_of_index_and_shift_and_bitcount_opt v = Some r <-> index_and_shift_and_bitcount_of_reg r = v.
Proof.
  split; [ | intro; subst; destruct r; vm_compute; reflexivity ].
  cbv [index_and_shift_and_bitcount_of_reg]; destruct v as [ [index shift] bitcount ].
  cbv [reg_of_index_and_shift_and_bitcount_opt].
  pose proof (reg_index_widest_register_of_index index) as H''.
  cbv [widest_register_of_index] in H''.
  rewrite <- widest_register_of_index_opt_Some_length_iff in H''.
  destruct widest_register_of_index_opt eqn:H; [ | intro H'; cbv in H'; now inversion H' ].
  cbv [Option.bind Option.sequence_return] in *.
  specialize (H'' (ex_intro _ _ eq_refl)).
  subst.
  rewrite find_some_iff.
  repeat first
    [ progress intros
    | progress destruct_head'_ex
    | progress destruct_head'_and
    | progress reflect_hyps
    | progress subst
    | match goal with
      | [ H : nth_error (overlapping_registers _) _ = Some _ |- _ ] =>
          apply reg_index_overlapping_registers in H; try rewrite H
      end
    | reflexivity ].
Qed.

Lemma reg_of_index_and_shift_and_bitcount_eq v r
  : reg_of_index_and_shift_and_bitcount v = r
    -> (index_and_shift_and_bitcount_of_reg r = v
        \/ ((~exists r, index_and_shift_and_bitcount_of_reg r = v)
            /\ r = widest_register_of_index (fst (fst v)))).
Proof.
  cbv [reg_of_index_and_shift_and_bitcount].
  destruct v as [ [index offset] size ].
  destruct reg_of_index_and_shift_and_bitcount_opt eqn:H;
    [ left | right; split; [ intros [r' H'] | ] ]; subst; try reflexivity.
  { rewrite reg_of_index_and_shift_and_bitcount_opt_correct in H; assumption. }
  { rewrite <- reg_of_index_and_shift_and_bitcount_opt_correct in H'; congruence. }
Qed.
