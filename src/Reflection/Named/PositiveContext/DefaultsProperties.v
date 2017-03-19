Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Named.PositiveContext.
Require Import Crypto.Reflection.CountLets.
Require Import Crypto.Reflection.Named.NameUtil.
Require Import Crypto.Reflection.Named.PositiveContext.Defaults.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Tactics.DestructHead.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.

  Lemma name_list_unique_map_pos_of_succ_nat_seq a b
    : name_list_unique (map BinPos.Pos.of_succ_nat (seq a b)).
  Proof.
    unfold name_list_unique, oname_list_unique, mname_list_unique.
    intros k n.
    rewrite !map_map, firstn_map, skipn_map, firstn_seq, skipn_seq.
    rewrite !in_map_iff; intros; destruct_head' ex; destruct_head' and; inversion_option; subst.
    match goal with H : _ |- _ => apply Pnat.SuccNat2Pos.inj in H end; subst.
    rewrite in_seq in *.
    omega *.
  Qed.

  Lemma name_list_unique_default_names_forf {var dummy t e}
    : name_list_unique (@default_names_forf base_type_code op var dummy t e).
  Proof. apply name_list_unique_map_pos_of_succ_nat_seq. Qed.
  Lemma name_list_unique_default_names_for {var dummy t e}
    : name_list_unique (@default_names_for base_type_code op var dummy t e).
  Proof. apply name_list_unique_map_pos_of_succ_nat_seq. Qed.
  Lemma name_list_unique_DefaultNamesFor {t e}
    : name_list_unique (@DefaultNamesFor base_type_code op t e).
  Proof. apply name_list_unique_map_pos_of_succ_nat_seq. Qed.
End language.
