Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Util.PrimitiveSigma.
Require Import Crypto.Util.MSetPositive.Facts.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Import Crypto.Language.
Require Import Crypto.LanguageInversion.
Require Import Crypto.IdentifiersGenerate.
Require Import Crypto.IdentifiersLibraryProofs.
Require Import Crypto.Util.FixCoqMistakes.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import IdentifiersGenerate.Compilers.
  Export IdentifiersLibraryProofs.Compilers.
  Local Set Primitive Projections.

  Module pattern.
    Import IdentifiersGenerate.Compilers.pattern.
    Export IdentifiersLibraryProofs.Compilers.pattern.
    Import Datatypes. (* for Some, None, option *)

    Local Notation type_of_list := (List.fold_right (fun A B => prod A B) unit).

    Import ProofGoalType.

    Module Raw.
      Export IdentifiersLibraryProofs.Compilers.pattern.Raw.
      Module ident.
        Export IdentifiersLibraryProofs.Compilers.pattern.Raw.ident.
        Import Datatypes. (* for Some, None, option *)

        Ltac prove_is_simple_correct0 _ :=
          intros;
          let p := lazymatch goal with | [ |- is_simple ?p = true <-> _ ] => p end in
          destruct p; cbn; cbv -[Datatypes.fst Datatypes.snd projT1 projT2] in *; split; intro H;
          try solve [ reflexivity | exfalso; discriminate ];
          repeat first [ match goal with
                         | [ H : nat -> ?A |- _ ] => specialize (H O)
                         | [ H : unit -> ?A |- _ ] => specialize (H tt)
                         | [ H : forall x y : PrimitiveProd.Primitive.prod _ _, _ |- _ ] => specialize (fun x1 y1 x2 y2 => H (PrimitiveProd.Primitive.pair x1 x2) (PrimitiveProd.Primitive.pair y1 y2)); cbn in H
                         | [ H : forall x y : Datatypes.prod _ _, _ |- _ ] => specialize (fun x1 y1 x2 y2 => H (Datatypes.pair x1 x2) (Datatypes.pair y1 y2)); cbn in H
                         | [ H : forall x y : PrimitiveSigma.Primitive.sigT ?P, _ |- _ ] => specialize (fun x1 y1 x2 y2 => H (PrimitiveSigma.Primitive.existT P x1 x2) (PrimitiveSigma.Primitive.existT P y1 y2)); cbn in H
                         | [ H : forall x y : Compilers.base.type, _ |- _ ] => specialize (fun x y => H (Compilers.base.type.type_base x) (Compilers.base.type.type_base y))
                         | [ H : forall x y : Compilers.base.type.base, _ |- _ ] => specialize (H Compilers.base.type.unit Compilers.base.type.nat); try congruence; cbn in H
                         end
                       | congruence ].

        Ltac prove_invert_bind_args_raw_to_typed _ :=
          intros;
          let p := lazymatch goal with |- @invert_bind_args _ _ _ ?p = Some _ => p end in
          destruct p; cbv in *;
          destruct_head' (@Primitive.sigT); destruct_head'_prod; destruct_head'_unit; reflexivity.

        Ltac prove_fold_invert_bind_args _ := reflexivity.

        Ltac prove_split_ident_to_ident _ :=
          intros;
          let ridc := lazymatch goal with |- context[@raw_ident_infos_of _ ?ridc] => ridc end in
          destruct ridc; reflexivity.

        Ltac prove_eq_indep_types_of_eq_types _ :=
          intros;
          let ridc := lazymatch goal with H : context[@raw_ident_infos_of _ ?ridc] |- _ => ridc end in
          destruct ridc; cbv in *;
          destruct_head'_prod; destruct_head'_unit; try reflexivity;
          type.inversion_type; reflexivity.

        Ltac prove_eq_invert_bind_args_unknown _ := reflexivity.
      End ident.
    End Raw.

    Module ident.
      Export IdentifiersLibraryProofs.Compilers.pattern.ident.
      Import Datatypes. (* for Some, None, option *)

      Ltac prove_fold_eta_ident_cps _ := reflexivity.

      Ltac prove_fold_unify _ :=
        lazymatch goal with
        | [ |- ?LHS = _ ] => vm_cast_no_check (eq_refl LHS)
        end.

      Ltac prove_to_typed_of_typed_ident _ :=
        intros;
        let idc := lazymatch goal with |- _ = ?idc => idc end in
        destruct idc;
        try (vm_compute; reflexivity);
        cbv -[type.type_ind type.relax type.subst_default Compilers.base.type.type_ind f_equal f_equal2 base.relax base.subst_default base.eq_subst_default_relax];
        cbn [type.type_ind type.relax type.subst_default f_equal f_equal2 base.relax base.subst_default base.eq_subst_default_relax];
        repeat first [ progress subst
                     | progress intros
                     | progress cbn [f_equal f_equal2]
                     | reflexivity
                     | match goal with
                       | [ |- context[@base.eq_subst_default_relax ?t ?evm] ]
                         => generalize (base.subst_default (base.relax t) evm), (@base.eq_subst_default_relax t evm)
                       end ].

      Ltac prove_eq_unify_unknown _ := reflexivity.
    End ident.

    Module ProofTactic.
      Module Export Settings.
        Export ident.GoalType.Settings.
      End Settings.
      Ltac prove_package_proofs _ :=
        idtac;
        let time_if_debug1 := Tactics.time_if_debug1 in
        let pkg := lazymatch goal with |- @package_proofs ?pkg => pkg end in
        cbv [pkg];
        unshelve econstructor;
        [ let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving is_simple_correct0...") in
          time_if_debug1 Raw.ident.prove_is_simple_correct0
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving invert_bind_args_raw_to_typed...") in
          time_if_debug1 Raw.ident.prove_invert_bind_args_raw_to_typed
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving fold_invert_bind_args...") in
          time_if_debug1 Raw.ident.prove_fold_invert_bind_args
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving split_ident_to_ident...") in
          time_if_debug1 Raw.ident.prove_split_ident_to_ident
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving eq_indep_types_of_eq_types...") in
          time_if_debug1 Raw.ident.prove_eq_indep_types_of_eq_types
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving fold_eta_ident_cps...") in
          time_if_debug1 ident.prove_fold_eta_ident_cps
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving fold_unify...") in
          time_if_debug1 ident.prove_fold_unify
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving to_typed_of_typed_ident...") in
          time_if_debug1 ident.prove_to_typed_of_typed_ident
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving eq_invert_bind_args_unknown...") in
          time_if_debug1 Raw.ident.prove_eq_invert_bind_args_unknown
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving eq_unify_unknown...") in
          time_if_debug1 ident.prove_eq_unify_unknown ].
      Ltac cache_build_package_proofs package :=
        let name := fresh "ident_package_proofs" in
        cache_proof_with_type_by (@package_proofs package) ltac:(prove_package_proofs ()) name.
    End ProofTactic.
  End pattern.
End Compilers.
