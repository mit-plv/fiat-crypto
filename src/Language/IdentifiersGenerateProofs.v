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
Require Import Crypto.Language.Language.
Require Import Crypto.Language.Inversion.
Require Import Crypto.Language.IdentifiersGenerate.
Require Import Crypto.Language.IdentifiersBasicLibrary.
Require Import Crypto.Language.IdentifiersLibraryProofs.
Require Import Crypto.Util.FixCoqMistakes.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import Language.Inversion.Compilers.
  Import IdentifiersBasicLibrary.Compilers.
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

        Ltac inhabit := (constructor; fail) + (constructor; inhabit).

        Ltac prove_is_simple_correct0 _ :=
          intros;
          let p := lazymatch goal with | [ |- is_simple ?p = true <-> _ ] => p end in
          destruct p; cbn; cbv -[Datatypes.fst Datatypes.snd projT1 projT2] in *; split; intro H;
          try solve [ reflexivity | exfalso; discriminate ];
          repeat first [ match goal with
                         | [ H : ?A -> ?B |- _ ] => specialize (H ltac:(inhabit))
                         | [ H : forall x y : PrimitiveProd.Primitive.prod _ _, _ |- _ ] => specialize (fun x1 y1 x2 y2 => H (PrimitiveProd.Primitive.pair x1 x2) (PrimitiveProd.Primitive.pair y1 y2)); cbn in H
                         | [ H : forall x y : Datatypes.prod _ _, _ |- _ ] => specialize (fun x1 y1 x2 y2 => H (Datatypes.pair x1 x2) (Datatypes.pair y1 y2)); cbn in H
                         | [ H : forall x y : PrimitiveSigma.Primitive.sigT ?P, _ |- _ ] => specialize (fun x1 y1 x2 y2 => H (PrimitiveSigma.Primitive.existT P x1 x2) (PrimitiveSigma.Primitive.existT P y1 y2)); cbn in H
                         | [ H : forall x y : Compilers.base.type _, _ |- _ ] => specialize (H Compilers.base.type.unit (Compilers.base.type.prod Compilers.base.type.unit Compilers.base.type.unit))
                         | [ H : forall x y : ?T, _ |- _ ] => specialize (H ltac:(constructor 1) ltac:(constructor 2 || fail 100 "Constructor 2 must exist for type" T)); try congruence; cbn in H
                         end
                       | congruence ].

        Ltac prove_invert_bind_args_raw_to_typed _ :=
          intros;
          let p := lazymatch goal with |- @invert_bind_args _ _ _ _ _ ?p = Some _ => p end in
          destruct p; cbv in *;
          destruct_head' (@Primitive.sigT); destruct_head'_prod; destruct_head'_unit; reflexivity.

        Ltac prove_fold_invert_bind_args _ := reflexivity.

        Ltac prove_split_ident_to_ident _ :=
          intros;
          let ridc := lazymatch goal with |- context[@raw_ident_infos_of _ _ _ ?ridc] => ridc end in
          destruct ridc; reflexivity.

        Ltac prove_eq_indep_types_of_eq_types reflect_base_beq _ :=
          pose proof reflect_base_beq;
          intros;
          let ridc := lazymatch goal with H : context[@raw_ident_infos_of _ _ _ ?ridc] |- _ => ridc end in
          destruct ridc; cbv in *;
          destruct_head'_prod; destruct_head'_unit; try reflexivity;
          inversion_type; reflexivity.

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
                       | [ |- context[@base.eq_subst_default_relax ?base ?t ?evm] ]
                         => generalize (base.subst_default (base.relax t) evm), (@base.eq_subst_default_relax base t evm)
                       end ].

      Ltac prove_eq_unify_unknown _ := reflexivity.
    End ident.

    Module ProofTactic.
      Module Export Settings.
        Export ident.GoalType.Settings.
      End Settings.
      Ltac prove_package_proofs_via ident_package :=
        idtac;
        let time_if_debug1 := Tactics.time_if_debug1 in
        let pkg := lazymatch goal with |- @package_proofs _ _ ?pkg => pkg end in
        let exprInfo := (eval hnf in (Basic.GoalType.exprInfo ident_package)) in
        let exprExtraInfo := (eval hnf in (Basic.GoalType.exprExtraInfo ident_package)) in
        let reflect_base_beq := lazymatch (eval hnf in exprExtraInfo) with {| Classes.reflect_base_beq := ?reflect_base_beq |} => reflect_base_beq end in
        cbv [pkg];
        unshelve econstructor;
        [ let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving is_simple_correct0...") in
          time_if_debug1 Raw.ident.prove_is_simple_correct0; fail 0 "A goal remains"
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving invert_bind_args_raw_to_typed...") in
          time_if_debug1 Raw.ident.prove_invert_bind_args_raw_to_typed; fail 0 "A goal remains"
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving fold_invert_bind_args...") in
          time_if_debug1 Raw.ident.prove_fold_invert_bind_args; fail 0 "A goal remains"
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving split_ident_to_ident...") in
          time_if_debug1 Raw.ident.prove_split_ident_to_ident; fail 0 "A goal remains"
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving eq_indep_types_of_eq_types...") in
          time_if_debug1 ltac:(Raw.ident.prove_eq_indep_types_of_eq_types reflect_base_beq); fail 0 "A goal remains"
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving fold_eta_ident_cps...") in
          time_if_debug1 ident.prove_fold_eta_ident_cps; fail 0 "A goal remains"
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving fold_unify...") in
          time_if_debug1 ident.prove_fold_unify; fail 0 "A goal remains"
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving to_typed_of_typed_ident...") in
          time_if_debug1 ident.prove_to_typed_of_typed_ident; fail 0 "A goal remains"
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving eq_invert_bind_args_unknown...") in
          time_if_debug1 Raw.ident.prove_eq_invert_bind_args_unknown; fail 0 "A goal remains"
        | let __ := Tactics.debug1 ltac:(fun _ => idtac "Proving eq_unify_unknown...") in
          time_if_debug1 ident.prove_eq_unify_unknown; fail 0 "A goal remains" ].
      Ltac prove_package_proofs :=
        idtac;
        lazymatch goal with
        | [ |- ProofGoalType.package_proofs_with_args ?ident_package ]
          => cbv [ProofGoalType.package_proofs_with_args];
             prove_package_proofs_via ident_package
        end.
      Ltac cache_build_package_proofs ident_package package :=
        let name := fresh "ident_package_proofs" in
        cache_proof_with_type_by (@package_proofs _ _ package) ltac:(prove_package_proofs_via ident_package) name.
    End ProofTactic.
  End pattern.
End Compilers.
