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
Require Import Crypto.Language.
Require Import Crypto.LanguageInversion.
Require Import Crypto.GENERATEDIdentifiersWithoutTypes.
Require Import Crypto.Util.FixCoqMistakes.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import GENERATEDIdentifiersWithoutTypes.Compilers.

  Module pattern.
    Import GENERATEDIdentifiersWithoutTypes.Compilers.pattern.
    Import Datatypes. (* for Some, None, option *)

    Local Lemma quick_invert_eq_option {A} (P : Type) (x y : option A) (H : x = y)
      : match x, y return Type with
        | Some _, None => P
        | None, Some _ => P
        | _, _ => True
        end.
    Proof. subst y; destruct x; constructor. Qed.

    Local Lemma quick_invert_neq_option {A} (P : Type) (x y : option A) (H : x <> y)
      : match x, y return Type with
        | Some _, None => True
        | None, Some _ => True
        | None, None => P
        | Some x, Some y => x <> y
        end.
    Proof. destruct x, y; try congruence; trivial. Qed.

    Local Lemma Some_neq_None {A x} : @Some A x <> None. Proof. congruence. Qed.

    Local Lemma None_neq_Some_fast {T} {P : T -> Prop} {v} : @None T = Some v -> P v.
    Proof. congruence. Qed.

    Local Lemma Some_eq_Some_subst_fast {T v1} {P : T -> Prop}
      : P v1 -> forall v2, Some v1 = Some v2 -> P v2.
    Proof. congruence. Qed.

    Local Lemma option_case_fast {T} {P : T -> Prop} {v'}
      : match v' with
        | Some v' => P v'
        | None => True
        end
        -> forall v,
          v' = Some v
          -> P v.
    Proof. destruct v'; congruence. Qed.

    Local Notation type_of_list := (List.fold_right (fun A B => prod A B) unit).
    Fixpoint eta_type_of_list {ls} : type_of_list ls -> type_of_list ls
      := match ls with
         | nil => fun _ => tt
         | cons x xs => fun v => (fst v, @eta_type_of_list xs (snd v))
         end.
    Lemma eq_eta_type_of_list ls v
      : @eta_type_of_list ls v = v.
    Proof. induction ls; destruct v; cbn; reflexivity + apply f_equal; auto with nocore. Defined.

    Module base.
      Fixpoint eq_subst_default_relax {t evm} : base.subst_default (base.relax t) evm = t.
      Proof.
        destruct t; cbn;
          first [ reflexivity
                | apply f_equal
                | apply f_equal2 ];
          auto with nocore.
      Defined.
    End base.

    Module type.
      Definition eq_subst_default_relax {t evm} : type.subst_default (type.relax t) evm = t.
      Proof.
        induction t; cbn;
          first [ apply f_equal, base.eq_subst_default_relax
                | apply f_equal2; assumption ].
      Defined.
    End type.

    Local Lemma fast_sig_forall1_eq_ind {A T g}
          (P : { f : forall a : A, T a | forall a, f a = g a } -> Type)
      : (forall x : forall a, { f : T a | f = g a },
            P (exist (fun f => forall a, f a = g a)
                     (fun a => proj1_sig (x a))
                     (fun a => proj2_sig (x a))))
        -> forall x, P x.
    Proof.
      intros H [x p]; refine (H (fun a => exist _ (x a) (p a))).
    Defined.

    Local Lemma fast_sig_forall2_eq_ind {A B T g}
          (P : { f : forall (a : A) (b : B a), T a b | forall a b, f a b = g a b } -> Type)
      : (forall x : forall a b, { f : T a b | f = g a b },
            P (exist (fun f => forall a b, f a b = g a b)
                     (fun a b => proj1_sig (x a b))
                     (fun a b => proj2_sig (x a b))))
        -> forall x, P x.
    Proof.
      intros H [x p]; refine (H (fun a b => exist _ (x a b) (p a b))).
    Defined.

    Local Ltac my_generalize_dependent_intros v :=
      let k := fresh in
      set (k := v) in *; clearbody k.
    Ltac my_prerevert_dependent H := (* apparently this is faster *)
      move H at bottom;
      repeat lazymatch goal with H' : _ |- _ => tryif constr_eq H H' then fail else revert H' end.
    Local Ltac generalize_proj1_sig_step :=
      match goal with
      | [ |- context[@proj1_sig _ (fun x => forall y, _ = _) ?p] ]
        => tryif is_var p then fail else my_generalize_dependent_intros p
      | [ |- context[@proj1_sig _ (fun x => forall y z, _ = _) ?p] ]
        => tryif is_var p then fail else my_generalize_dependent_intros p
      | [ H : context[@proj1_sig _ (fun x => forall y, _ = _) ?p] |- _ ]
        => tryif is_var p then fail else my_generalize_dependent_intros p
      | [ H : context[@proj1_sig _ (fun x => forall y z, _ = _) ?p] |- _ ]
        => tryif is_var p then fail else my_generalize_dependent_intros p
      end.
    Local Ltac specialize_sig_step :=
      match goal with
      | [ H : { f : forall (a : ?A), @?T a | forall a', f a' = @?g a' } |- _ ]
        => my_prerevert_dependent H;
           revert H;
           let P := lazymatch goal with |- forall x, @?P x => P end in
           refine (@fast_sig_forall1_eq_ind A T g P _);
           cbn [proj1_sig proj2_sig]; intros
      | [ H : { f : forall (a : ?A) (b : @?B a), @?T a b | forall a' b', f a' b' = @?g a' b' } |- _ ]
        => my_prerevert_dependent H;
           revert H;
           let P := lazymatch goal with |- forall x, @?P x => P end in
           refine (@fast_sig_forall2_eq_ind A B T g P _);
           cbn [proj1_sig proj2_sig]; intros
      end.
    Local Ltac rewrite_sig_step :=
      match goal with
      | [ p : forall t idc, sig (fun y => y = _) |- _ ]
        => lazymatch goal with
           | [ H : context[proj1_sig (p ?t ?idc)] |- _ ] => destruct (p t idc)
           | [ |- context[proj1_sig (p ?t ?idc)] ] => destruct (p t idc)
           end;
           subst; cbn [proj1_sig proj2_sig] in *; try clear p
      | [ p : forall idc, sig (fun y => y = _) |- _ ]
        => lazymatch goal with
           | [ H : context[proj1_sig (p ?idc)] |- _ ] => destruct (p idc)
           | [ |- context[proj1_sig (p ?idc)] ] => destruct (p idc)
           end;
           subst; cbn [proj1_sig proj2_sig] in *; try clear p
      | [ p : sig (fun y => y = _) |- _ ]
        => destruct p; subst; cbn [proj1_sig proj2_sig] in *
      end.
    Local Ltac clear_useless_step :=
      match goal with
      | [ H : forall t, { f : _ | f = _ } |- _ ] => clear H
      | [ H : forall t idc, { f : _ | f = _ } |- _ ] => clear H
      end.

    Local Ltac do_rew_proj2_sig :=
      repeat first [ progress cbn [eq_rect eq_sym] in *
                   | progress intros
                   | clear_useless_step
                   | rewrite_sig_step
                   | specialize_sig_step
                   | generalize_proj1_sig_step ].

    Local Notation iffT x y := ((x -> y) * (y -> x))%type.

    Module Raw.
      Module ident.
        Import GENERATEDIdentifiersWithoutTypes.Compilers.pattern.Generate.Raw.ident.
        Import GENERATEDIdentifiersWithoutTypes.Compilers.pattern.Raw.ident.
        Import Datatypes. (* for Some, None, option *)

        Global Instance eq_ident_Decidable : DecidableRel (@eq ident)
          := dec_rel_of_bool_dec_rel ident_beq ident_bl ident_lb.

        Lemma is_simple_correct0 p
          : is_simple p = true
            <-> (forall f1 f2, type_of p f1 = type_of p f2).
        Proof.
          destruct p; cbn; cbv -[Datatypes.fst Datatypes.snd projT1 projT2] in *; split; intro H;
            try solve [ reflexivity | exfalso; discriminate ].
          all: repeat first [ match goal with
                              | [ H : nat -> ?A |- _ ] => specialize (H O)
                              | [ H : unit -> ?A |- _ ] => specialize (H tt)
                              | [ H : forall x y : PrimitiveProd.Primitive.prod _ _, _ |- _ ] => specialize (fun x1 y1 x2 y2 => H (PrimitiveProd.Primitive.pair x1 x2) (PrimitiveProd.Primitive.pair y1 y2)); cbn in H
                              | [ H : forall x y : Datatypes.prod _ _, _ |- _ ] => specialize (fun x1 y1 x2 y2 => H (Datatypes.pair x1 x2) (Datatypes.pair y1 y2)); cbn in H
                              | [ H : forall x y : PrimitiveSigma.Primitive.sigT ?P, _ |- _ ] => specialize (fun x1 y1 x2 y2 => H (PrimitiveSigma.Primitive.existT P x1 x2) (PrimitiveSigma.Primitive.existT P y1 y2)); cbn in H
                              | [ H : forall x y : Compilers.base.type, _ |- _ ] => specialize (fun x y => H (Compilers.base.type.type_base x) (Compilers.base.type.type_base y))
                              | [ H : forall x y : Compilers.base.type.base, _ |- _ ] => specialize (H Compilers.base.type.unit Compilers.base.type.nat); try congruence; cbn in H
                              end
                            | congruence ].
        Qed.

        Lemma invert_bind_args_to_typed p f
          : invert_bind_args (to_typed p f) p = Some f.
        Proof.
          destruct p; cbv in *;
            destruct_head' (@Primitive.sigT); destruct_head'_prod; destruct_head'_unit; reflexivity.
        Qed.

        Lemma fold_invert_bind_args : @invert_bind_args = @folded_invert_bind_args.
        Proof. reflexivity. Qed.

        Lemma split_ident_to_ident ridc x y z
          : PrimitiveSigma.Primitive.projT1 (@split_ident_gen _ (to_ident (ident_infos_of ridc) x y z))
            = ridc.
        Proof. destruct ridc; reflexivity. Defined.

        Lemma eq_indep_types_of_eq_types (ridc : ident)
              (dt1 dt2 : type_of_list (dep_types (ident_infos_of ridc)))
              (idt1 idt2 : type_of_list_of_kind (indep_types (ident_infos_of ridc)))
              (Hty : to_type (ident_infos_of ridc) dt1 idt1 = to_type (ident_infos_of ridc) dt2 idt2)
          : idt1 = idt2.
        Proof.
          destruct ridc; cbv in *;
            destruct_head'_prod; destruct_head'_unit; try reflexivity;
              type.inversion_type; reflexivity.
        Qed.

        Lemma ident_transport_opt_correct P x y v
          : (@ident_transport_opt P x y v <> None -> x = y)
            * (forall pf : x = y, @ident_transport_opt P x y v = Some (rew pf in v)).
        Proof.
          cbv [ident_transport_opt].
          generalize (ident_beq_if x y), (ident_lb x y); destruct (ident_beq x y);
            intros; subst; split; try congruence; intros; subst;
              try intuition congruence.
          eliminate_hprop_eq; reflexivity.
        Qed.

        Lemma ident_transport_opt_correct' P x y v
          : @ident_transport_opt P x y v <> None
            -> { pf : x = y
               | @ident_transport_opt P x y v = Some (rew pf in v) }.
        Proof.
          intro H; apply ident_transport_opt_correct in H; exists H; apply ident_transport_opt_correct.
        Qed.

        Lemma ident_transport_opt_correct'' P x y v v'
          : @ident_transport_opt P x y v = Some v'
            -> { pf : x = y
               | v' = rew pf in v }.
        Proof.
          intro H.
          pose proof (@ident_transport_opt_correct' P x y v) as H'.
          rewrite H in H'.
          specialize (H' ltac:(congruence)).
          destruct H'; inversion_option; subst; (exists eq_refl); reflexivity.
        Qed.

        Lemma to_typed_invert_bind_args_gen t idc p f
          : @invert_bind_args t idc p = Some f
            -> { pf : t = type_of p f | @to_typed p f = rew [Compilers.ident.ident] pf in idc }.
        Proof.
          rewrite fold_invert_bind_args.
          cbv [folded_invert_bind_args type_of full_types to_typed] in *.
          do_rew_proj2_sig.
          all: repeat first [ match goal with
                              | [ |- context[@split_ident_gen ?t ?idc] ]
                                => destruct (@split_ident_gen t idc)
                              | [ H : context[@split_ident_gen ?t ?idc] |- _ ]
                                => destruct (@split_ident_gen t idc)
                              | [ H : Some _ = @ident_transport_opt _ _ _ _ |- _ ] => symmetry in H
                              | [ H : None = @ident_transport_opt _ _ _ _ |- _ ] => symmetry in H
                              | [ H : @ident_transport_opt ?P ?x ?y ?v = Some _ |- _ ]
                                => apply (@ident_transport_opt_correct'' P x y v) in H; destruct H
                              | [ H : @ident_transport_opt ?P ?x ?y ?v = None |- _ ]
                                => repeat intro; unshelve (erewrite (Datatypes.snd (ident_transport_opt_correct P x y v)) in H; inversion_option); []
                              end
                            | progress destruct_head'_sig
                            | progress subst
                            | progress cbv [eq_rect assemble_ident] in *
                            | (exists eq_refl)
                            | reflexivity
                            | break_innermost_match_step ].
        Qed.

        Lemma type_of_invert_bind_args t idc p f
          : @invert_bind_args t idc p = Some f -> t = type_of p f.
        Proof.
          intro pf; exact (proj1_sig (@to_typed_invert_bind_args_gen t idc p f pf)).
        Defined.

        Lemma to_typed_invert_bind_args t idc p f (pf : @invert_bind_args t idc p = Some f)
          : @to_typed p f = rew [Compilers.ident.ident] @type_of_invert_bind_args t idc p f pf in idc.
        Proof.
          exact (proj2_sig (@to_typed_invert_bind_args_gen t idc p f pf)).
        Defined.

        Lemma is_simple_correct p
          : is_simple p = true
            <-> (forall t1 idc1 t2 idc2, @invert_bind_args t1 idc1 p <> None -> @invert_bind_args t2 idc2 p <> None -> t1 = t2).
        Proof.
          rewrite is_simple_correct0; split; intro H.
          { intros t1 idc1 t2 idc2 H1 H2.
            destruct (invert_bind_args idc1 p) eqn:?, (invert_bind_args idc2 p) eqn:?; try congruence.
            erewrite (type_of_invert_bind_args t1), (type_of_invert_bind_args t2) by eassumption.
            apply H. }
          { intros f1 f2.
            apply (H _ (to_typed p f1) _ (to_typed p f2));
              rewrite invert_bind_args_to_typed; congruence. }
        Qed.

        Lemma try_unify_split_args_Some_correct ridc1 ridc2 dt1 dt2 (*idt1 idt2*) args v
          : iffT
              (@try_unify_split_args ridc1 ridc2 dt1 dt2 (*idt1 idt2*) args = Some v)
              { pf : existT _ ridc1 dt1 = existT _ ridc2 dt2 :> { ridc : _ & type_of_list (dep_types (preinfos (ident_infos_of ridc))) }
              | (rew [fun rdt => type_of_list (indep_args _ (projT2 rdt))] pf in
                    (args : type_of_list (indep_args _ (projT2 (existT _ ridc1 dt1)))))
                = v
                (*/\ (rew [fun ridc => type_of_list_of_kind (indep_types (preinfos (ident_infos_of ridc)))] f_equal (@projT1 _ _) pf in
                       idt1)
                   = idt2*) }.
        Proof.
          pose proof (dep_types_dec_transparent (ident_infos_of ridc1) : DecidableRel eq).
          cbv [try_unify_split_args].
          generalize (Raw.ident.ident_beq_if ridc1 ridc2).
          generalize (Raw.ident.ident_lb ridc1 ridc2).
          destruct (Raw.ident.ident_beq ridc1 ridc2);
            [
            | split;
              [ congruence
              | intros; destruct_head'_sig; Sigma.inversion_sigma; subst; specialize_by reflexivity; congruence ] ].
          intros ? ?; subst.
          (*pose proof (@Reflect.reflect_bool _ _ (indep_types_reflect _ idt1 idt2)) as H'.
          pose proof (indep_types_reflect _ idt1 idt2) as H''.*)
          repeat first [ break_innermost_match_step
                       | apply pair
                       | progress intros
                       | progress inversion_option
                       | progress subst
                       | progress specialize_by reflexivity
                       | apply conj
                       | progress destruct_head'_and
                       | progress destruct_head'_sig
                       | progress Sigma.inversion_sigma
                       | progress cbn [eq_rect eq_sym eq_rect_r Sigma.path_sigT Sigma.path_sigT_uncurried f_equal] in *
                       | (exists eq_refl)
                       | reflexivity
                       | progress eliminate_hprop_eq
                       | match goal with
                         | [ H : Bool.reflect _ false |- _ ] => inversion H; clear H
                         end
                       | congruence ].
        Qed.

        Lemma try_unify_split_args_None_correct ridc1 ridc2 dt1 dt2 (*idt1 idt2*) args
          : @try_unify_split_args ridc1 ridc2 dt1 dt2 (*idt1 idt2*) args = None
            -> forall pf : existT _ ridc1 dt1 = existT _ ridc2 dt2 :> { ridc : _ & type_of_list (dep_types (preinfos (ident_infos_of ridc))) },
              (*(rew [fun ridc => type_of_list_of_kind (indep_types (preinfos (ident_infos_of ridc)))] f_equal (@projT1 _ _) pf in
                  idt1)
              = idt2
              ->*) False.
        Proof.
          intros H pf (*pf'*).
          pose proof (fun v => snd (@try_unify_split_args_Some_correct ridc1 ridc2 dt1 dt2 (*idt1 idt2*) args v)) as H'.
          rewrite H in H'.
          specialize (H' _ (exist _ pf eq_refl(*(conj eq_refl pf')*))); cbv beta in *.
          congruence.
        Qed.
      End ident.
    End Raw.

    Module ident.
      Import GENERATEDIdentifiersWithoutTypes.Compilers.pattern.Generate.
      Import GENERATEDIdentifiersWithoutTypes.Compilers.pattern.Generate.ident.
      Import GENERATEDIdentifiersWithoutTypes.Compilers.pattern.ident.
      Import Datatypes. (* for Some, None, option *)

      Lemma fold_eta_ident_cps T t idc f : @eta_ident_cps T t idc f = proj1_sig (@pattern.eta_ident_cps_gen (fun t _ => T t) f) t idc.
      Proof. reflexivity. Qed.

      Lemma fold_unify : @unify = @folded_unify.
      Proof. vm_cast_no_check (eq_refl (@unify)). Qed.

      Lemma to_typed_of_typed_ident t idc evm
        : (rew [Compilers.ident] type.eq_subst_default_relax in
              @to_typed _ (@of_typed_ident t idc) evm (@arg_types_of_typed_ident t idc))
          = idc.
      Proof.
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
      Qed.

      Lemma eq_indep_types_of_eq_types {t1 t2} {idc1 : ident t1} {idc2 : ident t2} evm1 evm2
            (Hty : type.subst_default t1 evm1 = type.subst_default t2 evm2)
            (pf : Primitive.projT1 (@split_types_subst_default _ idc1 evm1)
                  = Primitive.projT1 (@split_types_subst_default _ idc2 evm2))
        : Datatypes.snd (Primitive.projT2 (@split_types_subst_default _ idc1 evm1))
          = rew <- [fun r => full_type_of_list_of_kind (Raw.ident.indep_types (Raw.ident.preinfos (Raw.ident.ident_infos_of r)))] pf in
          Datatypes.snd (Primitive.projT2 (@split_types_subst_default _ idc2 evm2)).
      Proof.
        pose proof (@to_type_split_types_subst_default_eq _ idc1 evm1).
        pose proof (@to_type_split_types_subst_default_eq _ idc2 evm2).
        generalize dependent (type.subst_default t1 evm1);
          generalize dependent (type.subst_default t2 evm2); intros; subst.
        cbv [split_types_subst_default] in *; cbn [Primitive.projT1 Primitive.projT2 fst snd] in *.
        destruct (split_types _ idc1), (split_types _ idc2);
          destruct_head'_prod;
          cbn [Primitive.projT1 Primitive.projT2 fst snd] in *;
          subst; cbn [eq_rect eq_rect_r eq_sym].
        eapply Raw.ident.eq_indep_types_of_eq_types; eassumption.
      Qed.

      Lemma eta_ident_cps_correct T t idc f
        : @eta_ident_cps T t idc f = f t idc.
      Proof. rewrite fold_eta_ident_cps; apply (proj2_sig (@pattern.eta_ident_cps_gen _ f)). Qed.

      Lemma unify_to_typed {t t' pidc idc}
        : forall v,
          @unify t t' pidc idc = Some v
          -> forall evm pf,
              rew [Compilers.ident] pf in @to_typed t pidc evm v = idc.
      Proof.
        intros v H evm pf; subst t'; cbn [eq_rect].
        pose proof (@eq_indep_types_of_eq_types _ _ (@of_typed_ident _ idc) pidc evm evm type.eq_subst_default_relax) as H'.
        revert v H.
        set (idc' := idc) at 1; rewrite <- (@to_typed_of_typed_ident _ idc evm); subst idc'.
        rewrite fold_unify.
        cbv [folded_unify arg_types Raw.ident.assemble_ident];
          cbn [Primitive.projT1 Primitive.projT2].
        intros v.
        Time do_rew_proj2_sig.
        Time
        repeat first [ progress cbn [eq_rect eq_sym] in *
                     | progress cbn [Primitive.projT1 Primitive.projT2 fst snd] in *
                     | clear_useless_step
                     | rewrite_sig_step
                     | specialize_sig_step
                     | generalize_proj1_sig_step
                     | progress cbv [to_typed Raw.ident.assemble_ident] in *
                     | match goal with
                       | [ |- context[@arg_types_of_typed_ident _ ?idc] ]
                         => is_var idc;
                            generalize dependent (@arg_types_of_typed_ident _ idc);
                            generalize dependent (@of_typed_ident _ idc);
                            clear idc;
                            intros
                       end
                     | progress cbv [arg_types prearg_types] in * ].
        repeat first [ progress cbn [Primitive.projT1 Primitive.projT2 fst snd] in *
                     | match goal with
                       | [ |- context[(rew [fun x : ?T => @?A x -> @?B x] ?pf in ?f) ?y] ]
                         => rewrite (@push_rew_fun_dep T A B _ _ pf f y)
                       | [ |- context[rew [fun _ : ?T => ?P] ?pf in ?f] ]
                         => rewrite (@Equality.transport_const T P _ _ pf f)
                       | [ |- context[(rew [?P] ?pf in ?x) = ?y] ]
                         => rewrite <- (@eq_rew_moveR _ P _ _ pf x y)
                       | [ |- context[rew [fun x : ?T => option (@?P x)] ?pf in Some ?v] ]
                         => rewrite <- (@commute_eq_rect _ P (fun x => option (P x)) (fun _ => Some) _ _ pf v)
                       | [ |- iffT (Raw.ident.try_unify_split_args _ (*_ _*) = Some _) _ ]
                         => eapply iffT_trans; [ apply Raw.ident.try_unify_split_args_Some_correct | ]
                       | [ H : pattern.Raw.ident.try_unify_split_args _ (*_ _*) = Some _ |- _ ]
                         => apply Raw.ident.try_unify_split_args_Some_correct in H
                       | [ |- context[to_type_split_types_subst_default_eq ?t ?i ?evm] ]
                         => generalize (to_type_split_types_subst_default_eq t i evm); intro
                       end
                     | progress cbv [eq_rect_r] in *
                     | progress cbv [split_types_subst_default] in *
                     | progress cbn [eq_rect] in *
                     | progress destruct_head'_prod
                     | progress subst
                     | match goal with
                       | [ |- context[existT _ (Primitive.projT1 (split_types ?t ?x)) _ = _] ]
                         => destruct (split_types t x); clear x
                       | [ H : context[existT _ (Primitive.projT1 (split_types ?t ?x)) _ = _] |- _ ]
                         => destruct (split_types t x); clear x
                       | [ |- context[@eq_trans (type.type ?base_type) ?x ?y ?z ?pf1 ?pf2] ]
                         => generalize (@eq_trans (type.type base_type) x y z pf1 pf2); intro
                       end
                     | rewrite <- !eq_trans_rew_distr ].
        Time
          all:
          repeat first [ apply pair
                       | progress cbn [eq_rect eq_rect_r eq_sym Sigma.path_sigT Sigma.path_sigT_uncurried f_equal] in *
                       | progress intros
                       | progress destruct_head'_sig
                       | progress destruct_head'_ex
                       | progress destruct_head'_and
                       | progress Sigma.inversion_sigma
                       | progress subst
                       | match goal with
                         | [ H : forall pf : ?x = ?x, _ |- _ ] => specialize (H eq_refl)
                         | [ H : lift_type_of_list_map _ ?f = _ |- _ ]
                           => is_var f; symmetry in H; destruct H; clear f
                         | [ H : context[@eq_trans (type.type ?base_type) ?x ?y ?z ?pf1 ?pf2] |- _ ]
                           => generalize dependent (@eq_trans (type.type base_type) x y z pf1 pf2); intros
                         | [ H : context[type.subst_default (type.relax _) _] |- _ ]
                           => rewrite type.eq_subst_default_relax in H
                         | [ H : ?x = ?x |- _ ] => clear H
                         | [ H : type.subst_default ?t ?evm = type.subst_default ?t ?evm'
                             |- context[lift_type_of_list_map (@subst_default_kind_of_type ?evm) (snd (Primitive.projT2 (split_types _ ?idc)))] ]
                           => let H' := fresh in
                              pose proof (@eq_indep_types_of_eq_types t idc idc evm evm' H eq_refl) as H';
                                cbv [split_types_subst_default] in H';
                                cbn [eq_rect_r eq_rect eq_sym Primitive.projT2 Primitive.projT1 fst snd] in H';
                                rewrite H' in *; clear H';
                                  generalize dependent (type.subst_default t evm); intros; subst; clear evm
                         end
                       | rewrite <- !eq_trans_rew_distr in *
                       | eexists; rewrite <- !eq_trans_rew_distr, concat_pV
                       | match goal with
                         | [ H : _ = type.subst_default ?t ?evm |- _ ]
                           => is_var t; is_var evm;
                                generalize dependent (type.subst_default t evm); intros
                         end
                       | progress eliminate_hprop_eq ].
      Qed.

      Lemma unify_of_typed_ident {t idc}
        : unify (@of_typed_ident t idc) idc <> None.
      Proof.
        rewrite fold_unify.
        cbv [folded_unify].
        Time do_rew_proj2_sig.
        generalize (of_typed_ident idc), (arg_types_of_typed_ident idc); intros.
        repeat first [ progress rewrite ?push_rew_fun_dep, ?transport_const
                     | progress cbv [eq_rect_r] in *
                     | intro
                     | match goal with
                       | [ H : (rew [?P] ?pf in ?v) = ?v2 |- _ ] => apply (@rew_r_moveL _ P _ _ pf v v2) in H
                       | [ H : context[rew [fun x : ?T => option (@?P x)] ?pf in @None ?K] |- _ ]
                         => let H' := fresh in
                            pose proof (@commute_eq_rect _ (fun _ => True) (fun x => option (P x)) (fun _ _ => @None _) _ _ pf I) as H';
                            setoid_rewrite <- H' in H;
                            clear H'
                       | [ H : @pattern.Raw.ident.try_unify_split_args ?a ?b ?c ?d ?e = None |- _ ]
                         => let H' := fresh in
                            pose proof (@Raw.ident.try_unify_split_args_None_correct a b c d e H) as H';
                            clear H
                       | [ H : forall pf : _ = _, _ |- _ ] => specialize (H eq_refl)
                       end
                     | assumption ].
      Qed.
    End ident.
  End pattern.
End Compilers.
