Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Util.MSetPositive.Facts.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.HProp.
Require Import Crypto.Language.
Require Import Crypto.LanguageInversion.
Require Import Crypto.GENERATEDIdentifiersWithoutTypes.
Require Import Crypto.Util.FixCoqMistakes.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
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

    Module base.
      Definition eq_subst_default_relax {t evm} : base.subst_default (base.relax t) evm = t.
      Proof.
        induction t; cbn;
          first [ reflexivity
                | apply f_equal
                | apply f_equal2 ];
          assumption.
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

    Module Raw.
      Module ident.
        Import GENERATEDIdentifiersWithoutTypes.Compilers.pattern.Raw.ident.
        Import Datatypes. (* for Some, None, option *)

        Global Instance eq_ident_Decidable : DecidableRel (@eq ident)
          := dec_rel_of_bool_dec_rel ident_beq ident_bl ident_lb.

        Lemma to_typed_invert_bind_args_gen t idc p f
          : @invert_bind_args t idc p = Some f
            -> { pf : t = type_of p f | @to_typed p f = rew [Compilers.ident.ident] pf in idc }.
        Proof.
          cbv [invert_bind_args type_of full_types].
          repeat first [ reflexivity
                       | (exists eq_refl)
                       | progress intros
                       | match goal with
                         | [ H : Some _ = None |- ?P ] => exact (@quick_invert_eq_option _ P _ _ H)
                         | [ H : None = Some _ |- ?P ] => exact (@quick_invert_eq_option _ P _ _ H)
                         end
                       | progress inversion_option
                       | progress subst
                       | break_innermost_match_step
                       | break_innermost_match_hyps_step ].
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

        Lemma invert_bind_args_to_typed p f
          : invert_bind_args (to_typed p f) p = Some f.
        Proof.
          destruct p; cbn in *;
            repeat first [ reflexivity
                         | progress destruct_head'_unit
                         | progress destruct_head'_prod
                         | progress destruct_head' (@PrimitiveSigma.Primitive.sigT) ].
        Qed.

        Lemma is_simple_correct0 p
          : is_simple p = true
            <-> (forall f1 f2, type_of p f1 = type_of p f2).
        Proof.
          destruct p; cbn; split; intro H;
            try solve [ reflexivity | exfalso; discriminate ].
          all: repeat first [ match goal with
                              | [ H : nat -> ?A |- _ ] => specialize (H O)
                              | [ H : unit -> ?A |- _ ] => specialize (H tt)
                              | [ H : forall x y : Datatypes.prod _ _, _ |- _ ] => specialize (fun x1 y1 x2 y2 => H (Datatypes.pair x1 x2) (Datatypes.pair y1 y2)); cbn in H
                              | [ H : forall x y : PrimitiveSigma.Primitive.sigT ?P, _ |- _ ] => specialize (fun x1 y1 x2 y2 => H (PrimitiveSigma.Primitive.existT P x1 x2) (PrimitiveSigma.Primitive.existT P y1 y2)); cbn in H
                              | [ H : forall x y : Compilers.base.type, _ |- _ ] => specialize (fun x y => H (Compilers.base.type.type_base x) (Compilers.base.type.type_base y))
                              | [ H : forall x y : Compilers.base.type.base, _ |- _ ] => specialize (H Compilers.base.type.unit Compilers.base.type.nat); try congruence; cbn in H
                              end
                            | congruence ].
        Qed.

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
      End ident.
    End Raw.

    Module ident.
      Import GENERATEDIdentifiersWithoutTypes.Compilers.pattern.ident.
      Import Datatypes. (* for Some, None, option *)

      Lemma eta_ident_cps_correct T t idc f
        : @eta_ident_cps T t idc f = f t idc.
      Proof. cbv [eta_ident_cps]; break_innermost_match; reflexivity. Qed.

      Lemma unify_to_typed {t t' pidc idc}
        : forall v,
          @unify t t' pidc idc = Some v
          -> forall evm pf,
            rew [Compilers.ident] pf in @to_typed t pidc evm v = idc.
      Proof.
        refine (@option_case_fast _ _ _ _).
        Time destruct pidc, idc; cbv [unify to_typed]; try exact I.
        Time all: break_innermost_match; try exact I.
        Time all: repeat first [ reflexivity
                               | progress intros
                               | progress eliminate_hprop_eq
                               | progress cbn [type.subst_default base.subst_default] in *
                               | progress Compilers.type.inversion_type ].
      Qed.

      Lemma unify_of_typed_ident {t idc}
        : unify (@of_typed_ident t idc) idc <> None.
      Proof.
        destruct idc; cbn; break_innermost_match; exact Some_neq_None.
      Qed.
    End ident.
  End pattern.
End Compilers.
