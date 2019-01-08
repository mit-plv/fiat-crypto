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

        Global Instance eq_ident_Decidable : DecidableRel (@eq ident) := ident_eq_dec.

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

        Lemma is_simple_correct p
          : is_simple p = true
            <-> (forall t1 idc1 t2 idc2, @invert_bind_args t1 idc1 p <> None -> @invert_bind_args t2 idc2 p <> None -> t1 = t2).
        Proof.
          split; intro H;
            [ | specialize (fun f1 f2 => H _ (@to_typed p f1) _ (@to_typed p f2)) ];
            destruct p; cbn in *; try solve [ reflexivity | exfalso; discriminate ];
              repeat first [ progress intros *
                           | match goal with
                             | [ |- ?x = ?x ] => reflexivity
                             | [ |- ?x = ?x -> _ ] => intros _
                             | [ |- None <> None -> ?P ] => exact (@quick_invert_neq_option _ P None None)
                             | [ |- Some _ <> None -> _ ] => intros _
                             | [ |- None <> Some _ -> _ ] => intros _
                             | [ H : forall x y, Some _ <> None -> _ |- _ ] => specialize (fun x y => H x y Some_neq_None)
                             | [ H : nat -> ?A |- _ ] => specialize (H O)
                             | [ H : unit -> ?A |- _ ] => specialize (H tt)
                             | [ H : forall x y : Datatypes.prod _ _, _ |- _ ] => specialize (fun x1 y1 x2 y2 => H (Datatypes.pair x1 x2) (Datatypes.pair y1 y2)); cbn in H
                             | [ H : forall x y : PrimitiveSigma.Primitive.sigT ?P, _ |- _ ] => specialize (fun x1 y1 x2 y2 => H (PrimitiveSigma.Primitive.existT P x1 x2) (PrimitiveSigma.Primitive.existT P y1 y2)); cbn in H
                             | [ H : forall x y : Compilers.base.type, _ |- _ ] => specialize (fun x y => H (Compilers.base.type.type_base x) (Compilers.base.type.type_base y))
                             | [ H : forall x y : Compilers.base.type.base, _ |- _ ] => specialize (H Compilers.base.type.unit Compilers.base.type.nat); try congruence; cbn in H
                             end
                           | break_innermost_match_step
                           | congruence ].
        Qed.
      End ident.
    End Raw.

    Module ident.
      Import GENERATEDIdentifiersWithoutTypes.Compilers.pattern.ident.

      Lemma eta_ident_cps_correct T t idc f
        : @eta_ident_cps T t idc f = f t idc.
      Proof. cbv [eta_ident_cps]; break_innermost_match; reflexivity. Qed.

(*
      Lemma is_simple_strip_types_iff_type_vars_nil {t} idc
        : Raw.ident.is_simple (@strip_types t idc) = true
          <-> type_vars idc = List.nil.
      Proof. destruct idc; cbn; intuition congruence. Qed.
*)

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

      Lemma to_typed_of_typed_ident {t idc}
        : forall v,
          unify (@of_typed_ident t idc) idc = Some v
          -> forall evm pf,
            (rew [Compilers.ident] pf in to_typed (@of_typed_ident t idc) evm v)
            = idc.
      Proof.
        destruct idc.
        all: repeat first [ break_innermost_match_step
                          | break_innermost_match_hyps_step
                          | progress intros
                          | reflexivity
                          | progress subst
                          | progress inversion_option
                          | progress eliminate_hprop_eq
                          | progress fold (@base.subst_default)
                          | progress cbn in *
                          | lazymatch goal with
                            | [ H : context[base.subst_default (base.relax ?t) ?evm] |- _ ]
                              => generalize dependent (base.subst_default (base.relax t) evm)
                            end
                          | progress Compilers.type.inversion_type ].
      Qed.

      (*
      Local Ltac solve_ex_or_eq :=
        lazymatch goal with
        | [ |- ex _ ] => eexists; solve_ex_or_eq
        | [ |- _ /\ _ ] => split; solve_ex_or_eq
        | [ |- _ \/ _ ] => (left + right); solve_ex_or_eq
        | [ |- _ = _ ] => reflexivity || eassumption
        end.
      Lemma type_vars_enough
        : forall t idc k,
          PositiveSet.mem k (pattern.type.collect_vars t) = true
          -> exists v, List.In v (@pattern.ident.type_vars t idc) /\ PositiveSet.mem k (pattern.type.collect_vars v) = true.
      Proof using Type.
        destruct idc; cbn [type.collect_vars ident.type_vars List.In base.collect_vars PositiveSet.mem PositiveSet.empty PositiveSet.union] in *.
        all: repeat first [ match goal with
                            | [ H : true = false |- _ ] => exfalso; apply Bool.diff_true_false, H
                            | [ H : false = true |- _ ] => exfalso; apply Bool.diff_false_true, H
                            | [ H : context[PositiveSet.mem _ (PositiveSet.union _ _)] |- _ ]
                              => rewrite PositiveSetFacts.union_b in H
                            | [ H : context[orb _ _ = true] |- _ ]
                              => rewrite Bool.orb_true_iff in H
                            end
                          | progress cbn [PositiveSet.mem PositiveSet.empty] in *
                          | progress intros
                          | progress destruct_head'_or
                          | solve_ex_or_eq ].
      Qed.
       *)
    End ident.
  End pattern.
End Compilers.
