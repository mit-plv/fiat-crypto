Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.GENERATEDIdentifiersWithoutTypes.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import GENERATEDIdentifiersWithoutTypes.Compilers.

  Module pattern.
    Import GENERATEDIdentifiersWithoutTypes.Compilers.pattern.
    Module ident.
      Import GENERATEDIdentifiersWithoutTypes.Compilers.pattern.ident.

      Local Lemma quick_invert_eq_option {A} (P : Type) (x y : option A) (H : x = y)
        : match x, y return Type with
          | Some _, None => P
          | None, Some _ => P
          | _, _ => True
          end.
      Proof. subst y; destruct x; constructor. Qed.

      Lemma eta_ident_cps_correct T t idc f
        : @eta_ident_cps T t idc f = f t idc.
      Proof. cbv [eta_ident_cps]; break_innermost_match; reflexivity. Qed.

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

      Lemma try_make_transport_ident_cps_correct P idc1 idc2 T k
        : try_make_transport_ident_cps P idc1 idc2 T k
          = k (match Sumbool.sumbool_of_bool (ident_beq idc1 idc2) with
               | left pf => Some (fun v => rew [P] internal_ident_dec_bl _ _ pf in v)
               | right _ => None
               end).
      Proof.
        destruct (Sumbool.sumbool_of_bool (ident_beq idc1 idc2)) as [pf|pf].
        { generalize (internal_ident_dec_bl idc1 idc2 pf); clear pf; intro; subst idc2; cbn [eq_rect].
          destruct idc1; reflexivity. }
        { destruct idc1, idc2; try reflexivity; solve [ inversion pf ]. }
      Qed.

      Global Instance eq_ident_Decidable : DecidableRel (@eq pattern.ident) := pattern.ident.ident_eq_dec.
    End ident.
  End pattern.
End Compilers.
