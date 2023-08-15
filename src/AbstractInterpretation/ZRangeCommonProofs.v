(* Proofs shared by Wf and Proofs *)
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ZUtil.Morphisms.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.AbstractInterpretation.ZRange.

Module Compilers.
  Import AbstractInterpretation.ZRange.Compilers.
  Export ZRange.Settings.

  Module ZRange.
    Module ident.
      Module option.
        Section interp_related.
          Context {shiftr_avoid_uint1 : shiftr_avoid_uint1_opt}
                  (assume_cast_truncates : bool).
          Global Instance interp_Proper {t} : Proper (eq ==> @type.eqv t) (ZRange.ident.option.interp assume_cast_truncates).
          Proof using Type.
            intros idc idc' ?; subst idc'.
            cbv [type.related respectful type.interp]; destruct idc;
              repeat first [ reflexivity
                           | progress subst
                           | progress cbn [ZRange.type.base.option.interp ZRange.type.base.interp base.interp base.base_interp Crypto.Util.Option.bind] in *
                           | progress cbv [Crypto.Util.Option.bind]
                           | intro
                           | progress destruct_head'_prod
                           | progress destruct_head'_bool
                           | progress destruct_head' option
                           | progress inversion_option
                           | discriminate
                           | solve [ eauto ]
                           | apply NatUtil.nat_rect_Proper_nondep
                           | apply ListUtil.list_rect_Proper
                           | apply ListUtil.list_rect_arrow_Proper
                           | apply ListUtil.list_case_Proper
                           | apply ListUtil.pointwise_map
                           | apply ListUtil.fold_right_Proper
                           | apply ListUtil.update_nth_Proper
                           | apply (@nat_rect_Proper_nondep_gen (_ -> _) (eq ==> eq)%signature)
                           | cbn; apply (f_equal (@Some _))
                           | progress cbn [ZRange.ident.option.interp]
                           | progress cbv [zrange_rect]
                           | apply (f_equal2 pair)
                           | break_innermost_match_step
                           | match goal with
                             | [ H : _ |- _ ] => erewrite H by (eauto; (eassumption || reflexivity))
                             | [ H : forall x y, x = y -> _ |- _ ] => specialize (fun x => H x x eq_refl)
                             | [ H : forall x, ?f x = ?g x, H1 : ?f ?y = _, H2 : ?g ?y = _ |- _ ]
                               => specialize (H y); rewrite H1, H2 in H
                             end ].
          Qed.
        End interp_related.
      End option.
    End ident.
  End ZRange.
End Compilers.
