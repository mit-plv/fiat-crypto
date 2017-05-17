Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.Wf.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.DestructHead.

Section language.
  Context {base_type_code Name interp_base_type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst}
          {Context : @Context base_type_code Name interp_base_type}.

  Lemma wff_interpf_not_None {ctx : Context} {t} {e : @exprf base_type_code op Name t}
        (Hwf : prop_of_option (wff ctx e))
    : @interpf base_type_code interp_base_type op Name Context interp_op t ctx e <> None.
  Proof using Type.
    revert dependent ctx; induction e;
      repeat first [ progress intros
                   | progress simpl in *
                   | progress unfold option_map, LetIn.Let_In in *
                   | congruence
                   | progress specialize_by_assumption
                   | progress destruct_head' and
                   | progress break_innermost_match_step
                   | progress break_match_hyps
                   | progress autorewrite with push_prop_of_option in *
                   | progress specialize_by auto
                   | solve [ intuition eauto ] ].
  Qed.

  Lemma wf_interp_not_None {ctx : Context} {t} {e : @expr base_type_code op Name t}
        (Hwf : wf ctx e)
        v
    : @interp base_type_code interp_base_type op Name Context interp_op t ctx e v <> None.
  Proof using Type.
    destruct e; unfold interp, wf in *; apply wff_interpf_not_None; auto.
  Qed.
End language.
