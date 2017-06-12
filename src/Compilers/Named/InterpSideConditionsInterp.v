Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.InterpSideConditions.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Option.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {Name : Type}
          {interp_base_type : base_type_code -> Type}
          {Context : Context Name interp_base_type}
          {interp_op : forall s d, op s d -> interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d}
          {interped_op_side_conditions : forall s d, op s d -> interp_flat_type interp_base_type s -> pointed_Prop}.

  Local Notation exprf := (@exprf base_type_code op Name).
  Local Notation expr := (@expr base_type_code op Name).

  Lemma snd_interpf_side_conditions_gen_eq {t} {ctx : Context} {e}
    : interpf (t:=t) (ctx:=ctx) (interp_op:=interp_op) e
      = option_map (@snd _ _) (interpf_side_conditions_gen interp_op interped_op_side_conditions ctx e).
  Proof.
    revert ctx; induction e; intros;
      repeat first [ reflexivity
                   | progress subst
                   | progress inversion_option
                   | progress unfold option_map, LetIn.Let_In in *
                   | break_innermost_match_step
                   | break_innermost_match_hyps_step
                   | progress simpl in *
                   | match goal with
                     | [ H : forall ctx, interpf ?e = _, H' : context[interpf ?e] |- _ ]
                       => rewrite H in H'
                     | [ H : forall ctx, interpf ?e = _ |- context[interpf ?e] ]
                       => rewrite H
                     end ].
  Qed.
  Lemma snd_interpf_side_conditions_gen_Some {t} {ctx : Context} {e v}
    : interpf (t:=t) (ctx:=ctx) (interp_op:=interp_op) e = Some v
      <-> option_map (@snd _ _) (interpf_side_conditions_gen interp_op interped_op_side_conditions ctx e) = Some v.
  Proof. rewrite snd_interpf_side_conditions_gen_eq; reflexivity. Qed.
End language.
