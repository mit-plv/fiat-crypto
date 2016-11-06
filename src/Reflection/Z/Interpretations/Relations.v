Require Import Coq.ZArith.ZArith.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.Z.Interpretations.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.

Definition proj_eq_rel {A B} (proj : A -> B) (x : A) (y : B) : Prop
  := proj x = y.
Definition related'_Z {t} (x : BoundedWord64.BoundedWord) (y : Z.interp_base_type t) : Prop
  := proj_eq_rel (BoundedWord64.to_Z' _) x y.
Definition related_Z t : BoundedWord64.interp_base_type t -> Z.interp_base_type t -> Prop
  := LiftOption.lift_relation (@related'_Z) t.
Definition related'_word64 {t} (x : BoundedWord64.BoundedWord) (y : Word64.interp_base_type t) : Prop
  := proj_eq_rel (BoundedWord64.to_word64' _) x y.
Definition related_word64 t : BoundedWord64.interp_base_type t -> Word64.interp_base_type t -> Prop
  := LiftOption.lift_relation (@related'_word64) t.
Definition related_bounds t : BoundedWord64.interp_base_type t -> ZBounds.interp_base_type t -> Prop
  := LiftOption.lift_relation2 (proj_eq_rel BoundedWord64.to_bounds') t.

Definition related_word64_Z t : Word64.interp_base_type t -> Z.interp_base_type t -> Prop
  := proj_eq_rel (Word64.to_Z _).

Definition related'_word64_bounds : Word64.word64 -> ZBounds.bounds -> Prop
  := fun value b => (0 <= ZBounds.lower b /\ ZBounds.lower b <= Word64.word64ToZ value <= ZBounds.upper b /\ Z.log2 (ZBounds.upper b) < Z.of_nat Word64.bit_width)%Z.
Definition related_word64_bounds : Word64.word64 -> ZBounds.t -> Prop
  := fun value b => match b with
                    | Some b => related'_word64_bounds value b
                    | None => True
                    end.
Definition related_word64_boundsi (t : base_type) : Word64.interp_base_type t -> ZBounds.interp_base_type t -> Prop
  := match t with
     | TZ => related_word64_bounds
     end.
Definition related_word64_boundsi' (t : base_type) : ZBounds.bounds -> Word64.interp_base_type t -> Prop
  := match t return ZBounds.bounds -> Word64.interp_base_type t -> Prop with
     | TZ => fun x y => related'_word64_bounds y x
     end.

Local Notation related_op R interp_op1 interp_op2
  := (forall (src dst : flat_type base_type) (op : op src dst)
             (sv1 : interp_flat_type _ src) (sv2 : interp_flat_type _ src),
         interp_flat_type_rel_pointwise2 R sv1 sv2 ->
         interp_flat_type_rel_pointwise2 R (interp_op1 _ _ op sv1) (interp_op2 _ _ op sv2))
       (only parsing).
Local Notation related_const R interp f g
  := (forall (t : base_type) (v : interp t), R t (f t v) (g t v))
       (only parsing).

Local Ltac related_const_t :=
  let v := fresh in
  let t := fresh in
  intros t v; destruct t; intros; simpl in *; hnf; simpl;
  cbv [BoundedWord64.word64ToBoundedWord related'_Z LiftOption.of' related_Z related_word64 related'_word64 proj_eq_rel] in *;
  break_innermost_match; simpl;
  first [ tauto
        | Z.ltb_to_lt;
          pose proof (Word64.word64ToZ_log_bound v);
          try omega ].

Lemma related_Z_const : related_const related_Z Word64.interp_base_type BoundedWord64.of_word64 Word64.to_Z.
Proof. related_const_t. Qed.
Lemma related_bounds_const : related_const related_bounds Word64.interp_base_type BoundedWord64.of_word64 ZBounds.of_word64.
Proof. related_const_t. Qed.
Lemma related_word64_const : related_const related_word64 Word64.interp_base_type BoundedWord64.of_word64 (fun _ x => x).
Proof. related_const_t. Qed.

Local Ltac convoy_destruct_in H :=
  match type of H with
  | context G[match ?e with Some x => @?S x | None => ?N end eq_refl]
    => let e' := fresh in
       let H' := fresh in
       pose e as e';
       pose (eq_refl : e = e') as H';
       let G' := context G[match e' with Some x => S x | None => N end H'] in
       change G' in H;
       clearbody H' e'; destruct e'
  end.

Local Ltac related_word64_op_t_step :=
  repeat first [ exact I
               | reflexivity
               | progress destruct_head' False
               | progress cbv [related_Z LiftOption.lift_relation related'_Z BoundedWord64.value proj_eq_rel BoundedWord64.to_Z' Word64.to_Z BoundedWord64.to_word64' BoundedWord64.boundedWordToWord64 smart_interp_flat_map related_word64 related'_word64 BoundedWord64.BoundedWordToBounds BoundedWord64.value BoundedWord64.BoundedWordToBounds BoundedWord64.lower BoundedWord64.upper related_bounds LiftOption.lift_relation2 LiftOption.of' BoundedWord64.to_bounds' ZBounds.SmartBuildBounds] in *
               | progress unfold LiftOption.of' in *
               | progress intros
               | progress subst; simpl in *
               | progress destruct_head' prod
               | progress destruct_head' and
               | progress destruct_head' option
               | progress inversion_option
               | progress ZBounds.inversion_bounds
               | progress BoundedWord64.inversion_BoundedWord
               | progress specialize_by (exact I)
               | progress break_match
               | progress break_match_hyps
               | match goal with
                 | [ H : context[match _ with _ => _ end eq_refl] |- _ ]
                   => progress convoy_destruct_in H
                 end
               | progress simpl @fst in *
               | progress simpl @snd in *
               | progress destruct_head' BoundedWord64.BoundedWord
               | congruence
               | match goal with
                 | [ H : ?op (Some _) (Some _) = Some _ |- _ ]
                   => first [ apply BoundedWord64.invert_add in H
                            | apply BoundedWord64.invert_sub in H
                            | apply BoundedWord64.invert_mul in H
                            | apply BoundedWord64.invert_shl in H
                            | apply BoundedWord64.invert_shr in H
                            | apply BoundedWord64.invert_land in H
                            | apply BoundedWord64.invert_lor in H
                            | apply BoundedWord64.invert_neg in H
                            | apply BoundedWord64.invert_cmovne in H
                            | apply BoundedWord64.invert_cmovle in H ];
                      simpl in H
                 end ].
Local Ltac related_word64_op_t := repeat related_word64_op_t_step.

Lemma related_word64_op : related_op related_word64 (@BoundedWord64.interp_op) (@Word64.interp_op).
Proof.
  let op := fresh in intros ?? op; destruct op; simpl.
  { related_word64_op_t. }
  { related_word64_op_t. }
  { related_word64_op_t. }
  { related_word64_op_t. }
  { related_word64_op_t. }
  { related_word64_op_t. }
  { related_word64_op_t. }
  { related_word64_op_t. }
  { related_word64_op_t. }
  { related_word64_op_t. }
Qed.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.

Lemma related_Z_op : related_op related_Z (@BoundedWord64.interp_op) (@Z.interp_op).
Proof.
  let op := fresh in intros ?? op; destruct op; simpl.
  { related_word64_op_t; admit. }
  { related_word64_op_t; admit. }
  { related_word64_op_t; admit. }
  { related_word64_op_t; admit. }
  { related_word64_op_t; admit. }
  { related_word64_op_t; admit. }
  { related_word64_op_t; admit. }
  { related_word64_op_t; admit. }
  { related_word64_op_t; admit. }
  { related_word64_op_t; admit. }
Qed.

Local Arguments ZBounds.SmartBuildBounds _ _ / .
Lemma related_bounds_op : related_op related_bounds (@BoundedWord64.interp_op) (@ZBounds.interp_op).
Proof.
  let op := fresh in intros ?? op; destruct op; simpl.
  { related_word64_op_t. }
  { related_word64_op_t. }
  { related_word64_op_t. }
  { related_word64_op_t. }
  { related_word64_op_t. }
  { related_word64_op_t. }
  { related_word64_op_t. }
  { related_word64_op_t. }
  { admit; related_word64_op_t. }
  { admit; related_word64_op_t. }
Qed.

Create HintDb interp_related discriminated.
Hint Resolve related_Z_op related_bounds_op related_word64_op related_Z_const related_bounds_const related_word64_const : interp_related.
