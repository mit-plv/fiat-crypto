Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
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
  := LiftOption.lift_relation2 (proj_eq_rel BoundedWord64.BoundedWordToBounds) t.

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

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.

Local Ltac related_word64_op_t_step :=
  first [ exact I
        | reflexivity
        | progress intros
        | progress inversion_option
        | progress ZBounds.inversion_bounds
        | progress subst
        | progress destruct_head' False
        | progress destruct_head' prod
        | progress destruct_head' and
        | progress destruct_head' option
        | progress destruct_head' BoundedWord64.BoundedWord
        | progress cbv [related_word64 related_bounds related_Z LiftOption.lift_relation LiftOption.lift_relation2 LiftOption.of' smart_interp_flat_map BoundedWord64.BoundedWordToBounds BoundedWord64.to_bounds'] in *
        | progress simpl @fst in *
        | progress simpl @snd in *
        | progress simpl @BoundedWord64.upper in *
        | progress simpl @BoundedWord64.lower in *
        | progress break_match
        | progress break_match_hyps
        | congruence
        | match goal with
          | [ H : ?op _ _ = Some _ |- _ ]
            => let H' := fresh in
               rename H into H';
               first [ pose proof (@BoundedWord64.t_map2_correct _ _ _ _ _ _ H') as H; clear H'
                     | pose proof (@BoundedWord64.t_map4_correct _ _ _ _ _ _ H') as H; clear H'
                     | pose proof (@BoundedWord64.t_map1_tuple2_correct _ _ _ _ _ _ H') as H; clear H' ];
               simpl in H
          | [ H : ?op _ _ = None |- _ ]
            => let H' := fresh in
               rename H into H';
               first [ pose proof (@BoundedWord64.t_map2_correct_None _ _ _ _ _ H') as H; clear H'
                     | pose proof (@BoundedWord64.t_map4_correct_None _ _ _ _ _ H') as H; clear H'
                     | pose proof (@BoundedWord64.t_map1_tuple2_correct_None _ _ _ _ _ H') as H; clear H' ];
               simpl in H
          end
        | progress cbv [related'_word64 proj_eq_rel BoundedWord64.to_word64' BoundedWord64.boundedWordToWord64 BoundedWord64.value] in *
        | match goal with
          | [ H : ?op None _ = Some _ |- _ ] => progress simpl in H
          | [ H : ?op _ None = Some _ |- _ ] => progress simpl in H
          | [ H : ?op (Some _) (Some _) = Some _ |- _ ] => progress simpl in H
          | [ H : ?op (Some _) (Some _) = None |- _ ] => progress simpl in H
          end ].
Local Ltac related_word64_op_t := repeat related_word64_op_t_step.

Lemma related_word64_t_map2 opW opB pf
      sv1 sv2
  : interp_flat_type_rel_pointwise2 (t:=Prod (Tbase TZ) (Tbase TZ)) related_word64 sv1 sv2
    -> @related_word64 TZ (BoundedWord64.t_map2 opW opB pf (fst sv1) (snd sv1)) (opW (fst sv2) (snd sv2)).
Proof.
  cbv [interp_flat_type BoundedWord64.interp_base_type ZBounds.interp_base_type LiftOption.interp_base_type' interp_flat_type_rel_pointwise2 interp_flat_type_rel_pointwise2_gen_Prop] in *.
  related_word64_op_t.
Qed.

Lemma related_word64_t_map4 opW opB pf
      sv1 sv2
  : interp_flat_type_rel_pointwise2 (t:=Prod (Prod (Prod (Tbase TZ) (Tbase TZ)) (Tbase TZ)) (Tbase TZ)) related_word64 sv1 sv2
    -> @related_word64 TZ (BoundedWord64.t_map4 opW opB pf (fst (fst (fst sv1))) (snd (fst (fst sv1))) (snd (fst sv1)) (snd sv1))
                       (opW (fst (fst (fst sv2))) (snd (fst (fst sv2))) (snd (fst sv2)) (snd sv2)).
Proof.
  cbv [interp_flat_type BoundedWord64.interp_base_type ZBounds.interp_base_type LiftOption.interp_base_type' interp_flat_type_rel_pointwise2 interp_flat_type_rel_pointwise2_gen_Prop] in *.
  related_word64_op_t.
Qed.

Lemma related_word64_t_map1_tuple2 {n} opW opB pf
      sv1 sv2
  : interp_flat_type_rel_pointwise2 (t:=Prod (Prod (Tbase TZ) (Syntax.tuple (Tbase TZ) (S n))) (Syntax.tuple (Tbase TZ) (S n))) related_word64 sv1 sv2
    -> interp_flat_type_rel_pointwise2
         (t:=Syntax.tuple (Tbase TZ) (S n)) related_word64
         (Syntax.flat_interp_untuple' (n:=n) (T:=Tbase TZ) (BoundedWord64.t_map1_tuple2 (n:=n) opW opB pf (fst (fst sv1)) (Syntax.flat_interp_tuple (snd (fst sv1))) (Syntax.flat_interp_tuple (snd sv1))))
         (Syntax.flat_interp_untuple' (n:=n) (T:=Tbase TZ) (opW (fst (fst sv2)) (Syntax.flat_interp_tuple (snd (fst sv2))) (Syntax.flat_interp_tuple (snd sv2)))).
Proof.
  destruct_head_hnf' prod; simpl; intro.
  destruct_head' and.
  destruct_head_hnf' option; destruct_head_hnf' False.
  Focus 2.
  { destruct_head_hnf' True.
    unfold BoundedWord64.t_map1_tuple2.
    admit. (* TODO(jadep (or jgross)): Fill me in *) }
  Unfocus.
  admit.  (* TODO(jadep (or jgross)): Fill me in *)
Admitted.

Lemma related_word64_op : related_op related_word64 (@BoundedWord64.interp_op) (@Word64.interp_op).
Proof.
  (let op := fresh in intros ?? op; destruct op; simpl);
    try first [ apply related_word64_t_map2
              | apply related_word64_t_map4
              | apply related_word64_t_map1_tuple2 ].
Qed.

Lemma related_bounds_t_map2 opW opB pf
      (HN0 : forall v, opB None v = None)
      (HN1 : forall v, opB v None = None)
      sv1 sv2
  : interp_flat_type_rel_pointwise2 (t:=Prod (Tbase TZ) (Tbase TZ)) related_bounds sv1 sv2
    -> @related_bounds TZ (BoundedWord64.t_map2 opW opB pf (fst sv1) (snd sv1)) (opB (fst sv2) (snd sv2)).
Proof.
  cbv [interp_flat_type BoundedWord64.interp_base_type ZBounds.interp_base_type LiftOption.interp_base_type' interp_flat_type_rel_pointwise2 interp_flat_type_rel_pointwise2_gen_Prop] in *.
  related_word64_op_t.
Qed.

Lemma related_bounds_t_map4 opW opB pf
      (HN0 : forall x y z, opB None x y z = None)
      (HN1 : forall x y z, opB x None y z = None)
      (HN2 : forall x y z, opB x y None z = None)
      (HN3 : forall x y z, opB x y z None = None)
      sv1 sv2
  : interp_flat_type_rel_pointwise2 (t:=Prod (Prod (Prod (Tbase TZ) (Tbase TZ)) (Tbase TZ)) (Tbase TZ)) related_bounds sv1 sv2
    -> @related_bounds TZ (BoundedWord64.t_map4 opW opB pf (fst (fst (fst sv1))) (snd (fst (fst sv1))) (snd (fst sv1)) (snd sv1))
                       (opB (fst (fst (fst sv2))) (snd (fst (fst sv2))) (snd (fst sv2)) (snd sv2)).
Proof.
  cbv [interp_flat_type BoundedWord64.interp_base_type ZBounds.interp_base_type LiftOption.interp_base_type' interp_flat_type_rel_pointwise2 interp_flat_type_rel_pointwise2_gen_Prop] in *.
  destruct_head prod.
  intros; destruct_head' prod.
  progress cbv [related_word64 related_bounds related_Z LiftOption.lift_relation LiftOption.lift_relation2 LiftOption.of' smart_interp_flat_map BoundedWord64.BoundedWordToBounds BoundedWord64.to_bounds' proj_eq_rel] in *.
  destruct_head' option; destruct_head_hnf' and; destruct_head_hnf' False; subst;
    try solve [ simpl; rewrite ?HN0, ?HN1, ?HN2, ?HN3; tauto ];
    [].
  related_word64_op_t.
Qed.

Lemma related_bounds_t_map1_tuple2 {n} opW opB pf
      (HN0 : forall x y, opB None x y = Tuple.push_option None)
      (HN1 : forall x y z, Tuple.lift_option y = None -> opB x y z = Tuple.push_option None)
      (HN2 : forall x y z, Tuple.lift_option z = None -> opB x y z = Tuple.push_option None)
      sv1 sv2
  : interp_flat_type_rel_pointwise2 (t:=Prod (Prod (Tbase TZ) (Syntax.tuple (Tbase TZ) (S n))) (Syntax.tuple (Tbase TZ) (S n))) related_bounds sv1 sv2
    -> interp_flat_type_rel_pointwise2
         (t:=Syntax.tuple (Tbase TZ) (S n)) related_bounds
         (Syntax.flat_interp_untuple' (n:=n) (T:=Tbase TZ) (BoundedWord64.t_map1_tuple2 (n:=n) opW opB pf (fst (fst sv1)) (Syntax.flat_interp_tuple (snd (fst sv1))) (Syntax.flat_interp_tuple (snd sv1))))
         (Syntax.flat_interp_untuple' (n:=n) (T:=Tbase TZ) (opB (fst (fst sv2)) (Syntax.flat_interp_tuple (snd (fst sv2))) (Syntax.flat_interp_tuple (snd sv2)))).
Proof.
  destruct_head_hnf' prod; simpl; intro.
  destruct_head' and.
  destruct_head_hnf' option; destruct_head_hnf' False.
  Focus 2.
  { rewrite HN0.
    unfold BoundedWord64.t_map1_tuple2.
    admit. (* TODO(jadep (or jgross)): Fill me in *) }
  Unfocus.
  admit.  (* TODO(jadep (or jgross)): Fill me in *)
Admitted.

Local Arguments ZBounds.SmartBuildBounds _ _ / .
Lemma related_bounds_op : related_op related_bounds (@BoundedWord64.interp_op) (@ZBounds.interp_op).
Proof.
  let op := fresh in intros ?? op; destruct op; simpl.
  { apply related_bounds_t_map2; intros; destruct_head' option; reflexivity. }
  { apply related_bounds_t_map2; intros; destruct_head' option; reflexivity. }
  { apply related_bounds_t_map2; intros; destruct_head' option; reflexivity. }
  { apply related_bounds_t_map2; intros; destruct_head' option; reflexivity. }
  { apply related_bounds_t_map2; intros; destruct_head' option; reflexivity. }
  { apply related_bounds_t_map2; intros; destruct_head' option; reflexivity. }
  { apply related_bounds_t_map2; intros; destruct_head' option; reflexivity. }
  { apply related_bounds_t_map2; intros; destruct_head' option; destruct_head' ZBounds.bounds; reflexivity. }
  { apply related_bounds_t_map4; intros; destruct_head' option; reflexivity. }
  { apply related_bounds_t_map4; intros; destruct_head' option; reflexivity. }
  { apply related_bounds_t_map1_tuple2; intros; destruct_head' option; try reflexivity;
      unfold ZBounds.conditional_subtract; rewrite ?Tuple.lift_push_option; try reflexivity;
        (rewrite_hyp ?* );
        break_match; try reflexivity. }
Qed.

Local Ltac Word64.Rewrites.word64_util_arith ::=
      solve [ autorewrite with Zshift_to_pow; omega
            | autorewrite with Zshift_to_pow; nia
            | autorewrite with Zshift_to_pow; auto with zarith
            | eapply Z.le_lt_trans; [ eapply Z.log2_le_mono | eassumption ];
              autorewrite with Zshift_to_pow; auto using Z.mul_le_mono_nonneg with zarith;
              solve [ omega
                    | nia
                    | etransitivity; [ eapply Z.div_le_mono | eapply Z.div_le_compat_l ];
                      auto with zarith ]
            | apply Z.land_nonneg; Word64.Rewrites.word64_util_arith
            | eapply Z.le_lt_trans; [ eapply Z.log2_le_mono | eassumption ];
              apply Z.min_case_strong; intros;
              first [ etransitivity; [ apply Z.land_upper_bound_l | ]; omega
                    | etransitivity; [ apply Z.land_upper_bound_r | ]; omega ] ].
Local Ltac related_Z_op_t_step :=
  first [ progress related_word64_op_t_step
        | progress cbv [related'_Z proj_eq_rel BoundedWord64.to_Z' BoundedWord64.to_word64' Word64.to_Z BoundedWord64.boundedWordToWord64 BoundedWord64.value] in *
        | autorewrite with push_word64ToZ ].
Local Ltac related_Z_op_t := repeat related_Z_op_t_step.

Lemma related_Z_op : related_op related_Z (@BoundedWord64.interp_op) (@Z.interp_op).
Proof.
  let op := fresh in intros ?? op; destruct op; simpl.
  { related_Z_op_t. }
  { related_Z_op_t. }
  { related_Z_op_t. }
  { related_Z_op_t. }
  { related_Z_op_t. }
  { related_Z_op_t. }
  { related_Z_op_t.
    rewrite Word64.word64ToZ_lor; try Word64.Rewrites.word64_util_arith.
    admit. (* TODO: Fill me in *)
    admit. (* TODO: Fill me in *) }
  { related_Z_op_t; admit. }
  { related_Z_op_t; admit. }
  { related_Z_op_t; admit. }
  { related_Z_op_t; admit. (** TODO(jadep or jgross): Fill me in *) }
Qed.

Create HintDb interp_related discriminated.
Hint Resolve related_Z_op related_bounds_op related_word64_op related_Z_const related_bounds_const related_word64_const : interp_related.
