Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.Z.Interpretations.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListZOperationsProofs.
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
                     | pose proof (@BoundedWord64.t_map4_correct _ _ _ _ _ _ H') as H; clear H' ];
               simpl in H
          | [ H : ?op _ _ = None |- _ ]
            => let H' := fresh in
               rename H into H';
               first [ pose proof (@BoundedWord64.t_map2_correct_None _ _ _ _ _ H') as H; clear H'
                     | pose proof (@BoundedWord64.t_map4_correct_None _ _ _ _ _ H') as H; clear H' ];
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

Lemma related_tuples_None_left
      n T interp_base_type'
      (R : forall t, LiftOption.interp_base_type' T t -> interp_base_type' t -> Prop)
      (RNone : forall v, R TZ None v)
      (v : interp_flat_type interp_base_type' (tuple (Tbase TZ) (S n)))
  : interp_flat_type_rel_pointwise2
      R
      (flat_interp_untuple' (T:=Tbase TZ) (Tuple.push_option (n:=S n) None))
      v.
Proof.
  induction n; simpl; intuition.
Qed.

Lemma related_tuples_Some_left
      n T interp_base_type'
      (R : forall t, T -> interp_base_type' t -> Prop)
      u
      (v : interp_flat_type interp_base_type' (tuple (Tbase TZ) (S n)))
  : interp_flat_type_rel_pointwise2
      R
      (flat_interp_untuple' (T:=Tbase TZ) u)
      v
    <-> interp_flat_type_rel_pointwise2
          (LiftOption.lift_relation R)
          (flat_interp_untuple' (T:=Tbase TZ) (Tuple.push_option (n:=S n) (Some u)))
          v.
Proof.
  induction n; [ reflexivity | ].
  simpl in *; rewrite <- IHn; clear IHn.
  reflexivity.
Qed.

Lemma related_tuples_Some_left_ext
      {n T interp_base_type'}
      {R : forall t, T -> interp_base_type' t -> Prop}
      {u v u'}
      (H : Tuple.lift_option (flat_interp_tuple (T:=Tbase TZ) (n:=S n) u) = Some u')
  : interp_flat_type_rel_pointwise2
      R
      (flat_interp_untuple' (T:=Tbase TZ) u') v
    <-> interp_flat_type_rel_pointwise2
          (LiftOption.lift_relation R)
          u v.
Proof.
  induction n.
  { simpl in *; subst; reflexivity. }
  { destruct_head_hnf' prod.
    simpl in H; break_match_hyps; inversion_option; inversion_prod; subst.
    simpl; rewrite <- IHn by eassumption; clear IHn.
    reflexivity. }
Qed.

Lemma related_tuples_proj_eq_rel_untuple
      {n T interp_base_type'}
      {proj : forall t, T -> interp_base_type' t}
      {u : Tuple.tuple _ (S n)} {v : Tuple.tuple _ (S n)}
  : interp_flat_type_rel_pointwise2
      (fun t => proj_eq_rel (proj t))
      (flat_interp_untuple' (T:=Tbase TZ) u)
      (flat_interp_untuple' (T:=Tbase TZ) v)
    <-> (Tuple.map (proj _) u = v).
Proof.
  induction n; [ reflexivity | ].
  destruct_head_hnf' prod.
  simpl @Tuple.tuple.
  rewrite !Tuple.map_S, path_prod_uncurried_iff, <- prod_iff_and; unfold fst, snd.
  rewrite <- IHn.
  reflexivity.
Qed.

Lemma related_tuples_proj_eq_rel_tuple
      {n T interp_base_type'}
      {proj : forall t, T -> interp_base_type' t}
      {u v}
  : interp_flat_type_rel_pointwise2
      (fun t => proj_eq_rel (proj t))
      u v
    <-> (Tuple.map (proj _) (flat_interp_tuple (n:=S n) (T:=Tbase TZ) u)
         = flat_interp_tuple (T:=Tbase TZ) v).
Proof.
  rewrite <- related_tuples_proj_eq_rel_untuple, !flat_interp_untuple'_tuple; reflexivity.
Qed.

Local Arguments LiftOption.lift_relation2 _ _ _ _ !_ !_ / .
Lemma related_tuples_lift_relation2_untuple'
      n T U
      (R : T -> U -> Prop)
      (t : option (Tuple.tuple T (S n)))
      (u : option (Tuple.tuple U (S n)))
  : interp_flat_type_rel_pointwise2
      (LiftOption.lift_relation2 R)
      (flat_interp_untuple' (T:=Tbase TZ) (Tuple.push_option t))
      (flat_interp_untuple' (T:=Tbase TZ) (Tuple.push_option u))
    <-> LiftOption.lift_relation2
          (interp_flat_type_rel_pointwise2 (fun _ => R))
          TZ
          (option_map (flat_interp_untuple' (interp_base_type:=fun _ => T) (T:=Tbase TZ)) t)
          (option_map (flat_interp_untuple' (interp_base_type:=fun _ => U) (T:=Tbase TZ)) u).
Proof.
  induction n.
  { destruct_head' option; reflexivity. }
  { specialize (IHn (option_map (@fst _ _) t) (option_map (@fst _ _) u)).
    destruct_head' option;
      destruct_head_hnf' prod;
      simpl @option_map in *;
      simpl @LiftOption.lift_relation2 in *;
      try (rewrite <- IHn; reflexivity);
      try (simpl @interp_flat_type_rel_pointwise2; tauto). }
Qed.

Lemma related_tuples_lift_relation2_untuple'_ext
      {n T U}
      {R : T -> U -> Prop}
      {t u}
      (H : (exists v, Tuple.lift_option (n:=S n) (flat_interp_tuple (T:=Tbase TZ) t) = Some v)
           \/ (exists v, Tuple.lift_option (n:=S n) (flat_interp_tuple (T:=Tbase TZ) u) = Some v))
  : interp_flat_type_rel_pointwise2
      (LiftOption.lift_relation2 R)
      t u
    <-> LiftOption.lift_relation2
          (interp_flat_type_rel_pointwise2 (fun _ => R))
          TZ
          (option_map (flat_interp_untuple' (interp_base_type:=fun _ => T) (T:=Tbase TZ)) (Tuple.lift_option (flat_interp_tuple (T:=Tbase TZ) t)))
          (option_map (flat_interp_untuple' (interp_base_type:=fun _ => U) (T:=Tbase TZ)) (Tuple.lift_option (flat_interp_tuple (T:=Tbase TZ) u))).
Proof.
  induction n.
  { destruct_head_hnf' option; reflexivity. }
  { specialize (IHn (fst t) (fst u)).
    lazymatch type of IHn with
    | ?T -> _ => let H := fresh in assert (H : T); [ | specialize (IHn H); clear H ]
    end.
    { destruct_head' or; [ left | right ]; destruct_head' ex; destruct_head_hnf' prod; eexists;
        (etransitivity;
         [ | first [ refine (f_equal (option_map (@fst _ _)) (_ : _ = Some (_, _))); eassumption
                   | refine (f_equal (option_map (@snd _ _)) (_ : _ = Some (_, _))); eassumption ] ]);
        instantiate; simpl in *; break_match; simpl in *; congruence. }
    destruct_head_hnf' prod;
      destruct_head_hnf' option;
      simpl @fst in *; simpl @snd in *;
        (etransitivity; [ simpl @interp_flat_type_rel_pointwise2 | reflexivity ]);
        try solve [ repeat first [ progress simpl in *
                                 | tauto
                                 | congruence
                                 | progress destruct_head ex
                                 | progress destruct_head or
                                 | progress break_match ] ]. }
Qed.

Lemma lift_option_flat_interp_tuple'
      {n T x y}
  : (Tuple.lift_option (n:=S n) (A:=T) (flat_interp_tuple' (interp_base_type:=LiftOption.interp_base_type' _) (T:=Tbase TZ) x) = Some y)
    <-> (x = flat_interp_untuple' (T:=Tbase TZ) (n:=n) (Tuple.push_option (n:=S n) (Some y))).
Proof.
  rewrite Tuple.push_lift_option; generalize (Tuple.push_option (Some y)); intro.
  split; intro; subst;
    rewrite ?flat_interp_tuple'_untuple', ?flat_interp_untuple'_tuple';
    reflexivity.
Qed.

Lemma lift_option_None_interp_flat_type_rel_pointwise2_1
      T U n R x y
      (H : interp_flat_type_rel_pointwise2 (LiftOption.lift_relation2 R) x y)
      (HNone : Tuple.lift_option (A:=T) (n:=S n) (flat_interp_tuple' (T:=Tbase TZ) (n:=n) x) = None)
  : Tuple.lift_option (A:=U) (n:=S n) (flat_interp_tuple' (T:=Tbase TZ) (n:=n) y) = None.
Proof.
  induction n; [ | specialize (IHn (fst x) (fst y) (proj1 H)) ];
    repeat first [ progress destruct_head_hnf' False
                 | reflexivity
                 | progress inversion_option
                 | progress simpl in *
                 | progress subst
                 | progress specialize_by congruence
                 | progress destruct_head_hnf' prod
                 | progress destruct_head_hnf' and
                 | progress destruct_head_hnf' option
                 | progress break_match
                 | progress break_match_hyps ].
Qed.

Local Arguments LiftOption.lift_relation _ _ _ _ !_ _ / .
Local Arguments LiftOption.of' _ _ !_ / .
Local Arguments BoundedWord64.BoundedWordToBounds !_ / .

Lemma related_word64_op : related_op related_word64 (@BoundedWord64.interp_op) (@Word64.interp_op).
Proof.
  (let op := fresh in intros ?? op; destruct op; simpl);
    try first [ apply related_word64_t_map2
              | apply related_word64_t_map4 ].
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

Local Arguments Tuple.lift_option : simpl never.
Local Arguments Tuple.push_option : simpl never.
Local Arguments Tuple.map : simpl never.
Local Arguments Tuple.map2 : simpl never.

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
              instantiate; apply Z.min_case_strong; intros;
              first [ etransitivity; [ apply Z.land_upper_bound_l | ]; omega
                    | etransitivity; [ apply Z.land_upper_bound_r | ]; omega ]
            | rewrite Z.log2_lor by omega;
              apply Z.max_case_strong; intro;
              (eapply Z.le_lt_trans; [ eapply Z.log2_le_mono; eassumption | assumption ])
            | eapply Z.le_lt_trans; [ eapply Z.log2_le_mono, neg_upperbound | ];
              Word64.Rewrites.word64_util_arith
            | (progress unfold ModularBaseSystemListZOperations.cmovne, ModularBaseSystemListZOperations.cmovl); break_match;
              Word64.Rewrites.word64_util_arith ].
Local Ltac related_Z_op_t_step :=
  first [ progress related_word64_op_t_step
        | progress cbv [related'_Z proj_eq_rel BoundedWord64.to_Z' BoundedWord64.to_word64' Word64.to_Z BoundedWord64.boundedWordToWord64 BoundedWord64.value] in *
        | autorewrite with push_word64ToZ ].
Local Ltac related_Z_op_t := repeat related_Z_op_t_step.

Local Notation is_bounded_by value lower upper
  := ((0 <= lower /\ lower <= Word64.word64ToZ value <= upper /\ Z.log2 upper < Z.of_nat Word64.bit_width)%Z)
       (only parsing).
Local Notation is_in_bounds value bounds
  := (is_bounded_by value (ZBounds.lower bounds) (ZBounds.upper bounds))
       (only parsing).

Lemma related_Z_t_map2 opZ opW opB pf
      (H : forall x y bxs bys brs,
          Some brs = opB (Some bxs) (Some bys)
          -> is_in_bounds x bxs
          -> is_in_bounds y bys
          -> is_in_bounds (opW x y) brs
          -> Word64.word64ToZ (opW x y) = (opZ (Word64.word64ToZ x) (Word64.word64ToZ y)))
      sv1 sv2
  : interp_flat_type_rel_pointwise2 (t:=Prod (Tbase TZ) (Tbase TZ)) related_Z sv1 sv2
    -> @related_Z TZ (BoundedWord64.t_map2 opW opB pf (fst sv1) (snd sv1)) (opZ (fst sv2) (snd sv2)).
Proof.
  cbv [interp_flat_type BoundedWord64.interp_base_type ZBounds.interp_base_type LiftOption.interp_base_type' interp_flat_type_rel_pointwise2 interp_flat_type_rel_pointwise2_gen_Prop] in *.
  related_Z_op_t.
  eapply H; eauto.
Qed.

Lemma related_Z_t_map4 opZ opW opB pf
      (H : forall x y z w bxs bys bzs bws brs,
          Some brs = opB (Some bxs) (Some bys) (Some bzs) (Some bws)
          -> is_in_bounds x bxs
          -> is_in_bounds y bys
          -> is_in_bounds z bzs
          -> is_in_bounds w bws
          -> is_in_bounds (opW x y z w) brs
          -> Word64.word64ToZ (opW x y z w) = (opZ (Word64.word64ToZ x) (Word64.word64ToZ y) (Word64.word64ToZ z) (Word64.word64ToZ w)))
      sv1 sv2
  : interp_flat_type_rel_pointwise2 (t:=(Tbase TZ * Tbase TZ * Tbase TZ * Tbase TZ)%ctype) related_Z sv1 sv2
    -> @related_Z TZ (BoundedWord64.t_map4 opW opB pf (fst (fst (fst sv1))) (snd (fst (fst sv1))) (snd (fst sv1)) (snd sv1))
                  (opZ (fst (fst (fst sv2))) (snd (fst (fst sv2))) (snd (fst sv2)) (snd sv2)).
Proof.
  cbv [interp_flat_type BoundedWord64.interp_base_type ZBounds.interp_base_type LiftOption.interp_base_type' interp_flat_type_rel_pointwise2 interp_flat_type_rel_pointwise2_gen_Prop] in *.
  related_Z_op_t.
  eapply H; eauto.
Qed.

Local Arguments related_Z _ !_ _ / .

Local Arguments related'_Z _ _ _ / .

Local Ltac related_Z_op_fin_t_step :=
  first [ progress subst
        | progress destruct_head' ZBounds.bounds
        | progress destruct_head' and
        | progress ZBounds.inversion_bounds
        | progress simpl in * |-
        | progress break_match_hyps
        | congruence
        | progress inversion_option
        | intro
        | progress autorewrite with push_word64ToZ
        | match goal with
          | [ H : andb _ _ = true |- _ ] => rewrite Bool.andb_true_iff in H
          | [ H : context[Tuple.lift_option (Tuple.push_option _)] |- _ ]
            => rewrite Tuple.lift_push_option in H
          end
        | progress Z.ltb_to_lt
        | (progress unfold ZBounds.conditional_subtract in * ); break_match_hyps ].
Local Ltac related_Z_op_fin_t := repeat related_Z_op_fin_t_step.

Local Opaque Word64.bit_width.

Lemma related_Z_op : related_op related_Z (@BoundedWord64.interp_op) (@Z.interp_op).
Proof.
  let op := fresh in intros ?? op; destruct op; simpl.
  { apply related_Z_t_map2; related_Z_op_fin_t. }
  { apply related_Z_t_map2; related_Z_op_fin_t. }
  { apply related_Z_t_map2; related_Z_op_fin_t. }
  { apply related_Z_t_map2; related_Z_op_fin_t. }
  { apply related_Z_t_map2; related_Z_op_fin_t. }
  { apply related_Z_t_map2; related_Z_op_fin_t. }
  { apply related_Z_t_map2; related_Z_op_fin_t. }
  { apply related_Z_t_map2; related_Z_op_fin_t. }
  { apply related_Z_t_map4; related_Z_op_fin_t. }
  { apply related_Z_t_map4; related_Z_op_fin_t. }
Qed.

Create HintDb interp_related discriminated.
Hint Resolve related_Z_op related_bounds_op related_word64_op related_Z_const related_bounds_const related_word64_const : interp_related.
