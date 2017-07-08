Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Saturated.Core.
Require Import Crypto.Arithmetic.Saturated.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.Wrappers.
Require Import Crypto.Arithmetic.Saturated.AddSub.
Require Import Crypto.Util.LetIn Crypto.Util.CPSUtil.
Require Import Crypto.Util.Tuple Crypto.Util.LetIn.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.AddGetCarry.
Require Import Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.Tactics.UniquePose.
Local Notation "A ^ n" := (tuple A n) : type_scope.

Section API.
  Context (bound : Z) {bound_pos : bound > 0}.
  Definition T : nat -> Type := tuple Z.

  (* lowest limb is less than its bound; this is required for [divmod]
  to simply separate the lowest limb from the rest and be equivalent
  to normal div/mod with [bound]. *)
  Local Notation small := (@small bound).

  Definition zero {n:nat} : T n := B.Positional.zeros n.

  (** Returns 0 iff all limbs are 0 *)
  Definition nonzero_cps {n} (p : T n) {cpsT} (f : Z -> cpsT) : cpsT
    := CPSUtil.to_list_cps _ p (fun p => CPSUtil.fold_right_cps runtime_lor 0%Z p f).
  Definition nonzero {n} (p : T n) : Z
    := nonzero_cps p id.

  Definition join0_cps {n:nat} (p : T n) {R} (f:T (S n) -> R)
    := Tuple.left_append_cps 0 p f.
  Definition join0 {n} p : T (S n) := @join0_cps n p _ id.

  Definition divmod_cps {n} (p : T (S n)) {R} (f:T n * Z->R) : R
    := Tuple.tl_cps p (fun d => Tuple.hd_cps p (fun m =>  f (d, m))).
  Definition divmod {n} p : T n * Z := @divmod_cps n p _ id.

  Definition drop_high_cps {n : nat} (p : T (S n)) {R} (f:T n->R)
    := Tuple.left_tl_cps p f.
  Definition drop_high {n} p : T n := @drop_high_cps n p _ id.

  Definition scmul_cps {n} (c : Z) (p : T n) {R} (f:T (S n)->R) :=
    Columns.mul_cps (n1:=1) (n3:=S n) (uweight bound) bound c p
      (* The carry that comes out of Columns.mul_cps will be 0, since
      (S n) limbs is enough to hold the result of the
      multiplication, so we can safely discard it. *)
      (fun carry_result =>f (snd carry_result)).
  Definition scmul {n} c p : T (S n) := @scmul_cps n c p _ id.

  Definition add_cps {n} (p q: T n) {R} (f:T (S n)->R) :=
    B.Positional.sat_add_cps (s:=bound) p q _
      (* join the last carry *)
      (fun carry_result => Tuple.left_append_cps (fst carry_result) (snd carry_result) f).
  Definition add {n} p q : T (S n) := @add_cps n p q _ id.

  (* Wrappers for additions with slightly uneven limb counts *)
  Definition add_S1_cps {n} (p: T (S n)) (q: T n) {R} (f:T (S (S n))->R) :=
    join0_cps q (fun Q => add_cps p Q f).
  Definition add_S1 {n} p q := @add_S1_cps n p q _ id.
  Definition add_S2_cps {n} (p: T n) (q: T (S n)) {R} (f:T (S (S n))->R) :=
    join0_cps p (fun P => add_cps P q f).
  Definition add_S2 {n} p q := @add_S2_cps n p q _ id.

  Definition sub_then_maybe_add_cps {n} mask (p q r : T n)
             {R} (f:T n -> R) :=
    B.Positional.sat_sub_cps (s:=bound) p q _
      (* the carry will be 0 unless we underflow--we do the addition only
         in the underflow case *)
      (fun carry_result =>
         B.Positional.select_cps mask (fst carry_result) r
      (fun selected => join0_cps selected
      (fun selected' =>
         B.Positional.sat_add_cps (s:=bound) (left_append (- (fst carry_result))%RT (snd carry_result)) selected' _
      (* We can now safely discard the carry and the highest digit.
         This relies on the precondition that p - q + r < bound^n. *)
      (fun carry_result' => drop_high_cps (snd carry_result') f)))).
  Definition sub_then_maybe_add {n} mask (p q r : T n) :=
    sub_then_maybe_add_cps mask p q r id.

   (* Subtract q if and only if p >= q. We rely on the preconditions
    that 0 <= p < 2*q and q < bound^n (this ensures the output is less
    than bound^n). *)
  Definition conditional_sub_cps {n} (p:Z^S n) (q:Z^n) R (f:Z^n->R) :=
    join0_cps q
    (fun qq => B.Positional.sat_sub_cps (s:=bound) p qq _
      (* if carry is zero, we select the result of the subtraction,
      otherwise the first input *)
      (fun carry_result =>
        Tuple.map2_cps (Z.zselect (fst carry_result)) (snd carry_result) p
      (* in either case, since our result must be < q and therefore <
      bound^n, we can drop the high digit *)
      (fun r => drop_high_cps r f))).
  Definition conditional_sub {n} p q := @conditional_sub_cps n p q _ id.

  Hint Opaque join0 divmod drop_high scmul add sub_then_maybe_add conditional_sub : uncps.

  Section CPSProofs.

    Local Ltac prove_id :=
      repeat autounfold; autorewrite with uncps; reflexivity.

    Lemma nonzero_id n p {cpsT} f : @nonzero_cps n p cpsT f = f (@nonzero n p).
    Proof. cbv [nonzero nonzero_cps]. prove_id. Qed.

    Lemma join0_id n p R f :
      @join0_cps n p R f = f (join0 p).
    Proof. cbv [join0_cps join0]. prove_id. Qed.

    Lemma divmod_id n p R f :
      @divmod_cps n p R f = f (divmod p).
    Proof. cbv [divmod_cps divmod]; prove_id. Qed.

    Lemma drop_high_id n p R f :
      @drop_high_cps n p R f = f (drop_high p).
    Proof. cbv [drop_high_cps drop_high]; prove_id. Qed.
    Hint Rewrite drop_high_id : uncps.

    Lemma scmul_id n c p R f :
      @scmul_cps n c p R f = f (scmul c p).
    Proof. cbv [scmul_cps scmul]. prove_id. Qed.

    Lemma add_id n p q R f :
      @add_cps n p q R f = f (add p q).
    Proof. cbv [add_cps add Let_In]. prove_id. Qed.
    Hint Rewrite add_id : uncps.

    Lemma add_S1_id n p q R f :
      @add_S1_cps n p q R f = f (add_S1 p q).
    Proof. cbv [add_S1_cps add_S1 join0_cps]. prove_id. Qed.

    Lemma add_S2_id n p q R f :
      @add_S2_cps n p q R f = f (add_S2 p q).
    Proof. cbv [add_S2_cps add_S2 join0_cps]. prove_id. Qed.

    Lemma sub_then_maybe_add_id n mask p q r R f :
      @sub_then_maybe_add_cps n mask p q r R f = f (sub_then_maybe_add mask p q r).
    Proof. cbv [sub_then_maybe_add_cps sub_then_maybe_add join0_cps Let_In]. prove_id. Qed.

    Lemma conditional_sub_id n p q R f :
      @conditional_sub_cps n p q R f = f (conditional_sub p q).
    Proof. cbv [conditional_sub_cps conditional_sub join0_cps Let_In]. prove_id. Qed.

  End CPSProofs.
  Hint Rewrite nonzero_id join0_id divmod_id drop_high_id scmul_id add_id sub_then_maybe_add_id conditional_sub_id : uncps.

  Section Proofs.

    Definition eval {n} (p : T n) : Z :=
      B.Positional.eval (uweight bound) p.

    Lemma eval_small n (p : T n) (Hsmall : small p) :
      0 <= eval p < uweight bound n.
    Proof.
      cbv [small eval] in *; intros.
      induction n; cbv [T uweight] in *; [destruct p|rewrite (subst_left_append p)];
      repeat match goal with
             | _ => progress autorewrite with push_basesystem_eval
             | _ => rewrite Z.pow_0_r
             | _ => specialize (IHn (left_tl p))
             | _ =>
               let H := fresh "H" in
               match type of IHn with
                 ?P -> _ => assert P as H by auto using Tuple.In_to_list_left_tl;
                              specialize (IHn H)
               end
             | |- context [?b ^ Z.of_nat (S ?n)] =>
               replace (b ^ Z.of_nat (S n)) with (b ^ Z.of_nat n * b) by
                   (rewrite Nat2Z.inj_succ, <-Z.add_1_r, Z.pow_add_r,
                    Z.pow_1_r by (omega || auto using Nat2Z.is_nonneg);
                    reflexivity)
             | _ => omega
             end.

        specialize (Hsmall _ (Tuple.In_left_hd _ p)).
        split; [Z.zero_bounds; omega |].
        apply Z.lt_le_trans with (m:=bound^Z.of_nat n * (left_hd p+1)).
        { rewrite Z.mul_add_distr_l.
          apply Z.add_le_lt_mono; omega. }
        { apply Z.mul_le_mono_nonneg; omega. }
    Qed.

    Lemma eval_zero n : eval (@zero n) = 0.
    Proof.
      cbv [eval zero].
      autorewrite with push_basesystem_eval.
      reflexivity.
    Qed.

    Lemma small_zero n : small (@zero n).
    Proof.
      cbv [zero small B.Positional.zeros]. destruct n; [simpl;tauto|].
      rewrite to_list_repeat.
      intros x H; apply repeat_spec in H; subst x; omega.
    Qed.

    Lemma small_hd n p : @small (S n) p -> 0 <= hd p < bound.
    Proof.
      cbv [small]. let H := fresh "H" in intro H; apply H.
      rewrite (subst_append p). rewrite to_list_append, hd_append.
      apply in_eq.
    Qed.

    Lemma In_to_list_tl {A n} (p : A^(S n)) x :
      In x (to_list n (tl p)) -> In x (to_list (S n) p).
    Proof.
      intros. rewrite (subst_append p).
      rewrite to_list_append. simpl In. tauto.
    Qed.

    Lemma small_tl n p : @small (S n) p -> small (tl p).
    Proof.
      cbv [small]. let H := fresh "H" in intros H ? ?; apply H.
      auto using In_to_list_tl.
    Qed.

    Lemma add_nonneg_zero_iff a b c : 0 <= a -> 0 <= b -> 0 < c ->
                               a = 0 /\ b = 0 <-> a + c * b = 0.
    Proof. nia. Qed.

    Lemma eval_pair n (p : T (S (S n))) : small p ->
      (snd p = 0 /\ eval (n:=S n) (fst p) = 0) <-> eval p = 0.
    Proof.
      intro Hsmall. cbv [eval].
      rewrite uweight_eval_step with (p:=p).
      change (fst p) with (tl p). change (snd p) with (hd p).
      apply add_nonneg_zero_iff; try omega.
      { apply small_hd in Hsmall. omega. }
      { apply small_tl, eval_small in Hsmall.
        cbv [eval] in Hsmall; omega. }
    Qed.

    Lemma eval_nonzero n p : small p -> @nonzero n p = 0 <-> eval p = 0.
    Proof.
      destruct n as [|n].
      { compute; split; trivial. }
      induction n as [|n IHn].
      { simpl; rewrite Z.lor_0_r; unfold eval, id.
        cbv -[Z.add iff].
        rewrite Z.add_0_r.
        destruct p; omega. }
      { destruct p as [ps p]; specialize (IHn ps).
        unfold nonzero, nonzero_cps in *.
        autorewrite with uncps in *.
        unfold id in *.
        setoid_rewrite to_list_S.
        set (k := S n) in *; simpl in *.
        intro Hsmall.
        rewrite Z.lor_eq_0_iff, IHn
          by (hnf in Hsmall |- *; simpl in *; eauto);
          clear IHn.
        exact (eval_pair n (ps, p) Hsmall). }
    Qed.

    Lemma eval_join0 n p
      : eval (@join0 n p) = eval p.
    Proof.
      cbv [join0 join0_cps eval]. autorewrite with uncps push_id.
      rewrite B.Positional.eval_left_append. ring.
    Qed.

    Local Ltac pose_uweight bound :=
      match goal with H : bound > 0 |- _ =>
                      pose proof (uweight_0 bound);
                      pose proof (@uweight_positive bound H);
                      pose proof (@uweight_nonzero bound H);
                      pose proof (@uweight_multiples bound);
                      pose proof (@uweight_divides bound H)
      end.

    Local Ltac pose_all :=
      pose_uweight bound;
      pose proof Z.add_get_carry_full_div;
      pose proof Z.add_get_carry_full_mod;
      pose proof Z.mul_split_div; pose proof Z.mul_split_mod;
      pose proof div_correct; pose proof modulo_correct.

    Lemma eval_add n p q :
      eval (@add n p q) = eval p + eval q.
    Proof.
      intros. pose_all. cbv [add_cps add eval Let_In].
      autorewrite with uncps push_id cancel_pair push_basesystem_eval.
      symmetry; auto using Z.div_mod.
    Qed.

    Lemma eval_add_same n p q
      :  eval (@add n p q) = eval p + eval q.
    Proof. apply eval_add; omega. Qed.
    Lemma eval_add_S1 n p q
      :  eval (@add_S1 n p q) = eval p + eval q.
    Proof.
      cbv [add_S1 add_S1_cps]. autorewrite with uncps push_id.
      rewrite eval_add; rewrite eval_join0; reflexivity.
    Qed.
    Lemma eval_add_S2 n p q
      :  eval (@add_S2 n p q) = eval p + eval q.
    Proof.
      cbv [add_S2 add_S2_cps]. autorewrite with uncps push_id.
      rewrite eval_add; rewrite eval_join0; reflexivity.
    Qed.
    Hint Rewrite eval_add_same eval_add_S1 eval_add_S2 using (omega || assumption): push_basesystem_eval.

    Local Definition compact {n} := Columns.compact (n:=n) (add_get_carry:=Z.add_get_carry_full) (div:=div) (modulo:=modulo) (uweight bound).
    Local Definition compact_digit := Columns.compact_digit (add_get_carry:=Z.add_get_carry_full) (div:=div) (modulo:=modulo) (uweight bound).
    Lemma small_compact {n} (p:(list Z)^n) : small (snd (compact p)).
    Proof.
      pose_all.
      match goal with
        |- ?G => assert (G /\ fst (compact p) = fst (compact p)); [|tauto]
      end. (* assert a dummy second statement so that fst (compact x) is in context *)
      cbv [compact Columns.compact Columns.compact_cps small
                   Columns.compact_step Columns.compact_step_cps];
        autorewrite with uncps push_id.
      change (fun i s a => Columns.compact_digit_cps (uweight bound) i (s :: a) id)
      with (fun i s a => compact_digit i (s :: a)).
      remember (fun i s a => compact_digit i (s :: a)) as f.

      apply @mapi_with'_linvariant with (n:=n) (f:=f) (inp:=p);
        intros; [|simpl; tauto]. split; [|reflexivity].
      let P := fresh "H" in
      match goal with H : _ /\ _ |- _ => destruct H end.
      destruct n0; subst f.
      { cbv [compact_digit uweight to_list to_list' In].
        rewrite Columns.compact_digit_mod by assumption.
        rewrite Z.pow_0_r, Z.pow_1_r, Z.div_1_r. intros x ?.
        match goal with
          H : _ \/ False |- _ => destruct H; [|exfalso; assumption] end.
        subst x. apply Z.mod_pos_bound, Z.gt_lt, bound_pos. }
      { rewrite Tuple.to_list_left_append.
        let H := fresh "H" in
        intros x H; apply in_app_or in H; destruct H;
          [solve[auto]| cbv [In] in H; destruct H;
                        [|exfalso; assumption] ].
        subst x. cbv [compact_digit].
        rewrite Columns.compact_digit_mod by assumption.
        rewrite !uweight_succ, Z.div_mul by
            (apply Z.neq_mul_0; split; auto; omega).
        apply Z.mod_pos_bound, Z.gt_lt, bound_pos. }
    Qed.

    Lemma small_left_append {n} b x :
      0 <= x < bound -> small b -> small (@left_append _ n x b).
    Proof.
      intros.
      cbv [small].
      setoid_rewrite Tuple.to_list_left_append.
      setoid_rewrite in_app_iff.
      intros y HIn; destruct HIn as [HIn|[]]; (contradiction||omega||eauto).
    Qed.

    Lemma small_add n a b :
      (2 <= bound) ->
      small a -> small b -> small (@add n a b).
    Proof.
      intros.
      cbv [add add_cps]; autorewrite with uncps push_id in *.
      pose proof @B.Positional.small_sat_add bound ltac:(omega) _ a b.
      eapply small_left_append; eauto.
      rewrite @B.Positional.sat_add_div by omega.
      repeat match goal with H:_|-_=> unique pose proof (eval_small _ _ H) end.
      cbv [eval] in *; Z.div_mod_to_quot_rem; nia.
    Qed.

    Lemma small_join0 {n} b : small b -> small (@join0 n b).
    Proof.
      cbv [join0 join0_cps]; autorewrite with uncps push_id in *.
      eapply small_left_append; omega.
    Qed.

    Lemma small_add_S1 n a b :
      (2 <= bound) ->
      small a -> small b -> small (@add_S1 n a b).
    Proof.
      intros.
      cbv [add_S1 add_S1_cps Let_In]; autorewrite with uncps push_id in *.
      eauto using small_add, small_join0.
    Qed.

    Lemma small_left_tl n (v:T (S n)) : small v -> small (left_tl v).
    Proof. cbv [small]. auto using Tuple.In_to_list_left_tl. Qed.

    Lemma eval_drop_high n v :
      small v -> eval (@drop_high n v) = eval v mod (uweight bound n).
    Proof.
      cbv [drop_high drop_high_cps eval].
      rewrite Tuple.left_tl_cps_correct, push_id. (* TODO : for some reason autorewrite with uncps doesn't work here *)
      intro H. apply small_left_tl in H.
      rewrite (subst_left_append v) at 2.
      autorewrite with push_basesystem_eval.
      apply eval_small in H.
      rewrite Z.mod_add_l' by (pose_uweight bound; auto).
      rewrite Z.mod_small; auto.
    Qed.

    Lemma small_drop_high n v : small v -> small (@drop_high n v).
    Proof.
      cbv [drop_high drop_high_cps].
      rewrite Tuple.left_tl_cps_correct, push_id.
      apply small_left_tl.
    Qed.

    Lemma div_nonzero_neg_iff x y : x < y -> 0 < y ->
                                    - (x / y) = 0 <-> x <? 0 = false.
    Proof.
      repeat match goal with
             | _ => progress intros
             | _ => rewrite Z.ltb_ge
             | _ => rewrite Z.opp_eq_0_iff
             | _ => rewrite Z.div_small_iff by omega
             | _ => split
             | _ => omega
             end.
   Qed.

    Lemma eval_sub_then_maybe_add n mask p q r:
      small p -> small q -> small r ->
      (map (Z.land mask) r = r) ->
      (0 <= eval p < eval r) -> (0 <= eval q < eval r) ->
      eval (@sub_then_maybe_add n mask p q r) = eval p - eval q + (if eval p - eval q <? 0 then eval r else 0).
    Proof.
      pose_all.
      pose proof (@uweight_le_mono _ bound_pos n (S n) (Nat.le_succ_diag_r _)).
      intros.
      repeat match goal with
             | _ => progress (intros; cbv [eval runtime_opp sub_then_maybe_add sub_then_maybe_add_cps] in * )
             | _ => progress autorewrite with uncps push_id push_basesystem_eval
             | _ => rewrite eval_drop_high by (apply @B.Positional.small_sat_add; omega)
             | _ => rewrite B.Positional.sat_sub_mod by omega
             | _ => rewrite B.Positional.sat_sub_div by omega
             | _ => rewrite B.Positional.sat_add_mod by omega
             | _ => rewrite B.Positional.eval_left_append
             | _ => rewrite eval_join0
             | H : small _ |- _ => apply eval_small in H
             end.
      let H := fresh "H" in
      match goal with |- context [- (?X / ?Y) = 0] =>
                      assert ((- (X / Y) = 0) <-> X <? 0 = false) as H
                             by (apply div_nonzero_neg_iff; omega)
      end; destruct H.
      break_match;  try match goal with
                          H : ?x = ?x -> _ |- _
                          => specialize (H (eq_refl x)) end;
      try congruence;
      match goal with
      | H : _ |- _ => rewrite Z.ltb_ge in H
      | H : _ |- _ => rewrite Z.ltb_lt in H
      end.
      { repeat (rewrite Z.mod_small; try omega). }
      { rewrite !Z.mul_opp_r, Z.opp_involutive.
        rewrite Z.mul_div_eq_full by (subst; auto).
        match goal with |- context [?a - ?b + ?b] =>
                        replace (a - b + b) with a by ring end.
        repeat (rewrite Z.mod_small; try omega). }
    Qed.

   Lemma small_sub_then_maybe_add n mask (p q r : T n) :
      small (sub_then_maybe_add mask p q r).
   Proof.
     cbv [sub_then_maybe_add_cps sub_then_maybe_add]; intros.
     repeat progress autounfold. autorewrite with uncps push_id.
     apply small_drop_high,  @B.Positional.small_sat_add; omega.
   Qed.

    Lemma map2_zselect n cond x y :
      Tuple.map2 (n:=n) (Z.zselect cond) x y = if dec (cond = 0) then x else y.
    Proof.
      unfold Z.zselect.
      break_innermost_match; Z.ltb_to_lt; subst; try omega;
        [ rewrite Tuple.map2_fst, Tuple.map_id
        | rewrite Tuple.map2_snd, Tuple.map_id ];
        reflexivity.
    Qed.

    Lemma eval_conditional_sub_nz n (p:T (S n)) (q:T n)
          (n_nonzero: (n <> 0)%nat) (psmall : small p) (qsmall : small q):
      0 <= eval p < eval q + uweight bound n ->
      eval (conditional_sub p q) = eval p + (if eval q <=? eval p then - eval q else 0).
    Proof.
      pose_all.
      pose proof (@uweight_le_mono _ bound_pos n (S n) (Nat.le_succ_diag_r _)).
      intros.
      repeat match goal with
             | _ => progress (intros; cbv [eval conditional_sub conditional_sub_cps] in * )
             | _ => progress autorewrite with uncps push_id push_basesystem_eval
             | _ => rewrite eval_drop_high
                 by (break_match; try assumption; apply @B.Positional.small_sat_sub; omega)
             | _ => rewrite map2_zselect
             | _ => rewrite B.Positional.sat_sub_mod by omega
             | _ => rewrite B.Positional.sat_sub_div by omega
             | _ => rewrite B.Positional.sat_add_mod by omega
             | _ => rewrite B.Positional.eval_left_append
             | _ => rewrite eval_join0
             | H : small _ |- _ => apply eval_small in H
             end.
      let H := fresh "H" in
      match goal with |- context [- (?X / ?Y) = 0] =>
                      assert ((- (X / Y) = 0) <-> X <? 0 = false) as H
                             by (apply div_nonzero_neg_iff; omega)
      end; destruct H.
      break_match;  try match goal with
                          H : ?x = ?x -> _ |- _
                          => specialize (H (eq_refl x)) end;
      repeat match goal with
      | H : _ |- _ => rewrite Z.leb_gt in H
      | H : _ |- _ => rewrite Z.leb_le in H
      | H : _ |- _ => rewrite Z.ltb_lt in H
      | H : _ |- _ => rewrite Z.ltb_ge in H
      end; try omega.
      { rewrite @B.Positional.sat_sub_mod by omega.
        rewrite eval_join0; cbv [eval].
        repeat (rewrite Z.mod_small; try omega). }
      { repeat (rewrite Z.mod_small; try omega). }
    Qed.

    Lemma eval_conditional_sub n (p:T (S n)) (q:T n)
           (psmall : small p) (qsmall : small q) :
      0 <= eval p < eval q + uweight bound n ->
      eval (conditional_sub p q) = eval p + (if eval q <=? eval p then - eval q else 0).
    Proof.
      destruct n; [|solve[auto using eval_conditional_sub_nz]].
      repeat match goal with
             | _ => progress (intros; cbv [T tuple tuple'] in p, q)
             | q : unit |- _ => destruct q
             | _ => progress (cbv [conditional_sub conditional_sub_cps eval] in * )
             | _ => progress autounfold
             | _ => progress (autorewrite with uncps push_id push_basesystem_eval in * )
             | _ => (rewrite uweight_0 in * )
             | _ => assert (p = 0) by omega; subst p; break_match; ring
             end.
    Qed.

    Lemma small_conditional_sub n (p:T (S n)) (q:T n)
           (psmall : small p) (qsmall : small q) :
      0 <= eval p < eval q + uweight bound n ->
      small (conditional_sub p q).
    Proof.
      intros.
      cbv [conditional_sub conditional_sub_cps]; autorewrite with uncps push_id.
      eapply small_drop_high.
      rewrite map2_zselect; break_match; [|assumption].
      eauto using @B.Positional.small_sat_sub with omega.
    Qed.

    Lemma eval_scmul n a v : small v -> 0 <= a < bound ->
      eval (@scmul n a v) = a * eval v.
    Proof.
      intro Hsmall. pose_all. apply eval_small in Hsmall.
      intros. cbv [scmul scmul_cps eval] in *. repeat autounfold.
      autorewrite with uncps push_id push_basesystem_eval.
      rewrite uweight_0, Z.mul_1_l. apply Z.mod_small.
      split; [solve[Z.zero_bounds]|]. cbv [uweight] in *.
      rewrite !Nat2Z.inj_succ, Z.pow_succ_r by auto using Nat2Z.is_nonneg.
      apply Z.mul_lt_mono_nonneg; omega.
    Qed.

    Lemma small_scmul n a v : small (@scmul n a v).
    Proof.
      cbv [scmul scmul_cps eval] in *. repeat autounfold.
      autorewrite with uncps push_id push_basesystem_eval.
      apply small_compact.
    Qed.

    (* TODO : move to tuple *)
    Lemma from_list_tl {A n} (ls : list A) H H':
      from_list n (List.tl ls) H = tl (from_list (S n) ls H').
    Proof.
      induction ls; distr_length. simpl List.tl.
      rewrite from_list_cons, tl_append, <-!(from_list_default_eq a ls).
      reflexivity.
    Qed.

    Lemma eval_div n p : small p -> eval (fst (@divmod n p)) = eval p / bound.
    Proof.
      cbv [divmod divmod_cps eval]. intros.
      autorewrite with uncps push_id cancel_pair.
      rewrite (subst_append p) at 2.
      rewrite uweight_eval_step. rewrite hd_append, tl_append.
      rewrite Z.div_add' by omega. rewrite Z.div_small by auto using small_hd.
      ring.
    Qed.

    Lemma eval_mod n p : small p -> snd (@divmod n p) = eval p mod bound.
    Proof.
      cbv [divmod divmod_cps eval]. intros.
      autorewrite with uncps push_id cancel_pair.
      rewrite (subst_append p) at 2.
      rewrite uweight_eval_step, Z.mod_add'_full, hd_append.
      rewrite Z.mod_small by auto using small_hd. reflexivity.
    Qed.

    Lemma small_div n v : small v -> small (fst (@divmod n v)).
    Proof.
      cbv [divmod divmod_cps]. intros.
      autorewrite with uncps push_id cancel_pair.
      auto using small_tl.
    Qed.
  End Proofs.
End API.
Hint Rewrite nonzero_id join0_id divmod_id drop_high_id scmul_id add_id add_S1_id add_S2_id sub_then_maybe_add_id conditional_sub_id : uncps.
