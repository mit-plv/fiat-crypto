Require Import coqutil.Datatypes.List.
Require Import Bedrock.P256.Specs.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.AbsintWordToZ coqutil.Z.Lia.

Import Specs.point
  bedrock2.Syntax
  bedrock2.NotationsCustomEntry
  micromega.Lia
  ProgramLogic
  WeakestPrecondition
  ProgramLogic.Coercions
  SeparationLogic
  letexists
  BasicC64Semantics
  ListIndexNotations
  SepAutoArray
  OfListWord
  BinInt
  PrimeFieldTheorems
  symmetry
  Arith
  Array
  memcpy.

Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.

(* TODO swap these for Import (notations) coqutil.Map.Memory. once landed.*)
Local Notation "xs $@ a" := (map.of_list_word_at a xs)
(at level 10, format "xs $@ a").
Local Notation "$ n" := (match word.of_Z n return word with w => w end) (at level 9, format "$ n").
Local Notation "p .+ n" := (word.add p (word.of_Z n)) (at level 50, format "p .+ n", left associativity).
Local Coercion F.to_Z : F >-> Z.

#[local] Notation sizeof_point := 96%nat.

Definition p256_precompute_multiples := func! (p_table, p_P) {
  p256_point_set_zero(p_table);
  br_memcpy(p_table + $sizeof_point, p_P, $sizeof_point);

  i = $2;
  while ($17 - i) {
    if (i & $1) {
      unpack! ok = p256_point_add_nz_nz_neq(
        p_table + ($sizeof_point * i),
        p_table + ($sizeof_point * (i - $1)),
        p_P
      );
      $(cmd.unset "ok")
    } else {
      p256_point_double(
        p_table + ($sizeof_point * i),
        p_table + ($sizeof_point * (i >> $1))
      )
    };
    i = i + $1
  }
}.

Import Crypto.Spec.WeierstrassCurve
  Crypto.Curves.Weierstrass.Affine
  Crypto.Curves.Weierstrass.AffineProofs
  Crypto.Curves.Weierstrass.Jacobian.Jacobian
  Curves.Weierstrass.P256
  Crypto.Bedrock.P256.Specs
  bedrock2.ZnWords.
Require Import bedrock2.bottom_up_simpl.

Module W.
  (* Creates 0..(n-1)*P as list. *)
  Definition multiples n P := map (fun i : nat => W.mul i P) (seq 0 n).
End W.

Lemma multiples_succ_l (n : nat) (P : W.point) :
  W.multiples (S n) P = W.multiples n P ++ [(W.mul n P)].
Proof. cbv [W.multiples]. rewrite seq_S, map_app, map_cons; trivial. Qed.

Lemma length_multiples (n : nat) (A : W.point) :
  Logic.eq (List.length (W.multiples n A)) n.
Proof. cbv [W.multiples]. rewrite length_map, length_seq; trivial. Qed.

Local Ltac solve_num_pre := repeat rewrite ?length_skipn, ?length_multiples, ?length_nil,
  ?length_firstn, ?map_length, ?length_point, ?length_app, ?length_cons in *.

Local Ltac solve_num := solve_num_pre; try lia; ZnWords.

Lemma multiples_add_l n m P :
  W.multiples (n+m) P = W.multiples n P ++ skipn n (W.multiples (n+m) P).
Proof.
  cbv [W.multiples].
  rewrite ListUtil.seq_add, map_app, skipn_app, skipn_all2.
  all: rewrite length_map, length_seq, ?Nat.sub_diag; trivial.
Qed.

Lemma skipn_multiples (n k : nat) P :
  (k <= n)%nat ->
  W.multiples n P = (W.multiples k P) ++ (skipn k (W.multiples n P)).
Proof.
  intros H.
  pose proof multiples_add_l k (n-k) P.
  replace (k + (n - k))%nat with n in * by lia; trivial.
Qed.

Lemma multiples_nth (n : nat) (A : W.point):
  forall i : nat, i < n ->
  (List.nth_default (W.zero) (W.multiples n A) i) = W.mul i A.
Proof.
  cbv [W.multiples]; intros.
  erewrite ListUtil.map_nth_default with (x:=O) by (rewrite length_seq; lia).
  rewrite ListUtil.nth_default_seq_inbounds by lia; trivial.
Qed.

#[local] Notation pointarray := (array (fun (p : word.rep) (Q : point) =>
  sepclause_of_map ((to_bytes Q)$@p)) (word.of_Z (Z.of_nat 96))).

#[local] Notation to_affine := Jacobian.to_affine.
#[local] Notation of_affine := Jacobian.of_affine.

#[export] Instance spec_of_p256_precompute_multiples : spec_of "p256_precompute_multiples" :=
  fnspec! "p256_precompute_multiples" p_table p_P / out (P : point) R,
  { requires t m :=
      m =* out$@p_table * P$@p_P * R /\
      length out = (sizeof_point * 17)%nat /\
      ~ Jacobian.iszero P;
    ensures t' m := t' = t /\ exists out,
      m =* pointarray p_table out * P$@p_P * R /\
      List.Forall2 W.eq (map to_affine out) (W.multiples 17 (to_affine P))
  }.

(* Matches up word additions in a simple equation. *)
Ltac match_up_pointers :=
  match goal with |- eq ?A ?B =>
    match A with context [word.add ?a1 ?a2] =>
    match B with context [word.add ?b1 ?b2] =>
      replace (word.add a1 a2) with (word.add b1 b2) by solve_num
    end end
  end.

Lemma pointlist_firstn_nth_skipn (l : list point) (n : nat):
  n < length l ->
  l = (firstn n l) ++ [(nth_default (of_affine W.zero) l n)] ++ (skipn (S n) l).
Proof. intros. rewrite nth_default_eq, firstn_nth_skipn; [reflexivity | solve_num]. Qed.

Lemma pointarray_split_nth p (l : list point) (n : nat):
  n < length l ->
  Lift1Prop.iff1
    (pointarray p l)
    (pointarray p (firstn n l) *
      (sepclause_of_map ((to_bytes (nth_default (of_affine W.zero) l n))$@(p.+(sizeof_point * n)))) *
      (pointarray (p .+ (sizeof_point * (S n))) (skipn (S n) l)))%sep.
Proof.
  intros. etransitivity.
  { eapply array_index_nat_inbounds with (n:=n). lia. }
  rewrite <- hd_skipn_nth_default.
  cancel.
  do 2 (cancel_seps_at_indices 0%nat 0%nat; [match_up_pointers; exact eq_refl|]).
  ecancel.
Qed.

#[local] Ltac hyp_containing a := match goal with H : context[a] |- _ => H end.

Lemma p256_precompute_multiples_ok : program_logic_goal_for_function! p256_precompute_multiples.
Proof.
  repeat straightline.

  seprewrite_in_by (Array.list_word_at_firstn_skipn p_table out sizeof_point) ltac:(hyp_containing (m)) solve_num.
  bottom_up_simpl_in_hyps.

  straightline_call; ssplit; [ecancel_assumption|solve_num|].

  repeat straightline.

  seprewrite_in_by (Array.list_word_at_firstn_skipn (p_table.+96) (skipn 96 out) sizeof_point)
      ltac:(hyp_containing (a0)) solve_num.
  bottom_up_simpl_in_hyps.

  straightline_call; ssplit.
  { ecancel_assumption. }
  1-3: solve_num.

  repeat straightline.

  refine ((Loops.tailrec
      (HList.polymorphic_list.nil)
      (["p_table";"p_P";"i"]))
      (fun (v:nat) t m p_table p_P i => PrimitivePair.pair.mk (
        exists multiples todo,
        m =* (todo$@(p_table.+(Z.mul i sizeof_point)) *
              pointarray p_table multiples * P$@p_P * R)%sep /\
              2 <= i <= 17 /\
              v = i :> Z /\
              length todo + sizeof_point*i = 17*sizeof_point /\
              Forall2 W.eq (map to_affine multiples) (W.multiples v (to_affine P)))
      (fun T M (P_TABLE P_P I : word) => t = T /\ exists multiples : list point,
              M =* pointarray p_table multiples * P$@p_P * R /\
              Forall2 W.eq (map to_affine multiples) ((W.multiples 17 (Jacobian.to_affine P)))))
      (fun v' v => v < v' <= 17)%nat
      _ _ _ _ _); Loops.loop_simpl.
  { cbv [Loops.enforce]; cbn. split; exact eq_refl. }
  { apply Nat.gt_wf. }
  { repeat straightline.
    eexists [(Jacobian.of_affine W.zero); P], _; ssplit.
    { cbv [array]. bottom_up_simpl_in_goal. ecancel_assumption. }
    { ZnWords. }
    { ZnWords. }
    { rewrite Znat.Z2Nat.id; [exact eq_refl|ZnWords]. }
    { listZnWords. }
    { repeat constructor. rewrite ScalarMult.scalarmult_1_l. reflexivity. }
  }

  (* Loop postcondition implies function postcondition. *)
  2: {
    repeat straightline.
    eexists; ssplit; [ecancel_assumption|trivial].
  }

  intros ?v ?t ?m ?p_table ?p_P ?i.
  repeat straightline.

  all : rename x into multiples.
  all : rename x0 into todo.

  (* Loop postcondition holds after the final iteration *)
  2: {
    replace todo with (@nil Byte.byte) in *; cycle 1.
    { symmetry. apply length_zero_iff_nil. listZnWords. }
    rewrite ?map.of_list_word_nil in *.

    (* TODO: extract this lemma to coqutil.Map.Separation *)
    assert (sepclause_of_map_empty : Lift1Prop.iff1 (sepclause_of_map (map:=mem) Interface.map.empty) (emp True)).
    { cbv [sepclause_of_map emp]; split; intuition congruence. }

    seprewrite_in sepclause_of_map_empty ltac:(hyp_containing m0).
    eexists; ssplit; [ecancel_assumption|].
    eqapply H12. f_equal. ZnWords.
  }

  (* Loop invariant is preserved. *)

  assert (word.unsigned i0 < 17) by ZnWords.

  (* Split it out the first element of todo, which is the one we will fill in this iteration. *)
  seprewrite_in_by (Array.list_word_at_firstn_skipn (p_table0.+word.unsigned i0 * Z.of_nat 96) todo sizeof_point)
      ltac:(hyp_containing (m0)) solve_num.

  unfold1_cmd_goal; cbv beta match delta [cmd_body].
  repeat straightline.
  split; repeat straightline.

  (* i is odd -> addition. *)
  { assert (3 <= word.unsigned i0). {
      let H := unsigned.zify_expr v0 in try rewrite H in *; clear H.
      ZnWords.
    }

    (* Length of multiples is v. *)
    match goal with H : _ |- _ =>
      let Hl := fresh in
      pose proof Forall2_length H as Hl; rewrite ?length_map, ?length_multiples in Hl
    end.

    (* Split out i-1 * P and remember equations to easily but multiples back together in the postcondition. *)
    seprewrite_in_by (pointarray_split_nth p_table0 multiples (v - 1))
        ltac:(hyp_containing (m0)) solve_num.

    set (nth_default (Jacobian.of_affine W.zero) multiples (v - 1)) as vm1P in *.
    assert (W.eq (Jacobian.to_affine vm1P)
                (W.mul (Z.of_nat (v - 1)) (Jacobian.to_affine P))) as Hvm1P. {
      subst vm1P.
      erewrite <-ListUtil.map_nth_default_always.
      erewrite <- (multiples_nth v) by lia.
      rewrite  Jacobian.to_affine_of_affine.
      eapply ListUtil.Forall2_forall_iff'; [solve_num|assumption|solve_num].
    }

    (* p256_point_add_nz_nz_neq *)
    straightline_call; ssplit.
    { use_sep_assumption; cancel.
      (* Set Ltac Profiling. *)
      cancel_seps_at_indices 3%nat 0%nat; [match_up_pointers; exact eq_refl|]. (* 0.4s *)
      cancel_seps_at_indices 1%nat 0%nat; [match_up_pointers; exact eq_refl|]. (* 0.5s *)
      cbv [seps]; ecancel. }
    { solve_num. }

    repeat straightline.

    let h := hyp_containing @Forall2 in rename h into Hf2.

    unshelve (match goal with H : ~ Jacobian.iszero ?P -> _ |- _ =>
        repeat (let HH := fresh in assert (~ Jacobian.iszero P);
        [shelve|specialize (H HH)]); trivial;
        rename H into Hadd end).
    { rewrite Jacobian.iszero_iff. rewrite Hvm1P.
       rewrite <- (ScalarMult.scalarmult_0_l (eq:=W.eq) (Jacobian.to_affine P)), p256_mul_mod_n.
        cbv [p256_group_order]; PreOmega.Z.div_mod_to_equations; lia. }

    destruct Hadd as [(?&?&?)|[? Hadd] ]; trivial; [|contradict Hadd]; cycle 1.
    { (* no doubling *)
      rewrite Jacobian.eq_iff. rewrite Hvm1P.
        rewrite <- (ScalarMult.scalarmult_1_l (eq:=W.eq) (to_affine P)) at 2.
        rewrite p256_mul_mod_n.
        cbv [p256_group_order]; PreOmega.Z.div_mod_to_equations; lia. }

    repeat straightline.

     eexists (S v); split.
    { subst i. subst x0.
      eexists (multiples ++ [_]), (skipn sizeof_point todo); ssplit.
      { rewrite (pointlist_firstn_nth_skipn multiples (v - 1)) by solve_num.
        repeat seprewrite @array_append; repeat seprewrite @array_cons;
        repeat rewrite List.skipn_all by solve_num; repeat seprewrite @array_nil.
        use_sep_assumption; rewrite List.skipn_all by solve_num; cancel.
        cancel_seps_at_indices 0%nat 0%nat; [match_up_pointers; exact eq_refl|].
        cancel_seps_at_indices 0%nat 0%nat; [match_up_pointers; exact eq_refl|].
        cancel_seps_at_indices 1%nat 0%nat; [match_up_pointers; exact eq_refl|].
        cbn [array seps]. cancel. }
      5: { rewrite multiples_succ_l. rewrite ?map_app.
        apply Forall2_app.
        { assumption. }
        repeat constructor.
        rewrite Jacobian.to_affine_add_inequal_nz_nz by assumption.
        rewrite Hvm1P.
        rewrite <- (ScalarMult.scalarmult_1_l (mul:=W.mul) (eq:=W.eq) (Jacobian.to_affine P)) at 2.
        rewrite <-ScalarMult.scalarmult_add_l.
        Morphisms.f_equiv; lia.
      }
      all: solve_num.
    }
    split; repeat ssplit; try trivial; lia.
  }
  (* i is even -> doubling. *)
  { assert (word.unsigned (word.sru i0 (word.of_Z 1)) = (v / 2)%nat) as Idiv2. {
      rewrite Znat.Nat2Z.inj_div. ZnWords.
    }
    let H := unsigned.zify_expr v0 in rewrite H in *; clear H.

    (* Length of multiples is v. *)
    match goal with H : _ |- _ =>
      let Hl := fresh in
      pose proof Forall2_length H as Hl; rewrite ?length_map, ?length_multiples in Hl
    end.

    (* We need point (i/2)*P from the table. *)
    seprewrite_in_by (pointarray_split_nth p_table0 multiples (v / 2))
                      ltac:(hyp_containing (p_table0)) solve_num.
    set (vd2P := nth_default (Jacobian.of_affine W.zero) multiples (v / 2)) in *.

    straightline_call; ssplit.
    { use_sep_assumption; cancel.
      cancel_seps_at_indices 3%nat 0%nat; [match_up_pointers; exact eq_refl|].
      cancel_seps_at_indices 1%nat 0%nat; [match_up_pointers; exact eq_refl|].
      cbv [seps]; ecancel.
    }
    { solve_num. }

    repeat straightline.
    eexists (S v).
    split; [ssplit|split; [lia|intros;assumption]].
    { eexists (multiples ++ [_]), (skipn sizeof_point todo); ssplit.
      { rewrite (pointlist_firstn_nth_skipn multiples (v / 2)) by solve_num.
        repeat seprewrite @array_append; repeat seprewrite @array_cons. repeat seprewrite @array_nil.
        use_sep_assumption; cancel.
        do 4 (cancel_seps_at_indices 0%nat 0%nat; [match_up_pointers; exact eq_refl|]).
        ecancel.
      }
      5: { rewrite multiples_succ_l. rewrite ?map_app.
        apply Forall2_app. { assumption. } repeat constructor.
        rewrite <- Jacobian.double_minus_3_eq_double, Jacobian.to_affine_double.

        assert (W.eq (Jacobian.to_affine vd2P) (W.mul (v / 2)%nat (Jacobian.to_affine P))) as ->. {
          subst vd2P.
          rewrite <- ListUtil.map_nth_default_always, Jacobian.to_affine_of_affine.
          erewrite <- multiples_nth.
          { apply ListUtil.Forall2_forall_iff; [|eassumption|]; solve_num. }
          solve_num.
        }
        rewrite <- ScalarMult.scalarmult_add_l.
        Morphisms.f_equiv. solve_num.
      }
      all: solve_num.
    }
  }
Qed.
