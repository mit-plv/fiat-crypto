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

Local Notation "xs $@ a" := (map.of_list_word_at a xs)
(at level 10, format "xs $@ a").
Local Notation "$ n" := (match word.of_Z n return word with w => w end) (at level 9, format "$ n").
Local Notation "p .+ n" := (word.add p (word.of_Z n)) (at level 50, format "p .+ n", left associativity).
Local Coercion F.to_Z : F >-> Z.

#[local] Notation sizeof_point := 96%nat.

Definition p256_precompute_table := func! (p_table, p_P) {
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
  (* Creates 0..n*P as list. *)
  Fixpoint multiples (n : nat) (P : W.point) : list W.point :=
    match n with
      | 0%nat => [(W.mul 0 P)]
      | S n => (multiples n P) ++ [(W.mul (S n) P)]
    end.
End W.

Lemma multiples_app (n : nat) (P : W.point) :
  W.multiples (S n) P = W.multiples n P ++ [(W.mul (S n) P)].
Proof. reflexivity. Qed.

Lemma length_multiples (n : nat) (A : W.point) :
  Logic.eq (List.length (W.multiples n A)) (S n).
Proof.
  induction n.
  - cbv [W.multiples length]. reflexivity.
  - rewrite multiples_app, length_app, length_cons, length_nil, IHn. lia.
Qed.

Local Ltac solve_num_pre := repeat rewrite ?length_skipn, ?length_multiples, ?length_nil, ?length_firstn,
    ?map_length, ?length_point, ?length_app, ?length_cons in *.

Local Ltac solve_num := solve_num_pre; try lia; pose proof Naive.word64_ok; ZnWords.

Local Ltac solve_mod_eq := unfold p256_group_order; rewrite Zdiv.Z.cong_iff_0, Z.mod_divide by solve_num;
      intros [?x]; solve_num.

Lemma skipn_multiples (n k : nat) P :
  (k <= n)%nat ->
  W.multiples n P = (W.multiples k P) ++ (skipn (S k) (W.multiples n P)).
Proof.
  generalize dependent k.
  induction n; intros.
  { destruct k; [reflexivity | lia]. }
  { destruct (lt_dec k (S n)).
    { rewrite multiples_app, (IHn k) by solve_num.
      rewrite <- app_assoc, !skipn_app. f_equal.
      rewrite (List.skipn_all (S k) (W.multiples k P)) by solve_num.
      rewrite app_nil_l, skipn_skipn. repeat f_equal; [solve_num|].
      etransitivity; [symmetry; apply skipn_0|].
      f_equal. solve_num.
    }
    { rewrite List.skipn_all; [rewrite app_nil_r|rewrite length_multiples;solve_num]. f_equal. solve_num. }
  }
Qed.

Lemma multiples_nth (n : nat) (A : W.point):
  forall k : nat, k <= n ->
  (List.nth k (W.multiples n A) (W.zero)) = W.mul k A.
Proof.
  intros.
  rewrite (skipn_multiples n k) by solve_num.
  rewrite app_nth1 by solve_num.
  destruct k.
  { cbv [W.multiples nth]. f_equal. }
  { rewrite multiples_app, app_nth2 by solve_num.
    rewrite length_multiples.
    replace (S k - S k)%nat with 0%nat by lia.
    reflexivity.
  }
Qed.

Notation pointarray := (array (fun (p : word.rep) (Q : point) => sepclause_of_map ((to_bytes Q)$@p)) (word.of_Z (Z.of_nat 96))).

#[export] Instance spec_of_p256_precompute_table : spec_of "p256_precompute_table" :=
  fnspec! "p256_precompute_table" p_table p_P / out (P : point) R,
  { requires t m := m =* out$@p_table * P$@p_P * R /\ length out = (sizeof_point * 17)%nat /\
      ~ Jacobian.iszero P;
    ensures t' m := t' = t /\ exists out_multiples,
      List.Forall2 W.eq (map Jacobian.to_affine out_multiples) (W.multiples 16 (Jacobian.to_affine P)) /\
      m =* pointarray p_table out_multiples * P$@p_P * R
  }%sep.

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
  l = (firstn n l) ++ [(nth n l (Jacobian.of_affine W.zero))] ++ (skipn (S n) l).
Proof. intros. rewrite firstn_nth_skipn; [reflexivity | solve_num]. Qed.

Lemma pointarray_split_nth p (l : list point) (n : nat):
  n < length l ->
  Lift1Prop.iff1
    (pointarray p l)
    (pointarray p (firstn n l) *
      (sepclause_of_map ((to_bytes (nth n l (Jacobian.of_affine W.zero)))$@(p.+(sizeof_point * n)))) *
      (pointarray (p .+ (sizeof_point * (S n))) (skipn (S n) l)))%sep.
Proof.
  intros. etransitivity.
  { eapply array_index_nat_inbounds with (n:=n). lia. }
  rewrite <- hd_skipn_nth_default, nth_default_eq.
  cancel.
  do 2 (cancel_seps_at_indices 0%nat 0%nat; [match_up_pointers; exact eq_refl|]).
  ecancel.
Qed.

Ltac hyp_containing a := match goal with H : context[a] |- _ => H end.

Lemma p256_precompute_table_ok : program_logic_goal_for_function! p256_precompute_table.
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
      (HList.polymorphic_list.cons _
      (HList.polymorphic_list.cons _
    (HList.polymorphic_list.nil)))
      (["p_table";"p_P";"i"]))
      (fun (j:nat) todo partial_multiples t m p_table p_P i => PrimitivePair.pair.mk (
        m =* (todo$@(p_table.+(Z.mul i sizeof_point)) *
              pointarray p_table partial_multiples * P$@p_P * R)%sep /\
              2 <= i <= 17 /\
              j = (17%nat - (Z.to_nat (word.unsigned i)))%nat/\
              length todo = (j * sizeof_point)%nat /\
              length partial_multiples = (Z.to_nat (word.unsigned i)) /\
        List.Forall2 W.eq (map Jacobian.to_affine partial_multiples)
            (W.multiples (Z.to_nat (word.unsigned i - 1)) (Jacobian.to_affine P))
          )
      (fun T M (P_TABLE P_P I : word) => t = T /\
                      exists multiples : list point,
                        M =* pointarray p_table multiples * P$@p_P * R /\
                        List.Forall2 W.eq (map Jacobian.to_affine multiples)
                          ((W.multiples 16%nat) (Jacobian.to_affine P))
                        ))
      lt
      _ _ _ _ _ _ _); Loops.loop_simpl.
  { cbv [Loops.enforce]; cbn. split; exact eq_refl. }
  { eapply Wf_nat.lt_wf. }
  { repeat straightline. subst i. ssplit.
    { instantiate (1:= ([(Jacobian.of_affine W.zero); P])).
      cbv [array]. bottom_up_simpl_in_goal. ecancel_assumption. }
    6: { bottom_up_simpl_in_goal. cbv [W.multiples map List.app].
      repeat constructor.
      { rewrite ScalarMult.scalarmult_1_l. reflexivity. }}
    3: exact eq_refl.
    all: solve_num.
  }

  (* Loop postcondition implies function postcondition. *)
  2: {
    repeat straightline.
    eexists _.
    split; [eassumption|ecancel_assumption].
  }

  intros ?j ?todo ?partial_multiples ?t ?m ?p_table ?p_P ?i.
  repeat straightline.

  (* Loop postcondition holds after the final iteration *)
  2: {
    assert (word.unsigned i0 = 17) as Hi0 by solve_num.
    subst j; rewrite Hi0 in *.

    destruct todo; [|solve_num].

    exists partial_multiples.
    split; [|assumption].
    rewrite map.of_list_word_nil in *.
    use_sep_assumption. cancel.
    cbv [seps emp Lift1Prop.iff1 sepclause_of_map]; intuition auto.
  }

  (* Loop invariant is preserved. *)

  assert (word.unsigned i0 < 17) by solve_num.

  (* Split it out the first element of todo, which is the one we will fill in this iteration. *)
  seprewrite_in_by (Array.list_word_at_firstn_skipn (p_table0.+word.unsigned i0 * Z.of_nat 96) todo sizeof_point)
      ltac:(hyp_containing (m0)) solve_num.

  unfold1_cmd_goal; cbv beta match delta [cmd_body].
  repeat straightline.
  split; repeat straightline.

  (* i is odd -> addition. *)
  { assert (3 <= word.unsigned i0). {
      let H := unsigned.zify_expr v in try rewrite H in *; clear H.
      solve_num.
    }

    (* Split out i-1 * P and remember equations to easily but partial_multiples back together in the postcondition. *)
    seprewrite_in_by (pointarray_split_nth p_table0 partial_multiples (Z.to_nat (word.unsigned i0 - 1)))
        ltac:(hyp_containing (m0)) solve_num.
    unshelve epose proof
        (pointlist_firstn_nth_skipn partial_multiples (Z.to_nat (word.unsigned i0 - 1)) _) as Hremember; [solve_num|].
    rewrite List.skipn_all in Hremember by solve_num. rewrite app_nil_r in Hremember.
    set (nth (Z.to_nat (word.unsigned i0 - 1)) partial_multiples (Jacobian.of_affine W.zero)) as i0m1P.

    (* p256_point_add_nz_nz_neq *)
    straightline_call; ssplit.
    { use_sep_assumption; cancel.
      (* Set Ltac Profiling. *)
      cancel_seps_at_indices 3%nat 0%nat; [match_up_pointers; exact eq_refl|].
      cancel_seps_at_indices 1%nat 0%nat; [match_up_pointers; exact eq_refl|].
      (* Show Ltac Profile. *)
      (* TODO: Resolve set bottleneck in better_lia:
       ─solve_num ----------------------------------   0.0%  42.1%      13    5.191s
        ├─solve_num_pre ----------------------------   0.1%  30.0%      13    3.202s
        │└rewrite ?length_skipn, ?length_multiples,   30.0%  30.0%      64    0.419s
        └─ZnWords ----------------------------------   0.0%  11.4%      13    1.936s
          ├─better_lia -----------------------------   0.0%   7.4%      13    1.314s
          │└PreOmega.Z.div_mod_to_equations --------   0.0%   6.8%      13    1.209s
          │└PreOmega.Z.div_mod_to_equations' -------   0.0%   5.3%      13    0.976s
          │└PreOmega.Z.div_mod_to_equations_step ---   0.1%   5.3%       0    0.060s
          │└PreOmega.Z.div_mod_to_equations_generali   0.1%   5.1%     170    0.058s
          │ ├─set (q := x / y) in * ----------------   2.5%   2.5%      85    0.029s
          │ └─set (r := x mod y) in * --------------   2.4%   2.4%      85    0.029s
          └─ZnWords_pre ----------------------------   0.0%   4.0%      13    0.622s
      *)
      cbv [seps]; ecancel. }
    { solve_num. }

    repeat straightline.

    assert (W.eq (Jacobian.to_affine i0m1P)
                (W.mul (Z.of_nat (Z.to_nat (word.unsigned i0 - 1))) (Jacobian.to_affine P))) as WeqI0m1P. {
      subst i0m1P.
      erewrite <- multiples_nth.
      { rewrite <- (map_nth Jacobian.to_affine), <- !nth_default_eq.
        apply ListUtil.Forall2_forall_iff; [|eassumption|]; solve_num. }
      { solve_num. }
    }

    (* To resolve the addition side condition, need that the points are not zero and not equal. *)
    assert (~ Jacobian.eq i0m1P P) as Ne. {
      rewrite Jacobian.eq_iff, <- (ScalarMult.scalarmult_1_l (eq:=W.eq) (Jacobian.to_affine P)),
          WeqI0m1P, p256_mul_mod_n.
      solve_mod_eq.
    }
    assert (~ Jacobian.iszero i0m1P) as Nz1. {
      rewrite Jacobian.iszero_iff, <- (ScalarMult.scalarmult_0_l (eq:=W.eq) (Jacobian.to_affine P)),
          WeqI0m1P, p256_mul_mod_n.
      solve_mod_eq.
    }

    (* TODO remove identifiers? *)
    specialize (H22 Nz1 H5). destruct H22.
    2: { destruct H18; contradiction. }

    repeat straightline.

    eexists _, _, _.
    split; [ssplit|split; [|intros;assumption]].
    { subst i.
      instantiate (1:= ((firstn (Z.to_nat (word.unsigned i0 - 1)) partial_multiples) ++ [i0m1P] ++ [(Jacobian.add_inequal_nz_nz i0m1P P x1) ])).
      rewrite !array_app. repeat seprewrite (array_cons (T:=point)).
      use_sep_assumption. cancel. subst x0. subst i0m1P.
      cancel_seps_at_indices 0%nat 0%nat; [match_up_pointers; exact eq_refl|].
      cancel_seps_at_indices 0%nat 1%nat; [match_up_pointers; exact eq_refl|].
      cancel_seps_at_indices 1%nat 2%nat; [match_up_pointers; exact eq_refl|].
      rewrite List.skipn_all by solve_num.
      cbv [array seps]. cancel.
    }
    6: { subst i; subst i0m1P.
      rewrite app_assoc, <-Hremember.
      destruct (Z.to_nat (word.unsigned i0)) as [|n] eqn: Hi0; [solve_num|].

      replace ((Z.to_nat (word.unsigned (i0.+1) - 1))) with (S n) by solve_num.
      rewrite multiples_app, ?map_app.
      apply Forall2_app.
      { replace n with (Z.to_nat (word.unsigned i0 - 1)) by solve_num.
        assumption.
      }
      repeat constructor.
      rewrite Jacobian.to_affine_add_inequal_nz_nz by assumption.
      set ((W.mul (Z.of_nat (S n)) (Jacobian.to_affine P))) as snp.
      rewrite <- (ScalarMult.scalarmult_1_l (eq:=W.eq) (Jacobian.to_affine P)).
      rewrite WeqI0m1P, <-ScalarMult.scalarmult_add_l.
      subst snp; Morphisms.f_equiv; solve_num.
    }
    3: exact eq_refl.
    all: solve_num.
  }
  (* i is even -> doubling. *)
  { let H := unsigned.zify_expr v in rewrite H in *; clear H.
    assert (word.unsigned (word.sru i0 (word.of_Z 1)) = word.unsigned i0 / 2) as Idiv2 by solve_num.

    (* We need point (i/2)*P from the table. *)
    seprewrite_in_by (pointarray_split_nth p_table0 partial_multiples (Z.to_nat (word.unsigned i0 / 2)))
                      ltac:(hyp_containing (p_table0)) solve_num.
    unshelve epose proof (pointlist_firstn_nth_skipn partial_multiples (Z.to_nat (word.unsigned i0 / 2)) _) as Hrem; [solve_num|].
    set (i0d2P := nth (Z.to_nat (word.unsigned i0 / 2)) partial_multiples (Jacobian.of_affine W.zero)) in *.

    straightline_call; ssplit.
    { use_sep_assumption; cancel.
      cancel_seps_at_indices 3%nat 0%nat; [match_up_pointers; exact eq_refl|].
      cancel_seps_at_indices 1%nat 0%nat; [match_up_pointers; exact eq_refl|].
      cbv [seps]; ecancel.
    }
    { solve_num. }

    repeat straightline.
    eexists _, _, _.
    split; [ssplit|split; [|intros;assumption]].
    { subst i.
      instantiate (1 := (
        (firstn (Z.to_nat (word.unsigned i0 / 2)) partial_multiples) ++
        [i0d2P] ++
        ((skipn (S (Z.to_nat (word.unsigned i0 / 2))) partial_multiples)) ++
        [(Jacobian.double_minus_3 eq_refl i0d2P)])).
      rewrite !array_app. seprewrite (array_cons (T:=point)).
      use_sep_assumption. cancel.
      cancel_seps_at_indices 1%nat 0%nat; [match_up_pointers; exact eq_refl|].
      cancel_seps_at_indices 1%nat 2%nat; [match_up_pointers; exact eq_refl|].
      cancel_seps_at_indices 1%nat 1%nat; [match_up_pointers; exact eq_refl|].
      cbv [array seps]. cancel.
      cancel_seps_at_indices 0%nat 0%nat; [match_up_pointers; exact eq_refl|].
      ecancel.
    }
    6: { (* Proof that 2 * (i/2) * P = i * P. *)
      subst i. rewrite !app_assoc, <- (app_assoc _ ([i0d2P])).
      rewrite <- Hrem, !map_app.
      destruct (Z.to_nat (word.unsigned i0)) as [|n] eqn:?H; [solve_num|].
      replace ((Z.to_nat (word.unsigned (i0.+1) - 1))) with (S n) by solve_num.
      rewrite  multiples_app.
      apply Forall2_app.
      { replace n with ((Z.to_nat (word.unsigned i0 - 1))) by solve_num. assumption. }
      repeat constructor. rewrite <- Jacobian.double_minus_3_eq_double, Jacobian.to_affine_double.
      assert (W.eq (Jacobian.to_affine i0d2P) (W.mul (word.unsigned i0 / 2) (Jacobian.to_affine P))) as Weq. {
        replace ((word.unsigned i0 / 2)) with (Z.of_nat (Z.to_nat (word.unsigned i0 / 2))) by solve_num.
        erewrite <- multiples_nth.
        { subst i0d2P. erewrite  <- (map_nth Jacobian.to_affine), <- !nth_default_eq by solve_num.
          apply ListUtil.Forall2_forall_iff; [|eassumption|]; solve_num.
        }
        solve_num.
      }
      rewrite !Weq, <- ScalarMult.scalarmult_add_l.
      Morphisms.f_equiv.
      solve_num.
    }
    3: exact eq_refl.
    all: solve_num.
  }
Qed.
