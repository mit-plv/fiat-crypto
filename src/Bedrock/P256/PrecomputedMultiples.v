Require Import ZArith BinInt Lia Arith PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

From coqutil Require Import
  letexists
  OfListWord
  Word.Properties
  Datatypes.List
  Tactics.Tactics.
Require Import (notations) coqutil.Map.Memory.

From bedrock2 Require Import
  Syntax
  bottom_up_simpl
  Array
  SepAutoArray
  ListIndexNotations
  wsize
  NotationsCustomEntry
  ProgramLogic
  WeakestPrecondition
  SeparationLogic
  AbsintWordToZ
  ZnWords.
Import ProgramLogic.Coercions.
Import symmetry.

From bedrock2Examples Require Import
  memcpy.

Require Import
  PrimeFieldTheorems
  Spec.WeierstrassCurve
  Curves.Weierstrass.Affine
  Curves.Weierstrass.AffineProofs
  Curves.Weierstrass.Jacobian.Jacobian
  Curves.Weierstrass.P256
  Bedrock.P256.Specs.
Import Specs.coord Specs.point.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

#[local] Notation sizeof_point := 96%nat.

(* TODO: Prove for both architectures by using a context. *)
Require Import bedrock2.BasicC64Semantics.
#[local] Notation width := 64%nat.

Local Notation "p .+ n" := (word.add p (word.of_Z n)) (at level 50, format "p .+ n", left associativity).

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

Definition p256_get_multiple := func! (p_out, p_table, k) {
  unpack! sign = br_broadcast_negative(k);
  unpack! idx = br_abs(k, sign);

  (* Copy the point in positive form. *)
  p256_select_point_from_table(p_out, p_table, idx);

  (* Calculate -y, and select to copy y or -y based on the sign of k. *)
  stackalloc 32 as p_y_opp;
  br_memcpy(p_y_opp, p_out + $32, $32);
  p256_coord_opp(p_y_opp);

  p256_coord_select_znz(p_out + $32, sign, p_out + $32, p_y_opp)
}.

Definition p256_select_point_from_table := func! (p_out, p_table, idx) {
  i = $0;
  while ($17 - i) {
    (* select condition is 0 iff i == idx *)
    p256_point_cmov(p_out, i ^ idx, p_table + ($sizeof_point * i));
    i = i + $1
  }
}.

(* Puts p_z into p_out if c is zero. *)
Definition p256_point_cmov := func! (p_out, c, p_z) {
  p256_coord_select_znz(p_out,       c, p_z,       p_out);
  p256_coord_select_znz(p_out + $32, c, p_z + $32, p_out + $32);
  p256_coord_select_znz(p_out + $64, c, p_z + $64, p_out + $64)
}.

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

#[local] Ltac solve_num_pre := repeat rewrite ?length_skipn, ?length_multiples, ?length_nil,
  ?length_firstn, ?map_length, ?length_point, ?length_app, ?length_cons, ?length_coord in * by (lia || ZnWords).

#[local] Ltac solve_num := solve_num_pre; (lia || ZnWords).

Lemma multiples_nth (n : nat) (A : W.point):
  forall i : nat, i < n ->
  (List.nth_default (W.zero) (W.multiples n A) i) = W.mul i A.
Proof.
  cbv [W.multiples]; intros.
  erewrite ListUtil.map_nth_default with (x:=O) by (rewrite length_seq; lia).
  rewrite ListUtil.nth_default_seq_inbounds by lia; trivial.
Qed.

#[local] Notation pointarray := (array (fun (p : word.rep) (Q : point) =>
  sepclause_of_map ((to_bytes Q)$@p)) (word.of_Z (Z.of_nat sizeof_point))).

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

#[export] Instance spec_of_p256_point_cmov : spec_of "p256_point_cmov" :=
  fnspec! "p256_point_cmov" (p_out c p_z : word) / (out z : point) R,
  { requires t m := m =* out$@p_out * z$@p_z * R;
    ensures t' m' := t' = t /\
      let r := if Z.eqb c 0 then z else out in (r$@p_out * z$@p_z* R)%sep m'
  }.

#[export] Instance spec_of_p256_select_point_from_table : spec_of "p256_select_point_from_table" :=
  fnspec! "p256_select_point_from_table" p_out p_table idx / (out_old : point) (multiples : list point) R,
  { requires t m :=
      m =* (out_old)$@p_out * pointarray p_table multiples * R /\
      length multiples = 17%nat /\
      0 <= word.unsigned idx < 17;
    ensures t' m := t' = t /\
      m =* (nth_default (of_affine W.zero) multiples (Z.to_nat idx))$@p_out *
          pointarray p_table multiples * R
  }.

#[export] Instance spec_of_p256_get_multiple : spec_of "p256_get_multiple" :=
  fnspec! "p256_get_multiple" p_out p_table k / (out_old P: point) (multiples : list point) R,
  { requires t m :=
      m =* out_old$@p_out * pointarray p_table multiples * R /\
      length multiples = 17%nat /\
      Forall2 W.eq (map to_affine multiples) (W.multiples 17 (to_affine P)) /\
      -17 < (word.signed k) < 17;
    ensures t' m := t' = t /\ exists (out_point : point),
      m =* out_point$@p_out * pointarray p_table multiples * R /\
      W.eq (to_affine out_point) (W.mul (word.signed k) (to_affine P))
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
  Morphisms.f_equiv. do 3 f_equal. solve_num.
Qed.

#[local] Ltac hyp_containing a := match goal with H : context[a] |- _ => H end.

Lemma p256_point_cmov_ok : program_logic_goal_for_function! p256_point_cmov.
Proof.
  repeat straightline.

  destruct z as (((?z_x & ?z_y) & ?z_z) & ?).
  destruct out as (((?nz_x & ?nz_y) & ?nz_z) & ?).
  cbv [proj1_sig proj2_sig fst snd point.to_bytes] in * |-.

  repeat (let H := hyp_containing m in seprewrite_in Array.sep_eq_of_list_word_at_app H;
    [reflexivity|solve_num|];
  rewrite ?length_coord in H).
  bottom_up_simpl_in_hyps.

  straightline_call; ssplit; repeat straightline.
  2,3: eexists. 1-3: ecancel_assumption. 1: solve_num.
  straightline_call; ssplit; repeat straightline.
  2,3: eexists. 1-3: ecancel_assumption. 1: solve_num.
  straightline_call; ssplit; repeat straightline.
  2,3: eexists. 1-3: ecancel_assumption. 1: solve_num.

  cbv [point.to_bytes fst snd proj1_sig].
  repeat (seprewrite Array.sep_eq_of_list_word_at_app; [reflexivity|solve_num|]).
  rewrite !length_coord.
  bottom_up_simpl_in_goal.
  destruct (Z.eqb_spec c1 0); ecancel_assumption.
Qed.

Lemma p256_select_point_from_table_ok : program_logic_goal_for_function! p256_select_point_from_table.
Proof.
  repeat straightline.

  refine ((Loops.tailrec
    HList.polymorphic_list.nil
    (["p_out"; "p_table"; "idx"; "i"]))
    (fun (v:nat) t m p_out p_table idx_cur i => PrimitivePair.pair.mk (
      let out := if idx <? v
          then nth_default (of_affine W.zero) multiples (Z.to_nat idx)
          else out_old in
      m =* out$@p_out * pointarray p_table multiples * R0 /\
      0 <= i <= 17 /\
      idx_cur = idx /\
      v = i :> Z
    )
    (fun T M _ _ _ _ => T = t /\
      M =* (nth_default (of_affine W.zero) multiples (Z.to_nat idx))$@p_out *
          pointarray p_table multiples * R0
    ))
    (fun v' v => v < v' <= 17)%nat
    _ _ _ _ _); Loops.loop_simpl.
  { cbv [Loops.enforce]; cbn. split; exact eq_refl. }
  { apply PeanoNat.Nat.gt_wf. }

  (* Initial state matches invariant. *)
  { repeat straightline.
    ssplit; cycle -1.
    { rewrite Znat.Z2Nat.id; [exact eq_refl|ZnWords]. }
    { case Z.ltb_spec0; try (intros; ecancel_assumption).
      subst i. bottom_up_simpl_in_goal; lia. }
    { ZnWords. }
    { ZnWords. }
    { trivial. }
  }

  (* Loop postcondition implies function postcondition. *)
  2:{ repeat straightline. assumption. }

  (* Loop body preserves invariant. *)
  intros ?v ?t ?m ?p_out ?p_table ?idx ?i.
  repeat straightline.

  (* Handle the loop termination case. *)
  2:{ replace v with 17%nat in * by ZnWords.
    destruct (Z.ltb_spec0 (word.unsigned idx) (Z.of_nat 17)); [ecancel_assumption | lia].
  }

  (* Inside the loop. *)
  assert (v < 17%nat) by ZnWords.

  (* Extract the point at i0. *)
  seprewrite_in_by (pointarray_split_nth p_table0 multiples (Z.to_nat (word.unsigned i0)))
        ltac:(hyp_containing (m0)) solve_num.

  (* constant time select of the point *)
  straightline_call; ssplit.
  { use_sep_assumption. cancel.
    cancel_seps_at_indices 1%nat 1%nat. { repeat f_equal. solve_num. }
    cbv [seps]; ecancel. }
  repeat straightline.
  exists (S v). split; ssplit; trivial; try solve_num.
  2:{ split; [solve_num|]. repeat straightline. assumption. }

  rewrite word.unsigned_xor_nowrap in *.
  seprewrite_by (pointarray_split_nth p_table0 multiples (Z.to_nat (word.unsigned i0))) solve_num.
  destruct (Z.eqb_spec (Z.lxor i0 idx) 0); rewrite Z.lxor_eq_0_iff in *.
  (* v == idx -> select point *)
  { destruct (Z.ltb_spec idx v); case Z.ltb_spec; intros; try lia.
    { use_sep_assumption. cancel.
      cancel_seps_at_indices 0%nat 1%nat. { repeat f_equal. solve_num. }
      repeat Morphisms.f_equiv. solve_num. }
  }
  (* v <> idx *)
  destruct (Z.ltb_spec idx v); case Z.ltb_spec; intros; try lia.
  all: use_sep_assumption; cancel; repeat Morphisms.f_equiv; solve_num.
Qed.

Lemma p256_get_multiple_ok : program_logic_goal_for_function! p256_get_multiple.
Proof.
  repeat straightline.
  straightline_call; trivial; repeat straightline.
  rename x into sign.

  assert (word.unsigned sign = if (word.signed k) <? 0 then (Z.ones width) else 0)
   as Hsign. {
    subst sign.
    case word.lts_spec; rewrite word.signed_of_Z_nowrap by solve_num; intros;
    case Z.ltb_spec; intros; try solve_num.
    { exact word.unsigned_broadcast_true. }
    { exact word.unsigned_broadcast_false. }
  }

  straightline_call; ssplit.
  { assumption. }

  repeat straightline.
  straightline_call; ssplit.
  { ecancel_assumption. }
  1-3: solve_num.
  rename x into idx.
  let H := hyp_containing (eq (word.unsigned idx)) in rename H into Hidx.

  repeat straightline.

  let H := hyp_containing (@Forall2) in rename H into HForall.

  eapply ListUtil.Forall2_forall_iff' with (d:=(W.zero)) (i:=(Z.to_nat (Z.abs (word.signed k)))) in HForall;
    [|solve_num|solve_num].
  rewrite multiples_nth in HForall by lia;
  rewrite <- (Jacobian.to_affine_of_affine W.zero) in HForall.
  rewrite ListUtil.map_nth_default_always in *.

  rewrite Hidx in *.
  set (nth_default (of_affine W.zero) multiples (Z.to_nat (Z.abs (word.signed k)))) as idxP in *.

  (* Remember the inverted point before destructing. Gives easy access to the proof that it's on the curve. *)
  pose (proj2_sig (Jacobian.opp idxP)) as HidxPopp.
  cbv [Jacobian.opp proj2_sig proj1_sig] in HidxPopp.

  set (idxP$@p_out) as Pmem in *.
  destruct idxP as (((x & y) & z) & HidxP).
  cbv [point.to_bytes fst snd proj1_sig] in Pmem. subst Pmem.

  repeat (let H := hyp_containing p_out in seprewrite_in Array.sep_eq_of_list_word_at_app H;
      [reflexivity|solve_num|]; rewrite ?length_coord in H).
  bottom_up_simpl_in_hyps.

  seprewrite_in_by array1_iff_eq_of_list_word_at ltac:(hyp_containing a) lia.

  straightline_call; ssplit.
  { ecancel_assumption. }
  { solve_num. }
  { rewrite length_coord; ZnWords. }
  { ZnWords. }

  repeat straightline.

  straightline_call; ssplit.
  { ecancel_assumption. }

  repeat straightline.

  straightline_call; ssplit.
  { ecancel_assumption. }
  { eexists. ecancel_assumption. }
  { eexists. ecancel_assumption. }
  { rewrite length_coord; ZnWords. }

  repeat straightline.

  (* Dealloc of a. Prep ptsto and length so straightline processes. *)
  Require Import coqutil.Macros.symmetry.
  pose proof (length_coord (F.opp y)).
  seprewrite_in_by (symmetry! (Array.array1_iff_eq_of_list_word_at a)) ltac:(hyp_containing a) lia.

  repeat straightline.

  (* Final postcondition verification. *)
  unshelve eexists (exist _ (x, if Z.ltb (word.signed k) 0 then F.opp y else y, z) _);
  ssplit.

  { case Z.ltb_spec; intros; assumption. }

  { rewrite Hsign, Z.ones_equiv in *.
    cbv [point.to_bytes fst snd proj1_sig] in *; cbv [seps];
    repeat (seprewrite Array.sep_eq_of_list_word_at_app;
        [reflexivity|solve_num|]; rewrite ?length_coord).
    bottom_up_simpl_in_goal.
    use_sep_assumption.
    cancel. case Z.ltb_spec; case Z.eqb_spec; try lia; intros; ecancel. }

  case Z.ltb_spec; intros.
  { rewrite <- (Z.opp_involutive (word.signed k)).
    rewrite ScalarMult.scalarmult_opp_l.
    match goal with H: W.eq _ ?v |- context [W.opp (?w)] =>
      assert (W.eq v w) as <-; [repeat Morphisms.f_equiv; lia | rewrite <- H]
    end.
    rewrite <-Jacobian.to_affine_opp.
    cbv [Jacobian.opp proj1_sig].
    reflexivity. }
  { etransitivity; [eassumption|]. repeat Morphisms.f_equiv. lia. }
Qed.

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
              pointarray p_table multiples * P$@p_P * R0)%sep /\
              2 <= i <= 17 /\
              v = i :> Z /\
              length todo + sizeof_point*i = 17*sizeof_point /\
              Forall2 W.eq (map to_affine multiples) (W.multiples v (to_affine P)))
      (fun T M (P_TABLE P_P I : word) => t = T /\ exists multiples : list point,
              M =* pointarray p_table multiples * P$@p_P * R0 /\
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
    seprewrite_in @sepclause_of_map_empty ltac:(hyp_containing m0).
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
