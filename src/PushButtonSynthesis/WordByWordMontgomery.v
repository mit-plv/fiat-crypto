(** * Push-Button Synthesis of Word-By-Word Montgomery *)
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Import Coq.Program.Tactics. (* For WBW Montgomery proofs *)
Require Import Coq.derive.Derive.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.Equality.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.ModInv. (* Only needed for WBW Montgomery *)
Require Import Crypto.Util.ZUtil.Modulo. (* Only needed for WBW Montgomery proofs *)
Require Import Crypto.Util.ZUtil.Le. (* Only needed for WBW Montgomery proofs *)
Require Import Crypto.Util.Prod. (* For WBW Montgomery proofs *)
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo. (* For WBW montgomery proofs *)
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall. (* For WBW montgomery proofs *)
Require Import Crypto.Util.ZUtil.Div. (* For WBW Montgomery proofs *)
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem. (* For WBW Montgomery proofs *)
Require Import Crypto.Util.ZUtil.Ones. (* For WBW montgomery proofs *)
Require Import Crypto.Util.ZUtil.Shift. (* For WBW montgomery proofs *)
Require Import Crypto.Util.Tactics.HasBody.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.LanguageWf.
Require Import Crypto.Language.
Require Import Crypto.AbstractInterpretation.
Require Import Crypto.CStringification.
Require Import Crypto.Arithmetic.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.PushButtonSynthesis.Primitives.
Require Import Crypto.PushButtonSynthesis.WordByWordMontgomeryReificationCache.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope bool_scope.

Import
  LanguageWf.Compilers
  Language.Compilers
  AbstractInterpretation.Compilers
  CStringification.Compilers.
Import Compilers.defaults.

Import COperationSpecifications.Primitives.
Import COperationSpecifications.Solinas.
Import COperationSpecifications.WordByWordMontgomery.

Import Associational Positional.
Import Arithmetic.WordByWordMontgomery.

Import WordByWordMontgomeryReificationCache.WordByWordMontgomery.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

(* needed for making [autorewrite] not take a very long time *)
Local Opaque
      reified_mul_gen
      reified_add_gen
      reified_sub_gen
      reified_opp_gen
      reified_to_bytes_gen
      reified_from_bytes_gen
      reified_nonzero_gen
      reified_square_gen
      reified_encode_gen
      reified_from_montgomery_gen
      reified_zero_gen
      reified_one_gen
      expr.Interp.

Section __.
  Context (m : Z)
          (machine_wordsize : Z).

  Let s := 2^Z.log2_up m.
  Let c := s - m.
  Let n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
  Let r := 2^machine_wordsize.
  Let r' := match Z.modinv r m with
            | Some r' => r'
            | None => 0
            end.
  Let m' := match Z.modinv (-m) r with
            | Some m' => m'
            | None => 0
            end.
  Let n_bytes := bytes_n machine_wordsize 1 n.
  Let prime_upperbound_list : list Z
    := Partition.partition (UniformWeight.uweight machine_wordsize) n (s-1).
  Let prime_bytes_upperbound_list : list Z
    := Partition.partition (weight 8 1) n_bytes (s-1).
  Let upperbounds : list Z := prime_upperbound_list.
  Definition prime_bound : ZRange.type.option.interp (base.type.Z)
    := Some r[0~>m-1]%zrange.
  Definition prime_bounds : ZRange.type.option.interp (base.type.list (base.type.Z))
    := Some (List.map (fun v => Some r[0 ~> v]%zrange) prime_upperbound_list).
  Definition prime_bytes_bounds : ZRange.type.option.interp (base.type.list (base.type.Z))
    := Some (List.map (fun v => Some r[0 ~> v]%zrange) prime_bytes_upperbound_list).
  Local Notation saturated_bounds_list := (saturated_bounds_list n machine_wordsize).
  Local Notation saturated_bounds := (saturated_bounds n machine_wordsize).

  (* We include [0], so that even after bounds relaxation, we can
       notice where the constant 0s are, and remove them. *)
  Definition possible_values_of_machine_wordsize
    := [0; 1; machine_wordsize; 2 * machine_wordsize]%Z.

  Definition possible_values_of_machine_wordsize_with_bytes
    := [0; 1; 8; machine_wordsize; 2 * machine_wordsize]%Z.

  Let possible_values := possible_values_of_machine_wordsize.
  Let possible_values_with_bytes := possible_values_of_machine_wordsize_with_bytes.
  Definition bounds : list (ZRange.type.option.interp base.type.Z)
    := Option.invert_Some saturated_bounds (*List.map (fun u => Some r[0~>u]%zrange) upperbounds*).

  (** Note: If you change the name or type signature of this
        function, you will need to update the code in CLI.v *)
  Definition check_args {T} (res : Pipeline.ErrorT T)
    : Pipeline.ErrorT T
    := fold_right
         (fun '(b, e) k => if b:bool then Error e else k)
         res
         [(negb (1 <? machine_wordsize)%Z, Pipeline.Value_not_ltZ "machine_wordsize <= 1" 1 machine_wordsize);
            ((negb (0 <? c)%Z, Pipeline.Value_not_ltZ "c ≤ 0" 0 c));
            ((negb (1 <? m))%Z, Pipeline.Value_not_ltZ "m ≤ 1" 1 m);
            ((n =? 0)%nat, Pipeline.Values_not_provably_distinctZ "n = 0" n 0%nat);
            ((r' =? 0)%Z, Pipeline.No_modular_inverse "r⁻¹ mod m" r m);
            (negb ((r * r') mod m =? 1)%Z, Pipeline.Values_not_provably_equalZ "(r * r') mod m ≠ 1" ((r * r') mod m) 1);
            (negb ((m * m') mod r =? (-1) mod r)%Z, Pipeline.Values_not_provably_equalZ "(m * m') mod r ≠ (-1) mod r" ((m * m') mod r) ((-1) mod r));
            (negb (s <=? r^n), Pipeline.Value_not_leZ "r^n ≤ s" s (r^n));
            (negb (s <=? UniformWeight.uweight machine_wordsize n), Pipeline.Value_not_leZ "weight n < s (needed for from_bytes)" s (UniformWeight.uweight machine_wordsize n));
            (negb (UniformWeight.uweight machine_wordsize n =? UniformWeight.uweight 8 n_bytes), Pipeline.Values_not_provably_equalZ "weight n ≠ bytes_weight n_bytes (needed for from_bytes)" (UniformWeight.uweight machine_wordsize n) (UniformWeight.uweight 8 n_bytes))].

  Local Arguments Z.mul !_ !_.
  Local Ltac use_curve_good_t :=
    repeat first [ assumption
                 | progress rewrite ?map_length, ?Z.mul_0_r, ?Pos.mul_1_r, ?Z.mul_1_r in *
                 | reflexivity
                 | lia
                 | rewrite expr.interp_reify_list, ?map_map
                 | rewrite map_ext with (g:=id), map_id
                 | progress distr_length
                 | progress cbv [Qceiling Qfloor Qopp Qdiv Qplus inject_Z Qmult Qinv] in *
                 | progress cbv [Qle] in *
                 | progress cbn -[reify_list] in *
                 | progress intros
                 | solve [ auto with zarith ]
                 | rewrite Z.log2_pow2 by use_curve_good_t ].

  Context (curve_good : check_args (Success tt) = Success tt).

  Lemma use_curve_good
    : Z.pos (Z.to_pos m) = m
      /\ m = s - c
      /\ Z.pos (Z.to_pos m) <> 0
      /\ s - c <> 0
      /\ 0 < s
      /\ s <> 0
      /\ 0 < machine_wordsize
      /\ n <> 0%nat
      /\ List.length bounds = n
      /\ 0 < 1 <= machine_wordsize
      /\ 0 < c < s
      /\ (r * r') mod m = 1
      /\ (m * m') mod r = (-1) mod r
      /\ 0 < machine_wordsize
      /\ 1 < m
      /\ m < r^n
      /\ s = 2^Z.log2 s
      /\ s <= UniformWeight.uweight machine_wordsize n
      /\ s <= UniformWeight.uweight 8 n_bytes
      /\ UniformWeight.uweight machine_wordsize n = UniformWeight.uweight 8 n_bytes.
  Proof.
    clear -curve_good.
    cbv [check_args fold_right] in curve_good.
    cbv [bounds prime_bound prime_bounds saturated_bounds] in *.
    break_innermost_match_hyps; try discriminate.
    rewrite negb_false_iff in *.
    Z.ltb_to_lt.
    rewrite NPeano.Nat.eqb_neq in *.
    intros.
    cbv [Qnum Qden Qceiling Qfloor Qopp Qdiv Qplus inject_Z Qmult Qinv] in *.
    rewrite ?map_length, ?Z.mul_0_r, ?Pos.mul_1_r, ?Z.mul_1_r in *.
    specialize_by lia.
    repeat match goal with H := _ |- _ => subst H end.
    repeat match goal with
           | [ H : list_beq _ _ _ _ = true |- _ ] => apply internal_list_dec_bl in H; [ | intros; Z.ltb_to_lt; omega.. ]
           end.
    repeat apply conj.
    { destruct m eqn:?; cbn; lia. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
  Qed.


  Local Notation valid := (Arithmetic.WordByWordMontgomery.valid machine_wordsize n m).
  Local Notation bytes_valid := (Arithmetic.WordByWordMontgomery.valid 8 n_bytes m).

  Local Notation from_montgomery_res := (from_montgomerymod machine_wordsize n m m').

  Local Notation evalf := (@eval machine_wordsize n).
  Local Notation initial_ctx prefix
    := (CorrectnessStringification.dyn_context.cons
          m "m"%string
          (CorrectnessStringification.dyn_context.cons
             from_montgomery_res (prefix ++ "from_montgomery")%string
             (CorrectnessStringification.dyn_context.cons
                (@eval 8 n_bytes) "bytes_eval"%string
                CorrectnessStringification.dyn_context.nil))).
  Local Notation stringify_correctness prefix pre_extra correctness
    := (stringify_correctness_with_ctx
          (initial_ctx prefix)
          evalf
          pre_extra
          correctness)
         (only parsing).

  Definition mul
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_mul_gen
            @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
         (Some bounds, (Some bounds, tt))
         (Some bounds).

  Definition smul (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "mul" mul
          (stringify_correctness
             prefix
             (fun fname : string => ["The function " ++ fname ++ " does stuff."]%string)
             (mul_correct machine_wordsize n m valid from_montgomery_res)).

  Definition square
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_square_gen
            @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
         (Some bounds, tt)
         (Some bounds).

  Definition ssquare (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "square" square
          (stringify_correctness
             prefix
             (fun fname : string => ["The function " ++ fname ++ " does stuff."]%string)
             (square_correct machine_wordsize n m valid from_montgomery_res)).

  Definition add
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_add_gen
            @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m)
         (Some bounds, (Some bounds, tt))
         (Some bounds).

  Definition sadd (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "add" add
          (stringify_correctness
             prefix
             (fun fname : string => ["The function " ++ fname ++ " does stuff."]%string)
             (add_correct machine_wordsize n m valid from_montgomery_res)).

  Definition sub
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_sub_gen
            @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m)
         (Some bounds, (Some bounds, tt))
         (Some bounds).

  Definition ssub (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "sub" sub
          (stringify_correctness
             prefix
             (fun fname : string => ["The function " ++ fname ++ " does stuff."]%string)
             (sub_correct machine_wordsize n m valid from_montgomery_res)).

  Definition opp
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_opp_gen
            @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m)
         (Some bounds, tt)
         (Some bounds).

  Definition sopp (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "opp" opp
          (stringify_correctness
             prefix
             (fun fname : string => ["The function " ++ fname ++ " does stuff."]%string)
             (opp_correct machine_wordsize n m valid from_montgomery_res)).

  Definition from_montgomery
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_from_montgomery_gen
            @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
         (Some bounds, tt)
         (Some bounds).

  Definition sfrom_montgomery (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "from_montgomery" from_montgomery
          (stringify_correctness
             prefix
             (fun fname : string => ["The function " ++ fname ++ " does stuff."]%string)
             (from_montgomery_correct machine_wordsize n m r' valid)).

  Definition nonzero
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         reified_nonzero_gen
         (Some bounds, tt)
         (Some r[0~>r-1]%zrange).

  Definition snonzero (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "nonzero" nonzero
          (stringify_correctness
             prefix
             (fun fname : string => ["The function " ++ fname ++ " does stuff."]%string)
             (nonzero_correct machine_wordsize n m valid from_montgomery_res)).

  Definition to_bytes
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values_with_bytes
         (reified_to_bytes_gen
            @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n)
         (prime_bounds, tt)
         prime_bytes_bounds.

  Definition sto_bytes (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "to_bytes" to_bytes
          (stringify_correctness
             prefix
             (fun fname : string => ["The function " ++ fname ++ " does stuff."]%string)
             (to_bytes_correct machine_wordsize n n_bytes m valid)).

  Definition from_bytes
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values_with_bytes
         (reified_from_bytes_gen
            @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify 1 @ GallinaReify.Reify n)
         (prime_bytes_bounds, tt)
         prime_bounds.

  Definition sfrom_bytes (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "from_bytes" from_bytes
          (stringify_correctness
             prefix
             (fun fname : string => ["The function " ++ fname ++ " does stuff."]%string)
             (from_bytes_correct machine_wordsize n n_bytes m valid bytes_valid)).

  Definition encode
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_encode_gen
            @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
         (prime_bound, tt)
         (Some bounds).

  Definition sencode (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "encode" encode
          (stringify_correctness
             prefix
             (fun fname : string => ["The function " ++ fname ++ " does stuff."]%string)
             (encode_correct machine_wordsize n m valid from_montgomery_res)).

  Definition zero
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_zero_gen
            @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
         tt
         (Some bounds).

  Definition szero (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "zero" zero
          (stringify_correctness
             prefix
             (fun fname : string => ["The function " ++ fname ++ " does stuff."]%string)
             (zero_correct machine_wordsize n m valid from_montgomery_res)).

  Definition one
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_one_gen
            @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
         tt
         (Some bounds).

  Definition sone (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "one" one
          (stringify_correctness
             prefix
             (fun fname : string => ["The function " ++ fname ++ " does stuff."]%string)
             (one_correct machine_wordsize n m valid from_montgomery_res)).

  Definition selectznz : Pipeline.ErrorT _ := Primitives.selectznz n machine_wordsize.
  Definition sselectznz (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
    := Primitives.sselectznz n machine_wordsize prefix.

  Lemma bounded_by_of_valid x
        (H : valid x)
    : ZRange.type.base.option.is_bounded_by (t:=base.type.list base.type.Z) (Some bounds) x = true.
  Proof using curve_good.
    pose proof use_curve_good as use_curve_good.
    clear -H use_curve_good curve_good.
    destruct H as [H _]; destruct_head'_and.
    cbv [small] in H.
    cbv [ZRange.type.base.option.is_bounded_by bounds saturated_bounds saturated_bounds_list Option.invert_Some].
    replace n with (List.length x) by now rewrite H, Partition.length_partition.
    rewrite <- map_const, fold_andb_map_map1, fold_andb_map_iff.
    cbv [ZRange.type.base.is_bounded_by is_bounded_by_bool lower upper].
    split; [ reflexivity | ].
    intros *; rewrite combine_same, in_map_iff, Bool.andb_true_iff, !Z.leb_le.
    intros; destruct_head'_ex; destruct_head'_and; subst *; cbn [fst snd].
    match goal with
    | [ H : In ?v x |- _ ] => revert v H
    end.
    rewrite H.
    generalize (eval (n:=n) machine_wordsize x).
    cbn [base.interp base.base_interp].
    generalize n.
    intro n'.
    induction n' as [|n' IHn'].
    { cbv [Partition.partition seq map In]; tauto. }
    { intros *; rewrite Partition.partition_step, in_app_iff; cbn [List.In].
      intros; destruct_head'_or; subst *; eauto; try tauto; [].
      rewrite UniformWeight.uweight_S by lia.
      assert (0 < UniformWeight.uweight machine_wordsize n') by now apply UniformWeight.uwprops.
      assert (0 < 2 ^ machine_wordsize) by auto with zarith.
      assert (0 < 2 ^ machine_wordsize * UniformWeight.uweight machine_wordsize n') by nia.
      rewrite <- Z.mod_pull_div by lia.
      rewrite Z.le_sub_1_iff.
      auto with zarith. }
  Qed.

  (* XXX FIXME *)
  Lemma bounded_by_prime_bounds_of_valid_gen lgr n' x
        (Hlgr : 0 < lgr)
        (Hs : s = 2^Z.log2 s)
        (Hs' : s <= UniformWeight.uweight lgr n')
        (H : WordByWordMontgomery.valid lgr n' m x)
    : ZRange.type.base.option.is_bounded_by (t:=base.type.list base.type.Z) (Some (List.map (fun v => Some r[0~>v]%zrange) (Partition.partition (UniformWeight.uweight lgr) n' (s-1)))) x = true.
  Proof using curve_good.
    pose proof use_curve_good as use_curve_good.
    clear -H use_curve_good curve_good Hlgr Hs Hs'.
    destruct H as [H ?]; destruct_head'_and.
    cbv [small] in H.
    cbv [ZRange.type.base.option.is_bounded_by].
    replace n' with (List.length x) by now rewrite H, Partition.length_partition.
    rewrite fold_andb_map_map1, fold_andb_map_iff.
    split; [ now autorewrite with distr_length | ].
    cbv [ZRange.type.base.is_bounded_by is_bounded_by_bool lower upper].
    rewrite H; autorewrite with distr_length.
    intros [v1 v0]; cbn [fst snd].
    rename x into x'.
    generalize dependent (eval (n:=n') lgr x').
    replace m with (s - c) in * by easy.
    intro x; intros ??? H; subst x'.
    eapply In_nth_error in H; destruct H as [i H].
    rewrite nth_error_combine in H.
    break_match_hyps; try discriminate; []; Option.inversion_option; Prod.inversion_prod; subst.
    cbv [Partition.partition] in *.
    apply nth_error_map in Heqo; apply nth_error_map in Heqo0; destruct Heqo as (?&?&?), Heqo0 as (?&?&?).
    rewrite nth_error_seq in *.
    break_match_hyps; try discriminate; Option.inversion_option; Prod.inversion_prod; subst.
    rewrite ?Nat.add_0_l.
    assert (0 <= x < s) by lia.
    replace s with (2^Z.log2 s) by easy.
    assert (1 < s) by lia.
    assert (0 < Z.log2 s) by now apply Z.log2_pos.
    assert (1 < 2^Z.log2 s) by auto with zarith.
    generalize dependent (Z.log2 s); intro lgs; intros.

    edestruct (UniformWeight.uwprops lgr); try lia.
    assert (forall i : nat, 0 <= UniformWeight.uweight lgr i) by (intro z; specialize (weight_positive z); lia).
    apply Bool.andb_true_intro; split; apply OrdersEx.Z_as_OT.leb_le;
      [apply Z.div_nonneg | apply Z.div_le_mono_nonneg]; trivial.
    apply Z.mod_pos_bound; trivial.

    cbv [UniformWeight.uweight].
    cbv [weight].
    rewrite Z.div_1_r.
    rewrite Z.opp_involutive.
    rewrite <-2Z.land_ones by nia.
    rewrite Z.sub_1_r, <-Z.ones_equiv.
    rewrite Z.land_ones_ones.
    destruct ((lgs <? 0) || (lgr * Z.of_nat (S i) <? 0)) eqn:?.
    { rewrite Z.land_ones, Z.ones_equiv, <-Z.sub_1_r by nia.
      pose proof Z.le_max_r lgs (lgr*Z.of_nat (S i)).
      etransitivity.
      2:rewrite <- Z.sub_le_mono_r.
      2:eapply Z.pow_le_mono_r; try lia; eassumption.
      eapply Z.le_sub_1_iff, Z.mod_pos_bound, Z.pow_pos_nonneg; nia. }
    rewrite (Z.ones_equiv (Z.min _ _)), <-Z.sub_1_r.
    enough (Z.land x (Z.ones (lgr * Z.of_nat (S i))) < 2 ^ Z.min lgs (lgr * Z.of_nat (S i))) by lia.
    eapply Testbit.Z.testbit_false_bound. nia.
    intros j ?; assert (Z.min lgs (lgr * Z.of_nat (S i)) <= j) by lia.
    rewrite Hs in *. revert H; intros.
    rewrite <-(Z.mod_small x (2^lgs)) by lia.
    rewrite OrdersEx.Z_as_OT.land_spec.
    destruct (Zmin_irreducible lgs (lgr * Z.of_nat (S i))) as [HH|HH]; rewrite HH in *; clear HH.
    { rewrite Z.mod_pow2_bits_high; trivial; lia. }
    { rewrite OrdersEx.Z_as_DT.ones_spec_high, Bool.andb_false_r; trivial; nia. }
  Qed.

  Lemma length_of_valid lgr n' x
        (H : WordByWordMontgomery.valid lgr n' m x)
    : List.length x = n'.
  Proof using Type.
    destruct H as [H _]; rewrite H.
    now autorewrite with distr_length.
  Qed.

  Lemma bounded_by_prime_bounds_of_valid x
        (H : valid x)
    : ZRange.type.base.option.is_bounded_by (t:=base.type.list base.type.Z) prime_bounds x = true.
  Proof using curve_good.
    pose proof use_curve_good as use_curve_good.
    destruct_head'_and.
    now apply bounded_by_prime_bounds_of_valid_gen.
  Qed.

  Lemma bounded_by_prime_bytes_bounds_of_bytes_valid x
        (H : bytes_valid x)
    : ZRange.type.base.option.is_bounded_by (t:=base.type.list base.type.Z) prime_bytes_bounds x = true.
  Proof using curve_good.
    pose proof use_curve_good as use_curve_good.
    destruct_head'_and.
    now apply bounded_by_prime_bounds_of_valid_gen.
  Qed.

  Lemma weight_bounded_of_bytes_valid x
        (H : bytes_valid x)
    : 0 <= eval 8 (n:=n_bytes) x < weight machine_wordsize 1 n.
  Proof using curve_good.
    cbv [bytes_valid] in H.
    destruct H as [_ H].
    pose proof use_curve_good.
    cbv [UniformWeight.uweight] in *; destruct_head'_and; lia.
  Qed.

  Local Ltac solve_extra_bounds_side_conditions :=
    solve [ cbn [lower upper fst snd] in *; Bool.split_andb; Z.ltb_to_lt; lia
          | cbv [valid small eval UniformWeight.uweight n_bytes] in *; destruct_head'_and; auto
          | now apply weight_bounded_of_bytes_valid
          | eapply length_of_valid; eassumption ].

  Hint Rewrite
       (@eval_mulmod machine_wordsize n m r' m')
       (@eval_squaremod machine_wordsize n m r' m')
       (@eval_addmod machine_wordsize n m r' m')
       (@eval_submod machine_wordsize n m r' m')
       (@eval_oppmod machine_wordsize n m r' m')
       (@eval_from_montgomerymod machine_wordsize n m r' m')
       (@eval_encodemod machine_wordsize n m r' m')
       eval_to_bytesmod
       eval_from_bytesmod
       using solve [ eauto using length_of_valid | congruence | solve_extra_bounds_side_conditions ] : push_eval.
  (* needed for making [autorewrite] fast enough *)
  Local Opaque
        Arithmetic.WordByWordMontgomery.onemod
        Arithmetic.WordByWordMontgomery.from_montgomerymod
        Arithmetic.WordByWordMontgomery.mulmod
        Arithmetic.WordByWordMontgomery.squaremod
        Arithmetic.WordByWordMontgomery.encodemod
        Arithmetic.WordByWordMontgomery.addmod
        Arithmetic.WordByWordMontgomery.submod
        Arithmetic.WordByWordMontgomery.oppmod
        Arithmetic.WordByWordMontgomery.to_bytesmod.
  Hint Unfold eval zeromod onemod : push_eval.

  Local Ltac prove_correctness op_correct :=
    let dont_clear H := first [ constr_eq H curve_good ] in
    let Hres := match goal with H : _ = Success _ |- _ => H end in
    let H := fresh in
    pose proof use_curve_good as H;
    (* I want to just use [clear -H Hres], but then I can't use any lemmas in the section because of COQBUG(https://github.com/coq/coq/issues/8153) *)
    repeat match goal with
           | [ H' : _ |- _ ]
             => tryif first [ has_body H' | constr_eq H' H | constr_eq H' Hres | dont_clear H' ]
             then fail
             else clear H'
           end;
    cbv zeta in *;
    destruct_head'_and;
    let f := match type of Hres with ?f = _ => head f end in
    try cbv [f] in *;
    hnf;
    PipelineTactics.do_unfolding;
    try (let m := match goal with m := _ - Associational.eval _ |- _ => m end in
         cbv [m] in * );
    intros;
    lazymatch goal with
    | [ |- _ <-> _ ] => idtac
    | [ |- _ = _ ] => idtac
    | _ => split; [ | try split ];
           cbv [small]
    end;
    PipelineTactics.use_compilers_correctness Hres;
    repeat first [ reflexivity
                 | now apply bounded_by_of_valid
                 | now apply bounded_by_prime_bounds_of_valid
                 | now apply bounded_by_prime_bytes_bounds_of_bytes_valid
                 | now apply weight_bounded_of_bytes_valid
                 | solve [ eapply op_correct; try eassumption; solve_extra_bounds_side_conditions ]
                 | progress autorewrite with interp interp_gen_cache push_eval
                 | progress autounfold with push_eval
                 | progress autorewrite with distr_length in *
                 | solve [ cbv [valid small eval UniformWeight.uweight n_bytes] in *; destruct_head'_and; auto ] ].

  (** TODO: DESIGN DECISION:

        The correctness lemmas for most of the montgomery things are
        parameterized over a `from_montgomery`.  When filling this in
        for, e.g., mul-correctness, should I use `from_montgomery`
        from arithmetic, or should I use `Interp
        reified_from_montgomery` (the post-pipeline version), and take
        in success of the pipeline on `from_montgomery` as well? *)

  Lemma mul_correct res
        (Hres : mul = Success res)
    : mul_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness mulmod_correct. Qed.

  Lemma square_correct res
        (Hres : square = Success res)
    : square_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness squaremod_correct. Qed.

  Lemma add_correct res
        (Hres : add = Success res)
    : add_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness addmod_correct. Qed.

  Lemma sub_correct res
        (Hres : sub = Success res)
    : sub_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness submod_correct. Qed.

  Lemma opp_correct res
        (Hres : opp = Success res)
    : opp_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness oppmod_correct. Qed.

  Lemma from_montgomery_correct res
        (Hres : from_montgomery = Success res)
    : from_montgomery_correct machine_wordsize n m r' valid (Interp res).
  Proof using curve_good. prove_correctness from_montgomerymod_correct. Qed.

  Lemma nonzero_correct res
        (Hres : nonzero = Success res)
    : nonzero_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness nonzeromod_correct. Qed.

  Lemma to_bytes_correct res
        (Hres : to_bytes = Success res)
    : to_bytes_correct machine_wordsize n n_bytes m valid (Interp res).
  Proof using curve_good. prove_correctness to_bytesmod_correct. Qed.

  Lemma from_bytes_correct res
        (Hres : from_bytes = Success res)
    : from_bytes_correct machine_wordsize n n_bytes m valid bytes_valid (Interp res).
  Proof using curve_good. prove_correctness eval_from_bytesmod_and_partitions. Qed.

  Strategy -1000 [encode]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma encode_correct res
        (Hres : encode = Success res)
    : encode_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness encodemod_correct. Qed.

  Strategy -1000 [zero]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma zero_correct res
        (Hres : zero = Success res)
    : zero_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness encodemod_correct. Qed.

  Strategy -1000 [one]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma one_correct res
        (Hres : one = Success res)
    : one_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness encodemod_correct. Qed.

  Local Opaque Pipeline.BoundsPipeline. (* need this or else [eapply Pipeline.BoundsPipeline_correct in Hres] takes forever *)
  Lemma selectznz_correct res
        (Hres : selectznz = Success res)
    : selectznz_correct machine_wordsize n saturated_bounds_list (Interp res).
  Proof using curve_good. Primitives.prove_correctness use_curve_good. Qed.

  Section ring.
    Context from_montgomery_res (Hfrom_montgomery : from_montgomery = Success from_montgomery_res)
            mul_res    (Hmul    : mul    = Success mul_res)
            add_res    (Hadd    : add    = Success add_res)
            sub_res    (Hsub    : sub    = Success sub_res)
            opp_res    (Hopp    : opp    = Success opp_res)
            encode_res (Hencode : encode = Success encode_res)
            zero_res   (Hzero   : zero   = Success zero_res)
            one_res    (Hone    : one    = Success one_res).

    Definition GoodT : Prop
      := GoodT
           machine_wordsize n m valid
           (Interp from_montgomery_res)
           (Interp mul_res)
           (Interp add_res)
           (Interp sub_res)
           (Interp opp_res)
           (Interp encode_res)
           (Interp zero_res)
           (Interp one_res).

    Theorem Good : GoodT.
    Proof using curve_good Hfrom_montgomery Hmul Hadd Hsub Hopp Hencode Hzero Hone.
      pose proof use_curve_good; cbv zeta in *; destruct_head'_and.
      eapply Good.
      all: repeat first [ assumption
                        | apply from_montgomery_correct
                        | lia ].
      all: hnf; intros.
      all: push_Zmod; erewrite !(fun v Hv => proj1 (from_montgomery_correct _ Hfrom_montgomery v Hv)), <- !eval_from_montgomerymod; try eassumption; pull_Zmod.
      all: repeat first [ assumption
                        | lazymatch goal with
                          | [ |- context[mul_res] ] => apply mul_correct
                          | [ |- context[add_res] ] => apply add_correct
                          | [ |- context[sub_res] ] => apply sub_correct
                          | [ |- context[opp_res] ] => apply opp_correct
                          | [ |- context[encode_res] ] => apply encode_correct
                          | [ |- context[zero_res] ] => apply zero_correct
                          | [ |- context[one_res] ] => apply one_correct
                          end ].
    Qed.
  End ring.

  Section for_stringification.
    Local Open Scope string_scope.
    Local Open Scope list_scope.

    Definition known_functions
      := [("mul", smul);
            ("square", ssquare);
            ("add", sadd);
            ("sub", ssub);
            ("opp", sopp);
            ("from_montgomery", sfrom_montgomery);
            ("nonzero", snonzero);
            ("selectznz", sselectznz);
            ("to_bytes", sto_bytes);
            ("from_bytes", sfrom_bytes)].

    Definition valid_names : string := Eval compute in String.concat ", " (List.map (@fst _ _) known_functions).

    (** Note: If you change the name or type signature of this
          function, you will need to update the code in CLI.v *)
    Definition Synthesize (function_name_prefix : string) (requests : list string)
      : list string * list (string * Pipeline.ErrorT (list string)) * PositiveSet.t (* types used *)
      := Primitives.Synthesize
           machine_wordsize valid_names known_functions (fun _ => nil)
           [] function_name_prefix requests.
  End for_stringification.
End __.
