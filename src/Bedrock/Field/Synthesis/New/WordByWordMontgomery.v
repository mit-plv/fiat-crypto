Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Util.
Require Import Crypto.Bedrock.Field.Common.Arrays.ByteBounds.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Synthesis.New.Signature.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Func.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.WordByWordMontgomery.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Import ListNotations API.Compilers Types.Notations.

Class word_by_word_Montgomery_ops
  {from_mont to_mont : string}
  {width BW word mem locals env ext_spec varname_gen error}
  {parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}
  {field_parameters : FieldParameters}
  {n m} : Type :=
  { mul_op :
      computed_op
        (WordByWordMontgomery.mul m width) Field.mul
        list_binop_insizes list_binop_outsizes (list_binop_inlengths n);
    add_op :
      computed_op
        (WordByWordMontgomery.add m width) Field.add
        list_binop_insizes list_binop_outsizes (list_binop_inlengths n);
    sub_op :
      computed_op
        (WordByWordMontgomery.sub m width) Field.sub
        list_binop_insizes list_binop_outsizes (list_binop_inlengths n);
    opp_op :
      computed_op
        (WordByWordMontgomery.opp m width) Field.opp
        list_unop_insizes list_unop_outsizes (list_unop_inlengths n);
    square_op :
      computed_op
        (WordByWordMontgomery.square m width)
        Field.square
        list_unop_insizes list_unop_outsizes (list_unop_inlengths n);
    from_bytes_op :
      computed_op
        (WordByWordMontgomery.from_bytes m width)
        Field.from_bytes
        from_bytes_insizes from_bytes_outsizes (from_bytes_inlengths
                                                  (n_bytes m));
    to_bytes_op :
      computed_op
        (WordByWordMontgomery.to_bytes m width)
        Field.to_bytes
        to_bytes_insizes to_bytes_outsizes (to_bytes_inlengths n);
    from_mont_op :
      computed_op
        (WordByWordMontgomery.from_montgomery m width)
        from_mont
        list_unop_insizes list_unop_outsizes (list_unop_inlengths n);
    to_mont_op :
      computed_op
        (WordByWordMontgomery.to_montgomery m width)
        to_mont
        list_unop_insizes list_unop_outsizes (list_unop_inlengths n);
    select_znz_op : 
        computed_op
        (WordByWordMontgomery.selectznz m width)
        Field.select_znz
        list_selectznz_insizes list_selectznz_outsizes (list_selectznz_inlengths n)
  }.

Arguments word_by_word_Montgomery_ops {_ _ _ _ _ _ _ _ _ _ _ _ _} n.

(** We need to tell [check_args] that we are requesting these functions in order to get the relevant properties out *)
Notation necessary_requests := ["to_bytes"; "from_bytes"]%string (only parsing).

Section WordByWordMontgomery.
  Context
  {width BW word mem locals env ext_spec error}
  {parameters_sentinel : @parameters width BW word mem locals env ext_spec default_varname_gen error}
  {field_parameters : FieldParameters}
  {field_parameters_ok : FieldParameters_ok}
  {ok : Types.ok}.

  Context (m : Z)
          (M_eq : M = m)
          (check_args_ok :
             check_args m width necessary_requests (ErrorT.Success tt)
             = ErrorT.Success tt)
                                 .
  Definition r' := @Field.r' width field_parameters.

  Lemma m_big : (2 < m)%Z.
  Proof.
    pose proof (use_curve_good m width _ check_args_ok) as H.
    apply (OrdersEx.Z_as_DT.le_neq 2 m). split; try lia.
    destruct (m =? 2)%Z eqn:eq; try lia.
    assert (H' : ((r width * PushButtonSynthesis.WordByWordMontgomery.r' m width) mod m)%Z =
    1%Z) by apply H.
    apply Z.eqb_eq in eq. clear H.
    rewrite Z.mul_mod in H'; try lia. rewrite eq in H'. cbv [r] in H'.
    rewrite PullPush.Z.pow_mod_push in H'; [| cbv; auto].
    rewrite Z_mod_same in H'; try lia.
    rewrite Z.pow_0_l in H'; try lia.
    pose proof (use_curve_good m width _ check_args_ok); lia. 
    Qed.

  Lemma gcd_aux' : forall n m (e : nat), (Z.gcd n m = 1)%Z -> (Z.gcd (n ^ (Z.of_nat e)) m = 1)%Z.
  Proof.
    intros. induction e; auto.
      - destruct m0; auto.
      - apply Znumtheory.Zgcd_1_rel_prime.
        apply Znumtheory.rel_prime_sym.
        apply Zpow_facts.rel_prime_Zpower_r; try lia.
        apply Znumtheory.rel_prime_sym.
        apply Znumtheory.Zgcd_1_rel_prime. auto.
  Qed.

  Lemma r'_correct : ((2 ^ (width) * r' ) mod M = 1)%Z. (*Not very elegant proof...*)
  Proof.
    cbv [r' Field.r' Field.r].
    assert (H1mod : (1 = 1 mod M)%Z).
    {
      rewrite Zmod_small; split; try lia; rewrite M_eq; eapply use_curve_good; eauto.
    }
    rewrite H1mod.
    apply (ModInv.Z.modinv_correct).
      - rewrite M_eq. pose proof (use_curve_good m width _ check_args_ok). try lia.
      - rewrite Z.gcd_abs_l. apply Z.bezout_1_gcd. cbv [Z.Bezout].
        pose proof (use_curve_good _ _ _ check_args_ok) as H'.
        do 11 destruct H' as [_ H']. destruct H' as [H' _].
        pose proof (Modulo.Z.div_mod'' (r width * PushButtonSynthesis.WordByWordMontgomery.r' m width) m) as H.
        assert (H1 : (m <> 0)%Z).
        {
          pose proof (use_curve_good _ _ _ check_args_ok); lia.
        }
        specialize(H H1). eexists. eexists. cbv [r] in *.
        apply (f_equal (fun y => y - m *
        (2 ^ width * PushButtonSynthesis.WordByWordMontgomery.r' m width / m))%Z) in H.
        rewrite OrdersEx.Z_as_DT.add_simpl_r in H.
        rewrite <- H in H'. clear H1 H.
        assert (H0 : (forall x y, x - y = x + (- y))%Z) by auto with zarith.
        rewrite H0 in H'. clear H0.
        assert (H : (forall x y, - (x * y) = (- y) * x)%Z) by auto with zarith.
        rewrite H in H'. rewrite Z.mul_comm in H'. rewrite M_eq. apply H'.
  Qed.

  Local Notation n := (WordByWordMontgomery.n m width).

  Context (from_mont : string)
          (to_mont : string)
          (ops : word_by_word_Montgomery_ops n m)
          mul_func add_func sub_func opp_func square_func
          from_bytes_func to_bytes_func
          from_mont_func to_mont_func select_znz_func
          (mul_func_eq : mul_func = b2_func mul_op)
          (add_func_eq : add_func = b2_func add_op)
          (sub_func_eq : sub_func = b2_func sub_op)
          (opp_func_eq : opp_func = b2_func opp_op)
          (square_func_eq : square_func = b2_func square_op)
          (from_bytes_func_eq : from_bytes_func = b2_func from_bytes_op)
          (to_bytes_func_eq : to_bytes_func = b2_func to_bytes_op)
          (from_mont_func_eq : from_mont_func = b2_func from_mont_op)
          (to_mont_func_eq : to_mont_func = b2_func to_mont_op)
          (select_znz_func_eq : select_znz_func = b2_func (@select_znz_op from_mont to_mont _ _ _ _ _ _ _ _ _ _ _ _ _ _)).

  Local Notation weight := (uweight width) (only parsing).
  Definition eval_trans := (WordByWordMontgomery.from_montgomerymod width n m (WordByWordMontgomery.m' m width)).
  Definition eval_raw : (list Z -> list Z) := fun x => x. 

  Inductive bounds_type := (*Bounds type for WBW. must distinguish between bounds for lists of words and lists of bytes*)
  | wordlist
  | bytelist
  .

  Definition list_in_bounds bounds_type x :=
    match bounds_type with
    | wordlist => WordByWordMontgomery.valid width n m x
    | bytelist => WordByWordMontgomery.valid 8 (n_bytes m) m x
    end.

  Local Instance field_representation_raw : FieldRepresentation
  := Signature.field_representation
      n (n_bytes m) weight bounds_type
      wordlist
      wordlist
      bytelist
      list_in_bounds eval_raw.

  Local Instance field_representation : FieldRepresentation
    := field_representation
         n (n_bytes m) weight bounds_type
         wordlist
         wordlist
         bytelist
         list_in_bounds eval_trans.
  
  Local Ltac specialize_correctness_hyp Hcorrect :=
    cbv [feval feval_bytes bounded_by bytes_in_bounds Field.loose_bounds
               field_representation Signature.field_representation
               Representation.frep Representation.eval_bytes
               Representation.eval_words
               bin_model bin_xbounds bin_ybounds
               un_model un_xbounds
               ] in *;
    lazymatch type of Hcorrect with
    | forall x y, ?Px x -> ?Py y -> _ =>
      match goal with
        | Hx : Px ?x, Hy : Py ?y |- _ =>
          specialize (Hcorrect x y Hx Hy)
      end
    | forall x, ?Px x -> _ =>
      match goal with
        | Hx : Px ?x |- _ =>
          specialize (Hcorrect x Hx)
      end
    end.

  Lemma loose_bounds_eq : Field.loose_bounds = wordlist.
  Proof using Type. reflexivity. Qed.
  Lemma tight_bounds_eq : Field.tight_bounds = wordlist.
  Proof. reflexivity. Qed.

  (* TODO: move to coqutil.Datatypes.List *)
  Lemma Forall_repeat : forall {A} (R : A -> Prop) n x,
    R x -> Forall R (repeat x n).
  Proof using. clear.
    intros; induction n; intros; cbn [repeat];
    constructor; auto.
  Qed.

  Local Hint Resolve
        (* relax_valid *)
        func_eq
        inname_gen_varname_gen_disjoint
        outname_gen_varname_gen_disjoint
        (* length_tight_bounds *)
        (* length_loose_bounds *)
        (* length_byte_bounds *)
        (* byte_bounds_tighter_than *)
    : helpers.

  Local Hint Unfold
        Solinas.selectznz_correct
        Solinas.from_bytes_correct
        Solinas.to_bytes_correct
        Solinas.carry_mul_correct
        Solinas.carry_square_correct
        Solinas.carry_scmul_const_correct
        Solinas.add_correct
        Solinas.sub_correct
        Solinas.opp_correct
        Solinas.carry_correct
        Solinas.zero_correct
        Solinas.one_correct : solinas_specs.

  (* We wrap the tactic in [once] so it doesn't take forever to fail *)
  Ltac handle_side_conditions :=
    once
      (lazymatch goal with
       | |- API.Wf (res ?op)
         => generalize (res op), (res_eq op);
            (* Kludge around auto being bad (COQBUG(https://github.com/coq/coq/issues/14190)) and eauto not respecting Hint Opaque *)
            typeclasses eauto with wf_op_cache;
            let e := lazymatch goal with | |- forall res, ?e = _ -> API.Wf _ => e end in
            idtac "Warning: Falling back to manually proving pipeline well-formedness for" e;
            PipelineTactics.prove_pipeline_wf ()
       | |- context [Field.tight_bounds] => rewrite tight_bounds_eq
       | |- context [Field.loose_bounds] => rewrite loose_bounds_eq
       | _ => idtac
       end;
       lazymatch goal with
       | |- context [expr.interp] =>
         cbv [expr.Interp] in *; autounfold with solinas_specs in *
       | _ => eauto with helpers
       end).

  Hint Resolve relax_list_Z_bounded_by partition_bounded_by : bounds.

  Ltac simpl_map_unsigned :=
    lazymatch goal with
    | |- context [map Interface.word.unsigned
                      (map Interface.word.of_Z _)] =>
      rewrite map_unsigned_of_Z;
      erewrite MaxBounds.map_word_wrap_bounded
        by eauto with bounds
    | |- context [map Byte.byte.unsigned
                      (map Byte.byte.of_Z _)] =>
      rewrite byte_map_unsigned_of_Z;
      erewrite map_byte_wrap_bounded
        by eauto with bounds
    end.
  Ltac FtoZ :=
    apply F.eq_of_Z_iff; rewrite ?F.to_Z_of_Z;
    cbv [M] in M_eq; rewrite ?M_eq; pull_Zmod.
  
    (* Ltac bounds_length := simpl; intros; erewrite length_list_Z_bounded_by; eauto; try apply length_tight_bounds; try apply length_loose_bounds.   *)
    Lemma valid_bounded_by_prime_bounds x :
      (check_args m width [] (ErrorT.Success tt)
       = ErrorT.Success tt) ->
      WordByWordMontgomery.valid width n m x ->
      list_Z_bounded_by (prime_bounds m width) x.
    Proof.
      intros; unshelve eapply bounded_by_prime_bounds_of_valid; eauto.
    Qed.

    Ltac maxbounds_from_valid := intros _ Hvalid; destruct Hvalid as [Hsmall _]; rewrite Hsmall; apply MaxBounds.partition_bounded_by.

Lemma valid_max_bounds n0 : forall x, @WordByWordMontgomery.valid width n0 m x ->list_Z_bounded_by (@MaxBounds.max_bounds width n0) x.
Proof.
    intros. destruct H. rewrite H. eapply MaxBounds.partition_bounded_by.
Qed.

  Lemma valid_length : forall x, WordByWordMontgomery.valid width n m x -> length x = n.
  Proof.
      intros. destruct H. erewrite WordByWordMontgomery.length_small; eauto.
  Qed.

  Lemma mul_func_correct :
    valid_func (res mul_op _) ->
    forall functions,
      spec_of_BinOp bin_mul (mul_func :: functions). Set Printing All.
  Proof using M_eq check_args_ok mul_func_eq ok.
        (* tight_bounds_tighter_than. *)
    intros. cbv [spec_of_BinOp bin_mul]. rewrite mul_func_eq.
    pose proof mul_correct
         m width _ ltac:(eassumption) _ (res_eq mul_op)     
      as Hcorrect.
    eapply list_binop_correct with (res:=res mul_op);
    try handle_side_conditions; [| | eapply valid_max_bounds; eauto | apply valid_length].
    {   
    (* output *value* is correct *)
      intros. cbv [feval]. simpl. cbv [Representation.eval_words]. simpl. 
      cbv [feval feval_bytes bounded_by bytes_in_bounds Field.loose_bounds
               field_representation Signature.field_representation
               Representation.frep Representation.eval_bytes
               Representation.eval_words
               bin_model bin_xbounds bin_ybounds
               un_model un_xbounds eval_trans
      ] in *.
      specialize (Hcorrect (map Interface.word.unsigned x) (map Interface.word.unsigned y) H0 H1).
      FtoZ. rewrite map_unsigned_of_Z. erewrite (MaxBounds.map_word_wrap_bounded).
      2: {
        eapply valid_max_bounds; eauto. destruct Hcorrect; eauto.
      }
      destruct Hcorrect. auto.
    } 
    { (* output *bounds* are correct *)
      intros. apply Hcorrect; auto. }
  Qed.

  Lemma square_func_correct :
    valid_func (res square_op _) ->
    forall functions,
      spec_of_UnOp un_square (square_func :: functions).
  Proof using M_eq check_args_ok ok square_func_eq.
    intros. cbv [spec_of_UnOp un_square]. rewrite square_func_eq.
    pose proof square_correct
         _ _ _ ltac:(eassumption) _ (res_eq square_op)
      as Hcorrect.
    eapply list_unop_correct with (res:=res square_op);
      handle_side_conditions; [ | | apply valid_max_bounds | apply valid_length ].
    { (* output *value* is correct *)
    intros. cbv [feval]. simpl. cbv [Representation.eval_words]. simpl. 
    cbv [feval feval_bytes bounded_by bytes_in_bounds Field.loose_bounds
             field_representation Signature.field_representation
             Representation.frep Representation.eval_bytes
             Representation.eval_words
             bin_model bin_xbounds bin_ybounds
             un_model un_xbounds eval_trans
    ] in *.
    specialize (Hcorrect (map Interface.word.unsigned x) H0).
    rewrite map_unsigned_of_Z. erewrite (MaxBounds.map_word_wrap_bounded).
    2: {
      eapply valid_max_bounds; eauto. destruct Hcorrect; eauto.
    }
    destruct Hcorrect. auto. assert ( forall (x : Z), (x ^ 2 = x * x)%Z) by auto with zarith.
    rewrite F.pow_2_r. rewrite <- F.of_Z_mul. FtoZ.
    auto.
    }
    { (* output *bounds* are correct *)
      intros. apply Hcorrect; auto. }
  Qed.

  Lemma add_func_correct :
    valid_func (res add_op _) ->
    forall functions,
      spec_of_BinOp bin_add (add_func :: functions).
  Proof using M_eq check_args_ok add_func_eq ok.
    intros. cbv [spec_of_BinOp bin_add]. rewrite add_func_eq.
    pose proof add_correct
         _ _ _ ltac:(eassumption) _ (res_eq add_op)
      as Hcorrect.
    eapply list_binop_correct with (res:=res add_op);
    handle_side_conditions; [ | | apply valid_max_bounds | apply valid_length ].
    { (* output *value* is correct *)
    intros. cbv [feval]. simpl. cbv [Representation.eval_words]. simpl. 
    cbv [feval feval_bytes bounded_by bytes_in_bounds Field.loose_bounds
             field_representation Signature.field_representation
             Representation.frep Representation.eval_bytes
             Representation.eval_words
             bin_model bin_xbounds bin_ybounds
             un_model un_xbounds eval_trans
    ] in *.
    specialize (Hcorrect (map Interface.word.unsigned x) (map Interface.word.unsigned y) H0 H1).
    rewrite map_unsigned_of_Z. erewrite (MaxBounds.map_word_wrap_bounded).
    2: {
      eapply valid_max_bounds; eauto. destruct Hcorrect; eauto.
    }
    destruct Hcorrect. FtoZ.
    auto.
     }
    { (* output *bounds* are correct *)
      intros. apply Hcorrect; auto. }
  Qed.

  Lemma sub_func_correct :
    valid_func (res sub_op _) ->
    forall functions,
      spec_of_BinOp bin_sub (sub_func :: functions).
  Proof using M_eq check_args_ok sub_func_eq ok.
    intros. cbv [spec_of_BinOp bin_sub]. rewrite sub_func_eq.
    pose proof sub_correct
         _ _ _ ltac:(eassumption) _ (res_eq sub_op)
      as Hcorrect.
    eapply list_binop_correct with (res:=res sub_op);
    handle_side_conditions; [ | | apply valid_max_bounds| apply valid_length ].
    { (* output *value* is correct *)
    intros. cbv [feval]. simpl. cbv [Representation.eval_words]. simpl. 
    cbv [feval feval_bytes bounded_by bytes_in_bounds Field.loose_bounds
             field_representation Signature.field_representation
             Representation.frep Representation.eval_bytes
             Representation.eval_words
             bin_model bin_xbounds bin_ybounds
             un_model un_xbounds eval_trans
    ] in *.
    specialize (Hcorrect (map Interface.word.unsigned x) (map Interface.word.unsigned y) H0 H1).
    rewrite map_unsigned_of_Z. erewrite (MaxBounds.map_word_wrap_bounded).
    2: {
      eapply valid_max_bounds; eauto. destruct Hcorrect; eauto.
    }
    destruct Hcorrect. rewrite <- F.of_Z_sub. FtoZ.
    auto. }
    { (* output *bounds* are correct *)
      intros. apply Hcorrect; auto. }
  Qed.

  Lemma opp_func_correct :
    valid_func (res opp_op _) ->
    forall functions,
      spec_of_UnOp un_opp (opp_func :: functions).
  Proof using M_eq check_args_ok opp_func_eq ok.
    intros. cbv [spec_of_UnOp un_opp]. rewrite opp_func_eq.
    pose proof opp_correct
         _ _ _ ltac:(eassumption) _ (res_eq opp_op)
      as Hcorrect.

    eapply list_unop_correct with (res:=res opp_op);
      handle_side_conditions; [ | | apply valid_max_bounds | apply valid_length ].
    { (* output *value* is correct *)
    intros. cbv [feval]. simpl. cbv [Representation.eval_words]. simpl. 
    cbv [feval feval_bytes bounded_by bytes_in_bounds Field.loose_bounds
             field_representation Signature.field_representation
             Representation.frep Representation.eval_bytes
             Representation.eval_words
             bin_model bin_xbounds bin_ybounds
             un_model un_xbounds eval_trans
    ] in *.
    specialize (Hcorrect (map Interface.word.unsigned x) H0).
    rewrite map_unsigned_of_Z. erewrite (MaxBounds.map_word_wrap_bounded).
    2: {
      eapply valid_max_bounds; eauto. destruct Hcorrect; eauto.
    }
    destruct Hcorrect. FtoZ.
    auto.
     }
    { (* output *bounds* are correct *)
      intros. apply Hcorrect; auto. }
  Qed.

  Lemma from_bytes_func_correct :
    valid_func (res from_bytes_op _) ->
    forall functions,
      (@spec_of_from_bytes _ _ _ _ _ _ _ field_representation_raw) (from_bytes_func :: functions).
  Proof using M_eq check_args_ok from_bytes_func_eq ok.
    intros. cbv [spec_of_from_bytes]. rewrite from_bytes_func_eq.
    pose proof from_bytes_correct
         _ _ _ ltac:(eassumption) _ (res_eq from_bytes_op)
      as Hcorrect.

    eapply Signature.from_bytes_correct with (res:=res from_bytes_op);
      handle_side_conditions; [ apply valid_max_bounds | apply valid_length | | ].
    { (* output *value* is correct *)
    intros. cbv [feval]. simpl. cbv [Representation.eval_words]. simpl. 
    cbv [feval feval_bytes bounded_by bytes_in_bounds Field.loose_bounds
             field_representation Signature.field_representation
             Representation.frep Representation.eval_bytes
             Representation.eval_words
             bin_model bin_xbounds bin_ybounds
             un_model un_xbounds eval_trans
    ] in *.
    
    specialize (Hcorrect (map Byte.byte.unsigned bs) H0).
    rewrite map_unsigned_of_Z. erewrite (MaxBounds.map_word_wrap_bounded).
    2: {
      eapply valid_max_bounds; eauto. destruct Hcorrect; eauto.
    }
    destruct Hcorrect.
    FtoZ; auto.
     }
    { (* output *bounds* are correct *)
      intros. apply Hcorrect; auto. }
  Qed.

  Lemma to_bytes_func_correct :
    valid_func (res to_bytes_op _) ->
    forall functions,
      (@spec_of_to_bytes _ _ _ _ _ _ _ field_representation_raw) (to_bytes_func :: functions).
  Proof using M_eq check_args_ok ok to_bytes_func_eq.
    intros. cbv [spec_of_to_bytes]. rewrite to_bytes_func_eq.
    pose proof to_bytes_correct
         _ _ _ ltac:(eassumption) _ (res_eq to_bytes_op)
      as Hcorrect.

    eapply Signature.to_bytes_correct with (res:=res to_bytes_op);
      handle_side_conditions; cbv [list_in_bounds]; [ | | | ].
    {
      intros. apply byte_bounds_range_iff; split; eauto.
        - destruct H0. eapply WordByWordMontgomery.length_small; eauto.
        - destruct H0. cbv [WordByWordMontgomery.small] in *.
          rewrite H0. apply partition_bytes_range.
    }
    {
      intros. destruct H0. apply WordByWordMontgomery.length_small in H0. rewrite H0. eauto.
    }
    { (* output *value* is correct *)
    intros. cbv [feval]. simpl. 
    cbv [feval feval_bytes bounded_by bytes_in_bounds Field.loose_bounds
             field_representation Signature.field_representation
             Representation.frep Representation.eval_bytes
             Representation.eval_words
             bin_model bin_xbounds bin_ybounds
             un_model un_xbounds eval_trans
    ] in *.
    
    specialize (Hcorrect (map Interface.word.unsigned x) H0).
    rewrite Hcorrect. cbv [M] in M_eq. rewrite M_eq. auto.
     }
    { (* output *bounds* are correct *)
      intros. rewrite Hcorrect by auto.
      cbn [bytes_in_bounds Representation.frep
                           Signature.field_representation].
      erewrite ByteBounds.byte_map_unsigned_of_Z,
      ByteBounds.map_byte_wrap_bounded
        by apply ByteBounds.partition_bounded_by.
      cbv [bounded_by] in *; simpl in H0.
      (*TODO: use valid_partition_small*)
      {
        split.
        - unfold WordByWordMontgomery.small. unfold WordByWordMontgomery.eval. rewrite Partition.eval_partition.
          2: {
            apply uwprops. lia.
          }
        rewrite Zmod_small.
        2: { destruct H0. unfold WordByWordMontgomery.eval in H1. auto. }
          cbv [uweight].
          rewrite Zmod_small; auto. split.
            + destruct H0. cbv [WordByWordMontgomery.eval] in H1. cbv [uweight] in H1. lia.
            + destruct H0. cbv [WordByWordMontgomery.eval] in H1. cbv [uweight] in H1. destruct H1.
              assert ( m < ModOps.weight 8 1 (n_bytes m))%Z.
              {
                pose proof (use_curve_good _ _ _ check_args_ok).
                assert (m < s m)%Z by lia.
                cbv [uweight] in H3. lia.
              }
            lia.
          - cbv [WordByWordMontgomery.eval]. rewrite Partition.eval_partition.
            2: {
              apply uwprops; lia.
              }
              split.
                + apply Z_mod_lt. destruct (uwprops 8); try lia.
                  cbv [uweight] in *. specialize (weight_positive (n_bytes m)). lia.
                + rewrite Zmod_small; [| split].
                  * apply Z_mod_lt. pose proof (use_curve_good _ _ _ check_args_ok); lia.
                  * apply Z_mod_lt. pose proof (use_curve_good _ _ _ check_args_ok); lia.
                  * pose proof (use_curve_good _ _ _ check_args_ok).
                    assert (m < s m)%Z by lia.
                    cbv [uweight] in *.
                    eapply Z.lt_trans.
                    {
                      apply Z_mod_lt. pose proof (use_curve_good _ _ _ check_args_ok). lia.
                    }
                     lia.
      }
    }
  Qed.

  Lemma m_nz : m <> 0%Z.
  Proof.
    epose proof (use_curve_good _ _ _ check_args_ok). lia.
  Qed.

  (*Correctness proof of from- and to_montgomery are somewhat messy. *)
  Lemma from_mont_func_correct :
  valid_func (res from_mont_op _) ->
  forall functions,
    (@spec_of_UnOp _ _ _ _ _ _ _ _ from_mont) un_from_mont (from_mont_func :: functions).
    Proof using M_eq check_args_ok ok from_mont_func_eq.
    clear field_parameters_ok.
    intros. cbv [spec_of_UnOp un_from_mont]. rewrite from_mont_func_eq.
    pose proof from_montgomery_correct
        _ _ _ ltac:(eassumption) _ (res_eq from_mont_op)
      as Hcorrect.

    eapply list_unop_correct with (res:=res from_mont_op);
      handle_side_conditions; [ | | apply valid_max_bounds | apply valid_length ].
    { (* output *value* is correct *)
    intros. cbv [feval]. simpl. cbv [Representation.eval_words]. simpl. 
    cbv [feval feval_bytes bounded_by bytes_in_bounds Field.loose_bounds
            field_representation Signature.field_representation
            Representation.frep Representation.eval_bytes
            Representation.eval_words
            bin_model bin_xbounds bin_ybounds
            un_model un_xbounds eval_trans
    ] in *.
    specialize (Hcorrect (map Interface.word.unsigned x) H0).
    rewrite map_unsigned_of_Z. erewrite (MaxBounds.map_word_wrap_bounded).
    2: {
      eapply valid_max_bounds; eauto. destruct Hcorrect; eauto.
    }
    destruct Hcorrect. FtoZ. pose proof (WordByWordMontgomery.from_montgomerymod_correct width n m (@Field.r' width field_parameters) (m' m width)) as Hcorrect.
    cbv [WordByWordMontgomery.eval] in *.
    edestruct Hcorrect as [Hvalue Hvalid]; [| | | | | | eapply H2| ]; try eapply use_curve_good; try eassumption; [pose proof r'_correct as Htemp; cbv [r' M] in Htemp; rewrite M_eq in Htemp; eauto |].
    rewrite Hvalue. rewrite Z.mul_mod; try apply m_nz. rewrite H1. rewrite <- Z.mul_mod; try apply m_nz.
    symmetry. rewrite Z.mul_mod; try apply m_nz. cbv [list_in_bounds] in *. clear H2.
    edestruct Hcorrect as [Hvalue' _]; [| | | | | | eapply H0 |]; try eapply use_curve_good; try eassumption; [pose proof r'_correct as Htemp; cbv [r' M] in Htemp; rewrite M_eq in Htemp; eauto |].
    rewrite Hvalue'. rewrite <- Z.mul_mod; try apply m_nz.
    cbv [Field.r' PushButtonSynthesis.WordByWordMontgomery.r' Field.r r M felem_size_in_words]. rewrite M_eq.
    auto.
    }
    { (* output *bounds* are correct *)
      intros. apply Hcorrect; auto. }
  Qed.

  Lemma to_mont_func_correct :
  valid_func (res to_mont_op _) ->
  forall functions,
    (@spec_of_UnOp _ _ _ _ _ _ _ _ to_mont) un_to_mont (to_mont_func :: functions).
    Proof using M_eq check_args_ok ok to_mont_func_eq.
    intros. cbv [spec_of_UnOp un_to_mont]. rewrite to_mont_func_eq.
    pose proof to_montgomery_correct
        _ _ _ ltac:(eassumption) _ (res_eq to_mont_op)
      as Hcorrect.

    eapply list_unop_correct with (res:=res to_mont_op);
      handle_side_conditions; [ | | apply valid_max_bounds | apply valid_length].
    { (* output *value* is correct *)
    intros. cbv [feval]. simpl. cbv [Representation.eval_words]. simpl. 
    cbv [feval feval_bytes bounded_by bytes_in_bounds Field.loose_bounds
            field_representation Signature.field_representation
            Representation.frep Representation.eval_bytes
            Representation.eval_words
            bin_model bin_xbounds bin_ybounds
            un_model un_xbounds eval_trans
    ] in *.
    specialize (Hcorrect (map Interface.word.unsigned x) H0).
    rewrite map_unsigned_of_Z. erewrite (MaxBounds.map_word_wrap_bounded).
    2: {
      eapply valid_max_bounds; eauto. destruct Hcorrect; eauto.
    }
    destruct Hcorrect. FtoZ.
    cbv [WordByWordMontgomery.eval] in *.
    rewrite H1.
    pose proof (WordByWordMontgomery.from_montgomerymod_correct width n m (@Field.r' width field_parameters) (m' m width)) as Hcorrect.
    cbv [WordByWordMontgomery.eval] in *.
    edestruct Hcorrect as [Hvalue _]; [ | | | | | | apply H0 |]; try eapply use_curve_good; try eassumption;
    [pose proof r'_correct as Htemp; cbv [r' M] in Htemp; rewrite M_eq in Htemp; auto| ].
    rewrite Z.mul_mod; try apply m_nz. rewrite Hvalue. rewrite <- Z.mul_mod; try apply m_nz.
    rewrite <- Z.mul_assoc. rewrite Z.mul_mod; try apply m_nz.
    lazymatch goal with
    | |- _ = (_ * (?prd)%Z mod _)%Z => eassert (Hr' : prd = _)
    | _ => idtac
    end.
      {
        pose proof (r'_correct) as Htemp. rewrite <- Z.pow_mul_l. rewrite PullPush.Z.mod_pow_full.
        rewrite Z.mul_comm.
        cbv [Field.r]. cbv [r' M] in Htemp. rewrite M_eq in Htemp.
        rewrite Htemp. rewrite Z.pow_1_l; auto with zarith.
      }
      rewrite Hr'. assert (H1' : (1 mod m = 1)%Z).
      {
        apply Zmod_small; split; [lia| ]. pose proof m_big. lia.
      }
      rewrite H1'. rewrite Z.mul_1_r. rewrite Zmod_mod. auto.
    }
    { (* output *bounds* are correct *)
      intros. apply Hcorrect; auto. }
  Qed.

  Lemma select_znz_func_correct :
  valid_func (res select_znz_op _) ->
  forall functions,
    spec_of_selectznz (select_znz_func :: functions).
Proof using M_eq check_args_ok select_znz_func_eq ok.
  intros. cbv [spec_of_selectznz]. rewrite select_znz_func_eq.
  pose proof selectznz_correct
       _ _ _ ltac:(eassumption) _ (res_eq select_znz_op)
    as Hcorrect.
  eapply Signature.select_znz_correct with (res:=res select_znz_op);
    handle_side_conditions. intros x y c H0 H1 H2.
    unfold COperationSpecifications.WordByWordMontgomery.selectznz_correct in Hcorrect.
    edestruct (bit_range_eq 1 (fun n => 1%Z) _ H2) as [Hbit | Hbit].
    - specialize (Hcorrect (Interface.word.unsigned c) (map Interface.word.unsigned x) (map Interface.word.unsigned y) H2 ltac:(eauto) ltac:(eauto)).
      destruct Hcorrect as [H4 H5]. rewrite Hbit in H4. simpl in H4. rewrite Hbit. simpl. auto.
    - specialize (Hcorrect (Interface.word.unsigned c) (map Interface.word.unsigned x) (map Interface.word.unsigned y) H2 ltac:(eauto) ltac:(eauto)).
      destruct Hcorrect as [H4 H5]. rewrite Hbit in H4. simpl in H4. rewrite Hbit. simpl. auto.
Qed.

End WordByWordMontgomery.


(* Prototyping full pipeline: *)

Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Field.Translation.Proofs.ValidComputable.Func.

(* TODO: move somewhere common *)
Definition field_parameters_prefixed
           M_pos a24 (prefix: string) : FieldParameters :=
  Build_FieldParameters
    M_pos a24
    (prefix ++ "mul")
    (prefix ++ "add")
    (prefix ++ "sub")
    (prefix ++ "opp")
    (prefix ++ "square")
    (prefix ++ "scmula24")
    (prefix ++ "inv")
    (prefix ++ "from_bytes")
    (prefix ++ "to_bytes")
    (prefix ++ "felem_copy")
    (prefix ++ "small_literal")
    (prefix ++ "select_znz")
.


Require Import bedrock2.ProgramLogic.

(* Section Tests.
  Definition m := (2^224 - 2^96 + 1)%Z.
  Definition prefix : string := "p224_"%string.

  Existing Instances Defaults64.default_parameters default_parameters_ok.
  Existing Instances no_select_size split_mul_to split_multiret_to.
  Definition n := Eval vm_compute in (WordByWordMontgomery.n m machine_wordsize).

  Instance field_parameters : FieldParameters.
  Proof using Type.
    let M := (eval vm_compute in (Z.to_pos (m))) in
    (* Curve25519 "A" parameter (see section 4.1 of RFC 7748) *)
    let a := constr:(F.of_Z M 486662) in
    let prefix := constr:("p224_"%string) in
    eapply
      (field_parameters_prefixed
         M ((a - F.of_Z _ 2) / F.of_Z _ 4)%F prefix).
  Defined.

  Instance p224_ops : word_by_word_Montgomery_ops n m.
  Proof using Type. Time constructor; make_computed_op. Defined.

  Local Ltac begin_derive_bedrock2_func :=
  lazymatch goal with
  | |- context [spec_of_BinOp bin_mul] => eapply mul_func_correct
  | |- context [spec_of_UnOp un_square] => eapply square_func_correct
  | |- context [spec_of_BinOp bin_add] => eapply add_func_correct
  | |- context [spec_of_BinOp bin_sub] => eapply sub_func_correct
  | |- context [spec_of_UnOp un_opp] => eapply opp_func_correct
  (* | |- context [spec_of_UnOp un_scmula24] => eapply scmula24_func_correct *)
  | |- context [spec_of_from_bytes] => eapply from_bytes_func_correct
  | |- context [spec_of_to_bytes] => eapply to_bytes_func_correct
  end.

  Local Ltac derive_bedrock2_func op :=
  begin_derive_bedrock2_func;
  (* this goal fills in the evar, so do it first for [abstract] to be happy *)
  try lazymatch goal with
      | |- _ = b2_func _ => vm_compute; reflexivity
      end;
  (* solve all the remaining goals *)
  lazymatch goal with
  | |- _ = @ErrorT.Success ?ErrT unit tt =>
    abstract (vm_cast_no_check (@eq_refl _ (@ErrorT.Success ErrT unit tt)))
  | |- list_Z_tighter_than _ _ =>
    abstract (vm_cast_no_check (@eq_refl bool true))
  | |- valid_func _ =>
    eapply valid_func_bool_iff;
    abstract vm_cast_no_check (eq_refl true)
  | |- (_ = _)%Z  => vm_compute; reflexivity
  | |- _ = default_varname_gen => vm_compute; reflexivity
  end.

Derive p224_to_bytes
  SuchThat (forall functions,
               spec_of_to_bytes
                 (field_representation:=field_representation_raw m)
                 (p224_to_bytes :: functions))
  As p224_to_bytes_correct.
Proof. derive_bedrock2_func to_bytes_op. Qed.

Derive p224_mul
  SuchThat (forall functions,
              spec_of_BinOp bin_mul
                (field_representation := field_representation m)
                (p224_mul :: functions))
  As p22_mul_correct.
Proof. derive_bedrock2_func mul_op. Qed.


End Tests. *)