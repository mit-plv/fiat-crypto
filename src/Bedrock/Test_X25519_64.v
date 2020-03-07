Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Translation.Func.
Require Import Crypto.Bedrock.Util.
Require Import Crypto.Bedrock.Proofs.Func.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import bedrock2.Array.
Require Import bedrock2.Scalars.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.Map.Separation.
Require bedrock2.NotationsCustomEntry.

Import Language.Compilers.
Import Associational Positional.
Import Types.Notations.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

(* Curve25519 64-bit *)
Module X25519_64.
  Section __.
    Context (n : nat := 5%nat)
            (s : Z := 2^255)
            (c : list (Z * Z) := [(1,19)])
            (machine_wordsize : Z := 64).

    Local Existing Instance default_low_level_rewriter_method.
    Local Instance only_signed : only_signed_opt := false.
    Local Instance should_split_mul : should_split_mul_opt := true.
    Local Instance should_split_multiret : should_split_multiret_opt := true.
    Local Instance widen_carry : widen_carry_opt := true.
    Local Instance widen_bytes : widen_bytes_opt := true.

    Let limbwidth := (Z.log2_up (s - Associational.eval c) / Z.of_nat n)%Q.
    Let idxs := (List.seq 0 n ++ [0; 1])%list%nat.

    Definition possible_values_of_machine_wordsize
      := prefix_with_carry [machine_wordsize; 2 * machine_wordsize]%Z.

    Let possible_values := possible_values_of_machine_wordsize.

    Local Instance split_mul_to : split_mul_to_opt :=
      split_mul_to_of_should_split_mul machine_wordsize possible_values.
    Local Instance split_multiret_to : split_multiret_to_opt :=
      split_multiret_to_of_should_split_multiret machine_wordsize possible_values.

    Let prime_upperbound_list : list Z
      := encode_no_reduce (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
    Let tight_upperbounds : list Z
      := List.map
           (fun v : Z => Qceiling (11/10 * v))
           prime_upperbound_list.
    Definition tight_bounds : list (ZRange.type.option.interp (type.base (base.type.type_base base.type.Z)))
      := List.map (fun u => Some r[0~>u]%zrange) tight_upperbounds.
    Definition loose_bounds : list (ZRange.type.option.interp (type.base (base.type.type_base base.type.Z)))
      := List.map (fun u => Some r[0 ~> 3*u]%zrange) tight_upperbounds.

    Let limbwidth_num := Eval vm_compute in Qnum limbwidth.
    Let limbwidth_den := Eval vm_compute in QDen limbwidth.

    Set Printing Depth 100000.
    Local Open Scope string_scope.
    Local Notation "'uint64,uint64'" := (ident.Literal
                                           (r[0 ~> 18446744073709551615]%zrange,
                                            r[0 ~> 18446744073709551615]%zrange)%core) : expr_scope.
    Local Notation "'uint64'" :=
      (ident.Literal (t:=Compilers.zrange) r[0 ~> 18446744073709551615]%zrange) : expr_scope.
    Local Open Scope expr_scope.
    Local Open Scope core_scope.

    Definition mulmod_ : Pipeline.ErrorT (Expr _) :=
      Pipeline.BoundsPipeline
        false (* subst01 *)
        None (* fancy *)
        possible_values
        ltac:(let r := Reify ((carry_mulmod limbwidth_num limbwidth_den s c n idxs)) in
              exact r)
               (Some loose_bounds, (Some loose_bounds, tt))
               (Some tight_bounds).
    Definition mulmod := Eval vm_compute in mulmod_.

    Local Existing Instances Types.rep.Z Types.rep.listZ_mem.
    Let wordsize_bytes := Eval vm_compute in (machine_wordsize / 8)%Z.

    Instance p : Types.parameters :=
      {| semantics := BasicC64Semantics.parameters;
         varname_gen := fun i => String.append "x" (Decimal.decimal_string_of_Z (Z.of_nat i));
         error := expr.var "ERROR";
         word_size_in_bytes := wordsize_bytes;
      |}.

    Local Definition bedrock_func : Type :=
      string * (list string * list string * cmd.cmd).
    Local Coercion name_of_func (f : bedrock_func) := fst f.

    Definition mulmod_bedrock : bedrock_func :=
      ("mulmod_bedrock",
       match mulmod with
       | ErrorT.Success e =>
         translate_func e
                        ("in0", ("in1", tt)) (* argument names *)
                        (n, (n, tt)) (* lengths for list arguments *)
                        (expr.var "in0") (* location(s) for returned lists (can be in terms of arguments) *)
                        "ret" (* return value name *)
       | ErrorT.Error _ => (nil, nil, Syntax.cmd.skip)
       end).

    Section Proofs.

      (* requires some kind of proof about decimal stringification *)
      Lemma decimal_varname_gen_unique :
        forall i j : nat, varname_gen i = varname_gen j <-> i = j.
      Admitted.

      Instance p_ok : Types.ok.
      Proof.
        constructor.
        { exact BasicC64Semantics.parameters_ok. }
        { reflexivity. }
        { exact decimal_varname_gen_unique. }
      Defined.

      Local Notation M := (s - Associational.eval c)%Z.
      Local Notation eval :=
        (eval (weight limbwidth_num limbwidth_den) n).
      
      Definition Bignum (addr : Semantics.word) (x : Z) :
        Semantics.mem -> Prop :=
        Lift1Prop.ex1
          (fun xs =>
             sep (emp (eval (map word.unsigned xs) = x))
                 (sep (emp (length xs = n))
                      (array scalar (word.of_Z word_size_in_bytes)
                             addr xs))).

      (* TODO: Ideally, the translation would take an extra argument for every
         list in the output, and remove those from the rets. *)
      (* TODO: it would be nice to say something like (rets = [px]); that
         returned lists are not just put back in some pointer somewhere that has
         the right frame, but are put back at exactly the correct pointer *)

      Instance spec_of_mulmod_bedrock : spec_of mulmod_bedrock :=
        fun functions =>
          forall x y px py t m
                 (R : Semantics.mem -> Prop),
            sep (sep (Bignum px x) (Bignum py y)) R m ->
            WeakestPrecondition.call
              (p:=@semantics p)
              functions mulmod_bedrock t m
              (px :: py :: nil)
              (fun t' m' rets =>
                 t = t' /\
                 rets = [px]%list /\
                 sep (sep (Bignum px ((x * y) mod M)%Z)
                          (Bignum py y)) R m').

      (* TODO: maybe make a computable condition for this *)
      (* Won't pass right now because valid_expr isn't complete *)
      Lemma mulmod_valid_func v :
        mulmod = ErrorT.Success v ->
        valid_func (v (fun H3 : API.type => unit)).
      Admitted.

      (* TODO: ask Jason for help *)
      Lemma mulmod_Wf v :
        mulmod = ErrorT.Success v ->
        Wf.Compilers.expr.Wf3 v.
      Admitted.

      Lemma mulmod_length v (x y : API.interp_type type_listZ) :
        mulmod = ErrorT.Success v ->
        length
          (expr.interp (@Compilers.ident_interp) (v API.interp_type)
                       x y) = n.
      Proof.
        intro Hmm. vm_compute in Hmm.
        inversion Hmm.
        vm_compute. reflexivity.
      Qed.

      (* TODO: here's where we need to use the FC pipeline to say things about
         correctness *)
      (* this can be changed to use type.app_curried if that's easier *)
      Lemma mulmod_correct v x y :
        mulmod = ErrorT.Success v ->
        eval
          (map word.wrap
               (expr.interp
                  (@Compilers.ident_interp) (v API.interp_type)
                  (map word.unsigned x) (map word.unsigned y))) =
        ((eval (map word.unsigned x) * eval (map word.unsigned y)) mod M)%Z.
      Admitted.

      (* TODO : move *)
      Lemma substring_0_0 :
        forall s, substring 0 0 s = "".
      Proof.
        clear. destruct s; reflexivity.
      Qed.

      Lemma varname_gen_startswith v i :
        v = varname_gen i ->
        String.startswith "x" v = true.
      Proof.
        cbn [varname_gen p]. intro.
        subst. cbn. rewrite substring_0_0.
        reflexivity.
      Qed.

      (* TODO : move *)
      Lemma map_of_Z_unsigned x :
        map word.of_Z (map word.unsigned x) = x.
      Proof.
        rewrite map_map.
        rewrite map_ext with (g:=id);
          [ solve [apply map_id] | ].
        intros. rewrite word.of_Z_unsigned.
        reflexivity.
      Qed.

      (* TODO : move *)
      Lemma map_unsigned_of_Z x :
        map word.unsigned (map word.of_Z x) = map word.wrap x.
      Proof.
        rewrite map_map. apply map_ext.
        exact word.unsigned_of_Z.
      Qed.

      Lemma mulmod_bedrock_correct :
        program_logic_goal_for_function! mulmod_bedrock.
      Proof.
        cbv [program_logic_goal_for spec_of_mulmod_bedrock].
        cbn [name_of_func mulmod_bedrock fst]. intros.
        cbv [mulmod_bedrock].
        case_eq mulmod;
          [ | let H := fresh in
              intros ? H; vm_compute in H; congruence ].
        intros. cbv [Bignum] in * |-. sepsimpl.
        eapply Proper_call.
        2:{
          let xs := match goal with
                      Hx : eval ?xs = x |- _ =>
                      xs end in
          let ys := match goal with
                      Hy : eval ?ys = y |- _ =>
                      ys end in
          apply translate_func_correct
            with (args:=(xs, (ys, tt)))
                 (Ra:=R) (Rr:=sep (Bignum py y) R).
          { apply mulmod_valid_func; eauto. }
          { apply mulmod_Wf; eauto. }
          { cbn [LoadStoreList.list_lengths_from_args
                   LoadStoreList.list_lengths_from_value
                   fst snd].
            rewrite !map_length.
            repeat match goal with H : length _ = n |- _ =>
                                   rewrite H end.
            reflexivity. }
          { intros.
            cbn [fst snd Types.varname_set_args Types.varname_set
                     Types.rep.varname_set Types.rep.listZ_mem
                     Types.rep.Z].
            cbv [PropSet.union PropSet.singleton_set PropSet.elem_of
                               PropSet.empty_set].
            destruct 1 as [? | [? | ?] ]; try tauto;
              match goal with H : _ = varname_gen _ |- _ =>
                              apply varname_gen_startswith in H;
                                vm_compute in H; congruence
              end. }
          { cbn [fst snd Types.equivalent_flat_args Types.rep.listZ_mem
                     Types.equivalent_flat_base Types.rep.equiv
                     Types.rep.Z]. sepsimpl.
            exists 1%nat. cbn [firstn skipn length hd].
            apply SeparationLogic.sep_comm.
            apply SeparationLogic.sep_assoc.
            apply SeparationLogic.sep_comm.
            apply SeparationLogic.sep_ex1_l.
            exists 1%nat. cbn [firstn skipn length hd].
            apply SeparationLogic.sep_assoc.
            sepsimpl; try reflexivity; [ ].
            eexists. sepsimpl; try reflexivity; [ ].
            apply SeparationLogic.sep_comm.
            apply SeparationLogic.sep_assoc.
            apply SeparationLogic.sep_comm.
            sepsimpl; try reflexivity; [ ].
            eexists. sepsimpl; try reflexivity; [ ].
            rewrite !map_of_Z_unsigned.
            rewrite !word.of_Z_unsigned in *.
            change parameters with semantics in *.
            SeparationLogic.ecancel_assumption. }
          { cbn. repeat constructor; cbn [In]; try tauto.
            destruct 1; congruence. }
          { intros.
            cbn [fst snd Types.varname_set type.final_codomain
                     Types.rep.varname_set Types.rep.listZ_mem
                     Types.rep.Z].
            cbv [PropSet.singleton_set PropSet.elem_of PropSet.empty_set].
            intro;
              match goal with H : _ = varname_gen _ |- _ =>
                              apply varname_gen_startswith in H;
                                vm_compute in H; congruence
              end. }
          { cbn. repeat constructor; cbn [In]; tauto. }
          { cbn. rewrite union_empty_r.
            apply disjoint_singleton_r_iff.
            cbv [PropSet.singleton_set PropSet.elem_of PropSet.union].
            destruct 1; congruence. }
          { cbn - [semantics Semantics.word p].
            cbv [Bignum].
            sepsimpl.
            (let xs := (match goal with
                          Hx : eval ?xs = x |- _ =>
                          xs end) in
             exists xs).
            sepsimpl;
              [ rewrite map_length, mulmod_length by assumption;
                congruence | ].
            exists (word.unsigned px). sepsimpl.
            { apply get_put_diff; [ congruence | ].
              apply get_put_same, word.of_Z_unsigned. }

            eexists. sepsimpl; eauto; [ ].
            rewrite map_of_Z_unsigned, word.of_Z_unsigned.
            change parameters with semantics in *.
            SeparationLogic.ecancel_assumption. } }
        repeat intro; cbv beta in *.
        cbn [Types.equivalent_flat_base
               Types.rep.equiv Types.rep.listZ_mem Types.rep.Z
               type.final_codomain] in *.
        repeat match goal with
               | _ => progress subst
               | _ => progress sepsimpl_hyps
               | H : _ /\ _ |- _ => destruct H
               | |- _ /\ _ => split; [ reflexivity | ]
               end.
        (* see TODO above spec *)
        match goal with
          |- ?rets = [px]%list /\ _ =>
          assert (rets = [px]%list) by admit;
            split; [ assumption | subst ]
        end.
        sepsimpl.
        match goal with
        | H : dexpr _ _ (expr.literal _) _ |- _ =>
          cbn [dexpr WeakestPrecondition.expr expr_body hd] in H;
            cbv [literal] in H; rewrite word.of_Z_unsigned in H;
              inversion H; clear H; subst
        end.
        match goal with
        | H : sep ?p (sep ?q ?r) ?m
          |- sep (sep _ ?q) ?r ?m =>
          eapply SeparationLogic.sep_assoc;
            eapply SeparationLogic.Proper_sep_impl1;
            [ | reflexivity | eapply H ]; [ ];
            clear H; repeat intro
        end.
        cbv [Bignum].
        eexists; sepsimpl;
          [ | | eassumption];
          [ | cbn [type.app_curried];
              rewrite map_length, mulmod_length; solve [eauto] ].
        clear H.
        cbn [type.app_curried fst snd].
        rewrite map_unsigned_of_Z.
        apply mulmod_correct; eauto.
      Admitted.

    End Proofs.

    Import NotationsCustomEntry.
    Local Set Printing Width 150.
    Redirect "Crypto.Bedrock.Test_X25519_64.mulmod_bedrock" Compute mulmod_bedrock.

  End __.
End X25519_64.
