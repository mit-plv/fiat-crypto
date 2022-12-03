Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Lib.Loops.
Require Import Rupicola.Lib.Gensym.
Require Import coqutil.Word.LittleEndianList.
Require Import Crypto.Bedrock.End2End.RupicolaCrypto.Low.
Require Import bedrock2.BasicC32Semantics.
Require Import Crypto.Bedrock.End2End.RupicolaCrypto.Broadcast.

Section Bedrock2.

  Instance spec_of_quarter : spec_of "quarter" :=
    fnspec! "quarter" (a b c d : word) ~> (a' b' c' d' : word),
    { requires tr mem := True;
      ensures tr' mem' :=
        tr = tr' /\
        mem = mem' /\
        let '\<w, x, y, z\> := quarter a b c d in
        (a' = w /\ b' = x /\ c' = y /\ d' = z)}.

  Derive quarter_body SuchThat
         (defn! "quarter" ("a", "b", "c", "d") ~> "a", "b", "c", "d" { quarter_body },
          implements (quarter) using [])
         As quarter_body_correct.
  Proof.
    compile.
  Qed.

  Lemma compile_quarter : forall {tr mem locals functions} a b c d,
      let v := quarter a b c d in

      forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
             a_var b_var c_var d_var,

        spec_of_quarter functions ->
        
        map.get locals a_var = Some a ->
        map.get locals b_var = Some b ->
        map.get locals c_var = Some c ->
        map.get locals d_var = Some d ->

        (let v := v in
           let '\<w, x, y, z\> := v in
        (<{ Trace := tr;
            Memory := mem;
            Locals := map.put (map.put (map.put (map.put locals a_var w) b_var x) c_var y) d_var z;
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        
        cmd.seq (cmd.call [a_var; b_var; c_var; d_var] "quarter" [expr.var a_var; expr.var b_var; expr.var c_var; expr.var d_var])
                k_impl
                
        <{ pred (nlet_eq [a_var; b_var; c_var; d_var] v k) }>.
  Proof.
    repeat straightline.
    repeat (eexists; split; eauto).
    handle_call; eauto.
  Qed.

  Lemma length_w32s_of_bytes l
    : length (w32s_of_bytes l) = ((length l + 3) / 4)%nat.
  Proof.
    unfold w32s_of_bytes.
    rewrite !map_length.
    rewrite length_chunk; eauto.
  Qed.

  Instance spec_of_chacha20_block : spec_of "chacha20_block" :=
    fnspec! "chacha20_block" (key_ptr nonce_ptr st_ptr : word) /
          (key nonce st : ListArray.t byte) R,
    { requires tr mem :=
        (Datatypes.length st = 64%nat) /\
          (Datatypes.length key = 32%nat) /\
          (*TODO: check nonce length*)
          (Datatypes.length nonce = 16%nat) /\
          (array ptsto (word.of_Z 1) key_ptr key
             ⋆ array ptsto (word.of_Z 1) nonce_ptr nonce
             ⋆ array ptsto (word.of_Z 1) st_ptr st ⋆ R) mem;
      ensures tr' mem' :=
        tr = tr' /\
          (array ptsto (word.of_Z 1) key_ptr key
             ⋆ array ptsto (word.of_Z 1) nonce_ptr nonce
             ⋆ array ptsto (word.of_Z 1) st_ptr (chacha20_block key nonce st) ⋆ R) mem' }.
  
  Import Loops.
  Existing Instance spec_of_unsizedlist_memcpy.

  Lemma replace_nth_nil A n (c :A)
    : replace_nth n [] c = [].
  Proof.
    reflexivity.
  Qed. 

  Lemma array_put_helper (a : list word) b c
    : array_put a b c = ListArray.put a b c.
  Proof.
    cbv [array_put ListArray.put cast id Convertible_self upd upds].
    cbn [Datatypes.length].
    destruct (lt_dec b ( Datatypes.length a)).
    {
      rewrite replace_nth_eqn by auto.
      f_equal.
      replace (Datatypes.length a - b)%nat
        with (S (Datatypes.length a - S b)) by lia.
      cbn [List.firstn].
      rewrite ListUtil.List.firstn_nil.
      reflexivity.
    }
    {
      replace (Datatypes.length a - b)%nat with 0%nat by lia.
      cbn [List.firstn Datatypes.app].
      rewrite skipn_all by lia.
      rewrite firstn_all2 by lia.
      replace a with (a++[]) at 2 by (rewrite List.app_nil_r; auto).
      rewrite replace_nth_app2 by lia.
      rewrite replace_nth_nil.
      reflexivity.
    }
  Qed.

  Lemma scalar32_helper
    : scalar32 = (scalar (word:=word)).
  Proof.
    unfold scalar32, scalar, truncated_word, truncated_scalar.
    change  (Memory.bytes_per access_size.word) with 4%nat.
    change  (Memory.bytes_per access_size.four) with 4%nat.
    reflexivity.
  Qed.

  Lemma buffer_at_full_array T c sz pT b a
    : c = Z.of_nat (Datatypes.length b) ->
    Lift1Prop.iff1 (buffer_at T sz pT c b a)
      (array pT sz a b).
  Proof.
    unfold buffer_at.
    intro; subst.
    split; intro; sepsimpl.
    {
      destruct x0.
      {
        cbn [array] in H0; sepsimpl.
        destruct H0; auto.
      }
      {
        exfalso; clear H0.
        cbn [Datatypes.length] in *.
        lia.
      }
    }
    {
      exists [].
      cbn [Datatypes.length].
      sepsimpl; try lia.
      cbn [array].
      exists map.empty, x; intuition (cbv [emp]; auto).
      eapply map.split_empty_l; auto.
    }
  Qed.

  Lemma bytes_of_w32s_iso nonce
    :  (Datatypes.length nonce mod 4)%nat = 0%nat ->
       nonce = bytes_of_w32s (w32s_of_bytes nonce).
  Proof.
    intro H.
    unfold w32s_of_bytes.
    unfold bytes_of_w32s.
    rewrite !List.map_map.
    erewrite map_ext_Forall; cycle 1.
    {
      eapply Forall_impl; [| eapply Forall_chunk_length_le; try lia].
      cbn beta.
      intros a H'.
      rewrite word.unsigned_of_Z.
      apply Z.mod_small.
      pose proof (le_combine_bound a).
      assert (8 * Z.of_nat (Datatypes.length a) <= 32) by lia.
      pose proof (Z.pow_le_mono_r 2 _ _ ltac:(lia) H1).
      lia.
    }
    rewrite flat_map_le_split_combine_chunk; auto; try lia.
  Qed.

  (*TODO: why is this necessary? seems like a bug*)
  Local Hint Extern 0 (spec_of "unsizedlist_memcpy") =>
          Tactics.rapply spec_of_unsizedlist_memcpy : typeclass_instances.
  
  Derive chacha20_block_body SuchThat
         (defn! "chacha20_block" ("key", "nonce", "st") { chacha20_block_body },
          implements (chacha20_block) using [ "quarter"  ; "unsizedlist_memcpy" ])
         As chacha20_block_body_correct.
  Proof.
    compile_setup.
    cbn [chacha20_block_init].
    repeat compile_step.

    simple eapply compile_nlet_as_nlet_eq.
    simple eapply compile_buf_backed_by; repeat compile_step.
    {
      instantiate (1 := (Naive.wrap 4)).
      simpl; lia.
    }

    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_push_word32; repeat compile_step.
    { simpl; lia. }
    { simpl; compile_step. }

    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_push_word32; repeat compile_step.
    { simpl; lia. }
    { simpl;compile_step. }

    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_push_word32; repeat compile_step.
    { simpl; lia. }
    { simpl;compile_step. }

    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_push_word32; repeat compile_step.
    { simpl; lia. }
    { simpl;compile_step. }

    simple eapply compile_nlet_as_nlet_eq.
    simple eapply compile_w32s_of_bytes; [repeat compile_step..|].

    compile_step.
    compile_step; [repeat compile_step ..|].

    Optimize Proof.

    eapply expr_compile_Z_literal with (z:= 4).
    {
      unfold copy.
      let x := eval compute in (Datatypes.length v3) in
        change (Datatypes.length v3) with x.
      unfold v4.
      rewrite length_w32s_of_bytes.
      rewrite H5.
      simpl.
      lia.
    }
    compile_step.
    simple eapply compile_word_memcpy.
    shelve (*TODO: what is this?*).
    repeat compile_step.
    {
      pose proof H6 as H6'.
      revert H6'; clear H6.
      unfold copy.
      subst v4.
      rewrite length_w32s_of_bytes.
      rewrite H5.
      rewrite !word.unsigned_of_Z.
      rewrite !word.wrap_small by lia.
      change 4 with (Z.of_nat 4%nat).
      rewrite <- Nat2Z.inj_mul.
      rewrite Nat2Z.inj_iff.
      intro H6; cbn in H6.
      
      unfold buf_push.
      rewrite !app_length.
      unfold buf_backed_by.
      cbn [length Nat.add].
      replace (Datatypes.length v3) with 4%nat in H2 by reflexivity.
      seprewrite_in words_of_bytes H2.
      {
        rewrite H6; reflexivity.
      }
      {
        revert H2.
        unfold listarray_value.
        cbn [ai_width ai_size Arrays._access_info ai_repr ai_type].
        rewrite !bytes_per_width_bytes_per_word.
        change (Memory.bytes_per_word 32) with 4.
        rewrite !word.unsigned_of_Z.
        rewrite !word.wrap_small by lia.
        change (Z.of_nat 4) with 4.
        intro.
        ecancel_assumption.
      }
    }
    {
      assumption.
    }
    {
      subst v4.
      rewrite length_w32s_of_bytes.
      rewrite H5.
      cbn -[word.unsigned].
      change (Z.of_nat 8) with 8.
      replace 8 with (word.wrap 8) by (rewrite word.wrap_small; lia).
      rewrite <- word.unsigned_of_Z.
      reflexivity.
    }
    {
      change (Memory.bytes_per access_size.word) with 4%nat.

      revert H6.
      unfold copy.
      subst v4.
      rewrite length_w32s_of_bytes.
      rewrite H5.
      rewrite !word.unsigned_of_Z.
      rewrite !word.wrap_small by lia.
      change 4 with (Z.of_nat 4%nat).
      rewrite <- Nat2Z.inj_mul.
      rewrite Nat2Z.inj_iff.
      intro H6; cbn in H6.
      
      rewrite bs2ws_length; try lia.
      
      {
        rewrite div_Zdiv by lia.
        rewrite H6.
        reflexivity.
      }
      {
        rewrite H6.
        reflexivity.
      }
    }
    

    Optimize Proof.
    
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    subst FillPred. (*TODO: make a part of the last compile_step*)
    compile_step.
    split.
    {
      revert H7.
      unfold listarray_value.
      cbn [ai_width ai_size
             Arrays._access_info ai_repr ai_type].
      change (Z.of_nat (Memory.bytes_per access_size.word)) with 4.
      replace scalar32 with (scalar (word:=word)) by apply  scalar32_helper.
      cbv [v3 v2 v1 v0 v buf_push buf_backed_by].
      cbn [Datatypes.app Datatypes.length].
      rewrite !word.unsigned_of_Z.
      rewrite !word.wrap_small by lia.
      change (Z.of_nat 4) with 4.
      unfold copy.
      intro.
      ecancel_assumption.
    }
    repeat compile_step.

    repeat (rewrite map.remove_put_same || 
              rewrite map.remove_put_diff by (unfold gs; compile_step));
      rewrite map.remove_empty.
    
    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_bytes_of_w32s; repeat compile_step.

    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_w32s_of_bytes; [repeat compile_step .. | ].
    compile_step.
    compile_step.
    compile_step.
    compile_step.

    

    Optimize Proof.
    {
      unfold v5, buf_append, copy.
      rewrite app_length.
      unfold v3,v2,v1,v0, buf_push, v, buf_backed_by, v4.
      rewrite length_w32s_of_bytes.
      rewrite H5.
      cbv [length Datatypes.app Nat.add Nat.div Nat.divmod fst Z.of_nat Pos.of_succ_nat Pos.succ].
      compile_step.
    }
    {
     unfold v5, buf_append, copy.
      rewrite app_length.
      unfold v3,v2,v1,v0, buf_push, v, buf_backed_by, v4, v8.
      rewrite !length_w32s_of_bytes.
      rewrite H5, H4.
      cbv; congruence.
    }
    compile_step.

    rewrite word.unsigned_of_Z in H7.
    rewrite word.wrap_small in H7 by lia.
    change 4 with (Z.of_nat 4) in H7.
    rewrite <- Nat2Z.inj_mul in H7.
    apply Nat2Z.inj in H7.

    simple eapply compile_word_memcpy.
    shelve (*TODO: what is this?*).
    compile_step.
    {
      pose proof H2 as H2'; clear H2.
        revert H2'.
        unfold listarray_value.
        cbn [ai_width ai_size Arrays._access_info ai_repr ai_type].
        rewrite !bytes_per_width_bytes_per_word.
        change (Memory.bytes_per_word 32) with 4.
        rewrite !word.unsigned_of_Z.
        rewrite !word.wrap_small by lia.
        change (Z.of_nat 4) with 4.

        
        unfold v5, buf_append, copy.
        rewrite !app_length.
        unfold v3,v2,v1,v0, buf_push, v, buf_backed_by, v4, v8.
        rewrite !length_w32s_of_bytes.
        rewrite H5.
        cbv [length Datatypes.app].
        replace scalar32 with (scalar (word:=word)) by apply  scalar32_helper.
        intro H2.
        seprewrite_in words_of_bytes H2.
        {
          rewrite H7.
          change (Memory.bytes_per access_size.word) with 4%nat.
          rewrite Nat.mul_comm.
          apply Nat.mod_mul; lia.
        }
        change ((Z.of_nat (Memory.bytes_per access_size.word))) with 4 in H2.
        ecancel_assumption.
    }
    assumption.
    {
      instantiate (1 := (word.of_Z _)).
      unfold v8.
      rewrite length_w32s_of_bytes.
      rewrite H4.
      rewrite word.unsigned_of_Z.
      rewrite word.wrap_small; auto.
      cbv; intuition congruence.
    }
    

    Optimize Proof.
    {
      let x := eval compute in (Z.of_nat ((16 + 3) / 4)) in
        change (Z.of_nat ((16 + 3) / 4)) with x.
      rewrite word.unsigned_of_Z.
      rewrite word.wrap_small; [|lia].
      rewrite bs2ws_length; [| intro H'; now inversion H'|];
        rewrite H7;
        change (Memory.bytes_per access_size.word) with 4%nat;
        unfold v8, copy;
        rewrite length_w32s_of_bytes;
        rewrite H4;
        reflexivity.
    }
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    unfold FillPred.
    compile_step.
    {
      
      replace scalar32 with (scalar (word:=word)) by apply  scalar32_helper.
      unfold v5, copy, v4, v3, v2, v1, v0, v, buf_backed_by, buf_append, buf_push in *.
      rewrite !app_length in *.
      rewrite ?length_w32s_of_bytes in *.
      rewrite ?H5 in *.
      cbn [Datatypes.app Datatypes.length Nat.add Nat.div Nat.divmod fst] in *.
      unfold listarray_value in *.
      cbn [ai_width ai_size Arrays._access_info ai_repr ai_type] in *.
      change (Z.of_nat (Memory.bytes_per access_size.word)) with 4 in *.
      ecancel_assumption.
    }

    compile_step.
    
    repeat (rewrite map.remove_put_same || 
              rewrite map.remove_put_diff by (unfold gs; compile_step));
      rewrite map.remove_empty.
    
    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_bytes_of_w32s; repeat compile_step.
    simple eapply compile_nlet_as_nlet_eq.
    (*TODO: improperly inlines computation*)
    simple eapply compile_buf_as_array.
    repeat compile_step.
    {
      unfold v9, v5, v8, v3, v4, v2, buf_append, copy.
      rewrite !app_length.
      rewrite !length_w32s_of_bytes.
      rewrite H4, H5.
      reflexivity.
    }
    compile_step.
    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_make_stack; [repeat compile_step .. |].
    {
      instantiate (1:=scalar).
      instantiate (1:=word.of_Z 4).
      eexists; split; cycle 1.
      {
        intro a.
        eapply Util.scalar_to_bytes.
      }
      cbn.
      rewrite length_le_split.
      reflexivity.
    }
    {
      rewrite word.unsigned_of_Z.
      rewrite word.wrap_small by lia.
      reflexivity.
    }
    compile_step.
    compile_step.
    (*TODO: compile step is doing something odd here*)
    ecancel_assumption.
    repeat compile_step.
    {
      (*listZnWords?*)
      unfold v12, v13, v9, v5, v8, v3, v4, v2, buf_append, copy, buf_as_array, buf_push.
      rewrite !app_length.
      rewrite !length_w32s_of_bytes.
      rewrite H4, H5.
      reflexivity.
    }
    compile_step.
    (*TODO: is compile step doing the wrong thing?*)
    simple eapply compile_word_memcpy.
    shelve (*TODO: what's this?*).
    

    Optimize Proof.
    compile_step.
    {
        revert H2.
        unfold listarray_value.
        cbn [ai_width ai_size Arrays._access_info ai_repr ai_type].
        rewrite !bytes_per_width_bytes_per_word.
        change (Memory.bytes_per_word 32) with 4.
        rewrite !word.unsigned_of_Z.
        rewrite ?word.wrap_small by lia.
        intro.
      
      replace scalar32 with (scalar (word:=word)) in * by apply scalar32_helper.
      fold v13.
      seprewrite_in words_of_bytes H2.
      {
        revert H8.
        cbv [v12 v9 buf_append copy buf_as_array v5 v8 v3 v4 v2 v1 v0 v buf_push buf_backed_by].
        rewrite !app_length.
        rewrite !length_w32s_of_bytes.
        rewrite H5, H4.
        cbn [length Datatypes.app Nat.add Nat.div Nat.divmod fst Z.of_nat Pos.of_succ_nat Pos.succ].
        rewrite !word.unsigned_of_Z.
        rewrite ?word.wrap_small; auto; try lia.
        intro.
        assert (Datatypes.length uninit1 = 64%nat) by lia.
        rewrite H9.
        reflexivity.
      }
      change ((Z.of_nat (Memory.bytes_per access_size.word))) with 4 in *.
      ecancel_assumption.
    }
    assumption.
    {
      cbv [v12 v9 buf_append copy buf_as_array v5 v8 v3 v4 v2 v1 v0 v buf_push buf_backed_by].
      rewrite !app_length.
      rewrite !length_w32s_of_bytes.
      rewrite H5, H4.
      cbv [length Datatypes.app Nat.add Nat.div Nat.divmod fst Z.of_nat Pos.of_succ_nat Pos.succ].
      rewrite !word.unsigned_of_Z.
      rewrite ?word.wrap_small; auto.
      lia.
    }
    {
      rewrite !word.unsigned_of_Z.
      rewrite ?word.wrap_small by lia.
      rewrite bs2ws_length.
      rewrite Nat2Z.inj_div.
      rewrite H8.
      cbv [v12 v9 buf_append copy buf_as_array v5 v8 v3 v4 v2 v1 v0 v buf_push buf_backed_by].
      rewrite !app_length.
      rewrite !length_w32s_of_bytes.
      rewrite H5, H4.
      cbv [length Datatypes.app Nat.add Nat.div Nat.divmod fst Z.of_nat Pos.of_succ_nat Pos.succ].
      rewrite !word.unsigned_of_Z.
      rewrite ?word.wrap_small; auto.
      lia.
      cbv; lia.
      {
        revert H8.
        cbv [v12 v9 buf_append copy buf_as_array v5 v8 v3 v4 v2 v1 v0 v buf_push buf_backed_by].
        rewrite !app_length.
        rewrite !length_w32s_of_bytes.
        rewrite H5, H4.
        cbn [length Datatypes.app Nat.add Nat.div Nat.divmod fst Z.of_nat Pos.of_succ_nat Pos.succ].
        rewrite !word.unsigned_of_Z.
        rewrite ?word.wrap_small; auto; try lia.
        intro.
        assert (Datatypes.length uninit1 = 64%nat) by lia.
        rewrite H9.
        reflexivity.
      }
    }
    now compile_step.
    now compile_step.
    compile_step.
    compile_step.
    clear FillPred; subst FillPred0.
    compile_step.
    compile_step.
    {
      replace scalar32 with (scalar (word:=word)) in * by apply scalar32_helper.
      revert H9.
      
      unfold listarray_value.
      cbn [ai_width ai_size Arrays._access_info ai_repr ai_type].
      rewrite !bytes_per_width_bytes_per_word.
      change (Memory.bytes_per_word 32) with 4.
      rewrite !word.unsigned_of_Z.
      rewrite !word.wrap_small by lia.
      change (Z.of_nat 4) with 4.
      fold v13 (*TODO:why?*).
      (*TODO: why v12 vs v15?*)
      unfold copy.
      intro.
      ecancel_assumption.
    }

    compile_step.

    

    Optimize Proof.

    repeat (rewrite map.remove_put_same || 
              rewrite map.remove_put_diff by (unfold gs; compile_step));
      rewrite map.remove_empty.
    
    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_as_array.
    ecancel_assumption.
    {
      cbv [v14 v13 v12 v9 buf_append copy buf_as_array v5 v8 v3 v4 v2 v1 v0 v buf_push buf_make buf_backed_by].
      rewrite !app_length.
      rewrite !length_w32s_of_bytes.
      rewrite H5, H4.
      cbv [length Datatypes.app Nat.add Nat.div Nat.divmod fst Z.of_nat Pos.of_succ_nat Pos.succ].
      reflexivity.
    }
    compile_step.
    
    repeat lazymatch goal with
    | |- context [array_get ?a ?b (word.of_Z 0)] =>
        replace (array_get a b (word.of_Z 0)) with
        (ListArray.get a b) by reflexivity
           end.
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get.
    {
      unfold listarray_value.
      cbn [ai_width ai_size Arrays._access_info ai_repr ai_type].
      rewrite !bytes_per_width_bytes_per_word.
      change (Memory.bytes_per_word 32) with 4.
      ecancel_assumption.
    }

    now compile_step.
    {
      change (cast 0%nat) with 0%nat.
      now compile_step.
    }
    {
      change (cast 0%nat) with 0%nat.
      cbv; reflexivity.
    }

    compile_step.
    repeat (eapply compile_nlet_as_nlet_eq;
    eapply compile_word_unsizedlistarray_get;
      [ unfold listarray_value;
        cbn [ai_width ai_size Arrays._access_info ai_repr ai_type];
        rewrite !bytes_per_width_bytes_per_word;
        change (Memory.bytes_per_word 32) with 4;
        now ecancel_assumption
      | now compile_step
      | change (cast ?a) with a; now compile_step
      | change (cast ?a) with a;
        cbv [v16 v14 v13 v12 v9 buf_append copy buf_as_array
               v5 v8 v3 v4 v2 v1 v0 v buf_push buf_make buf_backed_by];
        rewrite !app_length;
        rewrite !length_w32s_of_bytes;
        rewrite H5, H4;
        cbv [length Datatypes.app Nat.add Nat.div Nat.divmod fst Z.of_nat Pos.of_succ_nat Pos.succ];
        reflexivity
      |]).
    
    compile_step.

    rewrite  Nat_iter_as_nd_ranged_for_all with (i:=0).
    change (0 + Z.of_nat 10) with 10%Z.

    Import LoopCompiler.
    compile_step.
    compile_step.
    compile_step; [repeat compile_step; lia .. | |].
    all: repeat compile_step.
    1: remember acc as acc';
      destruct acc' as [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]]];
    cbv [P2.car P2.cdr] in *.
    2:remember v19 as v19';
    destruct v19' as [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]]];
    cbv [P2.car P2.cdr] in *.
      
    Optimize Proof.
    Optimize Heap.
    {
      (* TODO: why doesn't simple eapply work? *)
      do 7 (change (lp from' (ExitToken.new, ?y)) with ((fun v => lp from' (ExitToken.new, v)) y);
        simple eapply compile_nlet_as_nlet_eq;
        change (lp from' (ExitToken.new, ?y)) with ((fun v => lp from' (ExitToken.new, v)) y);
        simple eapply compile_quarter; [ now repeat compile_step ..| repeat compile_step]).

      change (lp from' (ExitToken.new, ?y)) with ((fun v => lp from' (ExitToken.new, v)) y);
        simple eapply compile_nlet_as_nlet_eq;
        change (lp from' (ExitToken.new, ?y)) with ((fun v => lp from' (ExitToken.new, v)) y).
       simple eapply compile_quarter; [ now repeat compile_step ..|].
      
      Optimize Proof.
      Optimize Heap.

      compile_step.
      
      compile_step.
      2: exact [].
      {
        (*TODO: why are quarter calls getting subst'ed?*)
        cbv [P2.car P2.cdr fst snd].
        cbv [map.remove_many fold_left].
        repeat (set (quarter _ _ _ _)).
        Ltac dedup s :=
          repeat rewrite map.put_put_diff with (k1:=s) by congruence;
          rewrite ?map.put_put_same with (k:=s).
        dedup "qv0".
        dedup "qv1".
        dedup "qv2".
        dedup "qv3".
        dedup "qv4".
        dedup "qv5".
        dedup "qv6".
        dedup "qv7".
        dedup "qv8".
        dedup "qv9".
        dedup "qv10".
        dedup "qv11".
        dedup "qv12".
        dedup "qv13".
        dedup "qv14".
        dedup "qv15".
        
        cbv [gs].
        dedup  "_gs_from0".
        dedup  "_gs_to0".
        reflexivity.
        (*TODO: why is all this work necessary for passable proof performance?*)
      }
    }

    repeat lazymatch goal with
    | |- context [array_put ?a ?b ?c] =>
        replace (array_put a b c) with
        (ListArray.put a b c) by (symmetry;apply array_put_helper);
        simple eapply compile_nlet_as_nlet_eq;        
        eapply compile_word_unsizedlistarray_put;
        [  change (cast ?a) with a; now compile_step .. 
        | lazymatch goal with
            |- _ < Z.of_nat (Datatypes.length ?v) =>
              unfold v;
              repeat match goal with
                  |- context [ListArray.put ?v _ _] =>
                    rewrite ListArray.put_length; unfold v
                end
          end;
          change (cast ?a) with a;
          cbv [v16 v14 v13 v12 v9 buf_append copy buf_as_array
                 v5 v8 v3 v4 v2 v1 v0 v buf_push buf_make buf_backed_by];
          rewrite !app_length;
          rewrite !length_w32s_of_bytes;
          rewrite H5, H4;
          cbv [length Datatypes.app Nat.add Nat.div Nat.divmod fst Z.of_nat Pos.of_succ_nat Pos.succ];
          reflexivity
        | compile_step ]
    end.

    Optimize Proof.
    Optimize Heap.

    
    eapply compile_nlet_as_nlet_eq.
      lazymatch goal with
  | [ |- WeakestPrecondition.cmd _ _ _ _ ?locals (_ (nlet_eq [?var] ?v _)) ] =>
      let idx_var_str := gensym locals constr:((var++"_idx")%string) in
      let to_var_str := gensym locals constr:((var++"_to")%string) in
      simple eapply compile_broadcast_expr
        with (idx_var:=idx_var_str) (to_var:=to_var_str)
      end.
      now eapply word_ac_ok.
      {
        compile_step.
        eapply expr_compile_var.
        reflexivity.
      }
      {
        cbv [predT sz_word word_ac szT].
        
        revert H25.
        unfold listarray_value.
        cbn [ai_width ai_size Arrays._access_info ai_repr ai_type].
        rewrite !bytes_per_width_bytes_per_word.
        change (Memory.bytes_per_word 32) with 4.
        change (Z.of_nat 4) with 4.        
        replace scalar32 with (scalar (word:=word)) by apply scalar32_helper.
        intro.
        ecancel_assumption.
      }
      4:cbv; congruence.
      4:reflexivity.
      4:reflexivity.
      4:{
        eapply broadcast_word_add.
        {
          cbn.
          unfold copy.
          cbn.
          rewrite !replace_nth_length.          
          reflexivity.
        }
        {
          simple eapply broadcast_id.
          apply word_ac_ok.
          compile_step.
          cbv; congruence.
        }
        {
          simple eapply broadcast_var.
          apply word_ac_ok.
          {
            (*TODO: reorder lemma args*)
            unfold listarray_value.
            cbn [ai_width ai_size Arrays._access_info ai_repr ai_type].
            cbv [predT sz_word szT word_ac].
            rewrite !bytes_per_width_bytes_per_word.
            change (Memory.bytes_per_word 32) with 4.
            ecancel.
          }
          all: repeat compile_step.
          cbv; congruence.
          {
            cbn.
            unfold copy.
            cbn.
            rewrite !replace_nth_length.
            lia.
          }
        }
      }
      {
        cbv [v12 v9 buf_append copy buf_as_array v5 v8 v3 v4 v2 v1 v0 v buf_push buf_backed_by].
        rewrite !app_length.
        rewrite !length_w32s_of_bytes.
        rewrite H5, H4.
        cbn [length Datatypes.app Nat.add Nat.div Nat.divmod fst Z.of_nat Pos.of_succ_nat Pos.succ].
        reflexivity.
      }
      {
        rewrite map_length.
        rewrite combine_length.
        subst v35.
        repeat match goal with
                 |- context [ListArray.put ?v _ _] =>
                   rewrite ListArray.put_length; unfold v
               end.
        cbv [ v14 v13 v12 v9 buf_append copy buf_as_array v5 v8 v3 v4 v2 v1 v0 v buf_push buf_backed_by buf_make].          rewrite !app_length.
        rewrite !length_w32s_of_bytes.
        rewrite !H5, !H4.
        cbn [length Datatypes.app Nat.add Nat.div Nat.divmod fst Z.of_nat Pos.of_succ_nat Pos.succ].
        reflexivity.
      }
      lia.
      compile_step.
      eapply compile_nlet_as_nlet_eq.
      eapply compile_bytes_of_w32s.
      now compile_step.
      now compile_step.
      compile_step.
      
      compile_step.
      
      Optimize Proof.
      Optimize Heap.

      2: exact [].
      sepsimpl.
      eexists.
      seprewrite buffer_at_full_array; cycle 1.
      {
        refine (subrelation_refl Lift1Prop.impl1 _ _ _ mem5 H27); clear H27.
        cancel.
        ecancel_step_by_implication.
        cbv [seps].
        unfold v7.
        replace (bytes_of_w32s (w32s_of_bytes key)) with key by
            (apply bytes_of_w32s_iso; rewrite H5; reflexivity).
        unfold v11.
        replace (bytes_of_w32s (w32s_of_bytes nonce)) with nonce by
          (apply bytes_of_w32s_iso; rewrite H4; reflexivity).
        intros m'' H''.
        eexists; intuition subst.
        ecancel_assumption.
      }
      {
        rewrite !ListArray.put_length.
        cbv [buf_append copy buf_as_array buf_push buf_backed_by].
        rewrite !app_length.
        rewrite !length_w32s_of_bytes.
        rewrite H5, H4.
        reflexivity.
      }
      Unshelve.
      (*TODO: what are these?*)
      exact 0%nat.
      exact 0%nat.
      exact 0%nat.
      shelve.
      exact wordok.
      exact mapok.
      exact localsok.
      exact envok.
      exact ext_spec_ok.
  (*
    TODO: Qed takes unreasonably long (unconfirmed whether it finishes)
  Qed.*)
  Abort.
  
    
End Bedrock2.
