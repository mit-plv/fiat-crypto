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
         forall m,
           let '\<w, x, y, z\> := v in
        (<{ Trace := tr;
            Memory := m;
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
             ⋆ array ptsto (word.of_Z 1) st_ptr (chacha20_block key nonce st) ⋆ R) mem }.
  
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
  
  Derive chacha20_block_body SuchThat
         (defn! "chacha20_block" ("key", "nonce", "st") ~> "st" { chacha20_block_body },
          implements (chacha20_block) using [ "quarter" (* ; "unsizedlist_memcpy"*)])
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
      rewrite H4.
      simpl.
      lia.
    }
    compile_step.
    simple eapply compile_word_memcpy.
    shelve (*TODO: what is this?*).
    repeat compile_step.
    {
      pose proof H5 as H5'.
      revert H5'; clear H5.
      unfold copy.
      subst v4.
      rewrite length_w32s_of_bytes.
      rewrite H4.
      rewrite !word.unsigned_of_Z.
      rewrite !word.wrap_small by lia.
      change 4 with (Z.of_nat 4%nat).
      rewrite <- Nat2Z.inj_mul.
      rewrite Nat2Z.inj_iff.
      intro H5; cbn in H5.
      
      unfold buf_push.
      rewrite !app_length.
      unfold buf_backed_by.
      cbn [length Nat.add].
      replace (Datatypes.length v3) with 4%nat in H1 by reflexivity.
      seprewrite_in words_of_bytes H1.
      {
        rewrite H5; reflexivity.
      }
      {
        revert H1.
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
      admit (*TODO: spec_of_unsizedlist_memcpy. *).
    }
    {
      subst v4.
      rewrite length_w32s_of_bytes.
      rewrite H4.
      cbn -[word.unsigned].
      change (Z.of_nat 8) with 8.
      replace 8 with (word.wrap 8) by (rewrite word.wrap_small; lia).
      rewrite <- word.unsigned_of_Z.
      reflexivity.
    }
    {
      change (Memory.bytes_per access_size.word) with 4%nat.

      revert H5.
      unfold copy.
      subst v4.
      rewrite length_w32s_of_bytes.
      rewrite H4.
      rewrite !word.unsigned_of_Z.
      rewrite !word.wrap_small by lia.
      change 4 with (Z.of_nat 4%nat).
      rewrite <- Nat2Z.inj_mul.
      rewrite Nat2Z.inj_iff.
      intro H5; cbn in H5.
      
      rewrite bs2ws_length; try lia.
      
      {
        rewrite div_Zdiv by lia.
        rewrite H5.
        reflexivity.
      }
      {
        rewrite H5.
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
      unfold listarray_value in H5.
      cbn [ai_width ai_size
             Arrays._access_info ai_repr ai_type]
            in H5.
      change (Z.of_nat (Memory.bytes_per access_size.word)) with 4 in H5.
      admit.
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
      rewrite H4.
      cbv [length Datatypes.app Nat.add Nat.div Nat.divmod fst Z.of_nat Pos.of_succ_nat Pos.succ].
      compile_step.
    }
    {
     unfold v5, buf_append, copy.
      rewrite app_length.
      unfold v3,v2,v1,v0, buf_push, v, buf_backed_by, v4, v8.
      rewrite !length_w32s_of_bytes.
      rewrite H4, H3.
      cbv; congruence.
    }
    compile_step.

    rewrite word.unsigned_of_Z in H6.
    rewrite word.wrap_small in H6 by lia.
    change 4 with (Z.of_nat 4) in H6.
    rewrite <- Nat2Z.inj_mul in H6.
    apply Nat2Z.inj in H6.

    simple eapply compile_word_memcpy.
    shelve (*TODO: what is this?*).
    compile_step.
    {
      pose proof H1 as H1'; clear H1.
        revert H1'.
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
        rewrite H4.
        cbv [length Datatypes.app].
        replace scalar32 with (scalar (word:=word)) by admit.
        intro H1.
        seprewrite_in words_of_bytes H1.
        {
          rewrite H6.
          change (Memory.bytes_per access_size.word) with 4%nat.
          rewrite Nat.mul_comm.
          apply Nat.mod_mul; lia.
        }
        change ((Z.of_nat (Memory.bytes_per access_size.word))) with 4 in H1.
        ecancel_assumption.
    }
    admit (*TODO*).
    {
      instantiate (1 := (word.of_Z _)).
      unfold v8.
      rewrite length_w32s_of_bytes.
      rewrite H3.
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
        rewrite H6;
        change (Memory.bytes_per access_size.word) with 4%nat;
        unfold v8, copy;
        rewrite length_w32s_of_bytes;
        rewrite H3;
        reflexivity.
    }
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    unfold FillPred.
    compile_step.
    {
      
      replace scalar32 with (scalar (word:=word)) by admit.
      unfold v5, copy, v4, v3, v2, v1, v0, v, buf_backed_by, buf_append, buf_push in *.
      rewrite !app_length in *.
      rewrite ?length_w32s_of_bytes in *.
      rewrite ?H4 in *.
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
      rewrite H3, H4.
      reflexivity.
    }
    compile_step.
    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_make_stack; [repeat compile_step .. |].
    {
      instantiate (1:=scalar).
      instantiate (1:=word.of_Z 4).
      admit (*TODO: replace w/ Allocable,
              when either Allocable has been generalized to variable len
             or this has been specialized *).
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
      rewrite H3, H4.
      reflexivity.
    }
    compile_step.
    (*TODO: is compile step doing the wrong thing?*)
    simple eapply compile_word_memcpy.
    shelve (*TODO: what's this?*).
    

    Optimize Proof.
    compile_step.
    {
        revert H1.
        unfold listarray_value.
        cbn [ai_width ai_size Arrays._access_info ai_repr ai_type].
        rewrite !bytes_per_width_bytes_per_word.
        change (Memory.bytes_per_word 32) with 4.
        rewrite !word.unsigned_of_Z.
        rewrite ?word.wrap_small by lia.
        intro.
      
      replace scalar32 with (scalar (word:=word)) in * by admit.
      fold v13.
      seprewrite_in words_of_bytes H1.
      {
        revert H7.
        cbv [v12 v9 buf_append copy buf_as_array v5 v8 v3 v4 v2 v1 v0 v buf_push buf_backed_by].
        rewrite !app_length.
        rewrite !length_w32s_of_bytes.
        rewrite H4, H3.
        cbn [length Datatypes.app Nat.add Nat.div Nat.divmod fst Z.of_nat Pos.of_succ_nat Pos.succ].
        rewrite !word.unsigned_of_Z.
        rewrite ?word.wrap_small; auto; try lia.
        intro.
        assert (Datatypes.length uninit1 = 64%nat) by lia.
        rewrite H8.
        reflexivity.
      }
      change ((Z.of_nat (Memory.bytes_per access_size.word))) with 4 in *.
      ecancel_assumption.
    }
    admit.
    {
      cbv [v12 v9 buf_append copy buf_as_array v5 v8 v3 v4 v2 v1 v0 v buf_push buf_backed_by].
      rewrite !app_length.
      rewrite !length_w32s_of_bytes.
      rewrite H4, H3.
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
      rewrite H7.
      cbv [v12 v9 buf_append copy buf_as_array v5 v8 v3 v4 v2 v1 v0 v buf_push buf_backed_by].
      rewrite !app_length.
      rewrite !length_w32s_of_bytes.
      rewrite H4, H3.
      cbv [length Datatypes.app Nat.add Nat.div Nat.divmod fst Z.of_nat Pos.of_succ_nat Pos.succ].
      rewrite !word.unsigned_of_Z.
      rewrite ?word.wrap_small; auto.
      lia.
      cbv; lia.
      {
        revert H7.
        cbv [v12 v9 buf_append copy buf_as_array v5 v8 v3 v4 v2 v1 v0 v buf_push buf_backed_by].
        rewrite !app_length.
        rewrite !length_w32s_of_bytes.
        rewrite H4, H3.
        cbn [length Datatypes.app Nat.add Nat.div Nat.divmod fst Z.of_nat Pos.of_succ_nat Pos.succ].
        rewrite !word.unsigned_of_Z.
        rewrite ?word.wrap_small; auto; try lia.
        intro.
        assert (Datatypes.length uninit1 = 64%nat) by lia.
        rewrite H8.
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
      replace scalar32 with (scalar (word:=word)) in * by admit.
      revert H8.
      
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
      rewrite H4, H3.
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
        rewrite H4, H3;
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
      (change (lp from' (ExitToken.new, ?y)) with ((fun v => lp from' (ExitToken.new, v)) y);
        simple eapply compile_nlet_as_nlet_eq;
        change (lp from' (ExitToken.new, ?y)) with ((fun v => lp from' (ExitToken.new, v)) y);
       simple eapply compile_quarter; [ now repeat compile_step ..|]).
      
      Optimize Proof.
      Optimize Heap.

      compile_step.
      compile_step.
      3: exact [].
      2:{
        
        replace scalar32 with (scalar (word:=word)) in * by admit.
        admit (*TODO: where is the assumption about m17?*).
      }
      {
        cbv [P2.car P2.cdr fst snd].
        cbv [map.remove_many fold_left].
        admit (*TODO: looks false (locals before = locals after?*).
      }
    }
    
    repeat lazymatch goal with
    | |- context [array_put ?a ?b ?c] =>
        replace (array_put a b c) with
        (ListArray.put a b c) by (symmetry;apply array_put_helper);
        simple eapply compile_nlet_as_nlet_eq;
        eapply compile_word_unsizedlistarray_put; [admit ..| compile_step]
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
      admit.
      {
        compile_step.
        eapply expr_compile_var.
        reflexivity.
      }
      ecancel_assumption.
      admit.
      admit.
      admit.
      cbv; congruence.
      reflexivity.
      reflexivity.
      {
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
            intros m'' H''.
            ecancel_assumption.
          }
          admit(*TODO: will work once a_ptr is concrete*).
          admit(*TODO: will work once a_ptr is concrete*).
          {
            cbn.
            unfold copy.
            cbn.
            rewrite !replace_nth_length.
            lia.
          }
        }
      }
      
      compile_step.
      eapply compile_nlet_as_nlet_eq.
      eapply compile_bytes_of_w32s; [admit.. |].
      compile_step.
      eapply compile_nlet_as_nlet_eq.
      eapply compile_buf_as_array; [admit.. |].
      Optimize Proof.
      Optimize Heap.
      compile_step.      

  Abort.
    
End Bedrock2.
