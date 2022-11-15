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
          (array ptsto (word.of_Z 1) key_ptr key
             ⋆ array ptsto (word.of_Z 1) nonce_ptr nonce
             ⋆ array ptsto (word.of_Z 1) st_ptr st ⋆ R) mem;
      ensures tr' mem' :=
        tr = tr' /\
          (array ptsto (word.of_Z 1) key_ptr key
             ⋆ array ptsto (word.of_Z 1) nonce_ptr nonce
             ⋆ array ptsto (word.of_Z 1) st_ptr (chacha20_block key nonce st) ⋆ R) mem }.
  
  Derive chacha20_block_body SuchThat
         (defn! "chacha20_block" ("key", "nonce", "st") ~> "st" { chacha20_block_body },
          implements (chacha20_block) using [ "quarter" (*; "unsizedlist_memcpy"*)])
         As chacha20_block_body_correct.
  Proof.
    compile_setup.
    cbn [chacha20_block_init].
    repeat compile_step.

    simple eapply compile_nlet_as_nlet_eq.
    simple eapply compile_buf_backed_by; repeat compile_step.
    instantiate (1 := (Naive.wrap 4)).
    1:simpl; lia.

    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_push_word32; repeat compile_step.
    subst v; cbn [buf_backed_by Datatypes.length]; lia.
    subst v; unfold buf_backed_by; compile_step.

    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_push_word32; repeat compile_step.
    subst v; unfold buf_backed_by. unfold buf_push. eauto. simpl. lia.
    subst v; unfold buf_backed_by. unfold buf_push.
    {
      simpl.
      compile_step.
    }

  (*compile_step.*)

    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_push_word32; repeat compile_step.
    { subst v; unfold buf_backed_by. unfold buf_push. eauto. simpl. lia. }
    { subst v; unfold buf_backed_by. unfold buf_push. simpl; compile_step. }

    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_push_word32; repeat compile_step.
    { subst v; unfold buf_backed_by. unfold buf_push. eauto. simpl. lia. }
    { subst v; unfold buf_backed_by. unfold buf_push. simpl;compile_step. }

    simple eapply compile_nlet_as_nlet_eq.
    simple eapply compile_w32s_of_bytes; [repeat compile_step..|].

    compile_step.
    compile_step; [repeat compile_step ..|].

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
    (*TODO: need a compile words lemma comparable to compile_byte_memcpy.
      Alternately, something generic over fixed-size elements (e.g. instances of Allocable).
     *)
    simple eapply compile_word_memcpy.
    shelve (*TODO: what is this?*).
    repeat compile_step.
    {
      unfold buf_push.
      rewrite !app_length.
      unfold buf_backed_by.
      cbn [length Nat.add].
      replace (Datatypes.length v3) with 4%nat in H1 by reflexivity.
      seprewrite_in words_of_bytes H1.
      {
        admit.
      }
      {
        revert H1.
        unfold listarray_value.
        cbn [ai_width ai_size Arrays._access_info ai_repr ai_type].
        rewrite !bytes_per_width_bytes_per_word.
        change (Memory.bytes_per_word 32) with 4.
        intro.
        ecancel_assumption.
      }
    }
    admit.
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

      revert H3.
      unfold copy.
      subst v4.
      rewrite length_w32s_of_bytes.
      rewrite H4.
      rewrite !word.unsigned_of_Z.
      rewrite !word.wrap_small by lia.
      change 4 with (Z.of_nat 4%nat).
      rewrite <- Nat2Z.inj_mul.
      rewrite Nat2Z.inj_iff.
      intro H3; cbn in H3.
      
      rewrite bs2ws_length; try lia.
      
      {
        rewrite div_Zdiv by lia.
        rewrite H3.
        reflexivity.
      }
      {
        rewrite H3.
        reflexivity.
      }
    }
    compile_step.
    compile_step.
    compile_step.
    eapply compile_skip_marker.
    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_bytes_of_w32s; repeat compile_step.
    {
      unfold listarray_value in H5.
      cbn [ai_width ai_size
             Arrays._access_info ai_repr ai_type]
            in H5.
      change (Z.of_nat (Memory.bytes_per access_size.word)) with 4 in H5.
      ecancel_assumption.
    }
    compile_step.
    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_w32s_of_bytes; repeat compile_step.
    admit.
    admit.
    admit.
    eapply compile_skip_marker.
    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_bytes_of_w32s; repeat compile_step.
    admit.
    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_as_array; repeat compile_step.
    admit.
    admit.
    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_make_stack; repeat compile_step; [shelve ..|].
    eapply compile_buf_as_array; [shelve ..|].
    eapply compile_skip_marker.
    
    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_as_array; [shelve ..|].

    repeat lazymatch goal with
    | |- context [array_get ?a ?b (word.of_Z 0)] =>
        replace (array_get a b (word.of_Z 0)) with
        (ListArray.get a b) by admit
           end.
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get; [shelve .. |].
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get; [shelve .. |].
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get; [shelve .. |].
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get; [shelve .. |].
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get; [shelve .. |].
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get; [shelve .. |].
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get; [shelve .. |].
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get; [shelve .. |].
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get; [shelve .. |].
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get; [shelve .. |].
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get; [shelve .. |].
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get; [shelve .. |].
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get; [shelve .. |].
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get; [shelve .. |].
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get; [shelve .. |].
    eapply compile_nlet_as_nlet_eq.
    eapply compile_word_unsizedlistarray_get; [shelve .. |].
    compile_step.

    rewrite  Nat_iter_as_nd_ranged_for_all with (i:=0).
    change (0 + Z.of_nat 10) with 10%Z.
    
    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_nd_ranged_for_all_fresh.
    shelve.
    shelve.
    shelve.
    shelve.
    shelve.
    shelve.

    {
      compile_step.
      simple eapply compile_nlet_as_nlet_eq.
      simple eapply compile_quarter; [ compile_step | shelve .. | compile_step].
      simple eapply compile_nlet_as_nlet_eq.
      simple eapply compile_quarter; [ compile_step | shelve .. | compile_step].
      simple eapply compile_nlet_as_nlet_eq.
      simple eapply compile_quarter; [ compile_step | shelve .. | compile_step].
      simple eapply compile_nlet_as_nlet_eq.
      simple eapply compile_quarter; [ compile_step | shelve .. | compile_step].
      simple eapply compile_nlet_as_nlet_eq.
      simple eapply compile_quarter; [ compile_step | shelve .. | compile_step].
      simple eapply compile_nlet_as_nlet_eq.
      simple eapply compile_quarter; [ compile_step | shelve .. | compile_step].
      simple eapply compile_nlet_as_nlet_eq.
      simple eapply compile_quarter; [ compile_step | shelve .. | compile_step].
      simple eapply compile_nlet_as_nlet_eq.
      simple eapply compile_quarter; [ compile_step | shelve .. | compile_step].
      admit.
    }
    compile_step.
    
    repeat lazymatch goal with
    | |- context [array_put ?a ?b ?c] =>
        replace (array_put a b c) with
        (ListArray.put a b c) by admit;
        simple eapply compile_nlet_as_nlet_eq;
        eapply compile_word_unsizedlistarray_put; [shelve ..| compile_step]
           end.

    eapply compile_nlet_as_nlet_eq.
      lazymatch goal with
  | [ |- WeakestPrecondition.cmd _ _ _ _ ?locals (_ (nlet_eq [?var] ?v _)) ] =>
      let idx_var_str := gensym locals constr:((var++"_idx")%string) in
      let to_var_str := gensym locals constr:((var++"_to")%string) in
      simple eapply compile_broadcast_expr
        with (idx_var:=idx_var_str) (to_var:=to_var_str)
      end; [shelve .. | |].
      {
        eapply broadcast_word_add.
        shelve.
        eapply broadcast_id; shelve.
        admit (*TODO: need one more broadcast lemma? double check*).
      }
      compile_step.
    eapply compile_nlet_as_nlet_eq.
      eapply compile_bytes_of_w32s; [shelve.. |].
      compile_step.
      eapply compile_nlet_as_nlet_eq.
      eapply compile_buf_as_array; [shelve.. |].
      compile_step.      

  Abort.
  
End Bedrock2.
