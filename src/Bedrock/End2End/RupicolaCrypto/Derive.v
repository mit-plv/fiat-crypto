Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Lib.Loops.
Require Import Rupicola.Lib.Gensym.
Require Import coqutil.Word.LittleEndianList.
Require Import Crypto.Bedrock.End2End.RupicolaCrypto.Low.
Require Import bedrock2.BasicC32Semantics.

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


  Instance spec_of_chacha20_block : spec_of "chacha20_block" :=
    fnspec! "chacha20_block" (key_ptr nonce_ptr st_ptr : word) /
          (key nonce st : ListArray.t byte) R,
    { requires tr mem :=
        (Z.of_nat (Datatypes.length st) = 64) /\
        (array ptsto (word.of_Z 1) key_ptr key ⋆
                                                array ptsto (word.of_Z 1) nonce_ptr nonce ⋆
                                                array ptsto (word.of_Z 1) st_ptr st ⋆ R) mem;
      ensures tr' mem' :=
        tr = tr' /\
        (array ptsto (word.of_Z 1) key_ptr key ⋆
                                                array ptsto (word.of_Z 1) nonce_ptr nonce ⋆
                                                array ptsto (word.of_Z 1) st_ptr (chacha20_block key nonce st) ⋆ R) mem }.

  Derive chacha20_block_body SuchThat
         (defn! "chacha20_block" ("key", "nonce", "st") ~> "st" { chacha20_block_body },
          implements (chacha20_block) using [ "quarter" ])
         As chacha20_block_body_correct.
  Proof.
    compile_setup.
    cbn [chacha20_block_init].
    repeat compile_step.

    simple eapply compile_nlet_as_nlet_eq.
    simple eapply compile_buf_backed_by; repeat compile_step.
    instantiate (1 := (Naive.wrap 4)).
    simpl; eauto.

    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_push_word32; repeat compile_step.
    subst v; cbn [buf_backed_by Datatypes.length]; lia.
    subst v; unfold buf_backed_by; compile_step.

    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_push_word32; repeat compile_step.
    subst v; unfold buf_backed_by. unfold buf_push. eauto. simpl. lia.
    subst v; unfold buf_backed_by. unfold buf_push.
    admit.


  (*compile_step.*)

    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_push_word32; repeat compile_step.
    { subst v; unfold buf_backed_by. unfold buf_push. eauto. simpl. lia. }
    { subst v; unfold buf_backed_by. unfold buf_push. admit (*compile_step*). }

    simple eapply compile_nlet_as_nlet_eq.
    eapply compile_buf_push_word32; repeat compile_step.
    { subst v; unfold buf_backed_by. unfold buf_push. eauto. simpl. lia. }
    { subst v; unfold buf_backed_by. unfold buf_push. admit (*compile_step.*). }

    simple eapply compile_nlet_as_nlet_eq.
    simple eapply compile_w32s_of_bytes; [repeat compile_step..|].

    compile_step.
    compile_step; [repeat compile_step ..|].

    eapply expr_compile_Z_literal with (z:= 4).
    shelve.
    compile_step.
    (*TODO: need a compile words lemma comparable to compile_byte_memcpy.
      Alternately, something generic over fixed-size elements (e.g. instances of Allocable).
     *)
    Fail simple eapply compile_byte_memcpy.
    (*compile_step.

    repeat compile_step. subst v4.

    simple eapply compile_w32s_of_bytes; repeat compile_step.
    simple eapply compile_nlet_as_nlet_eq.

    simple eapply compile_bytes_of_w32s with (a_ptr := key_ptr); repeat compile_step.
    admit.

    simple eapply compile_nlet_as_nlet_eq.
    simple eapply compile_w32s_of_bytes with (a_ptr := nonce_ptr); repeat compile_step.

    simple eapply compile_nlet_as_nlet_eq.
    compile_buf_append.
    repeat compile_step. subst v7.

    simple eapply compile_w32s_of_bytes; repeat compile_step.
    simple eapply compile_nlet_as_nlet_eq.
    simple eapply compile_bytes_of_w32s with (a_ptr := nonce_ptr); repeat compile_step.
    admit.

    simple eapply compile_nlet_as_nlet_eq.
    simple eapply compile_buf_as_array; repeat compile_step.

    unfold buffer_at in H17.

    admit.

    simple eapply compile_nlet_as_nlet_eq.
    simple eapply compile_buf_make_stack.

    (*
    (*simple eapply compile_buf_append; [shelve .. |].*)
    compile_step.
    compile_step.


    simple eapply compile_nlet_as_nlet_eq.
    simple eapply compile_bytes_of_w32s; repeat compile_step.
    compile_step.
    simple eapply compile_buf_append; [shelve..|].


    [ repeat compile_step.. |].
    admit.
    intros.
    repeat compile_step.
    {
      use_sep_assumption. cancel.




    subst v. unfold buffer_at. unfold buf_push. progress simpl. eauto.

    simpl.

    progress sepsimpl.

    compile_step.


    unfold buf_backed_by.
    unfold Datatypes.length. lia.

    instantiate (1 := "st").

    unfold buffer_at in H1

    unfold buffer_at.

    simpl.
    Set Printing Parentheses.
    eapply sep_assoc.
    Check (proj2(sep_emp_True_l (_ : _) mem) _).
    refine (proj2(sep_emp_True_l (_ : _) mem) _); repeat compile_step.
    replace (4 mod (Z.pow_pos 2 32)) with 4 by lia.
    replace (0 mod (Z.pow_pos 2 32)) with 0 by lia.
    Search Lift1Prop.ex1.

    4 : { simple eapply compile_nlet_as_nlet_eq.
          eapply compile_buf_push_word32; repeat compile_step.

     *)*)
    Abort.

End Bedrock2.
