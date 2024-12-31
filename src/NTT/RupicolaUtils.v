From Coq Require List.
Require Import Rupicola.Lib.Core Rupicola.Lib.Notations.
Require Import Rupicola.Lib.InlineTables.
Require Import Rupicola.Lib.Arrays.
Require Import bedrock2.Memory.

Section __.
  (* TODO: upstream to Rupicola *)
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {K: Type}.
  Context {Conv: Convertible K nat}.

  Context {HD_word: HasDefault word}.

  Section Utils.
    Lemma truncate_word_nop_word (value: word):
      truncate_word access_size.word value = value.
    Proof.
      cbv [truncate_word truncate_Z].
      rewrite bytes_per_width_bytes_per_word.
      unfold bytes_per_word. assert ((width + 7) / 8 * 8 = width) as ->.
      { destruct BW.(width_cases) as [-> | ->]; reflexivity. }
      rewrite word.of_Z_land_ones. apply word.of_Z_unsigned.
    Qed.
  End Utils.

  Section InlineTableAnyWord.
    Context {V: Type}.
    Context {HD: HasDefault V}.
    Context (ConvV: Convertible V word).
    Context (ConvW: Convertible word V).

    Lemma compile_inlinetable_get_any_as_word : forall {tr mem locals functions},
      forall (idx: K) (t: InlineTable.t V),
        let v := InlineTable.get t idx in
        forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
          var idx_expr,

      let n := cast idx in
      (n < List.length t)%nat ->
      (Z.of_nat (List.length (to_byte_table (List.map cast t))) <= 2 ^ width) ->

      WeakestPrecondition.dexpr mem locals idx_expr (word.of_Z (Z.of_nat n)) ->

      (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var (cast v);
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->

      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      (cmd.seq (cmd.set
                  var
                  (expr.inlinetable access_size.word (to_byte_table (List.map cast t))
                                    (expr.op bopname.mul (expr.literal (width / 8))
                                             idx_expr)))
               k_impl)
      <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros; repeat straightline.
      exists (cast v); split; repeat straightline; eauto.
      eapply WeakestPrecondition_dexpr_expr; eauto.
      eexists; split; eauto.
      unfold v0; rewrite <- word.ring_morph_mul.
      erewrite load_from_word_table; auto.
      - rewrite map_nth. reflexivity.
      - rewrite map_length. auto.
    Qed.

    Lemma compile_inlinetable_get_any_as_word' : forall {tr mem locals functions},
      forall (idx: K) (t: InlineTable.t V) (t': InlineTable.t word),
        let v := InlineTable.get t idx in
        let v' := InlineTable.get t' idx in
        forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
          var idx_expr,

      let n := cast idx in
      (n < List.length t)%nat ->
      (Z.of_nat (List.length (to_byte_table t')) <= 2 ^ width) ->
      (t = List.map cast t') ->

      WeakestPrecondition.dexpr mem locals idx_expr (word.of_Z (Z.of_nat n)) ->

      (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var v';
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->

      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      (cmd.seq (cmd.set
                  var
                  (expr.inlinetable access_size.word (to_byte_table t')
                                    (expr.op bopname.mul (expr.literal (width / 8))
                                             idx_expr)))
               k_impl)
      <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros; repeat straightline.
      exists v'; split; repeat straightline; eauto.
      eapply WeakestPrecondition_dexpr_expr; eauto.
      eexists; split; eauto.
      unfold v0; rewrite <- word.ring_morph_mul.
      erewrite load_from_word_table; auto.
      - reflexivity.
      - unfold t in H. rewrite map_length in H. assumption.
    Qed.
  End InlineTableAnyWord.
  Section ArrayAnyWord.
    Context {V: Type}.
    Context {HD: HasDefault V}.
    Context (ConvV: Convertible V word).
    Context (ConvW: Convertible word V).

    Lemma compile_sizedlistarray_get_any_as_word : forall {len} {tr mem locals functions}
          (a: ListArray.t V) (idx: K),
      let v := ListArray.get a idx in
      forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
        R (a_ptr: word) a_expr idx_expr var,

        sep (sizedlistarray_value access_size.word len a_ptr (List.map cast a)) R mem ->
        WeakestPrecondition.dexpr mem locals a_expr a_ptr ->
        WeakestPrecondition.dexpr mem locals idx_expr (word.of_Z (Z.of_nat (cast idx))) ->

        Z.of_nat (cast idx) < Z.of_nat len ->

        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var (cast v);
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.set
             var
             (expr.load
                access_size.word
                (offset a_expr idx_expr (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word))))))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros. repeat straightline.
      assert (Hlen: Datatypes.length (List.map cast a) = len).
      { erewrite <- SizedListArray_length by eassumption. reflexivity. }
      exists (cast (ListArray.get a idx)); split; repeat straightline; eauto.
      eapply WeakestPrecondition_dexpr_expr; eauto.
      eapply WeakestPrecondition_dexpr_expr; eauto.
      - eexists; split; eauto.
        seprewrite_in (SizedListArray_Hrw (sz:=access_size.word)) H.
        + assumption.
        + cbv [array_repr Arrays._access_info] in H. simpl in H.
          erewrite array_load_of_sep; try eassumption.
          2: reflexivity.
          2: rewrite Hlen; instantiate (1 := cast idx); Lia.lia.
          rewrite truncate_word_nop_word.
          unfold ListArray.get.
          erewrite nth_indep by (rewrite Hlen; Lia.lia).
          rewrite map_nth. reflexivity.
      - repeat straightline.
        eapply WeakestPrecondition_dexpr_expr; eauto.
        unfold v0; rewrite word.ring_morph_mul.
        cbv [bytes_per].
        rewrite Z2Nat.id by (destruct BW.(width_cases) as [-> | ->]; cbv; congruence).
        rewrite word.unsigned_of_Z. f_equal.
        rewrite <- word.of_Z_wrap. reflexivity.
    Qed.

    Lemma compile_sizedlistarray_get_any_as_word' : forall {len} {tr mem locals functions}
          (a: ListArray.t V) (a': ListArray.t word) (idx: K),
      let v := ListArray.get a idx in
      let v' := ListArray.get a' idx in
      forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
        R (a_ptr: word) a_expr idx_expr var,

        a = List.map cast a' ->
        sep (sizedlistarray_value access_size.word len a_ptr a') R mem ->
        WeakestPrecondition.dexpr mem locals a_expr a_ptr ->
        WeakestPrecondition.dexpr mem locals idx_expr (word.of_Z (Z.of_nat (cast idx))) ->

        Z.of_nat (cast idx) < Z.of_nat len ->

        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var v';
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.set
             var
             (expr.load
                access_size.word
                (offset a_expr idx_expr (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word))))))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros. repeat straightline.
      assert (Hlen: Datatypes.length a' = len).
      { erewrite <- SizedListArray_length by eassumption. reflexivity. }
      exists v'; split; repeat straightline; eauto.
      eapply WeakestPrecondition_dexpr_expr; eauto.
      eapply WeakestPrecondition_dexpr_expr; eauto.
      - eexists; split; eauto.
        seprewrite_in (SizedListArray_Hrw (sz:=access_size.word)) H0.
        + assumption.
        + cbv [array_repr Arrays._access_info] in H0. simpl in H0.
          erewrite array_load_of_sep; try eassumption.
          2: reflexivity.
          2: rewrite Hlen; instantiate (1 := cast idx); Lia.lia.
          rewrite truncate_word_nop_word.
          unfold v', ListArray.get.
          erewrite nth_indep by (rewrite Hlen; Lia.lia). reflexivity.
      - repeat straightline.
        eapply WeakestPrecondition_dexpr_expr; eauto.
        unfold v0; rewrite word.ring_morph_mul.
        cbv [bytes_per].
        rewrite Z2Nat.id by (destruct BW.(width_cases) as [-> | ->]; cbv; congruence).
        rewrite word.unsigned_of_Z. f_equal.
        rewrite <- word.of_Z_wrap. reflexivity.
    Qed.

    Lemma compile_sizedlistarray_put_any_as_word : forall {len} {tr mem locals functions}
          (a: ListArray.t V) (idx: K) val,
      let v := ListArray.put a idx val in
      forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
        R (a_ptr: word) a_expr idx_expr val_expr var,

        sep (sizedlistarray_value access_size.word len a_ptr (List.map cast a)) R mem ->
        WeakestPrecondition.dexpr mem locals a_expr a_ptr ->
        WeakestPrecondition.dexpr mem locals idx_expr (word.of_Z (Z.of_nat (cast idx))) ->
        WeakestPrecondition.dexpr mem locals val_expr (cast val) ->

        Z.of_nat (cast idx) < Z.of_nat len ->

        (let v := v in
         forall mem',
           sep (sizedlistarray_value access_size.word len a_ptr (List.map cast v)) R mem' ->
           <{ Trace := tr;
              Memory := mem';
              Locals := locals;
              Functions := functions }>
           k_impl
           <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.store
             access_size.word
             (offset a_expr idx_expr (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word))))
             val_expr)
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros. repeat straightline.
      assert (Hlen: Datatypes.length (List.map cast a) = len).
      { erewrite <- SizedListArray_length by eassumption. reflexivity. }
      eexists; split; repeat straightline; eauto.
      - repeat (eapply WeakestPrecondition_dexpr_expr; eauto).
        repeat straightline.
        eapply WeakestPrecondition_dexpr_expr; eauto.
      - eexists; split; eauto.
        seprewrite_in (SizedListArray_Hrw (sz:=access_size.word)) H; auto.
        cbv [array_repr Arrays._access_info] in H. simpl in H.
        seprewrite_in (array_index_nat_inbounds (T:=word)) H.
        + rewrite Hlen; instantiate (1 := cast idx); Lia.lia.
        + rewrite word.ring_morph_mul in H.
          rewrite word.of_Z_unsigned in H.
          eapply store_word_of_sep; [unfold bytes_per; ecancel_assumption|].
          intros m Hm. apply H4.
          assert (Hlen': Datatypes.length (List.map cast v) = len).
          { unfold v. rewrite <- Hlen. unfold ListArray.put.
            rewrite map_length, map_length, replace_nth_length. reflexivity. }
          seprewrite (SizedListArray_Hrw (sz:=access_size.word)); auto.
          cbv [array_repr Arrays._access_info]; simpl.
          seprewrite (array_index_nat_inbounds (T:=word)).
          { rewrite Hlen'. instantiate (1 := cast idx); Lia.lia. }
          assert (List.firstn (cast idx) (List.map cast v) = List.firstn (cast idx) (List.map cast a)) as ->.
          { unfold v, ListArray.put.
            rewrite replace_nth_eqn, firstn_map, firstn_map.
            2: rewrite map_length in Hlen; Lia.lia.
            rewrite firstn_app_l; [reflexivity|].
            rewrite firstn_length. rewrite map_length in Hlen. Lia.lia. }
          assert (List.skipn (S (cast idx)) (List.map cast v) = List.skipn (S (cast idx)) (List.map cast a)) as ->.
          { unfold v, ListArray.put.
            rewrite replace_nth_eqn, skipn_map, skipn_map.
            2: rewrite map_length in Hlen; Lia.lia.
            rewrite assoc_app_cons, skipn_app_r; [reflexivity|].
            rewrite app_length, firstn_length. rewrite map_length in Hlen.
            simpl. Lia.lia. }
          rewrite word.ring_morph_mul, word.of_Z_unsigned.
          instantiate (1:=default).
          assert (List.hd _ (List.skipn (cast idx) (List.map cast v)) = cast val) as ->.
          { unfold v, ListArray.put.
            rewrite replace_nth_eqn, skipn_map.
            2: rewrite map_length in Hlen; Lia.lia.
            rewrite skipn_app_r; [reflexivity|].
            rewrite firstn_length. rewrite map_length in Hlen. Lia.lia. }
          ecancel_assumption_impl Hm.
          Unshelve. exact default.
    Qed.
  End ArrayAnyWord.
End __.

#[export] Hint Extern 1 (WP_nlet_eq (ListArray.get _ _)) =>
  simple eapply (@compile_sizedlistarray_get_any_as_word); shelve : compiler.
#[export] Hint Extern 1 (WP_nlet_eq (ListArray.put _ _ _)) =>
  simple eapply (@compile_sizedlistarray_put_any_as_word); shelve : compiler.
#[export] Hint Extern 5 (WP_nlet_eq (InlineTable.get _ _)) =>
  simple eapply @compile_inlinetable_get_any_as_word; shelve : compiler.
