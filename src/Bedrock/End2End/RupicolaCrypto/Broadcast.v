
Require Import Coq.Unicode.Utf8.
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Loops.

Require Coq.Init.Byte Coq.Strings.String. Import Init.Byte(byte(..)) String.
Require Import coqutil.Datatypes.List. Import Lists.List List.ListNotations.
Require Import Coq.ZArith.BinInt. Import Zdiv. Local Open Scope Z_scope.
Require Import coqutil.Byte coqutil.Word.LittleEndianList.

(* TODO: move into core Bedrock *)
Require Import Crypto.Bedrock.Field.Common.Util.

Import Syntax.Coercions ProgramLogic.Coercions.
Import Datatypes.


Open Scope Z_scope.


(*TODO: move to Rupicola.Lib *)


(*TODO: this statement is specialized to its use below.
  Should it be generalized?
 *)
Lemma skipn_nth_0 {A} (i : nat) (l : list A) d
  : i < length l -> skipn i l = (nth 0 (skipn i l) d):: skipn (S i) l.
Proof using.
  change (S i) with (1+i)%nat.
  rewrite <- skipn_skipn.
  intros.
  assert (0 < length (skipn i l)) by (rewrite length_skipn;lia).
  revert H0; generalize (skipn i l).
  intros.
  destruct l0; simpl in *; [lia|].
  reflexivity.
Qed.


  Lemma length_fold_left_invariant {A B} (l : list A) (acc : list B) f
    : (forall a acc, length (f acc a) = length acc) ->
      length (fold_left f l acc) = length acc.
  Proof.
    revert acc; induction l; simpl; intros; auto.
    rewrite IHl; congruence.
  Qed.


  Lemma upd_firstn_skipn A (l old : list A) (start : nat) d
    : start < length l ->
      start < length old ->
      upd (firstn start l ++ skipn start old) start (nth start l d)
      = (firstn (S start) l ++ skipn (S start) old).
  Proof.
    intros.
    unfold upd, upds.
    repeat rewrite !firstn_app, !skipn_app,
      !app_length,
      !firstn_length,
      !skipn_length,
      !firstn_firstn,
      !length_cons,
      !length_nil,
      !Nat.min_id.
    rewrite !min_l by lia.
    rewrite app_assoc.
    f_equal.
    {
      erewrite <- firstn_nth by lia.
      f_equal.
      {
        replace (start - start)%nat with 0%nat by lia.
        simpl.
        rewrite app_nil_r.
        reflexivity.
      }
      {
        rewrite firstn_all2; eauto.
        simpl.
        lia.
      }
    }
    {
      rewrite skipn_all2.
      {
        rewrite skipn_skipn.
        replace (1 + start - start + start)%nat with (S start) by lia.
        reflexivity.
      }
      {
        rewrite firstn_length.
        rewrite min_l; lia.
      }
    }
  Qed.



  Lemma list_as_nd_ranged_for_all_helper {A} (l old : list A) d
        (measure len start : nat)
    : measure = (len - start)%nat ->
      length l = len ->
      length old = len ->
      fold_left (λ (old0 : list A) (i : Z), upd old0 (Z.to_nat i) (nth (Z.to_nat i) l d)) (z_range start (Z.of_nat len)) ((firstn start l) ++ (skipn start old))
      = l.
  Proof.
    revert start len l old.
    induction measure; simpl; intros.
    {
      assert (start >=len) by lia.
      rewrite z_range_nil by lia.
      rewrite firstn_all2 by lia.
      rewrite skipn_all2 by lia.
      rewrite app_nil_r.
      reflexivity.
    }
    {
      rewrite z_range_cons by lia.
      simpl.
      rewrite Nat2Z.id.
      rewrite upd_firstn_skipn by lia.
      replace (Z.of_nat start + 1) with (Z.of_nat (S start)) by lia.
      rewrite IHmeasure; eauto.
      lia.
    }
  Qed.

  Lemma list_as_nd_ranged_for_all {A} (l old : list A) d len
    : length l = len ->
      length old = len ->
      nd_ranged_for_all 0 len (fun old i => upd old (Z.to_nat i) (nth (Z.to_nat i) l d)) old = l.
  Proof.
    rewrite <- fold_left_as_nd_ranged_for_all.
    intros.
    change old with ((firstn 0 l) ++ (skipn 0 old)).
    replace 0 with (Z.of_nat 0%nat) by lia.
    eapply list_as_nd_ranged_for_all_helper; eauto.
  Qed.



Section with_parameters.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.


     (*TODO: should be in core bedrock*)
  Lemma expr_locals_put m l x v exp (P : word -> Prop)
    : map.get l x = None ->
      WeakestPrecondition.expr m l exp P ->
      WeakestPrecondition.expr m (map.put l x v) exp P.
  Proof using locals_ok word_ok.
    intros.
    eapply Util.expr_only_differ_undef; eauto.
    eapply Util.only_differ_sym; eauto.
    eapply Util.only_differ_put; eauto.
    unfold map.undef_on, PropSet.singleton_set.
    unfold map.agree_on.
    intros.
    cbv in H1; subst.
    rewrite map.get_empty; auto.
  Qed.

  Lemma dexpr_locals_put m l x v exp (w : word)
    : map.get l x = None ->
      DEXPR m l exp w ->
      DEXPR m (map.put l x v) exp w.
  Proof using locals_ok word_ok.
    intros.
    eapply expr_locals_put; eauto.
  Qed.

  Class FitsInLocal T : Type :=
    {
      predT : word -> T -> mem -> Prop;
      szT : access_size;
      word_of_T : T -> word;
    }.
  (*TODO: properties*)
  Class FitsInLocal_ok T `(FitsInLocal T) : Prop :=
    {
      truncate_of_T : forall t, truncate_word szT (word_of_T t) = word_of_T t;
      predT_to_truncated_word
      : forall ptr t,
        Lift1Prop.impl1 (predT ptr t) (truncated_word szT ptr (word_of_T t));
    }.

  Section WithAccessSize.
    Context (T : Type) {T_Fits: FitsInLocal T}
            {T_Fits_ok : @FitsInLocal_ok T T_Fits}
            `{HasDefault T}.
    Existing Instance T_Fits.

    Notation predT := (@predT T T_Fits).
    Notation szT := (@szT T T_Fits).
    Notation word_of_T := (@word_of_T T T_Fits).


    Declare Scope word_scope.
    Delimit Scope word_scope with word.
    Local Infix "+" := word.add : word_scope.
    Local Infix "*" := word.mul : word_scope.


    Definition sz_word : word := (word.of_Z (Z.of_nat (Memory.bytes_per (width:=width) szT))).

    Local Notation "xs $@ a" :=
      (array predT sz_word a%word xs%list) (at level 10, format "xs $@ a").

    (* Array broadcasting/pointwise expressions.
     Requires some care to make sure that the array being written to can also be read.
     allows more things to be written in a expr style rather than a statement style,
     avoiding dealing directly with a pile of loop invariant inference.
   *)

  (* TODO: could add knowledge about lstl, but it's not yet necessary *)
  (* TODO: m not mentioned? *)
  (* expr expect idx_var to hold the index
   *)
  (*
    TODO: this is hardcoded to bytes right now.
    Generalize to things that can be packed in a word
   *)
  Definition broadcast_expr
             l idx_var
             old_data ptr R
             (expr : expr.expr) (lst : list T) :=
    forall (m : mem) (lstl : list T),
      length lstl < length old_data ->
      ((lstl ++ skipn (length lstl) old_data)$@ptr * R)%sep m ->
      DEXPR m (map.put l idx_var (word.of_Z (length lstl)))
            expr (word_of_T (nth (length lstl) lst default)).





  Lemma compile_broadcast_expr' {t m l e} (len : nat) (lst scratch : list T) :
    len = length scratch ->
    len = length lst ->
    len < 2^width ->
    let v := lst in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
           (a_ptr : word) a_var lst_expr idx_var to_var R,

      DEXPR m l (expr.var a_var) a_ptr ->

      (scratch$@a_ptr * R)%sep m ->

      ~idx_var = to_var ->
      map.get l idx_var = None ->
      map.get l to_var = None ->

     broadcast_expr l idx_var scratch a_ptr R lst_expr v ->
      (let v := v in
       forall m,
         (v$@a_ptr* R)%sep m ->
         <{ Trace := t; Memory := m; Locals := l; Functions := e }>
           k_impl
         <{ pred (k v eq_refl) }>) ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
        cmd_loop_fresh false idx_var (expr.literal 0) to_var len
                       (cmd.store szT (expr.op bopname.add a_var
                                               (expr.op bopname.mul idx_var sz_word))
                                  lst_expr)
                       k_impl
      <{ pred (nlet_eq [a_var] v k) }>.
  Proof.
    intros len_scratch len_lst.
    rewrite <- (list_as_nd_ranged_for_all lst scratch default len ltac:(auto) ltac:(auto)).
    rewrite nd_as_ranged_for_all.
    rewrite ranged_for_all_as_ranged_for.
    repeat compile_step.

    assert (~ a_var = to_var) by admit.
    assert (~ a_var = idx_var) by admit.

    eapply (compile_ranged_for_fresh _ _ _ _ _ _ _ _ _ _ _ _ idx_var to_var).
    repeat compile_step.
    repeat compile_step.
    (*Issue: in loop invariant lp from -> lp from'*)
    let x := open_constr:(fun from' lst tr mem locals =>
                            (lst$@a_ptr ⋆ R) mem
                            /\ locals = map.put (map.put l idx_var (word.of_Z from'))
                                                to_var (word.of_Z (Z.of_nat (length scratch)))) in
    instantiate(1:= x).
    {
      cbn beta.
      repeat compile_step.
      rewrite map.get_put_diff; repeat compile_step.
      rewrite map.get_put_same; repeat compile_step.
      rewrite map.get_put_same; repeat compile_step.
    }
    {
      cbn beta.
      repeat compile_step.
      rewrite map.put_comm; try compile_step.
      f_equal.
      rewrite map.put_put_same.
      reflexivity.
    }
    {
      cbn beta.
      repeat compile_step.
    }
    {
      repeat compile_step; try lia.
    }
    {
      cbn beta.
      repeat compile_step.
      repeat straightline'.
      exists (word.add a_ptr (word.mul (word.of_Z from') sz_word)); repeat compile_step.
      {
        eapply Util.dexpr_put_diff; repeat compile_step.
        eapply Util.dexpr_put_diff; repeat compile_step.
      }
      {
        eapply Util.dexpr_put_diff; repeat compile_step.
        eapply Util.dexpr_put_same; repeat compile_step.
      }
      exists (word_of_T (nth (Z.to_nat from') lst default)); repeat compile_step.
      {
        unfold broadcast_expr in *.
        subst v.
        revert H6.
        rewrite <- ranged_for_all_as_ranged_for.
        rewrite <- nd_as_ranged_for_all.
        rewrite (list_as_nd_ranged_for_all lst scratch default (length scratch)
                                           ltac:(auto) ltac:(auto)).
        intro H'.
        eapply dexpr_locals_put.
        {
          rewrite map.get_put_diff; auto.
        }
        (*TODO: need to know about the ranged_for'*)
        specialize (H' mem0 (firstn (Z.to_nat from') acc)).
        rewrite firstn_length in H'.
        assert (from' <= length acc) by admit.
        rewrite Nat.min_l in H' by lia.
        rewrite Z2Nat.id in H'.
        eapply H'.
        all:try lia.
  (*TODO: need to prove last n of scratch and acc are the same
        ecancel_assumption.*)
  Admitted.

    Lemma compile_broadcast_expr {t m l e} (len : nat) (lst scratch : list T) :
      let v := lst in
      forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
             (a_ptr : word) a_var lst_expr idx_var to_var R,

        DEXPR m l (expr.var a_var) a_ptr ->

        (scratch$@a_ptr * R)%sep m ->

        len = length scratch ->
        len = length lst ->
        len < 2^width ->

        ~idx_var = to_var ->
        map.get l idx_var = None ->
        map.get l to_var = None ->

        broadcast_expr l idx_var scratch a_ptr R lst_expr v ->
        (let v := v in
         forall m,
           (v$@a_ptr* R)%sep m ->
           <{ Trace := t; Memory := m; Locals := l; Functions := e }>
             k_impl
           <{ pred (k v eq_refl) }>) ->
        <{ Trace := t; Memory := m; Locals := l; Functions := e }>
          cmd_loop_fresh false idx_var (expr.literal 0) to_var len
                         (cmd.store szT (expr.op bopname.add a_var
                                                 (expr.op bopname.mul idx_var sz_word))
                                    lst_expr)
                         k_impl
        <{ pred (nlet_eq [a_var] v k) }>.
    Proof using T_Fits_ok env_ok ext_spec_ok locals_ok mem_ok word_ok.
      eauto using compile_broadcast_expr'.
    Qed.

    Section Binops.

      Context (expr_op : expr -> expr -> expr)
              (word_op : word -> word -> word)
              (op : T -> T -> T).
      Context (word_morph : forall a b, word_of_T (op a b) = word_op (word_of_T a) (word_of_T b)).

      Context (expr_compile_word_op
                 : forall {m l} (w1 w2 : word.rep) (e1 e2 : expr),
                  DEXPR m l e1 w1 ->
                  DEXPR m l e2 w2 ->
                  DEXPR m l (expr_op e1 e2) (word_op w1 w2)).

    (*TODO: generalize to a DEXPR goal instead of bop?*)
      Lemma broadcast_binop l idx_var scratch a_ptr R l1_expr l2_expr (l1 l2 : list T)
        : (*TODO: not necessary, just makes proof using expr_compile_word_op word_morph easier*)
        op default default = default ->

        length l1 = length l2 ->
        broadcast_expr l idx_var scratch a_ptr R l1_expr l1 ->
        broadcast_expr l idx_var scratch a_ptr R l2_expr l2 ->
        broadcast_expr l idx_var scratch a_ptr R
                       (expr_op l1_expr l2_expr)
                       (List.map (fun '(w1, w2) => op w1 w2) (combine l1 l2)).
      Proof.
        unfold broadcast_expr; intuition idtac.
        set (op_uncurry:=fun '(w1,w2) => op w1 w2).
        replace default with (op_uncurry (default,default)).
        rewrite map_nth.
        rewrite combine_nth by auto.
        subst op_uncurry; cbn beta match.
        rewrite word_morph.
        eapply expr_compile_word_op; eauto.
      Qed.

    End Binops.

    (*TODO: this is awkward*)
    Local Definition predT_to_tw := @predT_to_truncated_word T T_Fits T_Fits_ok.

    Local Hint Resolve predT_to_tw : ecancel_impl.

  Lemma broadcast_id l idx_var scratch a_ptr R a_var
    : map.get l a_var = Some a_ptr ->
      ~a_var = idx_var ->
      broadcast_expr l idx_var scratch a_ptr R
                     (expr.load szT
                                (expr.op bopname.add a_var
                                                 (expr.op bopname.mul idx_var sz_word)))
                     scratch.
  Proof using T_Fits_ok locals_ok mem_ok word_ok.
    unfold broadcast_expr; intuition idtac.
    repeat straightline.
    exists a_ptr; intuition idtac.
    {
      rewrite map.get_put_diff by assumption.
      assumption.
    }
    exists (word.of_Z (Z.of_nat (length lstl))).
    intuition idtac.
    {
      rewrite map.get_put_same; eauto.
    }
    simpl.
    unfold WeakestPrecondition.literal.
    cbv [dlet].
    exists (word_of_T (nth (length lstl) scratch default)).
    split; auto.
    erewrite load_of_sep.
    {
      erewrite truncate_of_T.
      reflexivity.
    }
    seprewrite_in (array_append (T:=T) predT sz_word) H3.
    replace (nth (length lstl) scratch)
      with (nth ((length lstl)+0) scratch) by (f_equal;lia).
    rewrite <- nth_skipn.
    assert (0 < length (skipn (length lstl) scratch)).
    {
      rewrite length_skipn.
      lia.
    }
    erewrite skipn_nth_0 in H3 by lia.
    cbn [nth array] in *.
    lazymatch goal with
    | [H : context [predT ?ptr1] |- context [ truncated_word _ ?ptr2]] =>
        replace ptr2 with ptr1
    end.
    ecancel_assumption_impl.
    f_equal.
    rewrite Z.mul_comm.
    rewrite word.ring_morph_mul.
    reflexivity.
  Qed.


  End WithAccessSize.

  Instance byte_ac : FitsInLocal byte :=
    {|
      predT := ptsto;
      szT := access_size.one;
      word_of_T b := word_of_byte b;
    |}.

  Lemma byte_and_xff b : byte.and b xff = b.
  Proof using Type.
    destruct b; reflexivity.
  Qed.

  (*TODO: where to put?*)
  Axiom (width_at_least_byte : 8 <= width).

  Lemma byte_in_word_bounds t
    : 0 <= byte.unsigned t < 2 ^ width.
  Proof using Type.
    assert (256 <= 2^width).
    {
      assert (256 <= 2^8) by (compute; congruence).
      pose proof (Z.pow_le_mono_r 2 8 width).
      pose proof width_at_least_byte.
      lia.
    }
    destruct t; cbv [byte.unsigned Byte.to_N Z.of_N]; lia.
  Qed.


  Instance byte_ac_ok : FitsInLocal_ok byte byte_ac.
  Proof using BW mem_ok word_ok.
    constructor; unfold word_of_T, szT, predT, byte_ac.
    {
      intros; unfold truncate_word.
      cbn.
      unfold truncate_Z.
      simpl.
      rewrite word.morph_and.
      rewrite word.unsigned_of_Z_nowrap; [| apply byte_in_word_bounds].
      change (word.of_Z (Z.ones 8)) with (word_of_byte xff : word).
      rewrite <- byte_morph_and.
      rewrite byte_and_xff.
      reflexivity.
    }
    {
      intros ptr t m H.
      unfold  truncated_word, truncated_scalar.
      cbn.
      rewrite word.unsigned_of_Z_nowrap.
      rewrite word.byte_of_Z_unsigned.
      ecancel_assumption.
      apply byte_in_word_bounds.
    }
  Qed.


  Instance word_ac : FitsInLocal word :=
    {|
      predT := scalar;
      szT := access_size.word;
      word_of_T b := b;
    |}.

  Instance word_ac_ok : FitsInLocal_ok word word_ac.
  Proof.
    constructor; unfold word_of_T, szT, predT, word_ac.
    {
      intros.
      intros; unfold truncate_word.
      cbn.
      unfold truncate_Z.
      simpl.
      rewrite word.morph_and.
      rewrite !word.of_Z_unsigned.
      rewrite Z2Nat.id.
      unfold Memory.bytes_per_word.
      replace ((width + 7) / 8 * 8) with width by admit.
      admit (*TODO: a similar proof lives in CSwap.v*).
      admit (*easy*).
    }
    {
      intros ptr t m H.
      unfold scalar in *.
      assumption.
    }
  Admitted.




  (*TODO: define in general*)
  Lemma broadcast_byte_const l (idx_var : string) scratch a_ptr R (const_list : list byte)
    : broadcast_expr byte l idx_var scratch a_ptr R
                     (expr.inlinetable
                               access_size.one
                               const_list
                               idx_var)
                     const_list.
  Proof.
    unfold broadcast_expr.
    intros.
    repeat straightline.
    exists (word.of_Z (length lstl)); split; auto.
    {
      rewrite map.get_put_same; eauto.
    }
    unfold  WeakestPrecondition.load.
    exists (word_of_byte (nth (length lstl) const_list x00)).
    split; auto.
    eapply load_one_of_sep.
    (*TODO: preds for const list*)
  Admitted.



  Lemma broadcast_byte_and l idx_var scratch a_ptr R l1_expr l2_expr (l1 l2 : list byte)
    : length l1 = length l2 ->
      broadcast_expr byte l idx_var scratch a_ptr R l1_expr l1 ->
      broadcast_expr byte l idx_var scratch a_ptr R l2_expr l2 ->
      broadcast_expr byte l idx_var scratch a_ptr R
                     (expr.op bopname.and l1_expr l2_expr)
                     (List.map (fun '(w1, w2) => byte.and w1 w2) (combine l1 l2)).
  Proof using BW word_ok.
    eapply broadcast_binop.
    - exact byte_morph_and.
    - intros; eapply expr_compile_word_and; eauto.
    - reflexivity.
  Qed.


  Lemma broadcast_word_add l idx_var scratch a_ptr R l1_expr l2_expr (l1 l2 : list word)
    : length l1 = length l2 ->
      broadcast_expr word l idx_var scratch a_ptr R l1_expr l1 ->
      broadcast_expr word l idx_var scratch a_ptr R l2_expr l2 ->
      broadcast_expr word l idx_var scratch a_ptr R
                     (expr.op bopname.add l1_expr l2_expr)
                     (List.map (fun '(w1, w2) => word.add w1 w2) (combine l1 l2)).
  Proof using word_ok.
    eapply broadcast_binop.
    - intros; reflexivity.
    - intros; eapply expr_compile_word_add; eauto.
    - unfold default, HasDefault_word.
      rewrite <- word.ring_morph_add.
      reflexivity.
  Qed.

End with_parameters.

Ltac compile_broadcast_expr :=
  lazymatch goal with
  | [ |- WeakestPrecondition.cmd _ _ _ _ ?locals (_ (nlet_eq [?var] ?v _)) ] =>
      let idx_var_str := gensym locals constr:((var++"_idx")%string) in
      let to_var_str := gensym locals constr:((var++"_to")%string) in
      simple eapply compile_broadcast_expr
        with (idx_var:=idx_var_str) (to_var:=to_var_str);
      [ typeclasses eauto|..]
  end.
