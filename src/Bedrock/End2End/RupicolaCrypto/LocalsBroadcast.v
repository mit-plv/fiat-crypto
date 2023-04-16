(*
  A collection of broadcast-style lemmas that store their results in locals.
  TODO: generalize to any semantics
  TODO: unify with Broadcast.v
  TODO: move to Rupicola
 *)
(*TODO: remove unused imports *)
Require Import Coq.Unicode.Utf8.
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Loops.
Import coqutil.Word.LittleEndianList (le_combine, le_split).
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require coqutil.Word.Naive.
Require Import bedrock2.FE310CSemantics.
Require Import coqutil.Map.SortedListWord.
Import Syntax.Coercions ProgramLogic.Coercions.
Import Datatypes.
Import Lists.List.


Require Import Crypto.Bedrock.End2End.RupicolaCrypto.Broadcast.
Require Import Crypto.Bedrock.End2End.RupicolaCrypto.AbstractLength.

Local Notation word := (Naive.word 32).
Local Notation locals := (FE310CSemantics.locals (word:=word)).
Local Notation mem :=(@SortedListWord.map 32 (Naive.word 32) Naive.word32_ok Init.Byte.byte).
Local Notation predicate := (predicate (word:=word) (locals:=locals) (mem:=mem)).

Local Instance locals_ok : map.ok locals := (FE310CSemantics.locals_ok (word:=word)).





(*TODO: connect to Broadcast?*)
(* Tooling for representing a fixed-length array in local variables *)

(*TODO: generalize beyond word?*)
(*Note: stricter than dexpr because it should be writeable as well*)
Definition array_in_locals (l : locals) : list string -> list word -> Prop :=
  Forall2 (fun x w => map.get l x = Some w).

Lemma compile_set_locals_array_app {t} {m : mem} {l : locals} {e} (lst1 lst2 : list word) :
    let v := lst1 ++ lst2 in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl vars,
      (*length vars = length lst1 + length lst2 -> *)
      (let v := v in
         <{ Trace := t; Memory := m; Locals := l; Functions := e }>
           k_impl
         <{ pred (nlet_eq (firstn (length lst1) vars) lst1
                    (fun x1 Heqx1 =>
                       (nlet_eq (skipn (length lst1) vars) lst2
                          (fun x2 Heqx2 => k (x1 ++ x2) ltac:(subst;reflexivity))))) }>) ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
        k_impl
      <{ pred (nlet_eq vars v k) }>.
Proof.
  eauto.
Qed.


Lemma compile_set_locals_array_nil {t m l e}:
    let v := @nil word in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl,
      (*length vars = length lst1 + length lst2 -> *)
      (let v := v in
         <{ Trace := t; Memory := m; Locals := l; Functions := e }>
           k_impl
         <{ pred (k v eq_refl) }>) ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
        k_impl
      <{ pred (nlet_eq [] v k) }>.
Proof.
  eauto.
Qed.

Lemma compile_set_locals_array_cons_const {t m l e} w (lst : list word):
    let v := w::lst in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl var1 vars,
      (*length vars = length lst1 + length lst2 -> *)
      (let v := v in
         <{ Trace := t; Memory := m; Locals := map.put l var1 w; Functions := e }>
           k_impl
         <{ pred (k v eq_refl) }>) ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
        cmd.seq
          (cmd.set var1 w)
          k_impl
      <{ pred (nlet_eq (var1::vars) v k) }>.
Proof.
  intros.
  repeat straightline.
  subst v0.
  subst l0.
  rewrite word.of_Z_unsigned.
  eapply H.
Qed.

(* Used so that the locals evaluate without having to evaluate lst *)
Fixpoint array_locs (vars : list string) offset (lst : list word) :=
  match vars with
  | [] => []
  | v::vars =>
      (v, (nth offset lst (word.of_Z 0)))::(array_locs vars (S offset) lst)
  end.


Lemma sub_nz_implies_lt (m n o : nat)
  : m > 0 ->
    (m = n - o)%nat ->
    n > o.
Proof.
  intros; subst.
  revert n H.
  induction o;
    simpl; intros; lia.
Qed.

Lemma array_locs_is_combine' vars offset lst
  : (length vars = length lst - offset)%nat ->
    array_locs vars offset lst = combine vars (skipn offset lst).
Proof.
  revert offset.
  induction vars; intros; try  now (simpl; auto).
  specialize (IHvars (S offset)).
  simpl in H.
  
  assert (length lst > offset).
  {
    eapply sub_nz_implies_lt; eauto.
    lia.
  }
  assert (1 + length vars = (length lst) - offset).  
  {
    replace (1 + Z.of_nat (length vars)) with (Z.of_nat (S (length vars))) by lia.
    rewrite H.
    rewrite Nat2Z.inj_sub by lia.
    reflexivity.
  }
  erewrite split_hd_tl with (l := skipn _ _).
  2:{ simplify_len; lia. }
  simpl.
  f_equal.
  {
    rewrite <- hd_skipn_nth_default.
    rewrite nth_default_eq.
    reflexivity.
  }
  {
    rewrite tl_skipn.
    apply IHvars.
    lia.
  }
Qed.


Lemma array_locs_is_combine vars lst
  : length vars = length lst ->
    array_locs vars 0 lst = combine vars lst.
Proof.
  rewrite <- ListUtil.skipn_0 with (xs := lst) at 3.
  intros; apply array_locs_is_combine'; lia.
Qed.
  
Definition load_to_vars vars (lst : list expr) k_impl : cmd :=
  List.fold_right (fun '(x,e) k_impl => cmd.seq (cmd.set x e) k_impl) k_impl (combine vars lst).


Lemma array_dexpr_locals_put
  : ∀ (m : mem) (l : locals) (x : string) (v : word) exp w,
    map.get l x = None → Forall2 (DEXPR m l) exp w → Forall2 (DEXPR m #{ … l; x => v }#) exp w.
Proof.
  induction 2; constructor;
    eauto using dexpr_locals_put.
Qed.

(* we leave prior valiues abstract to support compound operations *)
Inductive locals_array_expr (P : mem -> Prop) : locals -> list string -> list expr -> list _ -> Prop :=
| locals_array_expr_nil l : locals_array_expr l [] [] []
| locals_array_expr_cons l v vars e lst_expr i lst 
  : (forall m, P m -> DEXPR m l e i) ->
    (forall i, locals_array_expr (map.put l v i) vars lst_expr lst) ->
    locals_array_expr l (v::vars) (e::lst_expr) (i::lst).
#[export] Hint Constructors locals_array_expr : core.

Lemma locals_array_expr_length m l vars lst_expr lst
  : locals_array_expr m l vars lst_expr lst ->
    length vars = length lst_expr
    /\ length lst_expr = length lst.
Proof.
  induction 1;
    simpl;
    intuition eauto.
Qed.

Lemma compile_set_locals_array {t m l e} (lst : list word):
    let v := lst in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl vars lst_expr,
      (*TODO: want to put arbitrary value for everything but current var
        (simplification of actual invariant, which is everything before current var)
        TODO: need to know current var for this
       
      Forall2 (fun e i => forall v',  DEXPR m l e i) lst_expr lst ->
       *)
      locals_array_expr (eq m) l vars lst_expr lst ->
      (*length vars = length lst -> implied by above *)
      NoDup vars ->
      (*
      (forall v, In v vars -> map.get l v = None) ->
       *)
      (let v := v in
       let l := map.putmany_of_list (array_locs vars 0 v) l in
         <{ Trace := t; Memory := m; Locals := l; Functions := e }>
           k_impl
         <{ pred (k v eq_refl) }>) ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
        load_to_vars vars lst_expr k_impl
      <{ pred (nlet_eq vars v k) }>.
Proof.
  unfold load_to_vars.
  intros until lst_expr.
  intros Hdexprs.
  pose proof (locals_array_expr_length _ _ _ _ _ Hdexprs) as H'.
  destruct H' as [Hlen H'].
  rewrite array_locs_is_combine by congruence.

  unfold nlet_eq.
  generalize (pred (k lst eq_refl)).
  clear pred k.
  
  revert k_impl.
  revert dependent lst_expr.
  revert dependent lst.
  revert l.
  induction vars;
    destruct lst;
    destruct lst_expr;
    intros;
    repeat lazymatch goal with
    | H : length _ =  length [] |- _ =>
        simpl in H; inversion H; subst; clear H
    | H : length [] =  length _ |- _ =>
        simpl in H; inversion H; subst; clear H
      end;
    cbn [combine fold_left map.putmany_of_list length] in *;
    repeat straightline;
    eauto.
  inversion H'.
  inversion Hdexprs; subst; clear Hdexprs.
  eexists; split; eauto.
  repeat straightline.
  apply IHvars with (l:=l0) (lst:=lst); eauto.
  (*(pose proof (H0 a (ltac:(simpl; intuition)))).*)
  (*eapply array_dexpr_locals_put; eauto.*)
  { inversion H; subst; auto. }
Qed.    


Definition load_offset e o :=
  expr.load access_size.word
    (expr.op bopname.add (expr.literal (4*o)) e).
Definition count_to (n : nat) : list Z := (z_range 0 n).


Fixpoint unroll {A} (default : A) (l : list A) n :=
  match n with
  | O => []
  | S n' =>
      unroll default l n' ++ [nth n' l default]
  end.
Lemma unroll_len_helper {A} a (l : list A) n
  : (n <= length l)%nat -> firstn n l = unroll a l n.
Proof.
  induction n; cbn [length unroll]; auto.
  intros.
  rewrite <- IHn by lia.
  erewrite ListUtil.firstn_succ by lia.
  rewrite nth_default_eq.
  reflexivity.
Qed.

Lemma unroll_len {A} a (l : list A)
  : l = unroll a l (length l).
Proof.
  rewrite <- unroll_len_helper by lia.
  rewrite firstn_all.
  reflexivity.
Qed.


Lemma truncate_word_word (w : word)
  : truncate_word access_size.word w = w.
Proof.
  unfold truncate_word.
  unfold truncate_Z.
  rewrite Z.land_ones_low.
  { apply word.of_Z_unsigned. }
  { pose proof (word.unsigned_range w); lia. }
  { pose proof (word.unsigned_range w).
    change (Z.of_nat (Memory.bytes_per access_size.word) * 8) with 32.
    destruct (Z.eqb_spec (word.unsigned w) 0).
    {
      rewrite e; cbn; lia.
    }
    apply Hints.log2_lt_pow2_proj_l2r; lia.
  }
Qed.


Notation map_remove_many m ks :=
  (List.fold_left map.remove ks m).

Lemma dexpr_locals_put_removed v
  : ∀ (m : mem) l exp (w : word),
    DEXPR m (map.remove l v) exp w → DEXPR m l exp w.
Proof.
  intros.
  remember (map.get l v) as mg eqn:Hget;
    destruct mg;
    symmetry in Hget.
  {
    erewrite <- map.put_noop with (m:=l) (k:=v); eauto.
    rewrite <- map.put_remove_same.
    eapply dexpr_locals_put; eauto.
    apply map.get_remove_same.
  }
  {
    rewrite map.remove_not_in in H; eauto.
  }
Qed.


(*TODO: generalize*)
Lemma map_remove_comm (l : locals) a b
  : (map.remove (map.remove l a) b) = map.remove (map.remove l b) a.
Proof.
  eapply map.ext_eq.
  unfold map.map_eq.
  intro k.
  destruct (String.eqb_spec k b);
    destruct (String.eqb_spec k a);
    subst;
    repeat rewrite ?map.get_remove_same, ?map.get_remove_diff by tauto;
    reflexivity.
Qed.  
  
(*TODO: generalize*)
Lemma map_remove_many_comm (l : locals) vars a
  : (map_remove_many (map.remove l a) vars) = map.remove (map_remove_many l vars) a.
Proof.
  unfold map_remove_many.
  revert l.
  induction vars; cbn [map_remove_many List.fold_left];  eauto.
  intros.
  rewrite <- IHvars.
  f_equal.
  destruct (String.eqb_spec a a0).
  {
    subst.
    rewrite map.remove_not_in.
    2:{ apply map.get_remove_same. }
    reflexivity.
  }
  {
    apply map_remove_comm.
  }
Qed.

Lemma dexpr_locals_put_removed_many vars
  : ∀ (m : mem) l exp (w : word),
    DEXPR m (map_remove_many l vars) exp w → DEXPR m l exp w.
Proof.
  intro m.
  induction vars; cbn [map_remove_many List.fold_left]; eauto.
  intros.
  apply IHvars in H.
  eapply dexpr_locals_put_removed; eauto.
Qed.

Lemma map_remove_remove_same s (l : locals)
  : map.remove (map.remove l s) s = map.remove l s.
Proof.
  apply map.map_ext.
  intros.
  destruct (String.eqb_spec s k); subst;
    rewrite ?map.get_remove_diff, ?map.get_remove_same by auto;
    auto.
Qed.


Lemma map_remove_remove_comm s1 s2 (l : locals)
  : map.remove (map.remove l s1) s2 =  map.remove (map.remove l s2) s1.
Proof.
  apply map.map_ext.
  intros.
  destruct (String.eqb_spec s1 k); subst;
  destruct (String.eqb_spec s2 k); subst;
    rewrite ?map.get_remove_diff, ?map.get_remove_same by auto;
    auto.
  rewrite ?map.get_remove_diff, ?map.get_remove_same by auto.
  auto.
Qed.

Lemma map_remove_remove_many_in s vars (l : locals)
  : In s vars ->
    (map_remove_many (map.remove l s) vars) = (map_remove_many l vars).
Proof.
  revert l.
  induction vars;
    cbn [List.fold_left In];
    intuition (subst; eauto).
  1: f_equal; apply map_remove_remove_same.
  rewrite map_remove_remove_comm.
  apply IHvars; auto.
Qed.
  
Lemma map_put_remove_many_in s i vars (l : locals)
        : In s vars ->
          (map_remove_many #{ … l; s => i }# vars)
          = (map_remove_many l vars).
Proof.
  revert l.
  induction vars;
    cbn [List.fold_left In];
    intuition (subst; eauto).
  1: f_equal; apply map.remove_put_same.
  destruct (String.eqb_spec s a); subst.
  {
    rewrite map.remove_put_same; auto.
  }
  {
    rewrite map.remove_put_diff; auto.
  }
Qed.


      
Lemma map_put_remove_many_notin s i vars (l : locals)
        : ~ In s vars ->
          (map_remove_many #{ … l; s => i }# vars)
          = map.put (map_remove_many l vars) s i.
Proof.
  revert l.
  induction vars;
    cbn [List.fold_left In];
    intuition (subst; eauto).
    rewrite map.remove_put_diff; auto.
Qed.

      
Lemma map_remove_remove_many_notin s vars (l : locals)
        : ~ In s vars ->
          (map_remove_many (map.remove l s) vars)
          = map.remove (map_remove_many l vars) s.
Proof.
  revert l.
  induction vars;
    cbn [List.fold_left In];
    intuition (subst; eauto).
    rewrite map_remove_comm; auto.
Qed.
  
      
Lemma expr_load_word_of_array_helper m l len lst e ptr R (n : nat)
  : length lst = len ->
    n <= len ->
    (array scalar (word.of_Z (word:=word) 4) ptr lst * R)%sep m ->
    forall vars,
      DEXPR m (map_remove_many l vars) e ptr ->
      length vars = (len - n)%nat ->
    locals_array_expr (eq m) l vars (map (load_offset e) (z_range n len)) (skipn n lst).
Proof.
  remember (len - n)%nat as diff.
  
  revert l n Heqdiff R lst.
  induction diff.
  {
    intros; simpl in *; subst.
    rewrite z_range_nil by lia.
    rewrite List.skipn_all by lia.
    simpl.
    destruct vars; simpl in *; try lia.
    constructor.
  }
  {
    intros.
    rewrite z_range_cons by lia.
    erewrite split_hd_tl with (l := skipn _ _).
    2:{ simplify_len; lia. }
    rewrite <- hd_skipn_nth_default.
    rewrite nth_default_eq.
    cbn [map].
    destruct vars; cbn [length] in *; try lia.
    constructor.
    {
      unfold load_offset.
      unfold DEXPR.
      cbn.
      unfold literal.
      unfold dlet.
      intros ? ?; subst.
      eapply WeakestPrecondition_dexpr_expr; eauto.
      unfold load.
      eexists; split; eauto.
      instantiate (1:= word.of_Z 0).
      change (@nth (@Naive.rep 32) n lst (@word.of_Z 32 word 0))
        with (@nth (@word.rep _ word) n lst (@word.of_Z 32 word 0)).
      replace (nth n lst (word.of_Z 0))
        with (truncate_word access_size.word (nth n lst (word.of_Z 0))).      
      eapply array_load_of_sep; eauto.
      {
        
        change (Naive.unsigned ?a) with (word.unsigned (word:=word) a).
        rewrite word.unsigned_of_Z.
        (*lia.
        rewrite Radd_comm by apply word.ring_theory.
        reflexivity.*)
        change (Naive.wrap ?a) with (word.of_Z (word:=word) a).
        rewrite word.ring_morph_add.
        rewrite word.of_Z_unsigned.
        rewrite Radd_comm by apply word.ring_theory.
        f_equal.
        rewrite word.unsigned_of_Z.
        symmetry.
        rewrite word.of_Z_wrap.
        change (word.wrap 4) with 4.
        reflexivity.
      }
      lia.
      {
        apply truncate_word_word.
      }
      eapply dexpr_locals_put_removed_many; eauto.
    }
    rewrite tl_skipn.
    replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia.
    intro.
    eapply IHdiff; eauto.
    lia.
    lia.
    cbn [List.fold_left map_remove_many] in H2.
    destruct (ListDec.In_dec string_dec s vars).
    {
      rewrite map_put_remove_many_in by assumption.
      rewrite map_remove_remove_many_in in H2 by assumption.
      auto.
    }
    {
      rewrite map_put_remove_many_notin; auto.
      rewrite map_remove_remove_many_notin in H2 by auto.
      eapply dexpr_locals_put with (x:=s) (v:=i) in H2.
      2: apply map.get_remove_same.
      rewrite map.put_remove_same in H2.
      auto.
    }
  }
Qed.

Lemma expr_load_word_of_array m l len lst e ptr R vars
  : length lst = len ->
    length vars = len ->
    (array scalar (word.of_Z (word:=word) 4) ptr lst * R)%sep m ->
    DEXPR m (map_remove_many l vars) e ptr ->
    locals_array_expr m l vars (map (load_offset e) (count_to len)) lst.
Proof.
  unfold count_to.
  change 0 with (Z.of_nat 0).
  change lst with (skipn 0 lst).
  intros.
  eapply expr_load_word_of_array_helper; eauto.
  lia.
  lia.
Qed.



Section Bedrock2.

  Declare Scope word_scope.
  Delimit Scope word_scope with word.
  Local Infix "+" := word.add : word_scope.
  Local Infix "*" := word.mul : word_scope.
  
  Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).
  Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").

  Definition le_combine l : word := word.of_Z (le_combine l).
  Definition le_split n (l : word) := le_split n (word.unsigned l).


Lemma expr_load_word_of_byte_array m l len lst e ptr R vars
  : (*(length lst mod Memory.bytes_per (width :=32) access_size.word)%nat = 0%nat ->*)
    length lst = (4*len)%nat ->
    length vars = len ->
    (lst$@ptr * R)%sep m ->
    DEXPR m (map_remove_many l vars) e ptr ->
    locals_array_expr (eq m) l vars (map (load_offset e) (count_to len)) (map le_combine (chunk 4 lst)).
Proof.
  intros.
  seprewrite_in words_of_bytes H1; auto.
  {
    rewrite H.
    rewrite Nat.mul_comm.
    rewrite Nat.mod_mul; cbv; congruence.
  }
  eapply expr_load_word_of_array; eauto.
  {
    simplify_len.
    rewrite Nat.mul_comm.
    rewrite Nat.div_up_exact; lia.
  }
  
  unfold le_combine.
  unfold bs2ws, zs2ws, bs2zs in *.
  rewrite <- map_map with (g:= word.of_Z (word:=word)).
  change (Z.of_nat (Memory.bytes_per access_size.word)) with 4 in *.
  change (Memory.bytes_per access_size.word) with 4%nat in *.
  ecancel_assumption.
Qed.



  
Definition store_offset e o :=
  cmd.store access_size.word
    (expr.op bopname.add (expr.literal (4*o)) e).

Definition store_to_array ptr (lst : list expr) (k_impl : cmd) : cmd :=
  List.fold_right (fun '(x,e) k_impl => cmd.seq (store_offset (expr.var ptr) x e) k_impl)
    k_impl
    (combine (count_to (length lst)) lst).


Lemma Forall2_distr_forall {A B C} (P : A -> B -> C -> Prop) l1 l2
  : Forall2 (fun b c => forall a, P a b c) l1 l2 ->
    forall (a:A), Forall2 (P a) l1 l2.
Proof.
  revert l2; induction l1; inversion 1; subst; intros; constructor; eauto.
Qed.


Lemma forall_distr_Forall2 {A B C} (P : A -> B -> C -> Prop) l1 l2
  : A ->
    (forall (a:A), Forall2 (P a) l1 l2) ->
    Forall2 (fun b c => forall a, P a b c) l1 l2.
Proof.
  intro a.
  revert l2; induction l1; intros.
  {
    specialize (H a); inversion H; subst; eauto.
  }
  {
    pose proof (H a) as H'; inversion H'; subst.
    constructor.
    {
      intros.
      specialize (H a1); inversion H; subst; eauto.
    }
    apply IHl1.
    intros.    
    specialize (H a1); inversion H; subst; eauto.
  }
Qed.


Lemma upd_chunk n lst a
  : (length lst mod 4 = 0)%nat ->
    upd (chunk 4 lst) n (LittleEndianList.le_split 4 a)
    = chunk 4 (upds lst (n * 4) (LittleEndianList.le_split 4 a)).
Proof.
  intro.
  unfold upd.
  unfold upds.
  cbn [length].
  rewrite !chunk_app; try lia.
  f_equal.
  1: rewrite !firstn_chunk by lia; reflexivity.
  f_equal.
  2:{
    rewrite skipn_chunk by lia.
    simplify_len.
    replace ((1 + n) * 4) with  (4 + n * 4) by lia.
    reflexivity.
  }
  {
    simplify_len.
    rewrite <- Nat.div_up_exact_mod with (a:= length lst) (b:=4%nat) at 2 by lia.
    generalize (Nat.div_up (length lst) 4).
    clear lst H.
    intros.
    replace (n0 * 4 - n * 4)%nat with ((n0 - n) * 4)%nat by lia.
    generalize (n0 - n)%nat; intros.
    destruct (n1); cbn [firstn chunk].
    { reflexivity. }
    {
      rewrite firstn_nil.
      rewrite <- firstn_chunk by lia.
      rewrite chunk_small.
      simpl.
      rewrite firstn_nil.
      reflexivity.
      simplify_len.
      lia.
    }
  }
  {
    simplify_len.
    apply Nat.min_case.
    {
      unfold Nat.modulo in *.
      pose proof (Nat.divmod_spec (length lst) 3 0 3 ltac:(lia)).
      remember (Nat.divmod (length lst) 3 0 3 ).
      destruct p.
      destruct H0.
      pose proof (Nat.divmod_spec (length lst - n * 4) 3 0 3 ltac:(lia)).
      remember (Nat.divmod (length lst - n * 4) 3 0 3 ).
      destruct p.
      destruct H2.
      cbn [snd] in *.
      lia.
    }
    apply Nat.mod_same; lia.
  }
  {
    simplify_len.
    apply Nat.min_case.
    apply Nat.mod_mul; lia.
    auto.
  }
Qed.

Lemma compile_store_locals_array' {t} {m : mem} {l e} (lst : list word) :
    forall (n : nat) P out ptr k_impl var lst_expr R,
      (out$@ptr * R)%sep m ->
      (*TODO: is this general enough?*)
      (Forall2 (fun e v => forall m' out', (out'$@ptr * R)%sep m' -> DEXPR m' l e v) lst_expr lst) ->
      (*TODO: move byte/word conversion to a better place*)
      length out = (4* (length lst + n))%nat ->
      DEXPR m l (expr.var var) ptr ->
      (forall m,
          ((firstn (4*n)%nat out)$@ptr * (array scalar (word.of_Z 4) (ptr + word.of_Z(4*n))%word lst) * R)%sep m ->
       <{ Trace := t; Memory := m; Locals := l; Functions := e }>
           k_impl
         <{ P }>) ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
        List.fold_right (fun '(x,e) k_impl => cmd.seq (store_offset (expr.var var) x e) k_impl)
          k_impl
          (combine (z_range n (length lst_expr + n)) lst_expr)
      <{ P }>.
Proof.
  revert m.
  induction lst.
  {
    
    intros until R;
      intros Hm Hlst.
    eapply Forall2_distr_forall in Hlst.
    eapply Forall2_distr_forall in Hlst.
    eapply Forall2_distr_forall in Hlst; eauto.
    inversion Hlst; subst.
                  
    cbn [length Nat.add] in *.
    rewrite z_range_nil by lia.
    intros HA HB HC.
    eapply HC.
    rewrite <- HA.
    rewrite firstn_all.
    cbn [array].
    ecancel_assumption.
  }
  {
    cbn [length].
    intros.
    inversion H0; subst; clear H0.
    
    cbn [length].
    replace (S (length l0) + n) with ((length l0) + (n+1)%nat) by lia.
    rewrite z_range_cons by lia.
    cbn [combine fold_right].
    repeat straightline.
    eexists; split; eauto.
    {
      eapply expr_compile_word_add.
      eapply expr_compile_Z_literal.
      eauto.
    }
    eexists; split; eauto.
    seprewrite_in words_of_bytes H.
    { rewrite H1.
      rewrite Nat.mul_comm.
      apply Nat.mod_mul.
      cbv; congruence.
    }
    unfold store.
    eapply array_store_of_sep; cycle 1.
    {
      unfold scalar in H.
      ecancel_assumption.
    }
    3:{
      rewrite Radd_comm by apply word.ring_theory.
      reflexivity.
    }
    {
      (*TODO: make work with simplify_len*)
      rewrite bs2ws_length.
      rewrite H1.
      rewrite Nat.mul_comm.
      rewrite Nat.div_mul.
      lia.
      cbv;congruence.
      cbv;congruence.
      rewrite H1.
      rewrite Nat.mul_comm.
      rewrite Nat.mod_mul.
      lia.
      cbv;congruence.
    }
    replace (Z.of_nat n + 1) with (Z.of_nat (n+1)) by lia.
    intros.
    eapply IHlst with (n := (n + 1)%nat); eauto.
    seprewrite words_of_bytes; cycle 1.
    {
      unfold scalar.
      unfold bs2ws, zs2ws, bs2zs in *.
      rewrite <- word.of_Z_unsigned with (x:=a) in H0.
      replace (word.unsigned a)
        with (word.unsigned a mod 2 ^ (Z.of_nat 4 * 8)) in H0.
Import coqutil.Word.LittleEndianList (le_combine_split).
      rewrite <- le_combine_split in H0.
      rewrite <- !map_upd in H0.
      rewrite upd_chunk in H0.
      change (Memory.bytes_per access_size.word) with 4%nat in *.
      ecancel_assumption.
      rewrite H1.
      rewrite Nat.mul_comm.
      rewrite Nat.mod_mul.
      lia.
      lia.
      {
        rewrite Z.mod_small; auto.
        apply word.unsigned_range.
      }
    }
    {
      simplify_len.
      rewrite Nat.mul_comm.
      rewrite Nat.mod_mul.
      lia.
      cbv; congruence.
    }
    {
      simplify_len; lia.
    }
    intros m' Hm'.
    eapply H3.
    cbn [array].
    unfold upds in Hm'.
    rewrite !firstn_app, !firstn_firstn in Hm'.
    rewrite !firstn_length, !LittleEndianList.length_le_split in Hm'.
    replace  (Init.Nat.min (4 * (n + 1)) (n * 4)) with (4 * n)%nat in Hm' by lia.
    assert (length out > n * 4) by lia.
    replace (4 * (n + 1) - Init.Nat.min (n * 4) (length out))%nat
      with 4%nat in Hm' by lia.
    replace (length out - n * 4)%nat
      with (4 * S (length lst))%nat in Hm' by lia.
    replace (Init.Nat.min 4 (4 * S (length lst)))%nat with 4%nat in Hm' by lia.
    replace (Init.Nat.min (4 * S (length lst)) 4)%nat with 4%nat in Hm' by lia.
    rewrite Nat.sub_diag in Hm'.
    rewrite firstn_all2 with (n:=4%nat) in Hm'.
    cbn [firstn] in Hm'.
    rewrite app_nil_r in Hm'.
    replace (4 * Z.of_nat (n + 1)) with (4 * Z.of_nat n + 4) in Hm' by lia.
    rewrite word.ring_morph_add in Hm'.
    seprewrite_in (bytearray_append (firstn (4*n) out) (LittleEndianList.le_split 4 (word.unsigned a)) ptr) Hm'.
    seprewrite_in (scalar_of_bytes (ptr + word.of_Z (Z.of_nat (length (firstn (4 * n) out))))%word
                     (LittleEndianList.le_split 4 (word.unsigned a))) Hm'.
    { simplify_len; lia. }
    rewrite !firstn_length in Hm'.
    replace  (Z.of_nat (Init.Nat.min (4 * n) (length out)))
      with (4 * Z.of_nat n) in Hm' by lia.
    rewrite le_combine_split in Hm'.
    {
      rewrite Z.mod_small in Hm'; auto.
      2:apply word.unsigned_range.
      rewrite word.of_Z_unsigned in Hm'.
      replace (ptr + (word.of_Z (4 * Z.of_nat n) + word.of_Z 4))%word
        with (ptr + word.of_Z (4 * Z.of_nat n) + word.of_Z 4)%word in Hm'.
      ecancel_assumption.
      {
        rewrite Radd_assoc.
        reflexivity.
        apply word.ring_theory.
      }
    }
    { simplify_len; lia. }
  }
Qed.
  

Lemma compile_store_locals_array {t m l e} (lst : list word):
    let v := lst in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v)
           out ptr k_impl var lst_expr R,
      (*TODO: is this general enough?*)
      (Forall2 (fun e v => forall m' out', (out'$@ptr * R)%sep m' -> DEXPR m' l e v) lst_expr lst) ->
      (*TODO: move byte/word conversion to a better place*)
      length out = (4* length v)%nat ->
      DEXPR m l (expr.var var) ptr ->
      (out$@ptr * R)%sep m ->
      (let v := v in
       forall m,
       (array scalar (word.of_Z 4) ptr v * R)%sep m ->
       <{ Trace := t; Memory := m; Locals := l; Functions := e }>
           k_impl
         <{ pred (k v eq_refl) }>) ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
       store_to_array var lst_expr k_impl
      <{ pred (nlet_eq [var] v k) }>.
Proof.
  intros.
  unfold store_to_array.
  unfold count_to.
  replace (Z.of_nat (length lst_expr)) with (Z.of_nat (length lst_expr) + 0%nat) by lia.
  change 0 with (Z.of_nat 0).
  eapply compile_store_locals_array'; eauto.
  {
    subst v.
    lia.
  }
  intros; apply H3.
  change (4*0)%nat with 0%nat in H4.
  replace (ptr + word.of_Z (4 * Z.of_nat 0))%word with ptr in H4.
  {
    cbn [firstn array] in H4.
    ecancel_assumption.
  }
  {
    rewrite <- word.of_Z_unsigned with (x := ptr) at 2.
    rewrite <- word.ring_morph_add.
    replace ((word.unsigned ptr + 4 * Z.of_nat 0)) with (word.unsigned ptr) by lia.
    rewrite word.of_Z_unsigned.
    reflexivity.
  }
Qed.


(*TODO: generalize to all ops*)

Lemma array_expr_compile_word_add P l vars
  : ∀ (w1 : list word) (e1 : list expr),
    locals_array_expr P l vars e1 w1 ->
    forall e2 w2,
     locals_array_expr P l vars e2 w2 ->
     locals_array_expr P l vars
      (map (λ '(s, t0), (expr.op bopname.add s t0)%word)
         (combine e1 e2))
      (map (λ '(s, t0), (s + t0)%word)
         (combine w1 w2)).
Proof.
  induction 1;
    inversion 1;
    subst;    
    cbn [combine map];
    constructor;
    eauto.
  {
    intros.
    eapply expr_compile_word_add; eauto.
  }
Qed.


Lemma forall_distr_Forall2' {A B C} (P : A -> B -> C -> Prop) l1 l2
  : length l1 = length l2 ->
    (forall (a:A), Forall2 (P a) l1 l2) ->
    Forall2 (fun b c => forall a, P a b c) l1 l2.
Proof.
  revert l2; induction l1; destruct l2; cbn [length];
    intros; try lia; constructor; intros.
  {
    specialize (H0 a0); inversion H0; subst; eauto.
  }
  {
    apply IHl1; try lia.
    intros.    
    specialize (H0 a0); inversion H0; subst; eauto.
  }
Qed.


Lemma locals_array_expr_app_helper m l vars1 vars2 le1 le2 l1 l2
  : locals_array_expr m l vars1 le1 l1 ->
    (forall l1', length l1' = length vars1 ->
                locals_array_expr m (map.putmany_of_list (combine vars1 l1') l) vars2 le2 l2) ->
    locals_array_expr m l (vars1 ++ vars2) (le1 ++ le2) (l1 ++ l2).
Proof.
  induction 1;
    intros;
    cbn [app] in *;
    try tauto.
  { eapply H; eauto. exact (eq_refl (x:= length [])). }
  {
    constructor;
    intuition (subst; eauto).
    specialize (H0 i0).
    specialize (H1 i0).
    eapply H1; eauto.
    intros.
    apply (H2 (i0::l1')).
    cbn [length]; congruence.
  }
Qed.
  
Lemma locals_array_expr_app m l vars le1 le2 l1 l2
  : locals_array_expr m l (firstn (length l1) vars) le1 l1 ->
    (forall l1', length l1' = length l1 ->
                 locals_array_expr m (map.putmany_of_list (array_locs (firstn (length l1) vars) 0 l1') l)
                   (skipn (length l1) vars) le2 l2) ->
    locals_array_expr m l vars (le1 ++ le2) (l1 ++ l2).
Proof.
  intros.
  rewrite <- firstn_skipn with (n:= length l1) (l:= vars).
  intros; eapply locals_array_expr_app_helper; eauto.
  intros l1' Hlen.
  pose proof (locals_array_expr_length _ _ _ _ _ H); intuition.
  rewrite firstn_length in Hlen.
  assert (length vars >= length l1)%nat.
  {
    revert H2 H3.
    repeat simplify_len.
    lia.
  }
  assert (length l1' = length l1) by lia.
  specialize (H0 l1').
  rewrite array_locs_is_combine in H0; eauto.
  intuition congruence.
Qed.


End Bedrock2.
