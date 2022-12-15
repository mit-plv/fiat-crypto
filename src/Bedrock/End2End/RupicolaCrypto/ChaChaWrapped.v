(* Rewritten versions of poly1305 and chacha20 that you can compile with Rupicola *)
Require Import Coq.Unicode.Utf8.
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Loops Rupicola.Lib.Loops.
(*TODO: move this file to Rupicola.Lib*)
Require Import Crypto.Bedrock.End2End.RupicolaCrypto.Broadcast.
Require Import Crypto.Bedrock.End2End.RupicolaCrypto.Low.
Require Import Crypto.Bedrock.End2End.RupicolaCrypto.Derive.
Require Import Crypto.Bedrock.End2End.RupicolaCrypto.Spec.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import bedrock2.BasicC32Semantics.
Import Syntax.Coercions ProgramLogic.Coercions.
Import Datatypes.


Import Loops.
Import LoopCompiler.


(*TODO: connect to Broadcast?*)
(* Tooling for representing a fixed-length array in local variables *)

(*TODO: generalize beyond word?*)
(*Note: stricter than dexpr because it should be writeable as well*)
Definition array_in_locals (l : locals) : list string -> list word -> Prop :=
  Forall2 (fun x w => map.get l x = Some w).

Lemma compile_set_locals_array_app {t m l e} (lst1 lst2 : list word) :
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
  2:{
    rewrite skipn_length.
    lia.
  }
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
  : ∀ (m l : map.rep) (x : string) (v : word) exp w,
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
Local Hint Constructors locals_array_expr : core.

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

Section Bedrock2.

  Declare Scope word_scope.
  Delimit Scope word_scope with word.
  Local Infix "+" := word.add : word_scope.
  Local Infix "*" := word.mul : word_scope.
  
  Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).
  Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").

  Definition le_combine l : word := word.of_Z (le_combine l).
  Definition le_split n (l : word) := le_split n (word.unsigned l).

  
Definition quarterround x y z t (st : list word) :=
  let '\<a,b,c,d\> := Low.quarter (nth x st (word.of_Z 0))
                        (nth y st (word.of_Z 0))
                        (nth z st (word.of_Z 0))
                        (nth t st (word.of_Z 0)) in
  upd (upd (upd (upd st x a) y b) z c) t d.

  (*Want: local_alloc; put a fixed-length array in local variables,
    accessible via broadcast
   *)


(* TODO: find a better way than hardcoding tuple length *)
Notation "'let/n' ( x0 , y0 , z0 , t0 , x1 , y1 , z1 , t1 , x2 , y2 , z2 , t2 , x3 , y3 , z3 , t3 ) := val 'in' body" :=
  (nlet [IdentParsing.TC.ident_to_string x0;
         IdentParsing.TC.ident_to_string y0;
         IdentParsing.TC.ident_to_string z0;
         IdentParsing.TC.ident_to_string t0;
         IdentParsing.TC.ident_to_string x1;
         IdentParsing.TC.ident_to_string y1;
         IdentParsing.TC.ident_to_string z1;
         IdentParsing.TC.ident_to_string t1;
         IdentParsing.TC.ident_to_string x2;
         IdentParsing.TC.ident_to_string y2;
         IdentParsing.TC.ident_to_string z2;
         IdentParsing.TC.ident_to_string t2;
         IdentParsing.TC.ident_to_string x3;
         IdentParsing.TC.ident_to_string y3;
         IdentParsing.TC.ident_to_string z3;
         IdentParsing.TC.ident_to_string t3]
        val (fun xyz => let '\< x0, y0, z0, t0,
                          x1, y1, z1, t1,
                          x2, y2, z2, t2,
                          x3, y3, z3, t3 \> := xyz in body))
    (at level 200,
      x0 name, y0 name, z0 name, t0 name,
      x1 name, y1 name, z1 name, t1 name,
      x2 name, y2 name, z2 name, t2 name,
      x3 name, y3 name, z3 name, t3 name,
      body at level 200,
      only parsing).
  
  Definition chacha20_block' (*256bit*)key (*32bit+96bit*)nonce :=
  nlet ["qv0"; "qv1"; "qv2"; "qv3"; "qv4"; "qv5"; "qv6"; "qv7";
         "qv8"; "qv9"; "qv10"; "qv11"; "qv12"; "qv13"; "qv14"; "qv15"] (*512bit*)
    (map le_combine (chunk 4 (list_byte_of_string"expand 32-byte k"))
    ++ map le_combine (chunk 4 key)
    ++ (word.of_Z 0)::(map le_combine (chunk 4 nonce))) (fun st =>
    let '\<qv0, qv1, qv2, qv3,
      qv4, qv5, qv6, qv7,
      qv8, qv9, qv10,qv11,
      qv12,qv13,qv14,qv15\> :=
                       \<(nth 0 st (word.of_Z 0)),
      (nth 1 st (word.of_Z 0)),
      (nth 2 st (word.of_Z 0)),
      (nth 3 st (word.of_Z 0)),
      (nth 4 st (word.of_Z 0)),
      (nth 5 st (word.of_Z 0)),
      (nth 6 st (word.of_Z 0)),
      (nth 7 st (word.of_Z 0)),
      (nth 8 st (word.of_Z 0)),
      (nth 9 st (word.of_Z 0)),
      (nth 10 st (word.of_Z 0)),
      (nth 11 st (word.of_Z 0)),
      (nth 12 st (word.of_Z 0)),
      (nth 13 st (word.of_Z 0)),
      (nth 14 st (word.of_Z 0)),
      (nth 15 st (word.of_Z 0))\>
    in
    let/n (qv0,qv1,qv2,qv3,
         qv4,qv5,qv6,qv7,
         qv8,qv9,qv10,qv11,
         qv12,qv13,qv14,qv15) :=
     Nat.iter 10 (fun '\<qv0, qv1, qv2, qv3,
                      qv4, qv5, qv6, qv7,
                      qv8, qv9, qv10,qv11,
                      qv12,qv13,qv14,qv15\>  =>
                    let/n (qv0, qv4, qv8,qv12) := Low.quarter qv0  qv4  qv8 qv12 in
                    let/n (qv1, qv5, qv9,qv13) := Low.quarter qv1  qv5  qv9 qv13 in
                    let/n (qv2, qv6, qv10,qv14) := Low.quarter qv2  qv6 qv10 qv14 in
                    let/n (qv3, qv7, qv11,qv15) := Low.quarter qv3  qv7 qv11 qv15 in
                    let/n (qv0, qv5, qv10,qv15) := Low.quarter qv0  qv5 qv10 qv15 in
                    let/n (qv1, qv6, qv11,qv12) := Low.quarter qv1  qv6 qv11 qv12 in
                    let/n (qv2, qv7, qv8,qv13) := Low.quarter qv2  qv7  qv8 qv13 in
                    let/n (qv3, qv4, qv9,qv14) := Low.quarter qv3  qv4  qv9 qv14 in
                    \<qv0,qv1,qv2,qv3,
                    qv4,qv5,qv6,qv7,
                    qv8,qv9,qv10,qv11,
                    qv12,qv13,qv14,qv15\>)
              \<qv0,qv1,qv2,qv3,
     qv4,qv5,qv6,qv7,
     qv8,qv9,qv10,qv11,
        qv12,qv13,qv14,qv15\> in
    let ss := [qv0; qv1; qv2; qv3; 
         qv4; qv5; qv6; qv7; 
         qv8; qv9; qv10; qv11; 
         qv12; qv13; qv14; qv15] in
  nlet ["qv0"; "qv1"; "qv2"; "qv3"; "qv4"; "qv5"; "qv6"; "qv7";
         "qv8"; "qv9"; "qv10"; "qv11"; "qv12"; "qv13"; "qv14"; "qv15"] (*512bit*)
    (map (fun '(s, t) => s + t)%word (combine ss (map le_combine (chunk 4 (list_byte_of_string"expand 32-byte k"))
            ++ map le_combine (chunk 4 key)
            ++ (word.of_Z 0)::(map le_combine (chunk 4 nonce))))) (fun ss =>
    let/n st := flat_map (le_split 4) ss in st)).

  #[export] Instance spec_of_chacha20 : spec_of "chacha20_block" :=
    fnspec! "chacha20_block" out key nonce / (pt k n : list Byte.byte) (R Rk Rn : map.rep -> Prop),
      { requires t m :=
          m =* pt$@out * R /\ length pt = 64%nat /\
            m =* k$@key * Rk /\ length k = 32%nat /\
            (*TODO: account for difference in nonce length*)
            m =* n$@nonce * Rn /\ length n = 12%nat;
        ensures T m := T = t /\ exists ct, m =* ct$@out * R /\ length ct = 64%nat /\
                                             ct = chacha20_block' k n }.

  Existing Instance spec_of_quarter.
Import Loops.

Existing Instance word_ac_ok.


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
  : ∀ m l exp (w : word),
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
  : ∀ m l exp (w : word),
    DEXPR m (map_remove_many l vars) exp w → DEXPR m l exp w.
Proof.
  intro m.
  induction vars; cbn [map_remove_many List.fold_left]; eauto.
  intros.
  apply IHvars in H.
  eapply dexpr_locals_put_removed; eauto.
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
    2:{
      rewrite skipn_length.
      cbn [length].
      lia.
    }
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
      replace (nth n lst (word.of_Z 0))
        with (truncate_word access_size.word (nth n lst (word.of_Z 0))).
      eapply array_load_of_sep; eauto.
      {
        rewrite Radd_comm by apply word.ring_theory.
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
      admit (*TODO: lemma for removing from in*).
    }
    {
      admit (*TODO: commutativity lemma *).
    }
Admitted.
 
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
    rewrite map_length, length_chunk by lia.
    rewrite H.
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
    rewrite length_le_split.
    replace ((1 + n) * 4) with  (4 + n * 4) by lia.
    reflexivity.
  }
  {
    rewrite length_chunk by lia.
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
      rewrite length_le_split.
      lia.
    }
  }
  {
    rewrite firstn_length.
    rewrite length_le_split.
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
    rewrite firstn_length.
    apply Nat.min_case.
    apply Nat.mod_mul; lia.
    auto.
  }
Qed.

Lemma compile_store_locals_array' {t m l e} (lst : list word) :
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
      rewrite <- le_combine_split in H0.
      rewrite !map_upd in H0.
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
      rewrite upds_length.
      rewrite H1.
      rewrite Nat.mul_comm.
      rewrite Nat.mod_mul.
      lia.
      cbv; congruence.
    }
    {
      rewrite upds_length.
      rewrite H1.
      rewrite Nat.mul_comm.
      lia.
    }
    intros m' Hm'.
    eapply H3.
    cbn [array].
    unfold upds in Hm'.
    rewrite !firstn_app, !firstn_firstn in Hm'.
    rewrite !firstn_length, !length_le_split in Hm'.
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
    seprewrite_in bytearray_append Hm'.
    seprewrite_in (scalar_of_bytes (ptr + word.of_Z (Z.of_nat (length (firstn (4 * n) out))))%word
                     (LittleEndianList.le_split 4 (word.unsigned a))) Hm'.
    {
      rewrite length_le_split.
      reflexivity.
    }
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
    {
      rewrite length_le_split; lia.
    }
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

    
  (*used because concrete computation on maps seems to be slow here*)
  Ltac eval_map_get :=
    repeat rewrite map.get_put_diff by (cbv; congruence);
    rewrite map.get_put_same; reflexivity.

  
        
  Ltac dedup s :=
    repeat rewrite map.put_put_diff with (k1:=s) by congruence;
    rewrite ?map.put_put_same with (k:=s).

  Axiom TODO : forall {A}, A.

  
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
    rewrite <- H3.
    rewrite <- H2.
    rewrite firstn_length.
    lia.
  }
  assert (length l1' = length l1).
  {
    rewrite Hlen.
    lia.
  }
  specialize (H0 l1').
  rewrite array_locs_is_combine in H0; eauto.
  intuition congruence.
Qed.

Derive chacha20_block_wrapped SuchThat
  (defn! "chacha20_block" ("st", "key", "nonce") { chacha20_block_wrapped },
    implements (chacha20_block') using [ "quarter" ])
  As chacha20_block_wrapped_correct.
Proof.
  compile_setup.
  compile_step.
  simple eapply compile_nlet_as_nlet_eq.
  simple eapply compile_set_locals_array.
  2:{
    repeat constructor; simpl;
    intuition congruence.
  }
  {
    repeat (apply locals_array_expr_app; intros).
    all: rewrite !map_length, !length_chunk by lia.
    all: rewrite ?H5, ?H8.
    all: cbn -[combine le_combine].
    all: repeat constructor; intros; subst.
    all: try compile_step.
    {
      eapply expr_load_word_of_byte_array; try eassumption.
      {
        rewrite H5.
        instantiate (1:= 8%nat).
        reflexivity.
      }
      compile_step.
      cbn [List.fold_left];
        repeat rewrite ?map.remove_put_same, ?map.remove_put_diff, ?map.remove_empty by congruence.        
      compile_step.
    }
    {
      eapply expr_load_word_of_byte_array; try eassumption.
      {
        rewrite H8.
        instantiate (1:= 3%nat).
        reflexivity.
      }
      compile_step.
      cbn [List.fold_left];
        repeat rewrite ?map.remove_put_same, ?map.remove_put_diff, ?map.remove_empty by congruence.     
      compile_step.
    }
  }
  compile_step.
  let l' := eval cbn in l in
    change l with l'.

  
  rewrite  Nat_iter_as_nd_ranged_for_all with (i:=0).
  change (0 + Z.of_nat 10) with 10%Z.

  compile_step.
  compile_step.
  assert (m = m) by reflexivity.
  compile_step.
  { compile_step. }
  { compile_step. }
  { intuition subst;
      repeat rewrite map.get_put_diff by (cbv;congruence);
      apply map.get_put_same.
  }
  { intuition subst.
    reflexivity.
  }
  { intuition subst. }
  { lia. }
  compile_step.
  {
    compile_step.
    compile_step.
    compile_step.

    Optimize Proof.
    Optimize Heap.
    


  (* TODO: why doesn't simple eapply work? *)
      do 7 (change (lp from' (ExitToken.new, ?y)) with ((fun v => lp from' (ExitToken.new, v)) y);
        simple eapply compile_nlet_as_nlet_eq;
        change (lp from' (ExitToken.new, ?y)) with ((fun v => lp from' (ExitToken.new, v)) y);
        simple eapply compile_quarter; [ now (eval_map_get || (repeat compile_step)) ..| repeat compile_step]).

      change (lp from' (ExitToken.new, ?y)) with ((fun v => lp from' (ExitToken.new, v)) y);
        simple eapply compile_nlet_as_nlet_eq;
        change (lp from' (ExitToken.new, ?y)) with ((fun v => lp from' (ExitToken.new, v)) y).
      simple eapply compile_quarter; [ now (eval_map_get || (repeat compile_step)) ..|].
      
      Optimize Proof.
      Optimize Heap.
      compile_step.

      
      (*TODO: compile_step takes too long (related to computations on maps?)*)
      unshelve refine (compile_unsets _ _ _); [ shelve | intros |  ]; cycle 1.
      simple apply compile_skip.
      2: exact [].
      cbv beta delta [lp].
      split; [tauto|].
      split.
      
      {
        
        (*TODO: why are quarter calls getting subst'ed?*)
        cbv [P2.car P2.cdr fst snd].
        cbv [map.remove_many fold_left].      
        cbv [gs].


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
        dedup  "_gs_from0".
        dedup  "_gs_to0".
        reflexivity.
      }
      ecancel_assumption.
  }

  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  
  simple eapply compile_nlet_as_nlet_eq.
  (*TODO: need to strengthen this a la broadcast
    so that it allows other vars to change, doesn't need fresh names
   *)
  simple eapply compile_set_locals_array.
  {
    
(*TODO: generalize to all ops*)
    eapply array_expr_compile_word_add.
    {
      repeat constructor; repeat compile_step.
    }
    {
      
      repeat (apply locals_array_expr_app; intros).
      {
        let x := eval cbn -[word.of_Z] in (map le_combine (chunk 4 (list_byte_of_string "expand 32-byte k"))) in
          change (map le_combine (chunk 4 (list_byte_of_string "expand 32-byte k"))) with x.
        unfold le_combine.
        cbn [firstn length].
        repeat (constructor; intros);
          apply expr_compile_Z_literal.
      }
      {
        eapply expr_load_word_of_byte_array; try eassumption.
        {
          rewrite H5.
          instantiate (1:= 8%nat).
          reflexivity.
        }
        {
          rewrite !map_length, !length_chunk, H5.
          reflexivity.
          all: lia.
        }
        {
          rewrite !map_length, !length_chunk, H5.
          all: try lia.
          repeat (set (Nat.div_up _ _) as x;
                  let x' := eval compute in x in
                    change x with x'; clear x).
          cbn [firstn skipn length map.putmany_of_list List.fold_left array_locs].
          repeat rewrite ?map.remove_put_same, ? map.remove_put_diff, ?map.remove_empty by (cbv;congruence).
          compile_step.
        }
      }
      {        
          rewrite !map_length, !length_chunk, H5.
          all: try lia.
          repeat (set (Nat.div_up _ _) as x;
                  let x' := eval compute in x in
                    change x with x'; clear x).
          cbn [firstn skipn length map.putmany_of_list List.fold_left array_locs].
          constructor.
          { repeat compile_step. }
          intros.
          eapply expr_load_word_of_byte_array; try eassumption.
          {
            rewrite H8.
            instantiate (1:= 3%nat).
            reflexivity.
          }
          compile_step.
          cbn [firstn skipn length map.putmany_of_list List.fold_left array_locs].
          repeat rewrite ?map.remove_put_same, ? map.remove_put_diff, ?map.remove_empty by (cbv;congruence).
          repeat compile_step.
        }
      }
    }
  {
    repeat constructor; cbv; intuition congruence.
  }
  compile_step.
  cbv [le_split].
  subst l0.
  change (array_locs ?a ?b ?c) with (array_locs a b v1).
  set (array_locs _ _ _) as l0.
  let l' := eval cbn -[v1 combine] in l0 in change l0 with l'.
  cbv [map.putmany_of_list gs].
  dedup  "_gs_from0".
  dedup  "_gs_to0".
  dedup  "qv0".
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
  
  (*TODO: earlier in derivation: why is key counted to 32? definitely wrong*)
  (*TODO: do I need to eval the combine?*)
  rewrite <- ListUtil.flat_map_map.
  change (flat_map _ (map _ v1)) with (bytes_of_w32s v1).
  
  simple eapply compile_nlet_as_nlet_eq.
  change (pred (let/n x as "st" eq:_ := bytes_of_w32s v1 in x))
    with (pred (let/n v1 as "st" eq:_ := v1 in
                let/n x as "st" eq:_ := bytes_of_w32s v1 in x)).
  simple eapply compile_store_locals_array.
  {
    rewrite unroll_len with (l:=v1) (a:= word.of_Z 0) at 1.
    replace (length v1) with 16%nat.
    cbn [unroll app].
    repeat constructor; repeat compile_step.
    {
      unfold v1.
      rewrite !map_length, !combine_length.
      cbn [length].
      rewrite !app_length, !map_length, !length_chunk.
      cbn [length].
      rewrite ?app_length, ?map_length, ?length_chunk.
      rewrite H5, H8.
      reflexivity.
      all: lia.
    }
  }
  2:{
    eapply expr_compile_var.
    eval_map_get.
  }
  2:{
    ecancel_assumption.
  }
  {
    rewrite H4.
      unfold v1.
      rewrite !map_length, !combine_length.
      cbn [length].
      rewrite !app_length, !map_length, !length_chunk.
      cbn [length].
      rewrite ?app_length, ?map_length, ?length_chunk.
      rewrite H5, H8.
      reflexivity.
      all: lia.
  }
  compile_step.
  simple eapply compile_bytes_of_w32s.
  compile_step.
  compile_step.
  compile_step.
  
  (*TODO: compile_step takes too long (related to computations on maps?)*)
  unshelve refine (compile_unsets _ _ _); [ shelve | intros |  ]; cycle 1.
  simple apply compile_skip.
  2: exact [].
  cbv beta delta [wp_bind_retvars pred].
  eexists; intuition eauto.
  eexists; split.
  ecancel_assumption.
  compile_step.
  {
    unfold v3.
    unfold bytes_of_w32s.
    erewrite length_flat_map; cycle 1.
    {
      intros; rewrite length_le_split; reflexivity.
    }
    rewrite map_length.
    unfold v2, v1.
    rewrite !map_length, !combine_length, !app_length.
    cbn [length].
    rewrite !map_length, ! length_chunk.
    rewrite H5,H8.
    reflexivity.
    all:lia.
  }
  auto.
Qed.


Lemma chacha20_block_ok key nonce :
  Spec.chacha20_block key ((le_split 4 (word.of_Z 0))++nonce) = chacha20_block' key nonce.
Proof.
  unfold chacha20_block, chacha20_block'.
  unfold le_split.
  repeat lazymatch goal with
           |- context c [nlet _ ?e ?f] =>
             let ex := fresh "x" in
             remember e as ex;
             let x := eval cbn beta in (f ex) in
               unfold nlet at 1
         end.
  subst x2.
  rewrite <- ListUtil.flat_map_map with (f:=word.unsigned(word:=word)).
  f_equal.
  subst x1.
  do 15 destruct x0 as [? x0].
  erewrite (map_ext _ _ word_add_pair_eqn).
  rewrite <- map_map with (g:= word.unsigned (word:=word)).
  f_equal.
  change (λ x1 : Z * Z, (word.of_Z (fst x1) + word.of_Z (snd x1))%word)
    with (fun x2 => (fun x => (fst x) + (snd x))%word ((fun x1 => (word.of_Z (word:=word)(fst x1), word.of_Z (snd x1))) x2)).
  rewrite <- map_map.
  erewrite map_ext with (g:=(λ '(s, t), (s + t)%word)).
  2:{
    intro a; destruct a; reflexivity.
  }
  f_equal.
  rewrite map_combine_separated.
  subst x.
  f_equal.
  2:{
    unfold le_combine.
    rewrite !map_app, !map_map.
    repeat (f_equal;[]).
    reflexivity.
  }
Admitted.

(*  

Local Open Scope string_scope.
Import Syntax Syntax.Coercions NotationsCustomEntry.
Import ListNotations.
Import Coq.Init.Byte.
Set Printing Depth 150.
Compute chacha20_block_wrapped.
Print Assumptions chacha20_block_wrapped_correct.
*)
