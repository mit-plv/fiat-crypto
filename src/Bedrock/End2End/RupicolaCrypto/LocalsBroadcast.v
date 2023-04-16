(*
  A collection of broadcast-style lemmas that store their results in locals.
  TODO: generalize to any semantics
  TODO: unify with Broadcast.v
  TODO: move to Rupicola
 *)
(*TODO: remove unused imports *)
Require Import Coq.Unicode.Utf8.
Require Import Rupicola.Lib.Api.
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
