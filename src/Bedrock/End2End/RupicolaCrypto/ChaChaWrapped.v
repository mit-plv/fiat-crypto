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

Lemma array_locs_is_combine' vars offset lst
  : (length vars = length lst - offset)%nat ->
    array_locs vars offset lst = combine vars (skipn offset lst).
Proof.
  revert offset.
  induction vars; intros; try  now (simpl; auto).
  specialize (IHvars (S offset)).
  simpl in H.
Admitted.


Lemma array_locs_is_combine vars lst
  : length vars = length lst ->
    array_locs vars 0 lst = combine vars lst.
Proof.
  rewrite <- ListUtil.skipn_0 with (xs := lst) at 3.
  intros; apply array_locs_is_combine'; lia.
Qed.
  
Definition load_to_vars vars (lst : list expr) k_impl : cmd :=
  List.fold_right (fun '(x,e) k_impl => cmd.seq (cmd.set x e) k_impl) k_impl (combine vars lst).

Lemma compile_set_locals_array {t m l e} (lst : list word):
    let v := lst in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl vars lst_expr,
      Forall2 (DEXPR m l) lst_expr lst ->
      length vars = length lst ->
      NoDup vars ->
      (forall v, In v vars -> map.get l v = None) ->
      (let v := v in
       let l := map.putmany_of_list (array_locs vars 0 lst) l in
         <{ Trace := t; Memory := m; Locals := l; Functions := e }>
           k_impl
         <{ pred (k v eq_refl) }>) ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
        load_to_vars vars lst_expr k_impl
      <{ pred (nlet_eq vars v k) }>.
Proof.
  unfold load_to_vars.
  intros until lst_expr.
  intros Hdexprs Hlen.
  pose proof (Forall.length_Forall2 Hdexprs) as H'.
  rewrite array_locs_is_combine by assumption.

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
  (pose proof (H0 a (ltac:(simpl; intuition)))).
  admit (*TODO: generalize from dexpr property*).
  { inversion H; subst; auto. }
  {
    intros.
    subst l0.
    admit (*TODO: cases on v = a*).
  }
Admitted.

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
    let/n st := map (fun '(s, t) => s + t)%word (combine ss (map le_combine (chunk 4 (list_byte_of_string"expand 32-byte k"))
            ++ map le_combine (chunk 4 key)
            ++ (word.of_Z 0)::(map le_combine (chunk 4 nonce))))in
    flat_map (le_split 4) st).

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
(*Existing Instance spec_of_unsizedlist_memcpy. *)
(*TODO: why is this necessary? seems like a bug*)
Local Hint Extern 0 (spec_of "unsizedlist_memcpy") =>
        Tactics.rapply spec_of_unsizedlist_memcpy : typeclass_instances.

Existing Instance word_ac_ok.

(*TODO: move to Bedrock/Field/Common/Util.v?*)
Lemma dexprs_app m (l : locals) es1 :
  forall es2 vs1 vs2,
    dexprs m l es1 vs1 ->
    dexprs m l es2 vs2 ->
    dexprs m l (es1 ++ es2) (vs1 ++ vs2).
Proof.
Admitted.


Definition load_offset e o :=
  expr.load access_size.word
    (expr.op bopname.add (expr.literal o) e).
Definition count_to (n : nat) : list Z := (z_range 0 n).

Lemma expr_load_word_of_byte_array m l len lst e ptr R
  : length lst = len ->
    (lst$@ptr * R)%sep m ->
    DEXPR m l e ptr ->
    Forall2 (DEXPR m l) (map (load_offset e) (count_to len)) (map le_combine (chunk 4 lst)).
Admitted.


  
Definition store_offset e o :=
  cmd.store access_size.word
    (expr.op bopname.add (expr.literal o) e).

Definition store_to_array ptr (lst : list expr) (k_impl : cmd) : cmd :=
  List.fold_right (fun '(x,e) k_impl => cmd.seq (store_offset (expr.var ptr) x e) k_impl)
    k_impl
    (combine (count_to (length lst)) lst).


Lemma compile_store_locals_array' {t m l e} (lst : list word) :
    forall (n : nat) P out ptr k_impl var lst_expr R,
      Forall2 (DEXPR m l) lst_expr lst ->
      (*TODO: move byte/word conversion to a better place*)
      length out = (4* (length lst + n))%nat ->
      DEXPR m l (expr.var var) ptr ->
      (out$@ptr * R)%sep m ->
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
  induction lst;
    inversion 1; subst;
    intros.
  {
    cbn [length Nat.add] in *.
    rewrite z_range_nil by lia.
    eapply H3.
    rewrite <- H0.
    rewrite firstn_all.
    cbn [array].
    ecancel_assumption.
  }
  {
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
    eexists; split.
    {
      admit.
    }
    replace (Z.of_nat n + 1) with (Z.of_nat (n+1)) by lia.
    eapply IHlst with (n := (n + 1)%nat).
    admit (*TODO: m*).
    2: (*TODO:m*) eauto.
    2: eauto.
    {
      rewrite H0.
      simpl.
      lia.
    }
    intros m' Hm'.
    eapply H5.
    admit (*TODO: ecancel_assumption*).
    
  }
Admitted.
  

Lemma compile_store_locals_array {t m l e} (lst : list word):
    let v := lst in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v)
           out ptr k_impl var lst_expr R,
      Forall2 (DEXPR m l) lst_expr v ->
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
  lia.
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
    Lemma 
    array_expr_compile_word_add m l
     : ∀ (w1 w2 : list word) (e1 e2 : list expr),
        Forall2 (DEXPR m l) e1 w1 →
        Forall2 (DEXPR m l) e2 w2 →
        Forall2 (DEXPR m l)          
          (map (λ '(s, t0), (expr.op bopname.add s t0)%word)
             (combine e1 e2))
          (map (λ '(s, t0), (s + t0)%word)
             (combine w1 w2)).
    Proof.
      intros w1 w2 e1 e2 H.
      revert e2 w2.
      induction H;
        inversion 1;
        subst;
        cbn [combine map];
        constructor;
        eauto.
      eapply expr_compile_word_add; eauto.
    Qed.

    
  (*used because concrete computation on maps seems to be slow here*)
  Ltac eval_map_get :=
    repeat rewrite map.get_put_diff by (cbv; congruence);
    rewrite map.get_put_same; reflexivity.

  
        
  Ltac dedup s :=
    repeat rewrite map.put_put_diff with (k1:=s) by congruence;
    rewrite ?map.put_put_same with (k:=s).

  Axiom TODO : forall {A}, A.

Derive chacha20_block_wrapped SuchThat
  (defn! "chacha20_block" ("st", "key", "nonce") { chacha20_block_wrapped },
    implements (chacha20_block') using [ "quarter"  ; "unsizedlist_memcpy" ])
  As chacha20_block_wrapped_correct.
Proof.
  compile_setup.
  compile_step.
  simple eapply compile_nlet_as_nlet_eq.
  simple eapply compile_set_locals_array.
  2:{
    rewrite ! app_length, !ListUtil.cons_length, ! map_length, !length_chunk; try lia.
    rewrite H6, H9.
    reflexivity.
  }
  2:{
    repeat constructor; simpl;
    intuition congruence.
  }
  2:{ apply TODO (*TODO: make a computation*). }
  {
    repeat apply Forall2_app.
    {
      let x := eval cbn -[word.of_Z] in (map le_combine (chunk 4 (list_byte_of_string "expand 32-byte k"))) in
        change (map le_combine (chunk 4 (list_byte_of_string "expand 32-byte k"))) with x.
      unfold le_combine.
      repeat constructor;
        apply expr_compile_Z_literal.
    }
    {
      eapply expr_load_word_of_byte_array; try eassumption.
      compile_step.
    }
    {
      constructor.
      {
        compile_step.
      }
      {
        eapply expr_load_word_of_byte_array; try eassumption.
        compile_step.
      }
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
  simple eapply compile_store_locals_array.
  {

    apply array_expr_compile_word_add.
    {
      repeat constructor;
        compile_step.
    }
    {
      repeat eapply Forall2_app.
      {
        cbn.
        repeat constructor;
          compile_step.
      }
      {
        eapply expr_load_word_of_byte_array; eauto.
        compile_step.
      }
      constructor.
      {
        compile_step.
      }
      {
        eapply expr_load_word_of_byte_array; eauto.
        compile_step.
      }
    }
  }
  shelve.
  {
    cbn.
    unfold WeakestPrecondition.get.
    eexists; split; eauto.
    eval_map_get.
  }
  {
    compile_step.
  }
  compile_step.

  
  (*TODO: compile_step takes too long (related to computations on maps?)*)
  unshelve refine (compile_unsets _ _ _); [ shelve | intros |  ]; cycle 1.
  simple apply compile_skip.
  2: exact [].
  cbv beta delta [wp_bind_retvars pred].
  eexists; intuition eauto.
  eexists; split.
  change 4 with (Z.of_nat (Memory.bytes_per (width:=32) access_size.word )) in H8.
  refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H8); clear H8.
  cancel.
  cbn [seps].
  eapply bytes_of_words.

  compile_step.
  {
    rewrite ws2bs_length.
    apply TODO(*TODO: length goal*).
  }
  {
    cbv [ws2bs le_split zs2bs ws2zs].
    rewrite ListUtil.flat_map_map.
    reflexivity.
  }
  Unshelve.
  apply TODO (*length goal*).
Qed.


Local Open Scope string_scope.
Import Syntax Syntax.Coercions NotationsCustomEntry.
Import ListNotations.
Import Coq.Init.Byte.
Compute chacha20_block_wrapped.
(*
TODO: offset of key loads
TODO: 0,nonce loads at start replaced by key loads

     = (["st"; "key"; "nonce"], [], bedrock_func_body:(
         $"qv0" = $(expr.literal 1634760805);
         $"qv1" = $(expr.literal 857760878);
         $"qv2" = $(expr.literal 2036477234);
         $"qv3" = $(expr.literal 1797285236);
         $"qv4" = load($(expr.literal 0) + $(expr.var "key"));
         $"qv5" = load($(expr.literal 1) + $(expr.var "key"));
         $"qv6" = load($(expr.literal 2) + $(expr.var "key"));
         $"qv7" = load($(expr.literal 3) + $(expr.var "key"));
         $"qv8" = load($(expr.literal 4) + $(expr.var "key"));
         $"qv9" = load($(expr.literal 5) + $(expr.var "key"));
         $"qv10" = load($(expr.literal 6) + $(expr.var "key"));
         $"qv11" = load($(expr.literal 7) + $(expr.var "key"));
         $"qv12" = load($(expr.literal 8) + $(expr.var "key"));
         $"qv13" = load($(expr.literal 9) + $(expr.var "key"));
         $"qv14" = load($(expr.literal 10) + $(expr.var "key"));
         $"qv15" = load($(expr.literal 11) + $(expr.var "key"));
         $"_gs_from0" = $(expr.literal 0);
         $"_gs_to0" = $(expr.literal 10);
         while $(expr.var "_gs_from0") < $(expr.var "_gs_to0") {
           {($"qv0", $"qv4", $"qv8", $"qv12") = $"quarter"($(expr.var "qv0"), $(expr.var "qv4"),
                                                          $(expr.var "qv8"), $(expr.var "qv12"));
            ($"qv1", $"qv5", $"qv9", $"qv13") = $"quarter"($(expr.var "qv1"), $(expr.var "qv5"),
                                                          $(expr.var "qv9"), $(expr.var "qv13"));
            ($"qv2", $"qv6", $"qv10", $"qv14") = $"quarter"($(expr.var "qv2"), $(expr.var "qv6"),
                                                           $(expr.var "qv10"), $(expr.var "qv14"));
            ($"qv3", $"qv7", $"qv11", $"qv15") = $"quarter"($(expr.var "qv3"), $(expr.var "qv7"),
                                                           $(expr.var "qv11"), $(expr.var "qv15"));
            ($"qv0", $"qv5", $"qv10", $"qv15") = $"quarter"($(expr.var "qv0"), $(expr.var "qv5"),
                                                           $(expr.var "qv10"), $(expr.var "qv15"));
            ($"qv1", $"qv6", $"qv11", $"qv12") = $"quarter"($(expr.var "qv1"), $(expr.var "qv6"),
                                                           $(expr.var "qv11"), $(expr.var "qv12"));
            ($"qv2", $"qv7", $"qv8", $"qv13") = $"quarter"($(expr.var "qv2"), $(expr.var "qv7"),
                                                          $(expr.var "qv8"), $(expr.var "qv13"));
            ($"qv3", $"qv4", $"qv9", $"qv14") = $"quarter"($(expr.var "qv3"), $(expr.var "qv4"),
                                                          $(expr.var "qv9"), $(expr.var "qv14"))};
           $"_gs_from0" = $(expr.var "_gs_from0") + $(expr.literal 1)
         };
         store($(expr.literal 0) + $(expr.var "st"), $(expr.var "qv0") + $(expr.literal 1634760805));
         store($(expr.literal 1) + $(expr.var "st"), $(expr.var "qv1") + $(expr.literal 857760878));
         store($(expr.literal 2) + $(expr.var "st"), $(expr.var "qv2") + $(expr.literal 2036477234));
         store($(expr.literal 3) + $(expr.var "st"), $(expr.var "qv3") + $(expr.literal 1797285236));
         store($(expr.literal 4) + $(expr.var "st"), $(expr.var "qv4") +
                                                     load($(expr.literal 0) + $(expr.var "key")));
         store($(expr.literal 5) + $(expr.var "st"), $(expr.var "qv5") +
                                                     load($(expr.literal 1) + $(expr.var "key")));
         store($(expr.literal 6) + $(expr.var "st"), $(expr.var "qv6") +
                                                     load($(expr.literal 2) + $(expr.var "key")));
         store($(expr.literal 7) + $(expr.var "st"), $(expr.var "qv7") +
                                                     load($(expr.literal 3) + $(expr.var "key")));
         store($(expr.literal 8) + $(expr.var "st"), $(expr.var "qv8") +
                                                     load($(expr.literal 4) + $(expr.var "key")));
         store($(expr.literal 9) + $(expr.var "st"), $(expr.var "qv9") +
                                                     load($(expr.literal 5) + $(expr.var "key")));
         store($(expr.literal 10) + $(expr.var "st"), $(expr.var "qv10") +
                                                      load($(expr.literal 6) + $(expr.var "key")));
         store($(expr.literal 11) + $(expr.var "st"), $(expr.var "qv11") +
                                                      load($(expr.literal 7) + $(expr.var "key")));
         store($(expr.literal 12) + $(expr.var "st"), $(expr.var "qv12") +
                                                      load($(expr.literal 8) + $(expr.var "key")));
         store($(expr.literal 13) + $(expr.var "st"), $(expr.var "qv13") +
                                                      load($(expr.literal 9) + $(expr.var "key")));
         store($(expr.literal 14) + $(expr.var "st"), $(expr.var "qv14") +
                                                      load($(expr.literal 10) + $(expr.var "key")));
         store($(expr.literal 15) + $(expr.var "st"), $(expr.var "qv15") +
                                                      load($(expr.literal 11) + $(expr.var "key")))))
     : func

*)
