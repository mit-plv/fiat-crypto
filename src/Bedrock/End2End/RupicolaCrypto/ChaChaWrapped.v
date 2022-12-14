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
       nlet ["qv0'"; "qv1'"; "qv2'"; "qv3'"; " qv4'"; "qv5'"; "qv6'"; "qv7'";
             "qv8'"; "qv9'"; "qv10'"; "qv11'"; "qv12'"; "qv13'"; "qv14'"; "qv15'"] (*512bit*)
         (map le_combine (chunk 4 (list_byte_of_string"expand 32-byte k"))
            ++ map le_combine (chunk 4 key)
            ++ (word.of_Z 0)::(map le_combine (chunk 4 nonce))) (fun st =>
    let/n st := map (fun '(s, t) => s + t)%word (combine ss st) in
    flat_map (le_split 4) st)).

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
  2:{ admit (*TODO: make a computation*). }
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
    

  (*used because concrete computation on maps seems to be slow here*)
  Ltac eval_map_get :=
    repeat rewrite map.get_put_diff by (cbv; congruence);
    rewrite map.get_put_same; reflexivity.

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
        dedup  "_gs_from0".
        dedup  "_gs_to0".
        reflexivity.
      }
      ecancel_assumption.
  }

  compile_step.

  (*TODO: duplicated from above*)
  
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
  2:{ admit (*TODO: make a computation*). }
  {
    intuition subst.
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
      repeat compile_step.
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
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  
  let l' := eval cbn in l0 in
    change l0 with l'.
  clear l0.

  
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
simple eapply compile_nlet_as_nlet_eq.
simple eapply compile_store_locals_array.
{
  repeat constructor.
  all: try apply expr_compile_word_add.
  {
    apply expr_compile_var.
    compile_step.
  }
  {
    unfold le_combine.
    apply expr_compile_Z_literal.
  }
  {
    apply expr_compile_var.
    compile_step.
  }
  {
    unfold le_combine.
    apply expr_compile_Z_literal.
  }
  admit.
  {
    unfold le_combine.
    cbn [Ascii.byte_of_ascii  Byte.of_bits app].
    apply expr_compile_Z_literal.
  }
  (
    sepsimpl.
  simpl in H4.
  clear H2.
  
  ecancel_assumption.
  intros P pred k.
  unfold nlet_eq.
  generalize (pred (k lst eq_refl)).
  clear P pred k.
  induction lst;
    inversion 1; subst;
    intros.
  {
    destruct out; simpl in H0; try lia.
    eapply H3.
  }
  {
    unfold count_to in *.
    cbn [length] in *.
    cbn [combine 
  }
    rewrite map.get_put_diff.
    2:{
      cbv.
      congruence.
    compile_step. }
  { intuition.
    { apply map.get_put_same. }
    { rewrite map.get_put_diff by (cbv;congruence); auto. }
    exact H11.
  }
  
  simple eapply compile_nlet_as_nlet_eq.
  (*TODO: loop inference hardcodes tuples for multiple vars*)
  let from_v := gensym locals "from" in
  let to_v := gensym locals "to" in
  eapply (compile_ranged_for_fresh false)
    with (from_var := from_v) (to_var := to_v)
         (loop_pred := fun from a0 tr mem locals =>
         map.get locals (gs "_gs_from0") = Some (word.of_Z from) ∧ map.get locals (gs "_gs_to0") = Some (word.of_Z 10) /\ _).
  (*lp :=
   map.get locals (gs "_gs_from0") = Some (word.of_Z from) ∧ map.get locals (gs "_gs_to0") = Some (word.of_Z 10)*)
  { compile_step. }
  { compile_step. }
  { intuition. }
  { intuition.
    { apply map.get_put_same. }
    { rewrite map.get_put_diff by (cbv;congruence); auto. }
    exact H11.
  }
  split.
  {
    repeat rewrite map.get_put_diff by (cbv;congruence);
      apply map.get_put_same. 
  }
  split.
  {
    repeat rewrite map.get_put_diff by (cbv;congruence);
      apply map.get_put_same. 
  }
  2: lia.
  refine (conj H3 (conj H4 (conj H7 _))).
  2:{
    repeat compile_step.
    unfold quarterround.
    intros.

    
(*
    
  Instance spec_of_quarterround : spec_of "quarterround" :=
    fnspec! "quarterround" ( : word) /
          (k msg output : array_t byte) (*(output : Z (*felem*))*) R,
      { requires tr mem :=
        (Z.of_nat (Datatypes.length k) = 32) /\ (*TODO: all lens*)
          (array ptsto (word.of_Z 1) key_ptr k ⋆
                 array ptsto (word.of_Z 1) msg_ptr msg ⋆
                 array ptsto (word.of_Z 1) out_ptr output ⋆ R) mem;
        ensures tr' mem' :=
        tr = tr' /\
          (array ptsto (word.of_Z 1) key_ptr k ⋆
                 array ptsto (word.of_Z 1) msg_ptr msg ⋆
                 array ptsto (word.of_Z 1) out_ptr (poly1305 k [] msg [] false false false output) ⋆ R) mem }.
*)
    
    Fail.
    
Ltac make_ranged_for_predicate from_var from_arg to_var to_val vars args tr pred locals :=
  lazymatch substitute_target from_var from_arg pred locals with
  | (?pred, ?locals) =>
    lazymatch substitute_target to_var to_val pred locals with
    | (?pred, ?locals) => make_predicate vars args tr pred locals
    end
  end.

Ltac infer_ranged_for_predicate' from_var to_var to_val argstype vars tr pred locals :=
  (** Like `make_predicate`, but with a binding for `idx` at the front. *)
  let idxtype := type of to_val in
  let val_pred :=
      constr:(fun (idx: idxtype) (args: argstype) =>
                ltac:(let f := make_ranged_for_predicate
                                from_var idx to_var to_val
                                vars args tr pred locals in
                      exact f)) in
  eval cbv beta in val_pred.
  let from_v := gensym locals "from" in
  let to_v := gensym locals "to" in
  let to_val := constr:(10) in
  let k := ltac:(infer_ranged_for_predicate' from_v to_v to_val) in
  let lp := lazymatch goal with
            | |- WeakestPrecondition.cmd _ _ ?tr ?mem ?locals (_ ?prog) =>
                lazymatch goal with
                | H:?pred mem
                  |- _ =>
                    lazymatch is_rupicola_binding prog with
                    | RupicolaBinding ?A ?vars => k A vars tr pred locals
                    | NotARupicolaBinding => fail 100 prog "does not look like a let-binding"
                    | ?a => fail 100 "weird" a
                    end
                | _ => fail 100  "No hypothesis mentions memory" mem
                end
            | |- ?g => fail 100 g "is not a Rupicola goal"
            end in
  eapply (compile_ranged_for_fresh false) with (from_var := from_v) (to_var := to_v).

   _compile_ranged_for locals 10 (compile_ranged_for_fresh false).
  compile_ranged_for.
  eapply nleq
  compile_step; [repeat compile_step; lia .. | |].
  all: repeat compile_step.
  compile_ranged_for.
  TODO: want the nat.iter to take vars in/out
  (*TODO: could do better about filling in locals values; shouldn't repeat apps*)
  
  Fail.
      
  Ltac compile_broadcast_expr :=
    lazymatch goal with
    | [ |- WeakestPrecondition.cmd _ _ _ _ ?locals (_ (nlet_eq [?var] ?v _)) ] =>
        let idx_var_str := gensym locals constr:((var++"_idx")%string) in
        let to_var_str := gensym locals constr:((var++"_to")%string) in
        simple eapply compile_broadcast_expr
          with (idx_var:=idx_var_str) (to_var:=to_var_str);
        [ typeclasses eauto|..]
    end.

  eapply compile_nlet_as_nlet_eq.
  compile_broadcast_expr.

  {
    apply expr_compile_var.
    repeat compile_step.
  }
  {
    Unset Printing Notations.
    
    ecancel_assumption.
  eapply compile_nlet_as_nlet_eq.
  compile_broadcast_expr.
  
  eapply compile_nlet_as_nlet_eq.
  lazymatch goal with
  | [ |- WeakestPrecondition.cmd _ _ _ _ ?locals (_ (nlet_eq [?var] ?v _)) ] =>
      let idx_var_str := gensym locals constr:((var++"_idx")%string) in
      let to_var_str := gensym locals constr:((var++"_to")%string) in
      simple eapply compile_broadcast_expr
        with (idx_var:=idx_var_str) (to_var:=to_var_str)
      end.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
