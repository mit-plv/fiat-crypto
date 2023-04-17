(* Rewritten versions of poly1305 and chacha20 that you can compile with Rupicola *)
Require Import Coq.Unicode.Utf8.
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Loops.
(*TODO: move this file to Rupicola.Lib*)
Require Import Crypto.Bedrock.End2End.RupicolaCrypto.Broadcast.
Require Import Crypto.Bedrock.End2End.RupicolaCrypto.Spec.
Import coqutil.Word.LittleEndianList (le_combine, le_split).
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require coqutil.Word.Naive.
Require Import bedrock2.FE310CSemantics.
Require Import coqutil.Map.SortedListWord.
Import Syntax.Coercions ProgramLogic.Coercions.
(*TODO: factor out shared deps*)
Require Import Crypto.Bedrock.End2End.RupicolaCrypto.AbstractLength.
Require Import Crypto.Bedrock.End2End.RupicolaCrypto.LocalsBroadcast.
Local Notation le_combine := LittleEndianList.le_combine.
Local Notation le_split := LittleEndianList.le_split.
Require Crypto.Bedrock.End2End.RupicolaCrypto.ChaCha20.
Import Datatypes.
Import Lists.List.

Import Loops.
Import LoopCompiler.


Notation word := (Naive.word 32).
Notation locals := (FE310CSemantics.locals (word:=word)).
Notation mem :=(@SortedListWord.map 32 (Naive.word 32) Naive.word32_ok Init.Byte.byte).
Notation predicate := (predicate (word:=word) (locals:=locals) (mem:=mem)).



Local Instance locals_ok : map.ok locals := (FE310CSemantics.locals_ok (word:=word)).


Lemma compile_set_locals_array {t m l e} {A} (v : A):
    let v := v in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl vars lst_expr f (lst : list word),
      (*TODO: want to put arbitrary value for everything but current var
        (simplification of actual invariant, which is everything before current var)
        TODO: need to know current var for this
       
      Forall2 (fun e i => forall v',  DEXPR m l e i) lst_expr lst ->
       *)
      v = f lst ->
      locals_array_expr (eq m) l vars lst_expr lst ->
      (*length vars = length lst -> implied by above *)
      NoDup vars ->
      (*
      (forall v, In v vars -> map.get l v = None) ->
       *)
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
  intros until lst.
  intros Hveq Hdexprs.
  pose proof (locals_array_expr_length _ _ _ _ _ Hdexprs) as H'.
  destruct H' as [Hlen H'].
  rewrite array_locs_is_combine by congruence.

  unfold nlet_eq.
  generalize (pred (k v eq_refl)).
  clear pred k.
  
  revert k_impl.
  revert dependent lst_expr.
  revert dependent v.
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
  apply IHvars with (l:=l0) (lst:=lst) (v:= f lst); eauto.
  (*(pose proof (H0 a (ltac:(simpl; intuition)))).*)
  (*eapply array_dexpr_locals_put; eauto.*)
  { inversion H; subst; auto. }
Qed.    



Definition p : positive := 2^130 - 5.

#[global]
Instance p_field_params : FieldParameters :=
  {|
  M_pos := p;
  a24 := 1%F;
  mul := "fe1305_mul";
  add := "fe1305_add";
  sub := "fe1305_sub";
  opp := "fe1305_opp";
  square := "fe1305_square";
  scmula24 := "fe1305_scmul1_dontuse";
  inv := "fe1305_inv";
  from_bytes := "fe1305_from_bytes";
  to_bytes := "fe1305_to_bytes";
  select_znz := "fe1305_select_znz";
  felem_copy := "fe1305_copy";
  from_word := "fe1305_from_word"
           |}.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
#[global]
  Instance p_field_representation : FieldRepresentation (mem:=mem) :=
  field_representation 5 (2^130) [(1,5)].


Lemma le_combine_app l1 l2
  : le_combine (l1 ++l2)
    = Z.lor (le_combine l1) (Z.shiftl (le_combine l2) (8 * length l1)).
Proof.
  induction l1; eauto.
  cbn [app le_combine length].
  rewrite IHl1.
  rewrite <- ! Z.lor_assoc.
  f_equal.
  replace (8 * Z.of_nat (S (length l1)))
    with ((8 * Z.of_nat (length l1)) + 8) by lia.
  rewrite <- Z.shiftl_shiftl by lia.
  rewrite Z.shiftl_lor.
  reflexivity.
Qed.


Lemma fold_right_sum_plus a b l
  : a + fold_right (λ x y : Z, x + y) b l
    = fold_right (λ x y : Z, x + y) (a + b) l.
Proof.
  induction l; simpl; eauto.
  lia.
Qed.

Lemma feval_bytes_as_le_combine_help l1 elts
  : fold_right (λ x y : Z, x + y) (le_combine l1)
      (map (λ t : Z * Z, fst t * snd t)
         (combine (map (ModOps.weight 8 1) (seq (length l1) (length elts))) (map byte.unsigned elts))) = 
      le_combine (l1 ++ elts).
Proof.
  revert l1.
  induction elts.
  {
    intros.
    rewrite app_nil_r.
    cbn.
    reflexivity.
  }
  {
    intros.
    cbn.
    replace (l1 ++ a :: elts) with ((l1 ++ [a]) ++ elts).
    2:rewrite <- app_assoc; reflexivity.
    rewrite <- IHelts.
    rewrite le_combine_app.
    rewrite fold_right_sum_plus.
    f_equal.
    {
      cbn.
      unfold ModOps.weight.
      rewrite Z.div_1_r.
      rewrite Z.opp_involutive.
      rewrite Z.lor_0_r.
      rewrite Shift.Z.lor_shiftl; try lia; try apply le_combine_bound.
      rewrite Z.add_comm.
      f_equal.
      rewrite Z.shiftl_mul_pow2 by lia.
      lia.
    }
    rewrite app_length; simpl.
    rewrite Nat.add_comm.
    reflexivity.
  }
Qed.

Lemma feval_bytes_as_le_combine elts
  : length elts = encoded_felem_size_in_bytes -> feval_bytes elts = F.of_Z M_pos (le_combine elts).
Proof.
  cbn.
  intros.
  unfold Representation.eval_bytes.
  f_equal.
  unfold Core.Positional.eval.
  unfold Core.Positional.to_associational.
  unfold Core.Associational.eval.
  rewrite <- H.
  apply feval_bytes_as_le_combine_help with (l1:=[]).
Qed.


(* TODO: fix up and prove*)
Lemma compile_bytes_as_felem_inplace elts :
  let v := F.of_Z _ (le_combine elts) in
  forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
         a (a_var : string) t m l e (R: mem -> Prop),
    (* TODO Note: the last 3 bytes should be able to *)
    (array ptsto (word.of_Z 1) a elts
     * Memory.anybytes (word.add a (word.of_Z (Z.of_nat encoded_felem_size_in_bytes))) (word.of_Z (word:=word) 3)
     * R)%sep m ->
    DEXPR m l a_var a ->
    spec_of_from_bytes e ->
    length elts = encoded_felem_size_in_bytes ->
    (* TODO: will this be a problem? *)
    bytes_in_bounds (elts) ->
    (let v := v in
     forall m,
       (FElem (field_parameters:= p_field_params) (Some tight_bounds) a v * R)%sep m ->
       <{ Trace := t; Memory := m; Locals := l; Functions := e }>
         k_impl
       <{ pred (k v eq_refl) }>) ->
       <{ Trace := t; Memory := m; Locals := l; Functions := e }>
         cmd.seq
           (cmd.call [] from_bytes [expr.var a_var; expr.var a_var])
           k_impl
       <{ pred (nlet_eq [a_var] v k) }>.
Proof.
  repeat straightline.
  
  destruct H0 as [? [? ?]]; subst.
  eexists; split.
  {
    repeat straightline.
    eexists; split; eauto.
    cbn.
    repeat straightline.
    eexists; split; eauto.
  }
  {
    eapply Proper_call.
    2:{
      assert ((Memory.anybytes x felem_size_in_bytes ⋆ R) m) as H5.
      {
        admit.
      }
      change (Memory.anybytes x felem_size_in_bytes) with (Placeholder x) in H5.
      seprewrite_in FElem_from_bytes H5.
      sepsimpl.
      eapply H1.
      split.
      2: repeat split; eauto.
      eexists.
      ecancel_assumption.
    }
    intros tr m' ws H'.
    repeat straightline.
    eapply H4.
    refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H9); clear H9.
    cancel.
    intros m''.
    cbn [seps].
    rewrite feval_bytes_as_le_combine in * by auto.
    unfold FElem.
    split; intro; sepsimpl.
    {
      eexists.
      sepsimpl; eauto.
    }
    {
      (*TODO: quantification ordering issue *)
Admitted.

Goal M_pos = Z.to_pos (2^130-5).
reflexivity.
Abort.
  
Definition poly1305 (k : list byte) (m : list byte) : list byte :=
  nlet ["r0"; "r1"; "r2"; "r3"]
    (F.of_Z M_pos (Z.land (le_combine (firstn 16 k)) 0x0ffffffc0ffffffc0ffffffc0fffffff))
    (fun r =>
       let/n t := F.of_Z M_pos 0 in
       let/n t := fold_left (fun (a : F _) n =>
                               (F.add a (F.mul (F.of_Z _ (le_combine(n++[x01]))) r))) (chunk 16 m) t in
       le_split 16 (F.to_Z (F.add t (F.of_Z _ (le_combine (skipn 16 k)))))).

#[global]
  Instance spec_of_poly1305 : spec_of "poly1305" :=
    fnspec! "poly1305" (key_ptr msg_ptr msg_len out_ptr : word) /
          (k msg output : list byte) (*(output : Z (*felem*))*) (R : mem -> Prop),
      { requires tr mem :=
        (Z.of_nat (Datatypes.length k) = 32) /\ (*TODO: all lens*)
          (Z.of_nat (length (chunk 16 msg)) = word.unsigned msg_len) /\ (*TODO: is this the right arg?*)
          (* this avoids some overflow management
        (word.unsigned msg_len < 2 ^ 32 - 15) /\*)
          (array ptsto (word.of_Z 1) key_ptr k ⋆
                 array ptsto (word.of_Z 1) msg_ptr msg ⋆
                 array ptsto (word.of_Z 1) out_ptr output ⋆ R) mem;
        ensures tr' mem' :=
        tr = tr' /\
          (array ptsto (word.of_Z 1) key_ptr k ⋆
             array ptsto (word.of_Z 1) msg_ptr msg ⋆
             (*TODO: use spec version*)
                 array ptsto (word.of_Z 1) out_ptr (poly1305 k msg) ⋆ R) mem }.

(*
Lemma bs2ws_and' (x y : word)
  : word.and x y
    = (word.of_Z (le_combine (map (fun '(x, y)=> byte.and x y) (combine (ChaCha20.le_split 4 x)
                                                                  (ChaCha20.le_split 4 y))))).
Proof.
  unfold ChaCha20.le_split.
  unfold word.and.
  cbn.
  destruct x.
  destruct y.
  f_equal.
  
  simpl.
  unfold word.and.

  Z_land_le_combine*)

(*
Lemma le_combine_and_chunk g (f : byte * byte -> _) (l1 l2 : list byte) n
  : (forall bs1 bs2,  g (le_combine bs1) (le_combine bs2) = le_combine (map f (combine bs1 bs2))) ->
    map le_combine (chunk n (map f (combine l1 l2)))
    = map (fun p => g (fst p) (snd p)) (combine (map le_combine (chunk n l1))
                                          (map le_combine (chunk n l2))).
Proof.
  intro.
  revert l1 l2; induction l1; destruct l2;
    cbn -[word.of_Z]; auto.
Proof.
  rewrite Z_land_le_combine.
 *)
Section List4Ind.
  Context
    (A : Type)
    (P : list A -> Prop)
    (P_nil : P [])
    (P_app : forall l l', length l' = 4%nat -> P l -> P(l'++l)).
      
  
  Fixpoint list_4_ind l
    : length l mod 4 = 0 ->
      P l.
  Proof.
    refine (match l with
            | [] => fun _ => P_nil
            | [_] => fun H => ltac:(now inversion H)
            | [_;_] => fun H => ltac:(now inversion H)
            | [_;_;_] => fun H => ltac:(now inversion H)
            | a::a0::a1::a2::l3 => fun H => P_app l3 [a; a0; a1; a2] eq_refl (list_4_ind l3 _)
            end).
    revert H; clear.
    simpl.
    replace (Z.of_nat (S (S (S (S (length l3)))))) with (4 + (length l3)) by lia.
    rewrite Z.add_mod by lia.
    rewrite Z_mod_same_full.
    simpl.
    rewrite Zmod_mod.
    auto.
  Qed.
End List4Ind.
    

Lemma chunk_map_comm A B (f : A -> B) l
  : length l mod 4 = 0 ->
    chunk 4 (map f l)
    = map (map f) (chunk 4 l).
Proof.
  intro H;
    pose proof H as H'.
  revert H.
  apply list_4_ind with (l:=l);
    intros; eauto.
  {
    revert H1.
    rewrite app_length.
    rewrite H.
    rewrite Nat2Z.inj_add.
    rewrite Z.add_mod by lia.
    rewrite Z_mod_same_full.
    simpl.
    rewrite Zmod_mod.
    intros.
    intuition idtac.
    
    rewrite map_app.
    rewrite !chunk_app; repeat rewrite ?H, ?map_length; try lia; try reflexivity.
    rewrite map_app.
    rewrite !H2.
    f_equal.
    {
      destruct l' as [|? [|? [|? [|]]]]; simpl in *;
        try now inversion H.
      destruct l1; try now inversion H.
    }
  }
Qed.


Lemma map_combine_map {A B C} (g1 g2 : A -> B) (f : B -> B -> C) l1 l2
  : map (fun '(a,b) => f a b) (combine (map g1 l1) (map g2 l2))
    = map (fun '(a,b) => f (g1 a) (g2 b)) (combine l1 l2).
Proof.
  revert l2; induction l1; destruct l2;
    intros; simpl in *;
    eauto.
  f_equal; eauto.
Qed.


Lemma combine_chunk {A} (l1 l2 : list A)
  : length l1 mod 4 = 0 ->
    length l2 = length l1 ->
    (chunk 4 (combine l1 l2))
    = map (fun p => combine (fst p) (snd p)) (combine (chunk 4 l1) (chunk 4 l2)).
Proof.
  intro.
  revert l2;
  apply list_4_ind with (l:=l1);
    intros; eauto.
  rewrite app_length in*.
  rewrite H0 in H2; simpl in H2.
  repeat (destruct l2 as [ | ? l2]; simpl in H2; try lia; []).
  inversion H2; clear H2.
  repeat (destruct l' as [ | ? l']; simpl in H0; try lia; []).
  cbn.
  do 4 f_equal.
  apply H1. auto.
Qed.
  
Lemma bs2ws_and (n:=(Memory.bytes_per (width:=32) access_size.word)) (l1 l2 : list byte)
  : length l1 mod 4 = 0 ->
    length l2 = length l1 ->
    (bs2ws n
        (map (fun '(x, y)=> byte.and x y) (combine l1 l2)))
     = map (fun '(x,y) => word.and (word:=word) x y) (combine (bs2ws n l1) (bs2ws n l2)).
Proof.
  intros.
  unfold bs2ws, bs2zs,zs2ws in *.
  replace n with 4%nat in *.
  2:{
    subst n.
    rewrite <- MakeAccessSizes.bytes_per_word_eq.
    cbn.
    reflexivity.
  }
  rewrite !chunk_map_comm.
  2:{
    rewrite combine_length.
    apply Nat.min_case; eauto.
    congruence.
  }
  {
    rewrite !map_combine_map.
    rewrite !map_map.
    rewrite combine_chunk; eauto.
    rewrite !map_map.
    eapply map_ext.
    intro p; destruct p; cbn -[word.of_Z word.and].
    rewrite <- Z_land_le_combine.
    rewrite word.morph_and.
    reflexivity.
  }
Qed.



(*TODO: generalize to all ops*)

Lemma array_expr_compile_word_and P l vars
  : ∀ (w1 : list word) (e1 : list expr),
    locals_array_expr P l vars e1 w1 ->
    forall e2 w2,
     locals_array_expr P l vars e2 w2 ->
     locals_array_expr P l vars
      (map (λ '(s, t0), (expr.op bopname.and s t0))
         (combine e1 e2))
      (map (λ '(s, t0), (word.and s t0))
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
    eapply expr_compile_word_and; eauto.
  }
Qed.


Derive poly1305_body SuchThat
  (defn! "poly1305" ("k", "msg", "msg_len", "output") ~> "output" { poly1305_body },
    implements (poly1305))
  As poly1305_body_correct.
Proof.
  compile_setup.
  
  simple eapply compile_nlet_as_nlet_eq.
  
  simple eapply compile_set_locals_array
    with (f:=fun l => F.of_Z _ (le_combine(ws2bs (Memory.bytes_per access_size.word) l))).
  {
    replace 0x0ffffffc0ffffffc0ffffffc0fffffff
      with (le_combine (le_split 16 0x0ffffffc0ffffffc0ffffffc0fffffff)).
    2:{
      rewrite le_combine_split.
      reflexivity.
    }
    rewrite Z_land_le_combine.
    f_equal.
    erewrite bs2ws2bs.
    {
      reflexivity.
    }
    
    rewrite map_length.
    rewrite combine_length.
    rewrite firstn_length.
    rewrite length_le_split.
    intuition idtac.
    replace (length k) with 32%nat by lia.
    reflexivity.
  }
  {
    rewrite bs2ws_and by (repeat simplify_len; lia).
    simple eapply array_expr_compile_word_and.
    {
      unfold bs2ws.
      unfold bs2zs.
      unfold zs2ws.
      rewrite map_map.
      simple eapply expr_load_word_of_byte_array.
      2: cbn; reflexivity.
      {
        rewrite firstn_length.
        lia.
      }
      {
        compile_step.
        rewrite <- firstn_skipn with (l:=k) (n:=16%nat) in H4.
        seprewrite_in (@array_append) H4.
        compile_step.
      }
      {
        cbn.
        repeat compile_step.
        repeat rewrite map.remove_not_in by reflexivity.
        simple eapply expr_compile_var with (s:="k").
        compile_step.
      }
    }
    {
      unfold bs2ws.
      unfold bs2zs, zs2ws.
      set (chunk _ _).
      vm_compute in l.
      subst l.
      cbn [map].
      cbn -[word.of_Z].
      repeat constructor; intros; subst.
      all: repeat compile_step.
    }
  }
  { repeat constructor;cbn; intuition congruence. }
  compile_step.
  compile_step.
  (*change (nlet ["t"] (?y 0) ?f) with (nlet ["t"] 0%F (fun t => nlet ["t"] (y t) f)).*)
  (*TODO: want it compiled as an F elem; change spec fn?*)
  change (F.of_Z M_pos 0) with (stack (F.of_Z M_pos 0)).
  compile_step; [ repeat compile_step .. |].
  compile_step.
  compile_step; [ repeat compile_step .. |].
  { admit. (*TODO*) }
  { exact (Some tight_bounds). }
  {
    erewrite word.unsigned_of_Z.
    rewrite word.wrap_small; auto; lia.
  }
  compile_step.
  simple eapply compile_nlet_as_nlet_eq.
  
Ltac _compile_fold_left locals to :=
  let from_v := gensym locals "from" in
  let lp := infer_ranged_for_predicate from_v "msg_len" to in
  eapply compile_scalar_fold_left with (idx_var := from_v) (*(to_var := to_v)*) (loop_pred := lp).
  _compile_fold_left l (word.unsigned msg_len).
  {
    reflexivity.
  }
  {
    unfold acts_as_foldl_step.
    intros.
    replace b with (nth (Z.to_nat idx) (chunk 16 msg) []) by (apply nth_error_nth; eauto).
    1: reflexivity.
  }
  {
    pose proof (Nat.div_up_range (length msg) 16%nat ltac:(lia)).
    pose proof (word.unsigned_range msg_len).
    lia.
  }
  {
    rewrite H3.
    eapply expr_compile_var with (s:= "msg_len").
    {
      cbn [map.putmany_of_list array_locs] in l.
      unfold gs, l.
      repeat compile_step.
    }
  }
  {
    repeat compile_step.
    rewrite H3.
    instantiate (1:= "msg_len").
    repeat compile_step.
  }
  {
    repeat compile_step.
  }
  {
    repeat compile_step.
    rewrite H3.
    repeat compile_step.
  }
  {
    compile_step.
    cbn beta.
    compile_step.
    (*
    TODO: get the nth chunk of msg
    TODO: what is t?
    TODO: msg_len vs gs_to
    rewrite length_chunk by lia.
    unfold Nat.div_up.
    rewrite Nat2Z.inj_div.
    change (Z.of_nat 16) with 16.
    rewrite Nat2Z.inj_add.
    rewrite H3.
    pose proof (word.unsigned_range msg_len).
    rewrite word.morph_divu by lia.
    rewrite word.ring_morph_add by lia.
    change (Z.of_nat (16 - 1)) with 15.
    repeat compile_step.
    eapply expr_compile_var with (s:= "msg_len").
    cbn [map.putmany_of_list ChaCha20.array_locs] in l.
    unfold gs, l.
    repeat rewrite map.get_put_diff by congruence.
    rewrite map.get_put_same.
    reflexivity.
  4:{
    compile_step.
    cbn.
    rewrite <- F.to_Z_of_Z.
    rewrite F.of_Z_mul.
    rewrite F.of_Z_add.
    set (F.of_Z _ (le_combine _)).
    change (F.to_Z _) with
      ( nlet ["x"] f (fun f => F.to_Z ((F.of_Z 1361129467683753853853498429727072845819 a' + f) * F.of_Z 1361129467683753853853498429727072845819 v))).
    change f with (stack f).
    subst f.
    simple eapply compile_nlet_as_nlet_eq.
    simple eapply compile_stack.
    admit.
    intros.
     *)
Abort.
    

(*
Lemma compile_fold_locals_array {t m l e} (lst : list word):
    let v := fold_left f l acc in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl vars lst_expr,
      (*TODO: want to put arbitrary value for everything but current var
        (simplification of actual invariant, which is everything before current var)
        TODO: need to know current var for this
       
      Forall2 (fun e i => forall v',  DEXPR m l e i) lst_expr lst ->
       *)
      Chacha20.locals_array_expr (eq m) l vars lst_expr lst ->
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
          
  simple eapply compile_set_locals_array
    with (f:=fun l => le_combine(ws2bs (Memory.bytes_per access_size.word) l)).
  repeat compile_step.
  
      all: try compile_step.
      {
      
    }
      rewrite H0.
        reflexivity.
      TODO: need to write muliple variables in poly1305 spec2: currently stuck at 'r'
      admit.
      
    TODO: separate version for a direct byte array? unfold bs2ws
    simple eapply ChaCha20.expr_load_word_of_byte_array.
    simple eapply ChaCha20.compile_set_locals_array.
    TODO: bytes-to-words change
    TODO: and compilation lemma
  }
    simpl.
    split.
    2:admit.
    
    TODO: change 16 into 4*4
    change 16 with ((Memory.bytes_per access_size.word)).
    
  TODO: Z vs list; spec is using a larger-than-word Z
- add a layer of indirection in lemma to convert?                                                    
  simple eapply ChaCha20.compile_set_locals_array.


*)
