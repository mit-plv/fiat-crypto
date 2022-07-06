(* Rewritten versions of poly1305 and chacha20 that you can compile with Rupicola *)
Require Import Coq.Unicode.Utf8.
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Loops Rupicola.Lib.Loops.
(*TODO: move this file to Rupicola.Lib*)
Require Import Crypto.Bedrock.End2End.RupicolaCrypto.Broadcast.
Require Import Crypto.Bedrock.End2End.RupicolaCrypto.Spec.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import bedrock2.BasicC32Semantics.
Import Syntax.Coercions ProgramLogic.Coercions.
Import Datatypes.

(* TODO array_split should record a special fact in the context to make it trivial to re-split. *)
Open Scope Z_scope.

(** * Properties missing from coqutil, bedrock2, or Coq's stdlib *)

(** * upd **)

Lemma upd_overflow {A} (l: list A) d n:
  (n >= length l)%nat ->
  upd l n d = l.
Proof.
  intros.
  unfold upd, upds.
  rewrite firstn_all2 by lia.
  rewrite skipn_all2 by lia.
  replace (length l - n)%nat with 0%nat by lia.
  simpl; rewrite app_nil_r; reflexivity.
Qed.

Lemma map_upds {A B} (f: A -> B) : forall l d n,
    upds (map f l) n (map f d) = map f (upds l n d).
Proof.
  unfold upds; intros;
    rewrite !firstn_map, !skipn_map, !map_app, !map_length; reflexivity.
Qed.

Lemma map_upd {A B} (f: A -> B) : forall l d n,
    upd (map f l) n (f d) = map f (upd l n d).
Proof. intros; apply @map_upds with (d := [d]). Qed.

Lemma nth_upd_same {A} (l: list A) (a d: A) (k: nat):
  (k < length l)%nat ->
  nth k (upd l k a) d = a.
Proof.
  unfold upd, upds; intros.
  rewrite app_nth2; rewrite firstn_length_le; auto with arith.
  rewrite Nat.sub_diag.
  replace ((length l - k)%nat) with (S (length l - k - 1)%nat) by lia.
  reflexivity.
Qed.

Lemma nth_upd_diff {A} (l: list A) (a d: A) (i k: nat):
  (i <> k) ->
  nth i (upd l k a) d = nth i l d.
Proof.
  intros; destruct (Nat.lt_ge_cases i (length l)); cycle 1.
  - rewrite !nth_overflow; rewrite ?upd_length; reflexivity || lia.
  - intros; destruct (Nat.lt_ge_cases k (length l)); cycle 1.
    + rewrite upd_overflow by lia. reflexivity.
    +  rewrite upd_firstn_skipn by lia.
       assert (i < k \/ i > k)%nat as [Hlt | Hgt] by lia.
       * rewrite app_nth1; rewrite ?firstn_length; try lia.
         rewrite nth_firstn by lia; reflexivity.
       * rewrite app_nth2; rewrite ?firstn_length; try lia.
         replace (Nat.min k (length l)) with k by lia.
         replace (i - k)%nat with (S (i - k - 1))%nat by lia.
         cbn [nth app].
         rewrite nth_skipn; f_equal; lia.
Qed.

Lemma nth_upd {A} (l: list A) (a d: A) (i k: nat):
  ((i >= length l)%nat /\ nth i (upd l k a) d = d) \/
  (i = k /\ nth i (upd l k a) d = a) \/
  (i <> k /\ nth i (upd l k a) d = nth i l d).
Proof.
  destruct (Nat.lt_ge_cases i (length l)); cycle 1; [ left | right ].
  - unfold upd; rewrite nth_overflow; rewrite ?upds_length; eauto.
  - destruct (Nat.eq_dec i k) as [-> | Heq]; [ left | right ].
    + rewrite nth_upd_same; auto.
    + rewrite nth_upd_diff; auto.
Qed.

Lemma Forall_upd {A} (P: A -> Prop) (l: list A) (a: A) k:
  P a ->
  Forall P l ->
  Forall P (upd l k a).
Proof.
  intros Ha Hl.
  rewrite @Forall_nth_default' with (d := a) in Hl |- *; eauto.
  intros; destruct (nth_upd l a a i k) as [(? & ->) | [ (? & ->) | (? & ->) ] ];
    subst; eauto; eauto.
Qed.

(** ** padding **)

Definition padded_len {A} (l: list A) (m: nat) :=
  (Nat.div_up (length l) m * m)%nat.

Definition padding_len {A} (l: list A) m :=
  (padded_len l m - length l)%nat.

Definition pad (bs: list byte) m :=
  bs ++ repeat x00 (padding_len bs m).

Lemma padding_eqn a b:
  (Nat.div_up a b * b - a =
   if a mod b =? 0 then 0 else b - a mod b)%nat.
Proof.
  destruct (Nat.eq_dec b 0); [subst; destruct (_ =? _)%nat; reflexivity|].
  intros; rewrite Nat.div_up_eqn by lia.
  destruct (Nat.eqb_spec (a mod b) 0); Nat.div_up_t.
Qed.

Lemma padding_len_eqn {T} (l: list T) m:
  padding_len l m = (if length l mod m =? 0 then 0 else m - length l mod m)%nat.
Proof. eauto using padding_eqn. Qed.

Lemma length_padded_mod {A} n (l: list A) a:
  (n <> 0)%nat ->
  (length (l ++ repeat a (Nat.div_up (length l) n * n - length l)) mod n = 0)%nat.
Proof.
  intros; pose proof Nat.div_up_range (length l) n ltac:(eauto).
  rewrite app_length, repeat_length, <- le_plus_minus by lia.
  apply Nat.mod_mul; assumption.
Qed.

(** * Types and operations **)

Definition array_t := List.list.
Definition array_len {T} (a: array_t T) := List.length a.
Definition array_split_at {T} (n: nat) (a: array_t T) :=
  (List.firstn n a, List.skipn n a).
Definition array_unsplit {T} (a1 a2: array_t T) := a1 ++ a2.
Definition array_slice_at {T} (start len: nat) (a: array_t T) :=
  let (before, rest) := array_split_at start a in
  let (middle, after) := array_split_at len rest in
  (before, middle, after).
Definition array_unslice {T} (a1 a2 a3: array_t T) := a1 ++ a2 ++ a3.

Definition array_get {T} (a: array_t T) (n: nat) (d: T) := List.nth n a d.
Definition array_put {T} (a: array_t T) (n: nat) (t: T) := upd a n t.

Definition buffer_t := List.list.
Definition buf_backed_by T (n : nat) (_ : list byte) : buffer_t T := [].
Definition buf_make T (n: nat) : buffer_t T := [].
Definition buf_push {T} (buf: buffer_t T) (t: T) := buf ++ [t].
Definition buf_append {T} (buf: buffer_t T) (arr: array_t T) : buffer_t T := buf ++ arr.
Definition buf_split {T} (buf: buffer_t T) : array_t T * buffer_t T := (buf, []).
Definition buf_unsplit {T} (arr: array_t T) (buf: buffer_t T) : buffer_t T := arr.
Definition buf_as_array {T} (buf: buffer_t T) : list T := buf.
Definition buf_pad {T} (buf: buffer_t T) (len: nat) (t: T) : buffer_t T := buf ++ repeat t (len - length buf).

Require Import bedrock2.NotationsCustomEntry.
Section CompileBufPolymorphic.
  Import ProgramLogic.Coercions WeakestPrecondition.
  Context (e : list Syntax.func).
  Context (T : Type) (sz : word) (pT : word -> T -> mem -> Prop).

  Declare Scope word_scope.
  Delimit Scope word_scope with word.
  Local Infix "+" := word.add : word_scope.
  Local Infix "*" := word.mul : word_scope.

  Local Notation "xs $T@ a" := (array pT sz a%word xs%list) (at level 10, format "xs $T@ a").
  Local Notation "xs $@ a" := (array ptsto (word.of_Z 1) a%word xs%list) (at level 10, format "xs $@ a").
  Implicit Types (t : Semantics.trace) (l : locals) (m : mem) (k : Syntax.cmd).


  Definition buffer_at c b a :=
    (b$T@a *
    (Lift1Prop.ex1 (fun s => emp (sz*length b + length s = sz*c)%Z
    *s$@(a+word.of_Z(sz*length b)))))%sep.

  Local Set Printing Coercions.
  Context (dealloc_T : forall x, exists bs,
    length bs = sz :>Z /\ forall a, Lift1Prop.iff1 (pT a x) (bs$@a)).
  Lemma _dealloc_array_T xs : exists bs, length bs = sz * length xs :>Z
    /\ forall a, Lift1Prop.iff1 (xs$T@a) (bs$@a).
  Proof using dealloc_T.
    induction xs as [|x xs'].
    { exists nil; cbn; split; eauto; rewrite ?Z.mul_0_r; reflexivity. }
    { destruct IHxs' as [bs' [Hlbs' Hbs'] ].
      destruct (dealloc_T x) as [b0s [Hlb0s Hb0s]].
      eexists (b0s++bs'); split.
      { cbn [length].
        rewrite app_length, !Nat2Z.inj_add, Hlb0s.
        rewrite Nat2Z.inj_succ, Z.mul_succ_r, <-Hlbs'.
        rewrite Z.add_comm.
        (*
        Z.of_nat (length bs') + word.unsigned sz =
        Z.of_nat (length bs') + word.unsigned sz
        *)
        lia || (match goal with |- ?g => idtac "WHY does lia fail to solve " g; trivial end). }
      { intros; cbn.
        etransitivity; [eapply Proper_sep_iff1; eauto|]; symmetry.
        etransitivity.
        1:eapply array_append.
        cancel; cbn [seps].
        rewrite word.unsigned_of_Z_1, Z.mul_1_l.
        rewrite <-(word.of_Z_unsigned sz), <-Hlb0s; reflexivity. } }
  Qed.
  Local Unset Printing Coercions.

  Lemma compile_buf_backed_by (n : nat) (bs : list byte) :
    let v := buf_backed_by T n bs in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
           a a_var t m l (R: mem -> Prop),
      (bs$@a * R)%sep m ->
      sz * n = length bs ->
      (let v := v in
       forall m,
         (buffer_at n nil a * R)%sep m ->
         <{ Trace := t; Memory := m; Locals := l; Functions := e }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
      k_impl
      <{ pred (nlet_eq [a_var] v k) }>.
  Proof using Type.
    intros * HA HB HC; eapply HC.
    cbv [buffer_at]; cbn [array]; sepsimpl; trivial; [].
    eexists; sepsimpl; cbn [length]; rewrite Z.mul_0_r, ?Z.add_0_l, ?HB; trivial; [].
    replace a with (word.add a (word.of_Z 0)) in HA by ring; eassumption.
  Qed.

  Lemma compile_buf_as_array (n : nat) elts :
    let v := buf_as_array elts in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
    a a_var t m l (R: mem -> Prop),
      (buffer_at n elts a * R)%sep m ->
      length elts = n ->
      (let v := v in
       forall m,
         (elts$T@a * R)%sep m ->
         <{ Trace := t; Memory := m; Locals := l; Functions := e }>
         k_impl
         <{ pred (k v eq_refl) }> ->
         <{ Trace := t; Memory := m; Locals := l; Functions := e }>
         k_impl
         <{ pred (nlet_eq [a_var] v k) }>).
  Proof using Type.
    intros * HA HB HC HD HE HF. eapply HF; subst n.
  Qed.
  (*
intros * HA HB HC HD; eapply HC; subst n.
    cbv [buffer_at] in HC.
    eapply sep_assoc, sep_comm, sep_assoc, sep_ex1_l  in HA; case HA as [? ?]; sepsimpl.
    destruct x; cbn [length] in *; try lia; cbn [array] in *; sepsimpl.
    ecancel_assumption.
   *)


 Lemma compile_buf_make_stack (n:nat) :
    let v := buf_make T n in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
    a_var t m l (R: mem -> Prop),
      (sz * n) mod Memory.bytes_per_word 32 = 0 ->
      R m ->
      (let v:= v in
       forall a m, (buffer_at n nil a * R)%sep m ->
       <{ Trace := t; Memory := m; Locals := #{ … l; a_var => a }#;
          Functions := e }>
         k_impl
         <{ pred_sep (Lift1Prop.ex1 (fun b => buffer_at n b a))
                      pred (k v eq_refl) }>) ->
    <{ Trace := t; Memory := m; Locals := l; Functions := e }>
      bedrock_func_body:(
      stackalloc (sz*n) as $a_var;
      $k_impl
     )
    <{ pred (nlet_eq [a_var] v k) }>.
  Proof using dealloc_T.
    repeat straightline; split; eauto.
    intros.
    (* straightline_stackalloc with lia for length *)
    pose proof word.unsigned_range sz.
  match goal with
  | Hanybytes:Memory.anybytes ?a ?n ?mStack
    |- _ =>
        let m :=
         match goal with
         | H:map.split ?mCobined ?m mStack |- _ => m
         end
        in
        let mCombined :=
         match goal with
         | H:map.split ?mCobined ?m mStack |- _ => mCobined
         end
        in
        let Hsplit :=
         match goal with
         | H:map.split ?mCobined ?m mStack |- _ => H
         end
        in
        let Hm := multimatch goal with
                  | H:_ m |- _ => H
                  end in
        let Hm' := fresh Hm in
        let Htmp := fresh in
        let Pm := match type of Hm with
                  | ?P m => P
                  end in
        assert_fails
         (idtac;
          match goal with
          | Halready:(Pm ⋆ _$@a) mCombined |- _ => idtac
          end);
          rename Hm into Hm';
         (let stack := fresh "stack" in
          let stack_length := fresh "length_" stack in
          destruct (anybytes_to_array_1 mStack a n Hanybytes)
           as (stack, (Htmp, stack_length));
           epose proof
            (ex_intro _ m (ex_intro _ mStack (conj Hsplit (conj Hm' Htmp)))
             :
             (_ ⋆ _$@a) mCombined) as Hm; clear Htmp;
           try (let m' := fresh m in
                rename
                m into m'); rename mCombined into m;
           assert (length stack = n :> Z) by Lia.lia)
  end.
  repeat straightline.
  eapply Proper_cmd; [eapply Proper_call | intros ? ? ? ? | eapply H1 ]; cbn [app]; eauto; cycle 1.
  { cbv [buffer_at]; cbn.
    sepsimpl; trivial.
    exists stack; cbn.
    rewrite !Z.mul_0_r, !Z.add_0_l.
    replace (a + word.of_Z 0)%word with a; cycle 1.
    { eapply word.unsigned_inj.
      rewrite word.unsigned_add, word.unsigned_of_Z_0, Z.add_0_r.
      symmetry; eapply word.wrap_unsigned. }
    use_sep_assumption; cancel; cbn [seps]; sepsimpl; split; cbv [emp]; intuition eauto. }
  { case H8 as (?&?&?&(?&?)&?).
    cbv [buffer_at] in H9; sepsimpl.
    eapply map.split_comm in H8.
    eexists _, _; split; [|split; [eassumption|] ]; eauto.
    destruct (_dealloc_array_T x1) as [bs [Hlbs Hbs]].
    rename H9 into Hm; seprewrite_in Hbs H11.
    replace (word.of_Z (sz * length x1))%word with
      (word.of_Z (width:=32) (1 * (length bs))) in H11; cycle 1.
    { rewrite Z.mul_1_l. rewrite Hlbs; trivial. }
    pose proof proj2 (array_append _ _ _ _ _ _) H11 as Hmm.
    eapply array_1_to_anybytes in Hmm.
    rewrite app_length, Nat2Z.inj_add, Hlbs, Hm in Hmm; exact Hmm. }
  Qed.


  (*TODO: this is a bit of a hack, is there a better way?*)
  (* This marker is inserted to separate code from different blocks.
     When encountered, rupicola applies compile_skip
   *)
  Definition skip_marker := tt.
  Arguments skip_marker : simpl never.

  Notation skip_and_then k := (nlet_eq [] skip_marker (fun _ _ => k)).


  Lemma compile_buf_append {t m l} var ax_expr arr_var
        (buf : buffer_t T) (arr : array_t T) (c : Z) (buf_ptr : word) :
    let v := buf_append buf arr in
    let offset := word.of_Z (sz * length buf) in
    let ax := word.add buf_ptr offset in
    (*TODO: need var_app notin l?
      Probably not, but should be checked
     *)
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) fill_impl k_impl R,
      (buffer_at c buf buf_ptr * R)%sep m ->
      DEXPR m l ax_expr ax ->
      (length buf + length arr <= c) ->
      (let v := v in
       forall (uninit : list Init.Byte.byte) (Rbuf : mem -> Prop) m',
         (array pT sz buf_ptr buf ⋆ array ptsto (word.of_Z 1) ax uninit ⋆ Rbuf ⋆ R) m' ->
         Z.of_nat (length uninit) = sz * length arr ->
         let FillPred prog t m l :=
           (array pT sz buf_ptr buf ⋆ array pT sz ax arr ⋆ Rbuf ⋆ R) m /\
             (forall m', (buffer_at c (buf++arr) buf_ptr * R)%sep m' ->
              <{ Trace := t; Memory := m'; Locals := (map.remove l arr_var); Functions := e }>
                k_impl
              <{ pred prog }>) in
         <{ Trace := t; Memory := m'; Locals := map.put l arr_var ax; Functions := e }>
           fill_impl
         <{ FillPred (nlet_eq [arr_var] arr
                      (fun _ _ => skip_and_then (k v eq_refl))) }>) ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
        bedrock_func_body:($arr_var = $ax_expr;
                           $fill_impl;
                           $(cmd.unset arr_var);
                           $k_impl
                          )
                          <{ pred (nlet_eq [var] v k) }>.
  Proof using Type.
    repeat straightline.
    eexists; split; eauto.
    repeat straightline.
    unfold buffer_at in *.
    eapply sep_comm, sep_assoc, sep_comm in H; sepsimpl.
    rename x into pad.
    rewrite <-(firstn_skipn (Z.to_nat sz * length arr) pad) in H3.
    seprewrite_in @bytearray_append H3.
    unfold nlet_eq in H2.
    eapply Proper_cmd; [eapply Proper_call| |eapply H2].
    2: ecancel_assumption.
    2: {
      pose proof word.unsigned_range sz.
      rewrite firstn_length; nia. }
    intros t1 m1 l1 [Hm Hk].
    repeat straightline.
    eapply Hk; clear Hk.
    seprewrite open_constr:(array_append _ _ buf arr).
    rewrite app_length, Nat2Z.inj_add, Z.mul_add_distr_l.

    sepsimpl. eexists. sepsimpl; cycle 1.
    1: { use_sep_assumption. cancel; repeat ecancel_step.
      f_equiv. f_equiv. f_equal.
      rewrite firstn_length, word.ring_morph_add, word.add_assoc.
      f_equal; f_equal.
      pose proof word.unsigned_range sz.
      nia. }
    { pose proof word.unsigned_range sz.
      rewrite skipn_length.
      nia. }
  Qed.


  Lemma compile_buf_push {t m l} var ax_expr arr_var
        (buf : buffer_t T) (x : T) (c : Z) (buf_ptr : word) :
    let v := buf_push buf x in
    let offset := (word.of_Z (word.unsigned sz * Z.of_nat (Datatypes.length buf))) in
    let ax := word.add buf_ptr offset in
    (*TODO: need var_app notin l?
      Probably not, but should be checked
     *)
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) fill_impl k_impl R,
      (buffer_at c buf buf_ptr * R)%sep m ->
      DEXPR m l ax_expr ax ->
      (length buf + 1 <= c) ->
      (let v := v in
       forall (uninit : list Init.Byte.byte) (Rbuf : mem -> Prop) m',
         (array pT sz buf_ptr buf ⋆ uninit$@ax ⋆ Rbuf ⋆ R) m' ->
         Z.of_nat (length uninit) = sz ->
         let FillPred prog t m l :=
           (array pT sz buf_ptr buf ⋆ pT ax x ⋆ Rbuf ⋆ R) m /\
             (forall m', (buffer_at c (buf++[x]) buf_ptr * R)%sep m' ->
              <{ Trace := t; Memory := m'; Locals := (map.remove l arr_var); Functions := e }>
                k_impl
              <{ pred prog }>) in
         <{ Trace := t; Memory := m'; Locals := map.put l arr_var ax; Functions := e }>
           fill_impl
         <{ FillPred (nlet_eq [arr_var] x
                      (fun _ _ => skip_and_then (k v eq_refl))) }>) ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
        bedrock_func_body:($arr_var = $ax_expr;
                           $fill_impl;
                           $(cmd.unset arr_var);
                           $k_impl
                          )
                          <{ pred (nlet_eq [var] v k) }>.
  Proof using dealloc_T.
    intros.  eapply compile_buf_append with (arr:=[x]).
    { ecancel_assumption. }
    all: try eassumption.
    intros.
    eapply Proper_cmd;
      [eapply Proper_call| |eapply H2].
    2:{ ecancel_assumption. }
    2:{ cbn [length] in *; lia. }
    intros t1 m1 l1 [Hm Hk].
    cbv [nlet_eq] in *.
    cbn [array] in *.
    split; sepsimpl.
    {
      ecancel_assumption.
    }
    eapply Hk.
  Qed.

  Lemma compile_buf_split {t m l} (n : nat) (bs : buffer_t T) :
    let v := buf_split bs in
    let offset := (word.of_Z (word.unsigned sz * Z.of_nat (length bs))) in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
           c a a_var b_var  R,
      let b := word.add a offset in
      (buffer_at c bs a * R)%sep m ->
      sz * n = length bs ->
      (let v := v in
       forall m,
         (bs$T@a * buffer_at (c - length bs) nil b * R)%sep m ->
         <{ Trace := t; Memory := m; Locals := l; Functions := e }>
           k_impl
         <{ pred (k v eq_refl) }>) ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
        k_impl
      <{ pred (nlet_eq [a_var; b_var] v k) }>.
  Proof using Type.
    intros * HA HB HC; eapply HC; clear HC.
    unfold buffer_at in *.
    cbn [array]; sepsimpl; trivial; [].

    refine (subrelation_refl Lift1Prop.impl1 _ _ _ m HA).
    cancel.
    eapply Proper_sep_impl1; [intro; tauto|].
    eapply Proper_sep_impl1; [|intro; tauto].
    eapply Lift1Prop.Proper_ex1_impl1.
    intro bs'.
    cbn [length].
    clear.
    intros m H.
    sepsimpl.
    lia.
    rewrite Z.mul_0_r.
    rewrite (Radd_comm word.ring_theory); eauto.
    rewrite (Radd_0_l word.ring_theory);eauto.
  Qed.


  Lemma compile_buf_unsplit {t m l} (n : nat) (a : array_t T) (bs : buffer_t T) :
    let v := buf_unsplit a bs in
    forall offset lenbs (*quantified for better sep condition resolution*),
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
           c a var  R,
      let b := word.add a offset in
      (bs$T@a * buffer_at (c - lenbs) nil b * R)%sep m ->

      lenbs = length bs ->
      offset = (word.of_Z (word.unsigned sz * Z.of_nat (length bs))) ->
      sz * n = length bs ->
      (let v := v in
       forall m,
         (buffer_at c bs a * R)%sep m ->
         <{ Trace := t; Memory := m; Locals := l; Functions := e }>
           k_impl
         <{ pred (k v eq_refl) }>) ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
        k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof using Type.
    intros * HA Hlen Hoff HB HC; eapply HC; clear HC.
    subst lenbs offset.
    unfold buffer_at in *.
    cbn [array]; sepsimpl; trivial; [].

    refine (subrelation_refl Lift1Prop.impl1 _ _ _ m HA).
    eapply Proper_sep_impl1; [|intro; tauto].
    eapply Proper_sep_impl1; [ intro; tauto|].

    intros m' H.
    sepsimpl.
    exists x.
    cbn [length] in *.
    sepsimpl; [lia |].
    subst b.
    lazymatch goal with
    | [H : (?x$@?ptr1 * ?P)%sep ?m|- (?x$@?ptr2) ?m] =>
        replace ptr2 with ptr1;[ecancel_assumption_impl|]
    end.
    rewrite <- word.add_assoc.
    rewrite <- !word.ring_morph_add.
    f_equal.
    f_equal.
    lia.
  Qed.

  (*Only included to support the byte and word lemmas below. Do not use.*)
  Section Deprecated.
    Local Lemma deprecated_do_not_use_compile_buf_append {t m l} var (buf : buffer_t T) (arr : array_t T) (c : Z) (a : word) :
    let v := buf_append buf arr in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) fill_impl k_impl R,
    (buffer_at c buf a * R)%sep m ->
    (length buf + length arr <= c) ->
    (forall uninit Rbuf,
      let ax := (a + word.of_Z (sz * length buf))%word in
      (array pT sz a buf * uninit$@ax * Rbuf * R)%sep m ->
      length uninit = sz * length arr :>Z ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
        fill_impl
        <{ nlet_eq [append var "_app"] arr (fun arr _ t m l =>
          (array pT sz a buf * arr$T@ax * Rbuf * R)%sep m /\ (
          (buffer_at c (buf++arr) a * R)%sep m ->
          <{ Trace := t; Memory := m; Locals := l; Functions := e }>
            k_impl
          <{ pred (k v eq_refl) }> )) }> ) ->
    <{ Trace := t; Memory := m; Locals := l; Functions := e }>
      bedrock_cmd:($fill_impl; $k_impl)
    <{ pred (nlet_eq [var] v k) }>.
  Proof using Type.
    repeat straightline.
    unfold buffer_at in *.
    eapply sep_comm, sep_assoc, sep_comm in H; sepsimpl.
    rename x into pad.
    rewrite <-(firstn_skipn (Z.to_nat sz * length arr) pad) in H2.
    seprewrite_in @bytearray_append H2.
    eapply Proper_cmd; [eapply Proper_call| |eapply H1].
    2: ecancel_assumption.
    2: {
      pose proof word.unsigned_range sz.
      rewrite firstn_length; nia. }
    intros t1 m1 l1 [Hm Hk]; eapply Hk; clear Hk.
    seprewrite open_constr:(array_append _ _ buf arr).
    rewrite app_length, Nat2Z.inj_add, Z.mul_add_distr_l.
    sepsimpl. eexists. sepsimpl; cycle 1.
    1: { use_sep_assumption. cancel; repeat ecancel_step.
      f_equiv. f_equiv. f_equal.
      rewrite firstn_length, word.ring_morph_add, word.add_assoc.
      f_equal; f_equal.
      pose proof word.unsigned_range sz.
      nia. }
    { pose proof word.unsigned_range sz.
      rewrite skipn_length.
      nia. }
  Qed.

  Lemma deprecated_do_not_use_compile_buf_push {t m l} var (buf : buffer_t T) (x : T) (c : Z) (a : word) :
    let v := buf_push buf x in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) fill_impl k_impl R,
    (buffer_at c buf a * R)%sep m ->
    (length buf + 1 <= c) ->
    (forall uninit Rbuf,
      let ax := (a + word.of_Z (sz * length buf))%word in
      (array pT sz a buf * uninit$@ax * Rbuf * R)%sep m ->
      length uninit = sz :>Z ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
        fill_impl
        <{ nlet_eq [append var "_app"] x (fun arr _ t m l =>
          (array pT sz a buf * pT ax x * Rbuf * R)%sep m /\ (
          (buffer_at c (buf++[x]) a * R)%sep m ->
          <{ Trace := t; Memory := m; Locals := l; Functions := e }>
            k_impl
          <{ pred (k v eq_refl) }> )) }> ) ->
    <{ Trace := t; Memory := m; Locals := l; Functions := e }>
      bedrock_cmd:($fill_impl; $k_impl)
    <{ pred (nlet_eq [var] v k) }>.
  Proof using dealloc_T.
    intros.  eapply deprecated_do_not_use_compile_buf_append with (arr:=[x]).  {
    ecancel_assumption. } { eassumption. } intros.  eapply Proper_cmd;
    [eapply Proper_call| |eapply H1].  2:{ ecancel_assumption. } 2:{ cbn
  [length] in *; lia. } intros t1 m1 l1 [Hm Hk].  cbv [nlet_eq] in *.  cbn
  [array] in *.  split; sepsimpl.  { ecancel_assumption. } eapply Hk.  Qed.
  End Deprecated.

  (* TODO: where best to put this? *)
  Definition copy {T} (x : T) := x.

  Lemma firstn_extend {A} `{HasDefault A} (l1 : list A) z
    :0 <= z < length l1 ->
     (firstn (Z.to_nat z) l1 ++ [Arrays.ListArray.get l1 z])
     = firstn (Z.to_nat (z + 1)) l1.
  Proof using Type.
    unfold Arrays.ListArray.get.
    unfold cast, Convertible_Z_nat.
    intros.
    replace ((Z.to_nat (z + 1))) with (S (Z.to_nat z)) by lia.
    erewrite ListUtil.firstn_succ by lia.
    do 2 f_equal.
    rewrite nth_default_eq.
    reflexivity.
  Qed.


  Local Lemma memcpy_helper (l1 l2 : list word) z len
    : len = length l1 ->
      len = length l2 ->
      len <= 2^32 ->
      0 <= z <= len ->
      snd
        (Loops.foldl
           (λ (acc : Loops.ExitToken.t * Arrays.ListArray.t word) (idx : Z),
             let/n v as "v" := Arrays.ListArray.get l1 (word.of_Z (word:=word) idx) in
             let/n a2 as "a2" := Arrays.ListArray.put (snd acc) (word.of_Z (word:=word) idx) v in
             (false, a2))
           (λ tok_acc : Loops.ExitToken.t * Arrays.ListArray.t word,
               Loops.ExitToken.get (fst tok_acc)) (Loops.z_range z len)
           (false, firstn (Z.to_nat z) l1 ++ skipn (Z.to_nat z) l2)) = l1.
  Proof using Type.
    intros Hlen1 Hlen2 Hlen_bound Hz.
    remember (Loops.z_range z len) as lst.
    revert z Hz Heqlst.
    induction lst.
    {
      intros.
      destruct (Z.eq_dec z len).
      {
        subst z.
        simpl.
        rewrite Hlen1 at 1.
        rewrite Hlen2 at 1.
        rewrite !Nat2Z.id.
        rewrite firstn_all, skipn_all.
        rewrite app_nil_r.
        reflexivity.
      }
      {
        exfalso.
        assert (z < len) by lia.
        rewrite Loops.z_range_cons in Heqlst by auto.
        inversion Heqlst.
      }
    }
    {
      intros.
      destruct (Z.eq_dec z len).
      {
        exfalso.
        subst.
        rewrite Loops.z_range_nil in Heqlst by lia.
        inversion Heqlst.
      }
      {
        unfold nlet in *.
        rewrite Loops.z_range_cons in Heqlst by lia.
        inversion Heqlst; subst.
        set (tmp := word.of_Z).
        simpl; subst tmp.
        rewrite Arrays.ListArray.put_app_len.
        {
          change (?e ++ ?a::?e') with (e++[a]++e').
          rewrite app_assoc.
          replace (Arrays.ListArray.get l1 (word.of_Z (word:=word) z))
            with (Arrays.ListArray.get l1 z).
          {
            rewrite firstn_extend.
            rewrite tl_skipn.
            replace (S (Z.to_nat z)) with (Z.to_nat (z + 1)) by lia.
            eapply IHlst; eauto.
            all: try lia.
            split; try lia.
            destruct Hz.
            destruct (Z.le_gt_cases (length l1) z); try lia; auto.
          }
          {
            unfold Arrays.ListArray.get.
            unfold cast, Convertible_word_nat, Convertible_Z_nat.
            rewrite word.unsigned_of_Z.
            rewrite word.wrap_small by lia.
            reflexivity.
          }
        }
        {
          rewrite skipn_length.
          change  (@Naive.rep 32) with (@word.rep 32 word).
          lia.
        }
        {
          unfold cast, Convertible_word_nat, Convertible_Z_nat.
          rewrite firstn_length.
          rewrite Nat.min_l; try lia.
          rewrite word.unsigned_of_Z.
          rewrite word.wrap_small by lia; auto.
          change (@Naive.rep 32) with (@word.rep 32 word).
          erewrite <- (Nat2Z.id (length l1)).
          apply Z2Nat.inj_le; lia.
        }
      }
    }
  Qed.


  Lemma memcpy_identity (l1 l2 : list word) len
    : word.unsigned len = length l1 ->
      word.unsigned len = length l2 ->
      list_memcpy len l1 l2 = (l1, l1).
  Proof using Type.
    unfold list_memcpy, Loops.ranged_for_u, Loops.ranged_for_w.
    unfold Loops.w_body_tok.
    rewrite <- Loops.nd_as_ranged_for.
    unfold Loops.nd_ranged_for, Loops.nd_ranged_for', Loops.nd_ranged_for_break,
      Loops.ExitToken.new.
    unfold nlet at 1.
    intro Hlen.
    f_equal.
    revert l1 l2 Hlen.
    pose proof (word.unsigned_range len) as H'; revert H'.
    generalize (word.unsigned len).
    intros z z_gt_0.
    rewrite <- (Z2Nat.id z); [|lia].
    assert (z = Z.to_nat z) by lia.
    rewrite H in z_gt_0.
    revert z_gt_0.
    clear H.
    generalize (Z.to_nat z).
    clear z.


    intros.

    f_equal.
    replace l2 with (firstn (Z.to_nat 0) l1 ++ skipn (Z.to_nat 0) l2).
    rewrite <- (word.unsigned_of_Z_nowrap ((Z.of_nat n))).
    rewrite word.unsigned_of_Z_0.
    erewrite <- (memcpy_helper l1) at 2.
    repeat f_equal; eauto.
    rewrite !word.unsigned_of_Z.
    rewrite word.wrap_small by auto.
    all: eauto.
    rewrite Hlen in H.
    apply Nat2Z.inj; auto.
    lia.
    lia.
  Qed.

Lemma compile_byte_memcpy (n : nat) (bs bs2 : list byte) :
    let v := copy bs in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
           len a a2 len_expr a_expr a2_var t m l (R: mem -> Prop),

      map.get l a2_var = Some a2 ->

      (bs$@a * bs2$@a2 * R)%sep m ->

      spec_of_unsizedlist_memcpy e ->


      (word.unsigned len) * 4 = Z.of_nat (List.length bs) ->
      (word.unsigned len) * 4 = Z.of_nat (List.length bs2) ->

      DEXPR m l a_expr a ->
      DEXPR m l len_expr len ->

      (let v := v in
       forall m,
         (bs$@a * bs$@a2 * R)%sep m ->
         <{ Trace := t; Memory := m; Locals := l; Functions := e }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
      cmd.seq
        (cmd.call [] "unsizedlist_memcpy"
                  [len_expr; a_expr; expr.var a2_var])
        k_impl
      <{ pred (nlet_eq [a2_var] v k) }>.
  Proof using Type.
    repeat straightline.
    exists [len; a; a2]; split.
    {
      cbv [dexprs list_map list_map_body].
      repeat (eapply WeakestPrecondition_dexpr_expr; eauto).
      eapply expr_compile_var; auto.
    }
    eapply Proper_call; cycle -1.
    eapply H1; cycle 2.
    {
      cbv [Arrays.listarray_value
             Arrays.ai_width
             Arrays.ai_repr
             Arrays.ai_size
             Arrays._access_info
             Memory.bytes_per
             Memory.bytes_per_word].
      change (BinIntDef.Z.to_nat ((32 + 7) / 8) : Z) with 4%Z.
      seprewrite_in @ArrayCasts.truncated_scalars_of_bytes H0; cycle 1.
      seprewrite_in @ArrayCasts.truncated_scalars_of_bytes H0; cycle 1.


      unfold scalar.
      change (word.of_Z 4) with (word.of_Z (word:=word) (Memory.bytes_per (width:=32) access_size.word)).

      refine (subrelation_refl Lift1Prop.impl1 _ _ _ m H0).
      cancel.
      cancel_seps_at_indices_by_implication 1%nat 0%nat.
      {
        intros m' H'.
        eapply ArrayCasts.truncated_words_of_truncated_scalars in H'.
        exact H'.
      }
      eapply Proper_sep_impl1.
      {
        intros m' H'.
        eapply ArrayCasts.truncated_words_of_truncated_scalars in H'.
        exact H'.
      }
      exact (fun m H => H).
      all:cbv [Arrays.listarray_value
             Arrays.ai_width
             Arrays.ai_repr
             Arrays.ai_size
             Arrays._access_info
             Memory.bytes_per
             Memory.bytes_per_word];
        change (BinIntDef.Z.to_nat ((32 + 7) / 8)) with 4%nat.
      1:pose proof (Nat2Z.inj_mod (length bs2) 4).
      2:pose proof (Nat2Z.inj_mod (length bs) 4).
      all: nia.
    }
    (*OK*)
    {
      cbv [Arrays.listarray_value
             Arrays.ai_width
             Arrays.ai_repr
             Arrays.ai_size
             Arrays._access_info
             Memory.bytes_per
             Memory.bytes_per_word];
      change (BinIntDef.Z.to_nat ((32 + 7) / 8)) with 4%nat.
      rewrite ArrayCasts.zs2ws_length.
      rewrite ArrayCasts.bs2zs_length; try nia.
      2:pose proof (Nat2Z.inj_mod (length bs) 4); nia.
      rewrite Nat2Z.inj_div.
      nia.
    }
    {
      cbv [Arrays.listarray_value
             Arrays.ai_width
             Arrays.ai_repr
             Arrays.ai_size
             Arrays._access_info
             Memory.bytes_per
             Memory.bytes_per_word];
      change (BinIntDef.Z.to_nat ((32 + 7) / 8)) with 4%nat.
      rewrite ArrayCasts.zs2ws_length.
      rewrite ArrayCasts.bs2zs_length; try nia.
      2:pose proof (Nat2Z.inj_mod (length bs2) 4); nia.
      rewrite Nat2Z.inj_div.
      nia.
    }
    (*OK*)
    intros t' m' l' H'.
    intuition subst.
    exists l; intuition.


    eapply H6.
    revert H10.
    rewrite !memcpy_identity.
    {
      set (tmp := word.of_Z).
      simpl; subst tmp.
      cbv [Arrays.listarray_value
             Arrays.ai_width
             Arrays.ai_repr
             Arrays.ai_size
             Arrays._access_info
             Memory.bytes_per
             Memory.bytes_per_word
             Pos.to_nat Pos.iter_op Init.Nat.add].
      eapply Proper_sep_impl1; [| exact (fun _ x => x)].
      intros m'' H''.
      refine (subrelation_refl Lift1Prop.impl1 _ _ _ m'' H'').
      eapply Proper_sep_impl1.
      {
        clear m' m'' H''.
        intros m'' H''.
        eapply (ArrayCasts.words_of_bytes a bs); eauto.
        {
          cbn.
          cbv [Arrays.listarray_value
                 Arrays.ai_width
                 Arrays.ai_repr
                 Arrays.ai_size
                 Arrays._access_info
                 Memory.bytes_per
                 Memory.bytes_per_word
                 Pos.to_nat Pos.iter_op Init.Nat.add].
          eapply Nat.div_exact; try lia.
          eapply Nat2Z.inj.
          rewrite <- (Nat2Z.id (length bs)) at 2.
          rewrite <- !H2.
          rewrite Z2Nat.inj_mul; try lia.
          change (Z.to_nat 4) with 4%nat.
          rewrite Nat.div_mul.
          lia.
          lia.
        }
      }
      {
        clear m' m'' H''.
        intros m'' H''.
        eapply (ArrayCasts.words_of_bytes a2 bs); eauto.
        {
          cbn.
          cbv [Arrays.listarray_value
                 Arrays.ai_width
                 Arrays.ai_repr
                 Arrays.ai_size
                 Arrays._access_info
                 Memory.bytes_per
                 Memory.bytes_per_word
                 Pos.to_nat Pos.iter_op Init.Nat.add].
          eapply Nat.div_exact; try lia.
          eapply Nat2Z.inj.
          rewrite <- (Nat2Z.id (length bs)) at 2.
          rewrite <- !H2.
          rewrite Z2Nat.inj_mul; try lia.
          change (Z.to_nat 4) with 4%nat.
          rewrite Nat.div_mul.
          lia.
          lia.
        }
      }
    }
    all: rewrite !ArrayCasts.zs2ws_length.
    all: rewrite !ArrayCasts.bs2zs_length.
    all: cbn;
          cbv [Arrays.listarray_value
                 Arrays.ai_width
                 Arrays.ai_repr
                 Arrays.ai_size
                 Arrays._access_info
                 Memory.bytes_per
                 Memory.bytes_per_word
                 Pos.to_nat Pos.iter_op Init.Nat.add].
    all: try lia.
    {
      assert (length bs = (Z.to_nat len * 4)%nat) as H7 by lia.
      rewrite H7.
      rewrite Nat.div_mul; lia.
    }
    {
      assert (length bs = (Z.to_nat len * 4)%nat) as H7 by lia.
      rewrite H7.
      rewrite Nat.mod_mul; lia.
    }
    {
      assert (length bs2 = (Z.to_nat len * 4)%nat) as H7 by lia.
      rewrite H7.
      rewrite Nat.div_mul; lia.
    }
    {
      assert (length bs2 = (Z.to_nat len * 4)%nat) as H7 by lia.
      rewrite H7.
      rewrite Nat.mod_mul; lia.
    }
  Qed.

End CompileBufPolymorphic.

Ltac compile_buf_append:=
  lazymatch goal with
  | [ |- WeakestPrecondition.cmd _ _ _ _ ?locals (_ (nlet_eq [?var] ?v _)) ] =>
      let arr_var_str := gensym locals constr:((var++"_app")%string) in
      simple eapply compile_buf_append with (arr_var:=arr_var_str)
  end.


Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (buf_append _ _) _))) =>
       compile_buf_append; shelve : compiler.

Section CompileBufByte.
  Context (e : list Syntax.func).
  Context (T := byte) (sz : word := word.of_Z 1) (pT := ptsto(map:=mem)).

  Declare Scope word_scope.
  Delimit Scope word_scope with word.
  Local Infix "+" := word.add : word_scope.
  Local Infix "*" := word.mul : word_scope.

  Local Notation "xs $T@ a" := (array pT sz a%word xs%list) (at level 10, format "xs $T@ a").
  Local Notation "xs $@ a" := (array ptsto (word.of_Z 1) a%word xs%list) (at level 10, format "xs $@ a").
  Implicit Types (t : Semantics.trace) (l : locals) (m : mem) (k : Syntax.cmd).

  Local Notation buffer_at := (@buffer_at T sz pT).

  Lemma compile_buf_push_byte {t m l} var buf_expr len_expr x_expr (buf : buffer_t T) (x : T) (c : Z) (a : word) :
    let v := buf_push buf x in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl R,
    (buffer_at c buf a * R)%sep m ->
    (length buf + 1 <= c) ->

    WeakestPrecondition.dexpr m l buf_expr a ->
    WeakestPrecondition.dexpr m l len_expr (word.of_Z (length buf)) ->
    WeakestPrecondition.dexpr m l x_expr (word.of_Z (byte.unsigned x)) ->

    let ax := (a + word.of_Z (sz * length buf))%word in
    (forall m,
      (buffer_at c (buf++[x]) a * R)%sep m ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
        k_impl
      <{ pred (k v eq_refl) }>) ->
    <{ Trace := t; Memory := m; Locals := l; Functions := e }>
      bedrock_cmd:(store1($buf_expr+$len_expr, $x_expr); $k_impl)
    <{ pred (nlet_eq [var] v k) }>.
  Proof using Type.
    intros.
    eapply deprecated_do_not_use_compile_buf_push with (pT := pT) (sz:=sz).
    { clear. subst pT; subst sz. intros x.
      eexists (cons _ nil); split; eauto. intros. cbn [array]. ecancel. }
    { ecancel_assumption. }
    { eassumption. }
    repeat straightline.
    eexists.
    eexists.
    { repeat straightline.
      eapply WeakestPrecondition_dexpr_expr; eauto.
      eapply WeakestPrecondition_dexpr_expr; eauto. }
    eexists.
    split.
    { eapply WeakestPrecondition_dexpr_expr; eauto. }
    subst sz.
    rewrite word.unsigned_of_Z_1 in H6.
    eapply (f_equal Z.to_nat) in H6; rewrite Nat2Z.id in H6. (* handle injection *)
    destruct uninit as [|? []]; try solve [inversion H6]; []. subst pT ax0.
    rewrite word.unsigned_of_Z_1, Z.mul_1_l in H5.
    cbn [array] in *; seprewrite_in @sep_emp_True_r H5.
    eapply store_one_of_sep.
    { ecancel_assumption. }
    intros.
    cbv [nlet_eq].
    split.
    rewrite to_byte_of_byte_nowrap in H7.
    { rewrite word.unsigned_of_Z_1, Z.mul_1_l.
      ecancel_assumption. }
    eauto.
  Qed.


 (*Specialized to bytes.
   TODO: necessary?
  *)
 Lemma compile_buf_make_stack_bytes (n:nat) :
    let v := buf_make byte n in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
    a_var t m l (R: mem -> Prop),
      (sz * n) mod Memory.bytes_per_word 32 = 0 ->
      R m ->
      (let v:= v in
       forall a m, (buffer_at n nil a * R)%sep m ->
       <{ Trace := t; Memory := m; Locals := #{ … l; a_var => a }#;
          Functions := e }>
         k_impl
         <{ pred_sep (Lift1Prop.ex1 (fun b => buffer_at n b a))
                      pred (k v eq_refl) }>) ->
    <{ Trace := t; Memory := m; Locals := l; Functions := e }>
      bedrock_func_body:(
      stackalloc (sz*n) as $a_var;
      $k_impl
     )
    <{ pred (nlet_eq [a_var] v k) }>.
  Proof using Type.
    intros; eapply compile_buf_make_stack; eauto.
    intro x; exists [x]; intuition (try lia).
    unfold pT.
    cbn [array].
    split; intro; ecancel_assumption.
  Qed.
End CompileBufByte.

Section CompileBufWord32.
  Context (e : list Syntax.func).
  Context (T := word) (sz : word := word.of_Z 4) (pT := scalar32(word:=word)).

  Declare Scope word_scope.
  Delimit Scope word_scope with word.
  Local Infix "+" := word.add : word_scope.
  Local Infix "*" := word.mul : word_scope.

  Local Notation "xs $T@ a" := (array pT sz a%word xs%list) (at level 10, format "xs $T@ a").
  Local Notation "xs $@ a" := (array ptsto (word.of_Z 1) a%word xs%list) (at level 10, format "xs $@ a").
  Implicit Types (t : Semantics.trace) (l : locals) (m : mem) (k : Syntax.cmd).

  Local Notation buffer_at := (@buffer_at T sz pT).

  Lemma compile_buf_push_word32 {t m l} var buf_expr len_expr x_expr (buf : buffer_t T) (x : T) (c : Z) (a : word) :
    let v := buf_push buf x in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl R,
    (buffer_at c buf a * R)%sep m ->
    (length buf + 1 <= c) ->

    WeakestPrecondition.dexpr m l buf_expr a ->
    WeakestPrecondition.dexpr m l len_expr (word.of_Z (length buf)) ->
    WeakestPrecondition.dexpr m l x_expr x ->

    let ax := (a + word.of_Z (sz * length buf))%word in
    (let v := v in
      forall m,
      (buffer_at c v a * R)%sep m ->
      <{ Trace := t; Memory := m; Locals := l; Functions := e }>
        k_impl
      <{ pred (k v eq_refl) }>) ->
    <{ Trace := t; Memory := m; Locals := l; Functions := e }>
      bedrock_cmd:(store($buf_expr+$len_expr<<$2,$x_expr); $k_impl)
    <{ pred (nlet_eq [var] v k) }>.
  Proof using Type.
    intros.
    eapply deprecated_do_not_use_compile_buf_push with (pT := pT) (sz:=sz).
    { clear. subst pT; subst sz. intros x.
      unfold scalar32, truncated_word, truncated_scalar, littleendian, ptsto_bytes.ptsto_bytes.
      rewrite HList.tuple.to_list_of_list.
      eexists.
      split.
      2:intros; reflexivity.
      reflexivity. }
    { ecancel_assumption. }
    { eassumption. }
    repeat straightline.
    eexists.
    eexists.
    { repeat straightline.
      eapply WeakestPrecondition_dexpr_expr; eauto.
      eapply WeakestPrecondition_dexpr_expr; eauto.
      cbn.
      eapply WeakestPrecondition_dexpr_expr; eauto.
      eexists. }
    eexists.
    split.
    { eapply WeakestPrecondition_dexpr_expr; eauto. }
    seprewrite_in @scalar32_of_bytes H5; trivial.
    { subst sz. rewrite word.unsigned_of_Z in H6.
      rewrite word.wrap_small in H6; lia. }
    eapply store_four_of_sep.
    { subst ax0. subst sz.
      rewrite Z.mul_comm, <-(Z.shiftl_mul_pow2 _ 2), word.morph_shiftl  in H5 by lia.
      ecancel_assumption. }
    intros.
    cbv [nlet_eq].
    split.
    { subst ax0. subst sz.
      use_sep_assumption.
      cancel. subst pT. f_equiv. f_equal. f_equal. f_equal.
      rewrite <-word.morph_shiftl, word.unsigned_of_Z, word.wrap_small by lia.
      rewrite Z.shiftl_mul_pow2, Z.mul_comm by lia. reflexivity. }
    eauto.
  Qed.
End CompileBufWord32.



Definition p : positive := 2^130 - 5.
Definition felem_init_zero : F p := 0.
Definition bytes_as_felem_inplace (bs: list byte) : F p :=
  F.of_Z _ (le_combine bs).
Definition felem_as_uint128 (z : F p) : Z := (F.to_Z z) mod 2 ^ 128.

Definition uint128_add z1 z2 : Z :=
  (z1 + z2) mod 2 ^ 128.
Definition uint128_as_bytes (z: Z) :=
  le_split 16 z.
Definition bytes_as_uint128 (bs: list byte) :=
  le_combine bs.

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
Instance p_field_representation : FieldRepresentation := field_representation 5 (2^130) [(1,5)].

(*Set Printing All.*)

Lemma compile_bytes_as_felem_inplace elts :
  let v := bytes_as_felem_inplace elts in
  forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
         a (a_var : string) t m l e (R: mem -> Prop),
    (buffer_at byte (word.of_Z 1) ptsto felem_size_in_bytes elts a * R)%sep m ->
    length elts = encoded_felem_size_in_bytes ->
    (let v := v in
     forall m,
       (FElem (field_parameters:= p_field_params) (Some tight_bounds) a v * R)%sep m ->
       <{ Trace := t; Memory := m; Locals := l; Functions := e }>
         k_impl
       <{ pred (k v eq_refl) }>) ->
       <{ Trace := t; Memory := m; Locals := l; Functions := e }>
         cmd.seq
           (cmd.call [] "from_bytes" [expr.var a_var; expr.var a_var])
           k_impl
       <{ pred (nlet_eq [a_var] v k) }>.
Admitted.


Definition w32s_of_bytes (bs: array_t byte) : array_t word :=
  List.map word.of_Z (List.map le_combine (chunk 4 bs)).

Definition bytes_of_w32s (w32s: array_t word) : array_t byte :=
  List.flat_map (le_split 4) (List.map word.unsigned w32s).


Lemma compile_bytes_of_w32s {tr mem locals functions} w32s :
      let v := bytes_of_w32s w32s in
      forall P (pred: P v -> predicate) (k: nlet_eq_k P v) (k_impl : cmd)
        R (var : string) a_ptr,

        (*Note: hardcoded length of words here*)
        sep ((array scalar (word.of_Z 4) a_ptr w32s)) R mem ->
        WeakestPrecondition.dexpr mem locals var a_ptr ->

        (let v := v in
         (*Forall mem is not necessary,
           but included so that Rupicola doesn't pick up the old predicate.
          TODO: Assess whether this is the right approach.
          *)
         forall mem,
         sep ((array ptsto (word.of_Z 1) a_ptr v)) R mem ->
         <{ Trace := tr;
            Memory := mem;
            Locals := locals;
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
Proof.
Admitted.

Lemma compile_w32s_of_bytes {tr mem locals functions} bytes :
      let v := w32s_of_bytes bytes in
      forall P (pred: P v -> predicate) (k: nlet_eq_k P v) (k_impl : cmd)
        R (var : string) a_ptr,

        (*Note: hardcoded length of words here*)
        sep ((array ptsto (word.of_Z 1) a_ptr bytes)) R mem ->
        WeakestPrecondition.dexpr mem locals var a_ptr ->

        (let v := v in
         (*Forall mem is not necessary,
           but included so that Rupicola doesn't pick up the old predicate.
          TODO: Assess whether this is the right approach.
          *)
         forall mem,
         sep ((array scalar (word.of_Z 4) a_ptr v)) R mem ->
         <{ Trace := tr;
            Memory := mem;
            Locals := locals;
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
Proof.
Admitted.

Definition array_fold_chunked {A T}
           (a: array_t T) (size: nat)
           (f: nat -> A -> list T -> A)
           a0 :=
  List.fold_left (fun acc '(i, c) => f i acc c) (enumerate 0 (chunk size a)) a0.

Definition array_map_chunked {T}
           (a: array_t T) (size: nat)
           (f: nat -> list T -> list T) :=
  List.flat_map (fun '(i, c) => f i c) (enumerate 0 (chunk size a)).

Axiom felem_size : nat.

#[local] Hint Unfold buf_make : poly.
#[local] Hint Unfold buf_push buf_append : poly.
#[local] Hint Unfold buf_split buf_unsplit buf_as_array : poly.
#[local] Hint Unfold array_split_at array_unsplit : poly.
#[local] Hint Unfold array_fold_chunked array_map_chunked : poly.
#[local] Hint Unfold array_get array_put : poly.
#[local] Hint Unfold bytes_as_felem_inplace : poly.
#[local] Hint Unfold felem_init_zero felem_as_uint128 : poly.
#[local] Hint Unfold uint128_add bytes_as_uint128 uint128_as_bytes : poly.
#[local] Hint Unfold bytes_of_w32s w32s_of_bytes : poly.

(** * Poly1305 **)

Definition poly1305_loop scratch output msg (padded: bool) :=
  let/n output :=
     array_fold_chunked
       msg 16
       (fun idx output ck =>
          let/n nscratch := buf_make byte felem_size in
          let/n nscratch := buf_append nscratch ck in (* len = 16 *)
          let/n nscratch := if padded then
                             let/n nscratch := buf_pad nscratch 16 x00 in
                             nscratch
                           else
                             nscratch in
          let/n nscratch := buf_push nscratch x01 in (* len = 17 *)
          let/n nscratch := bytes_as_felem_inplace nscratch in
          let/n output := F.add output nscratch in
          let/n output := F.mul output scratch in
          output)
       output in
  output.

Definition poly1305
           (k : array_t byte)
           (header msg footer : array_t byte)
           (pad_header pad_msg pad_footer : bool)
           (output: array_t byte): array_t byte :=
  let/n (f16, l16) := array_split_at 16 k in
  let/n scratch := buf_make byte felem_size in
  let/n scratch := buf_append scratch (copy f16) in
  let/n (scratch, lone_byte_and_felem_spare_space) := buf_split scratch in
  let/n scratch := List.map (fun '(w1, w2) => let/n w1 := byte.and w1 w2 in w1)
                           (combine scratch (le_split 16 0x0ffffffc0ffffffc0ffffffc0fffffff)) in
  let/n scratch := buf_unsplit scratch lone_byte_and_felem_spare_space in
  let/n scratch := buf_push scratch x00 in
  let/n scratch := bytes_as_felem_inplace scratch in (* B2 primitive reads first 17 bytes of longer array *)
  let/n output := felem_init_zero in
  let/n output := poly1305_loop scratch output header pad_header in
  let/n output := poly1305_loop scratch output msg pad_msg in
  let/n output := poly1305_loop scratch output footer pad_footer in
  let/n output := felem_as_uint128 output in
  let/n l16 := bytes_as_uint128 l16 in
  let/n output := uint128_add output l16 in
  let/n l16 := uint128_as_bytes l16 in
  let/n k := array_unsplit f16 l16 in
  let/n output := uint128_as_bytes output in
  output.


  Instance spec_of_poly1305 : spec_of "poly1305" :=
    fnspec! "poly1305" (key_ptr msg_ptr out_ptr : word) /
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



Definition offset base idx width :=
  (expr.op bopname.add base (expr.op bopname.mul width idx)).


Lemma compile_skip_marker :
  forall {P} {pred: P skip_marker -> predicate} {k: nlet_eq_k P skip_marker} {k_impl}
         {t m l e},
    <{ Trace := t; Memory := m; Locals := l; Functions := e }>
      k_impl
    <{ pred (k skip_marker eq_refl) }> ->
    <{ Trace := t; Memory := m; Locals := l; Functions := e }>
      k_impl
    <{ pred (nlet_eq [] skip_marker k) }>.
Proof.
  auto.
Qed.

Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ skip_marker _))) =>
               simple eapply compile_skip_marker;
               simple eapply compile_skip; shelve : compiler.

Lemma compile_array_split_at {tr} {mem : mem} {locals functions}
      (*TODO: not bytes*) (a : array_t _) idx a_ptr (*a_expr idx_expr*):
      let v := array_split_at idx a in
      forall P (pred: P v -> predicate) (k: nlet_eq_k P v) (k_impl: cmd)
        R (varfst varsnd: string),

      (idx <= Datatypes.length a)%nat ->

      sep (array ptsto (word.of_Z 1) a_ptr a) R mem ->
      (*
      WeakestPrecondition.dexpr mem locals a_expr a_ptr ->
      WeakestPrecondition.dexpr mem locals idx_expr (word.of_Z (Z.of_nat idx)) ->
       *)
      (let v := v in
       forall mem',
         ((array ptsto (word.of_Z 1) a_ptr (fst v))
          * (array ptsto (word.of_Z 1) (word.add a_ptr (word.of_Z (Z.of_nat idx))) (snd v)) * R)%sep mem' ->
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
        (*TODO: do I need local var(s) for arrays?*)
    (*  cmd.seq
        (cmd.store
           (word.of_Z 1)
           (offset a_expr idx_expr (expr.literal (word.of_Z 1)))
           val_expr)*)
        k_impl
      <{ pred (nlet_eq [varfst; varsnd] v k) }>.
    Proof.
      cbn; intros Hlt *.
      repeat straightline'.
      eapply H1; clear H1.
      erewrite <- (firstn_skipn idx a) in H0.
      seprewrite_in @array_append H0.
      rewrite (word.unsigned_of_Z_1) in H0.
      rewrite Z.mul_1_l in H0.
      rewrite firstn_length in H0.
      rewrite Nat.min_l in H0; auto.
    Qed.


Existing Instance byte_ac.
Existing Instance byte_ac_ok.



Lemma poly1305_loop_nil scratch output
  : poly1305_loop scratch output [] false = output.
Proof.
  reflexivity.
Qed.

  Derive poly1305_body SuchThat
         (defn! "poly1305" ("k", "msg", "output") ~> "output" { poly1305_body },
          implements (poly1305))
         As poly1305_body_correct.
Proof.
  compile.
  eapply compile_nlet_as_nlet_eq.
  eapply compile_array_split_at.
  lia.
  repeat compile_step.
  compile_step.
  change v with (fst v, snd v).
  compile_step.
  eapply compile_nlet_as_nlet_eq.
  eapply compile_buf_make_stack_bytes.

  shelve.
  compile_step.

  compile_step.

  compile_step.
  compile_step.
  compile_step.
  shelve.
  compile_step.
  eapply compile_byte_memcpy.
  shelve.
  repeat compile_step.
  repeat compile_step.
  admit (*TODO*).
  shelve.
  shelve.
  {
    eapply Util.dexpr_put_diff; [shelve|].
    eapply Util.dexpr_put_diff; [shelve|].
    eapply Util.dexpr_put_diff; [shelve|].
    eapply Util.dexpr_put_diff; [shelve|].
    eapply Util.dexpr_put_same.
  }
  shelve.
  repeat compile_step.
  unfold FillPred; cbn beta.
  repeat compile_step.
  shelve.
  eapply compile_nlet_as_nlet_eq.
  eapply compile_buf_split.
  {
    change v1 with (v0++(copy (fst v))).
    ecancel_assumption.
  }
  shelve.
  compile_step.
  change v3 with (fst v3, snd v3).
  repeat compile_step.

  Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (map _ (combine _ _)) _))) =>
         compile_broadcast_expr; shelve : compiler.
  compile_step. (*TODO: why does repeat compile_step break the later goal?*)
  {
    rewrite map.remove_put_same.
    rewrite map.remove_put_diff.
    eapply Util.dexpr_put_same.
    unfold gs.
    repeat compile_step.
  }
  {
    change (sz_word _) with (word.of_Z 1 : word); cbn.
    repeat compile_step.
  }
  shelve (*TODO: should I have the len param?*).
  shelve (*TODO: should I have the len param?*).
  shelve (*TODO: should I have the len param?*).
  unfold gs; compile_step.
  unfold gs; compile_step.
  unfold gs; compile_step.
  eapply broadcast_byte_and.
  shelve (*TODO: length*).
  {
    change (fst v3) with v1.
    eapply broadcast_id.
    typeclasses eauto.
    rewrite map.remove_put_same.
    rewrite map.remove_put_diff.
    rewrite map.get_put_same.
    reflexivity.
    unfold gs; compile_step.
    unfold gs; compile_step.
  }
  eapply broadcast_byte_const.
  repeat compile_step.
  eapply compile_nlet_as_nlet_eq.
  eapply compile_buf_unsplit.
  {
    replace (snd v3) with (fst v).
    (*cancel_assumption.*)
    admit.
    admit.
  }
  admit.
  admit.
  admit.
  repeat compile_step.
  eapply compile_nlet_as_nlet_eq.
  eapply compile_buf_push_byte.
  ecancel_assumption.
  admit.

  repeat compile_step.
  shelve.
  shelve.
  shelve.
  repeat compile_step.
  eapply compile_nlet_as_nlet_eq.
  eapply compile_bytes_as_felem_inplace.
  admit.
  subst v5 v4 v3.
  unfold buf_unsplit.
  unfold buf_push.
  rewrite app_length.
  rewrite map_length.
  rewrite combine_length.
  admit.
  clear m3 H4 m4 H5.
  repeat compile_step.

  eapply compile_nlet_as_nlet_eq.
  change felem_init_zero with (F.of_Z M_pos 0).
  (*eapply compile_from_word with (x:=0) (P:=fun _ => list byte).*)
  lazymatch goal with
    [|- ?G] =>
      let x := open_constr:(compile_from_word 0 (fun _ => list byte) _ _ _ _ _ _ _ _ _ _ _ _ _ _) in
      let t := type of x in
      replace G with t; cycle 1
  end.
  {
    repeat f_equal.
  }
  eapply compile_from_word with (x:=0) (P:=fun _ => list byte).
  admit.
  repeat compile_step.
  ecancel_assumption.
  eapply word.unsigned_of_Z_0.
  repeat compile_step.
  rewrite poly1305_loop_nil.
  unfold nlet at 1.
Abort.

(** ** Equivalence proof **)

(* change (nlet _ ?v ?k) with (k v) at 1; cbv beta iota. *)

#[local] Hint Unfold poly1305_loop : poly.

Lemma poly1305_ok' k header msg footer output:
  (length header mod 16 = 0)%nat ->
  (length msg mod 16 = 0)%nat ->
  Spec.poly1305 k (header ++ msg ++ footer) =
  poly1305 k header msg footer false false false output.
Proof.
  intros; unfold Spec.poly1305, poly1305.
  autounfold with poly; unfold nlet.
  Z.push_pull_mod.
  rewrite <- le_split_mod.
  unfold enumerate.
  rewrite <- !fold_left_combine_fst by (rewrite seq_length; lia).
  rewrite <- !fold_left_app, <- !chunk_app by assumption || lia.
  repeat f_equal.
  repeat (apply FunctionalExtensionality.functional_extensionality; intros).
  Z.push_pull_mod.
  rewrite !app_nil_l.
  repeat f_equal.
  rewrite le_combine_snoc_0.
  rewrite <- Z_land_le_combine.
  reflexivity.
Qed.

Lemma poly1305_ok k msg output:
  Spec.poly1305 k msg = poly1305 k [] msg [] false false false output.
Proof.
  intros; pose proof (poly1305_ok' k [] [] msg output) as H.
  simpl in H. erewrite H; reflexivity.
Qed.

(** * ChaCha20 **)

Local Notation "a + b" := (word.add (word := word) a b).
Local Notation "a ^ b" := (word.xor (word := word) a b).
Local Notation "a <<< b" := (word.slu a b + word.sru a (word.sub (word.of_Z 32) b)) (at level 30).

Definition quarter a b c d : \<< word, word, word, word \>> :=
  let/n a := a + b in  let/n d := d ^ a in  let/n d := d <<< word.of_Z 16 in
  let/n c := c + d in  let/n b := b ^ c in  let/n b := b <<< word.of_Z 12 in
  let/n a := a + b in  let/n d := d ^ a in  let/n d := d <<< word.of_Z 8 in
  let/n c := c + d in  let/n b := b ^ c in  let/n b := b <<< word.of_Z 7 in
  \< a, b, c, d \>.

Hint Rewrite word.Z_land_ones_rotate using (split; reflexivity) : quarter.
Hint Rewrite <- word.unsigned_xor_nowrap : quarter.
Hint Rewrite word.Z_land_ones_word_add : quarter.

Lemma quarter_ok0 a b c d:
  Spec.quarter (word.unsigned a, word.unsigned b, word.unsigned c, word.unsigned d) =
  let '\<a', b', c', d'\> := quarter a b c d in
  (word.unsigned a', word.unsigned b', word.unsigned c', word.unsigned d').
Proof.
  unfold Spec.quarter, quarter, nlet;
    autorewrite with quarter;
    reflexivity.
Qed.

Lemma quarter_ok a b c d:
  in_bounds 32 a -> in_bounds 32 b -> in_bounds 32 c -> in_bounds 32 d ->
  quarter (word.of_Z a) (word.of_Z b) (word.of_Z c) (word.of_Z d) =
  let '(a', b', c', d') := Spec.quarter (a, b, c, d) in
  \< word.of_Z a', word.of_Z b', word.of_Z c', word.of_Z d' \>.
Proof.
  unfold in_bounds; intros.
  set (wa := word.of_Z a); set (wb := word.of_Z b); set (wc := word.of_Z c); set (wd := word.of_Z d).
  rewrite <- (word.unsigned_of_Z_nowrap a), <- (word.unsigned_of_Z_nowrap b) by assumption.
  rewrite <- (word.unsigned_of_Z_nowrap c), <- (word.unsigned_of_Z_nowrap d) by assumption.
  rewrite quarter_ok0; subst wa wb wc wd; destruct (quarter _ _ _ _) as (?&?&?&?); cbn -[word.of_Z].
  rewrite !word.of_Z_unsigned; reflexivity.
Qed.

Lemma quarter_in_bounds a b c d:
  in_bounds 32 a -> in_bounds 32 b -> in_bounds 32 c -> in_bounds 32 d ->
  let '(a', b', c', d') := Spec.quarter (a, b, c, d) in
  in_bounds 32 a' /\ in_bounds 32 b' /\ in_bounds 32 c' /\ in_bounds 32 d'.
Proof.
  unfold in_bounds; intros.
  rewrite <- (word.unsigned_of_Z_nowrap a), <- (word.unsigned_of_Z_nowrap b) by assumption.
  rewrite <- (word.unsigned_of_Z_nowrap c), <- (word.unsigned_of_Z_nowrap d) by assumption.
  rewrite quarter_ok0; destruct (quarter _ _ _ _) as (?&?&?&?); cbn -[word.of_Z Z.pow].
  repeat (split; try apply word.unsigned_range).
Qed.

Definition quarterround x y z t (st : list word) : list word :=
  let/n stx := array_get st x (word.of_Z 0) in
  let/n sty := array_get st y (word.of_Z 0) in
  let/n stz := array_get st z (word.of_Z 0) in
  let/n stt := array_get st t (word.of_Z 0) in
  let/n (stx, sty, stz, stt) := quarter stx sty stz stt in
  let/n st := array_put st x stx in
  let/n st := array_put st y sty in
  let/n st := array_put st z stz in
  let/n st := array_put st t stt in
  st.

Lemma quarterround_ok x y z t st :
  Forall (in_bounds 32) st ->
  List.map word.of_Z (Spec.quarterround x y z t st) =
  quarterround x y z t (List.map word.of_Z st).
Proof.
  unfold Spec.quarterround, quarterround, nlet; autounfold with poly; intros H.
  rewrite forall_in_bounds in H by lia.
  rewrite !map_nth, !quarter_ok by auto.
  destruct (Spec.quarter _) as (((?&?)&?)&?).
  rewrite !map_upd; reflexivity.
Qed.

Lemma quarterround_in_bounds x y z t a:
  Forall (in_bounds 32) a ->
  Forall (in_bounds 32) (Spec.quarterround x y z t a).
Proof.
  unfold Spec.quarterround, nlet; autounfold with poly; intros Ha.
  pose proof Ha as Ha'; rewrite forall_in_bounds in Ha by lia.
  pose proof quarter_in_bounds (nth x a 0) (nth y a 0) (nth z a 0) (nth t a 0)
       ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(eauto) as Hb.
  destruct (Spec.quarter _) as (((?&?)&?)&?).
  destruct Hb as (?&?&?&?).
  repeat (apply Forall_upd; auto).
Qed.

Definition chacha20_block_init : \<< word, word, word, word \>> :=
  Eval cbn -[word.of_Z] in
  match w32s_of_bytes (list_byte_of_string"expand 32-byte k") as l
        return match l with | [w1; w2; w3; w4] => _ | _ => True end with
  | [w1; w2; w3; w4] => \<w1, w2, w3, w4\>
  | _ => I
  end.

Require Import Rupicola.Lib.ControlFlow.DownTo.

(* FIXME word/Z conversion *)
Definition chacha20_block' (*256bit*)key (*32bit+96bit*)nonce (*512 bits*)st :=
  let '\< i1, i2, i3, i4 \> := chacha20_block_init in
  let/n st := buf_push st i1 in
  let/n st := buf_push st i2 in
  let/n st := buf_push st i3 in
  let/n st := buf_push st i4 in (* the inits are the chunks of "expand …" *)

  let/n key := w32s_of_bytes key in
  let/n st := buf_append st (copy key) in
  let/n key := bytes_of_w32s key in

  let/n nonce := w32s_of_bytes nonce in
  let/n st := buf_append st (copy nonce) in
  let/n nonce := bytes_of_w32s nonce in

  let/n st := buf_as_array st in
  let/n ss := buf_make word 16 in
  let/n ss := buf_append ss (copy st) in
  let/n ss := buf_as_array ss in
  let/n ss := Nat.iter 10 (fun ss =>
    let/n ss := quarterround  0  4  8 12  ss in
    let/n ss := quarterround  1  5  9 13  ss in
    let/n ss := quarterround  2  6 10 14  ss in
    let/n ss := quarterround  3  7 11 15  ss in
    let/n ss := quarterround  0  5 10 15  ss in
    let/n ss := quarterround  1  6 11 12  ss in
    let/n ss := quarterround  2  7  8 13  ss in
    let/n ss := quarterround  3  4  9 14  ss in
    ss) ss in

  let/n st := List.map (fun '(st_i, ss_i) =>
                         let/n st_i := st_i + ss_i in
                         st_i) (combine st ss) in

  let/n st := bytes_of_w32s st in
  st.


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

(* This is the function that should be compiled by Rupicola.
   TODO: either prove this equivalent to the above older version
   or directly adapt the proof below to fit this function.
 *)

(* FIXME word/Z conversion *)

Definition chacha20_block (*256bit*)key (*32bit+96bit*)nonce (*512 bits*)st :=
  let '\< i1, i2, i3, i4 \> := chacha20_block_init in
  let/n st := buf_backed_by word 16 st in
  let/n st := buf_push st i1 in
  let/n st := buf_push st i2 in
  let/n st := buf_push st i3 in
  let/n st := buf_push st i4 in (* the inits are the chunks of "expand …" *)

  let/n key := w32s_of_bytes key in
  let/n st := buf_append st (copy key) in
  let/n key := bytes_of_w32s key in

  let/n nonce := w32s_of_bytes nonce in
  let/n st := buf_append st (copy nonce) in
  let/n nonce := bytes_of_w32s nonce in

  let/n st := buf_as_array st in
  let/n ss := buf_make word 16 in
  let/n ss := buf_append ss (copy st) in
  let/n ss := buf_as_array ss in

  let/n qv0 := array_get ss 0 (word.of_Z 0) in
  let/n qv1 := array_get ss 1 (word.of_Z 0) in
  let/n qv2 := array_get ss 2 (word.of_Z 0) in
  let/n qv3 := array_get ss 3 (word.of_Z 0) in
  let/n qv4 := array_get ss 4 (word.of_Z 0) in
  let/n qv5 := array_get ss 5 (word.of_Z 0) in
  let/n qv6 := array_get ss 6 (word.of_Z 0) in
  let/n qv7 := array_get ss 7 (word.of_Z 0) in
  let/n qv8 := array_get ss 8 (word.of_Z 0) in
  let/n qv9 := array_get ss 9 (word.of_Z 0) in
  let/n qv10 := array_get ss 10 (word.of_Z 0) in
  let/n qv11 := array_get ss 11 (word.of_Z 0) in
  let/n qv12 := array_get ss 12 (word.of_Z 0) in
  let/n qv13 := array_get ss 13 (word.of_Z 0) in
  let/n qv14 := array_get ss 14 (word.of_Z 0) in
  let/n qv15 := array_get ss 15 (word.of_Z 0) in
  let/n (qv0,qv1,qv2,qv3,
         qv4,qv5,qv6,qv7,
         qv8,qv9,qv10,qv11,
         qv12,qv13,qv14,qv15) :=
     Nat.iter 10 (fun '\<qv0, qv1, qv2, qv3,
                      qv4, qv5, qv6, qv7,
                      qv8, qv9, qv10,qv11,
                      qv12,qv13,qv14,qv15\>  =>
                    let/n (qv0, qv4, qv8,qv12) := quarter qv0  qv4  qv8 qv12 in
                    let/n (qv1, qv5, qv9,qv13) := quarter qv1  qv5  qv9 qv13 in
                    let/n (qv2, qv6, qv10,qv14) := quarter qv2  qv6 qv10 qv14 in
                    let/n (qv3, qv7, qv11,qv15) := quarter qv3  qv7 qv11 qv15 in
                    let/n (qv0, qv5, qv10,qv15) := quarter qv0  qv5 qv10 qv15 in
                    let/n (qv1, qv6, qv11,qv12) := quarter qv1  qv6 qv11 qv12 in
                    let/n (qv2, qv7, qv8,qv13) := quarter qv2  qv7  qv8 qv13 in
                    let/n (qv3, qv4, qv9,qv14) := quarter qv3  qv4  qv9 qv14 in
                    \<qv0,qv1,qv2,qv3,
                    qv4,qv5,qv6,qv7,
                    qv8,qv9,qv10,qv11,
                    qv12,qv13,qv14,qv15\>)
              \<qv0,qv1,qv2,qv3,
     qv4,qv5,qv6,qv7,
     qv8,qv9,qv10,qv11,
     qv12,qv13,qv14,qv15\> in

  let/n ss := array_put ss 0 qv0 in
  let/n ss := array_put ss 1 qv1 in
  let/n ss := array_put ss 2 qv2 in
  let/n ss := array_put ss 3 qv3 in
  let/n ss := array_put ss 4 qv4 in
  let/n ss := array_put ss 5 qv5 in
  let/n ss := array_put ss 6 qv6 in
  let/n ss := array_put ss 7 qv7 in
  let/n ss := array_put ss 8 qv8 in
  let/n ss := array_put ss 9 qv9 in
  let/n ss := array_put ss 10 qv10 in
  let/n ss := array_put ss 11 qv11 in
  let/n ss := array_put ss 12 qv12 in
  let/n ss := array_put ss 13 qv13 in
  let/n ss := array_put ss 14 qv14 in
  let/n ss := array_put ss 15 qv15 in

  let/n st := List.map (fun '(st_i, ss_i) =>
                          let/n st_i := st_i + ss_i in
                         st_i) (combine st ss) in

  let/n st := bytes_of_w32s st in
  let/n st := buf_as_array st in
  st.

Lemma word_add_pair_eqn st:
  (let '(s, t) := st in Z.land (s + t) (Z.ones 32)) =
  word.unsigned (word.of_Z (fst st) + word.of_Z (snd st)).
Proof.
  destruct st.
  rewrite Z.land_ones, <- word.ring_morph_add, word.unsigned_of_Z by lia.
  reflexivity.
Qed.

Lemma chacha20_block_ok key nonce :
  Spec.chacha20_block key nonce =
  chacha20_block' key nonce [].
Proof.
  unfold Spec.chacha20_block, chacha20_block', chacha20_block_init, nlet.
  autounfold with poly.

  simpl (map le_combine (chunk 4 (list_byte_of_string _))); cbn [List.app].
  erewrite (map_ext _ _ word_add_pair_eqn).
  rewrite <- List.map_map.
  rewrite <- List.map_map with (f := fun st => (_, _)) (g := fun '(s, t) => s + t).
  rewrite map_combine_separated, map_combine_comm by (cbn; intros; ring).
  cbn [List.map]; rewrite List.map_app.
  repeat f_equal.

  (*About Nat_iter_rew_inv.*)

  eapply Nat_iter_rew_inv with (P := Forall (in_bounds 32)); intros.
  - eauto 10 using quarterround_in_bounds.
  - rewrite !quarterround_ok; try reflexivity;
      eauto 10 using quarterround_in_bounds.
  - repeat (apply Forall_cons; [ red; lia | ]).
    apply Forall_app; split;
      apply (Forall_le_combine_in_bounds 4); lia.
  - cbn [List.map]; rewrite List.map_app; reflexivity.
Qed.

Lemma quarterround_eq :
  forall ss a b c d,
    quarterround a b c d ss =
    let '\<qv0, qv1, qv2, qv3\> := (quarter (nth a ss (word.of_Z 0))
                                            (nth b ss (word.of_Z 0))
                                            (nth c ss (word.of_Z 0))
                                            (nth d ss (word.of_Z 0))) in
upd (upd (upd (upd ss a qv0) b qv1) c qv2) d qv3.
Proof.
  intros.
  unfold quarterround, nlet, array_put.
  reflexivity.
Qed.

Ltac reduce_nth_hyp :=
  lazymatch goal with
  | [ |- not (_%nat = _%nat) ] => lia
  | [ |- (_ < length _)%nat ] => rewrite upd_length
  | [ H : nth ?k (upd ?l ?k _) _ = ?x |- context [?x] ] => rewrite nth_upd_same in H
  | [ H : nth ?k (upd ?l ?k2 _) _ = ?x |- context [?x] ] => rewrite nth_upd_diff in H
  end.

Ltac reduce_nth_goal :=
  repeat lazymatch goal with
  | [ |- nth ?k (upd ?l ?k _) _ = _ ] => rewrite nth_upd_same
  | [ |- nth ?k (upd ?l ?k2 _) _ = _ ] => rewrite nth_upd_diff
  end;
  try reflexivity;
  try lia;
  try repeat rewrite upd_length.

Definition put_ss (ss : array_t word) p :=
  let/n (qv0,qv1,qv2,qv3,
         qv4,qv5,qv6,qv7,
         qv8,qv9,qv10,qv11,
         qv12,qv13,qv14,qv15) := p in
  let/n ss := array_put ss 0 qv0 in
  let/n ss := array_put ss 1 qv1 in
  let/n ss := array_put ss 2 qv2 in
  let/n ss := array_put ss 3 qv3 in
  let/n ss := array_put ss 4 qv4 in
  let/n ss := array_put ss 5 qv5 in
  let/n ss := array_put ss 6 qv6 in
  let/n ss := array_put ss 7 qv7 in
  let/n ss := array_put ss 8 qv8 in
  let/n ss := array_put ss 9 qv9 in
  let/n ss := array_put ss 10 qv10 in
  let/n ss := array_put ss 11 qv11 in
  let/n ss := array_put ss 12 qv12 in
  let/n ss := array_put ss 13 qv13 in
  let/n ss := array_put ss 14 qv14 in
  let/n ss := array_put ss 15 qv15 in
  ss.

Ltac simplify_quarterround :=
   lazymatch goal with
    | [ |- context [ quarterround ?a0 ?b0 ?c0 ?d0 (upd ?inner ?k ?def) ] ] =>
      set inner;
        rewrite quarterround_eq with (a := a0) (b := b0) (c := c0) (d := d0)
    end;
   repeat straightline.

Ltac simplify_nth :=
  lazymatch goal with
  | [ |- context [ (nth ?k ?l ?def) ] ] =>
    set (nth k l def);
    try lazymatch goal with
        | [ r := nth k l def |- _ ] => unfold l in r
        end
  end.

Ltac rewrite_r rk :=
  assert (Heq : rk = rk) by reflexivity;
  unfold rk in Heq at 1;
  repeat reduce_nth_hyp;
  try lia;
  rewrite <- Heq;
  clear Heq.

Ltac rewrite_quarter :=
  simplify_quarterround;
  lazymatch goal with
  | [ |- context [nth _ (upd ?list ?index ?val)]] =>
    set (upd list index val)
  end.


Ltac rewrite_r_auto :=
  lazymatch goal with
  | [ |- context [quarter ?r0 ?r1 ?r2 ?r3] ] =>
    rewrite_r r0;
    rewrite_r r1;
    rewrite_r r2;
    rewrite_r r3
  end.

Lemma chacha20_blocks_equiv :
  forall ss,
    length ss = 16%nat ->
    (let/n ss := Nat.iter 10 (fun ss =>
                                let/n ss := quarterround  0  4  8 12  ss in
                                let/n ss := quarterround  1  5  9 13  ss in
                                let/n ss := quarterround  2  6 10 14  ss in
                                let/n ss := quarterround  3  7 11 15  ss in
                                let/n ss := quarterround  0  5 10 15  ss in
                                let/n ss := quarterround  1  6 11 12  ss in
                                let/n ss := quarterround  2  7  8 13  ss in
                                let/n ss := quarterround  3  4  9 14  ss in
                                ss) ss in
     ss) =
    (let/n qv0 := array_get ss 0 (word.of_Z 0) in
     let/n qv1 := array_get ss 1 (word.of_Z 0) in
     let/n qv2 := array_get ss 2 (word.of_Z 0) in
     let/n qv3 := array_get ss 3 (word.of_Z 0) in
     let/n qv4 := array_get ss 4 (word.of_Z 0) in
     let/n qv5 := array_get ss 5 (word.of_Z 0) in
     let/n qv6 := array_get ss 6 (word.of_Z 0) in
     let/n qv7 := array_get ss 7 (word.of_Z 0) in
     let/n qv8 := array_get ss 8 (word.of_Z 0) in
     let/n qv9 := array_get ss 9 (word.of_Z 0) in
     let/n qv10 := array_get ss 10 (word.of_Z 0) in
     let/n qv11 := array_get ss 11 (word.of_Z 0) in
     let/n qv12 := array_get ss 12 (word.of_Z 0) in
     let/n qv13 := array_get ss 13 (word.of_Z 0) in
     let/n qv14 := array_get ss 14 (word.of_Z 0) in
     let/n qv15 := array_get ss 15 (word.of_Z 0) in
     let/n (qv0,qv1,qv2,qv3,
            qv4,qv5,qv6,qv7,
            qv8,qv9,qv10,qv11,
            qv12,qv13,qv14,qv15) :=
        Nat.iter 10 (fun '\<qv0, qv1, qv2, qv3,
                         qv4, qv5, qv6, qv7,
                         qv8, qv9, qv10,qv11,
                         qv12,qv13,qv14,qv15\>  =>
                       let/n (qv0, qv4, qv8,qv12) := quarter qv0  qv4  qv8 qv12 in
                       let/n (qv1, qv5, qv9,qv13) := quarter qv1  qv5  qv9 qv13 in
                       let/n (qv2, qv6, qv10,qv14) := quarter qv2  qv6 qv10 qv14 in
                       let/n (qv3, qv7, qv11,qv15) := quarter qv3  qv7 qv11 qv15 in
                       let/n (qv0, qv5, qv10,qv15) := quarter qv0  qv5 qv10 qv15 in
                       let/n (qv1, qv6, qv11,qv12) := quarter qv1  qv6 qv11 qv12 in
                       let/n (qv2, qv7, qv8,qv13) := quarter qv2  qv7  qv8 qv13 in
                       let/n (qv3, qv4, qv9,qv14) := quarter qv3  qv4  qv9 qv14 in
                       \<qv0,qv1,qv2,qv3,
                       qv4,qv5,qv6,qv7,
                       qv8,qv9,qv10,qv11,
                       qv12,qv13,qv14,qv15\>)
                 \<qv0,qv1,qv2,qv3,
        qv4,qv5,qv6,qv7,
        qv8,qv9,qv10,qv11,
        qv12,qv13,qv14,qv15\> in

     let/n ss := array_put ss 0 qv0 in
     let/n ss := array_put ss 1 qv1 in
     let/n ss := array_put ss 2 qv2 in
     let/n ss := array_put ss 3 qv3 in
     let/n ss := array_put ss 4 qv4 in
     let/n ss := array_put ss 5 qv5 in
     let/n ss := array_put ss 6 qv6 in
     let/n ss := array_put ss 7 qv7 in
     let/n ss := array_put ss 8 qv8 in
     let/n ss := array_put ss 9 qv9 in
     let/n ss := array_put ss 10 qv10 in
     let/n ss := array_put ss 11 qv11 in
     let/n ss := array_put ss 12 qv12 in
     let/n ss := array_put ss 13 qv13 in
     let/n ss := array_put ss 14 qv14 in
     let/n ss := array_put ss 15 qv15 in
     ss).
Proof.
  (*
  intros.
  repeat straightline.
  unfold nlet at 1.
  lazymatch goal with
  | [ |- context [Nat.iter _ ?x _] ] => set x
  end.
  lazymatch goal with
  | [ |- ?x = _ ] => set x
  end.
  lazymatch goal with
  | [ |- context [Nat.iter _ ?x _] ] => set x
  end.
  lazymatch goal with
  | [ |- _ = ?x ] => set x
  end.
  unfold l0.
  set (\< array_get ss 0 (word.of_Z 0),
       array_get ss 1 (word.of_Z 0),
       array_get ss 2 (word.of_Z 0),
       array_get ss 3 (word.of_Z 0),
       array_get ss 4 (word.of_Z 0),
       array_get ss 5 (word.of_Z 0),
       array_get ss 6 (word.of_Z 0),
       array_get ss 7 (word.of_Z 0),
       array_get ss 8 (word.of_Z 0),
       array_get ss 9 (word.of_Z 0),
       array_get ss 10 (word.of_Z 0),
       array_get ss 11 (word.of_Z 0),
       array_get ss 12 (word.of_Z 0),
       array_get ss 13 (word.of_Z 0),
       array_get ss 14 (word.of_Z 0),
       array_get ss 15 (word.of_Z 0) \>).

  specialize @Nat_iter_rew with (fA := p0) (fB := l) (b := ss) (a := p1) (g := put_ss ss); intros.
  rewrite <- H0.

  - unfold put_ss.
    unfold nlet.
    fold p1.
    set (Nat.iter 10 p0 p1).
    unfold l1, nlet; reflexivity.

  - intros.
    unfold l, put_ss.
    destruct a as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?) in *.
    unfold nlet, array_put.
    subst p1.
    subst p0.
    subst l.

    lazymatch goal with
    | [ |- ?x = _ ] => set x
    end.

    destruct (quarter car car3 car7 car11) as (?&?&?&?) eqn:q.
    destruct (quarter car0 car4 car8 car12) as (?&?&?&?) eqn:q0.
    destruct (quarter car1 car5 car9 car13) as (?&?&?&?) eqn:q1.
    destruct (quarter car2 car6 car10 cdr) as (?&?&?&?) eqn:q2.
    destruct (quarter car14 car18 car22 cdr3) as (?&?&?&?) eqn:q3.
    destruct (quarter car17 car21 car25 cdr0) as (?&?&?&?) eqn:q4.
    destruct (quarter car20 car24 car16 cdr1) as (?&?&?&?) eqn:q5.
    destruct (quarter car23 car15 car19 cdr2) as (?&?&?&?) eqn:q6.

    rewrite_quarter.
    unfold l2 in l0.
    repeat simplify_nth.
    rewrite_r_auto.
    rewrite q; clear q.
    repeat straightline.

    rewrite_quarter.
    unfold l0 in l1.
    unfold l1 in l2.
    repeat simplify_nth.
    rewrite_r_auto.
    rewrite q0; clear q0.
    repeat straightline.

    rewrite_quarter.
    unfold l0, l2 in l1.
    repeat simplify_nth.
    rewrite_r_auto.
    rewrite q1; clear q1.
    repeat straightline.

    rewrite_quarter.
    unfold l0, l1 in l2.
    repeat simplify_nth.
    rewrite_r_auto.
    rewrite q2; clear q2.
    repeat straightline.

    rewrite_quarter.
    unfold l0, l2 in l1.
    repeat simplify_nth.
    rewrite_r_auto.
    rewrite q3; clear q3.
    repeat straightline.

    rewrite_quarter.
    unfold l0, l1 in l2.
    repeat simplify_nth.
    rewrite_r_auto.
    rewrite q4; clear q4.
    repeat straightline.

    rewrite_quarter.
    unfold l0, l2 in l1.
    repeat simplify_nth.
    rewrite_r_auto.
    rewrite q5; clear q5.
    repeat straightline.

    rewrite_quarter.
    unfold l0, l1 in l2.
    repeat simplify_nth.
    rewrite_r_auto.
    rewrite q6; clear q6.

    unfold l0.
    unfold l2.
    unfold l.

    admit.

  - unfold p1; fold p1.
    unfold array_put.
    assert (forall (k : nat) default,
               k < 16 -> ss = (upd ss k (array_get ss k default))).
    { intros.
      unfold array_get.
      admit.
    }

    unfold p1, put_ss, nlet; cbn [P2.cdr P2.car].
    repeat rewrite <- H1; easy.
    *)
Admitted.

Lemma chacha20_block_ok' key nonce st :
  chacha20_block' key nonce [] =
  chacha20_block key nonce st.
Proof.
  unfold chacha20_block, chacha20_block'.
  unfold buf_backed_by.
  symmetry.
  unfold nlet at 1.
  pose chacha20_blocks_equiv.
  unfold nlet in *.
  rewrite e.
  reflexivity.
  simpl.
  admit.
Admitted.

Definition chacha20_encrypt key start nonce plaintext :=
  let plaintext := array_map_chunked plaintext 64 (fun idx chunk => (* FIXME nplaintext *)
                                                     let counter := word.add (word.of_Z (Z.of_nat start)) (word.of_Z (Z.of_nat idx)) in
                                                     let scratch := buf_make word 4 in
                                                     let scratch := buf_push scratch counter in
                                                     let nonce := w32s_of_bytes nonce in
                                                     let scratch := buf_append scratch (copy nonce) in (* FIXME? You can save a scratch buffer by doing the nonce concatenation of chacha20 here instead *)
                                                     let nonce := bytes_of_w32s nonce in
                                                     let scratch := buf_as_array scratch in
                                                     let scratch := bytes_of_w32s scratch in
                                                     let st := buf_make word 16 in
                                                     let st := chacha20_block' key scratch st in
                                                     let chunk := List.map (fun '(st_i, ss_i) =>
                                                                              let st_i := byte.xor st_i ss_i in
                                                                              st_i)
                                                                           (combine chunk st) in
                                                     chunk) in
  plaintext.

Lemma chacha20_encrypt_ok key start nonce plaintext :
  (length nonce mod 4 = 0)%nat ->
  Spec.chacha20_encrypt key start nonce plaintext =
  chacha20_encrypt key start nonce plaintext.
Proof.
  unfold Spec.chacha20_encrypt, chacha20_encrypt, nlet, copy;
    autounfold with poly; intros.
  rewrite enumerate_offset.
  rewrite flat_map_concat_map, map_map, <- flat_map_concat_map.
  f_equal.
  apply FunctionalExtensionality.functional_extensionality; intros (?&?).
  unfold zip; rewrite map_combine_comm by apply byte_xor_comm; f_equal.
  f_equal.
  rewrite chacha20_block_ok.
  f_equal.
  cbn [List.app List.map].
  rewrite word.unsigned_add, !word.unsigned_of_Z, map_map.
  pose proof map_unsigned_of_Z_le_combine as P. cbn zeta in P. rewrite P. clear P.
  cbn [List.flat_map]. f_equal.
  + unfold word.wrap; Z.push_pull_mod; rewrite <- le_split_mod.
    f_equal; simpl; lia.
  + rewrite flat_map_le_split_combine_chunk; eauto. cbv. lia.
Qed.

Definition chacha20poly1305_aead_encrypt aad key iv constant plaintext tag :=
  let/n nonce := buf_make word 2 in
  let/n otk_nonce := buf_make word 4 in

  let/n otk_nonce := buf_push otk_nonce (word.of_Z 0) in

  let/n constant := w32s_of_bytes constant in
  let/n nonce := buf_append nonce (copy constant) in
  let/n otk_nonce := buf_append otk_nonce (copy constant) in
  let/n constant := bytes_of_w32s constant in

  let/n iv := w32s_of_bytes iv in
  let/n nonce := buf_append nonce (copy iv) in
  let/n otk_nonce := buf_append otk_nonce (copy iv) in
  let/n iv := bytes_of_w32s iv in

  let/n nonce := buf_as_array nonce in
  let/n nonce := bytes_of_w32s nonce in

  let/n otk_nonce := buf_as_array otk_nonce in
  let/n otk_nonce := bytes_of_w32s otk_nonce in

  let/n otk := buf_make word 16 in
  let/n otk := chacha20_block' key otk_nonce otk in
  let/n (otk, rest) := array_split_at 32 otk in

  let/n plaintext := chacha20_encrypt key 1 nonce plaintext in

  let/n footer := buf_make word 4 in
  let/n footer := buf_push footer (word.of_Z (Z.of_nat (length aad))) in
  let/n footer := buf_push footer (word.of_Z 0) in
  let/n footer := buf_push footer (word.of_Z (Z.of_nat (length plaintext))) in
  let/n footer := buf_push footer (word.of_Z 0) in
  let/n footer := buf_as_array footer in
  let/n footer := bytes_of_w32s footer in

  let mac_data := aad in
  let/n tag := poly1305 otk mac_data plaintext footer true true true tag in
  let/n otk := array_unsplit otk rest in
  (plaintext, tag).

Lemma length_spec_quarterround x y z t st:
  length (Spec.quarterround x y z t st) = length st.
Proof.
  unfold Spec.quarterround.
  destruct (Spec.quarter _) as (((?&?)&?)&?).
  rewrite !upd_length; reflexivity.
Qed.

Lemma length_spec_chacha20_block key nonce:
  (length key >= 32)%nat ->
  (length nonce >= 16)%nat ->
  (length (Spec.chacha20_block key nonce) >= 64)%nat.
Proof.
  unfold Spec.chacha20_block; intros.
  erewrite flat_map_const_length with (n := 4%nat); try apply length_le_split.
  repeat (rewrite ?map_length, ?combine_length, ?app_length, ?length_chunk,
          ?Nat_iter_const_length, ?Nat.min_id, ?Nat.mul_add_distr_l);
    eauto; cycle 1.
  - intros; rewrite !length_spec_quarterround; reflexivity.
  - simpl (length _); simpl (Nat.div_up 16 4).
    pose proof Nat.div_up_range (length key) 4 ltac:(lia).
    pose proof Nat.div_up_range (length nonce) 4 ltac:(lia).
    lia.
Qed.

Lemma length_spec_chacha20_encrypt key start nonce plaintext :
  (length key >= 32)%nat ->
  (length nonce >= 12)%nat ->
  length (Spec.chacha20_encrypt key start nonce plaintext) = length plaintext.
Proof.
  unfold Spec.chacha20_encrypt; intros.
  rewrite flat_map_concat_map, length_concat_sum, map_map.
  erewrite map_ext_in with (g := fun x => length (snd x)); cycle 1.
  - intros (?&?); unfold zip.
    rewrite map_length, combine_length. cbn [snd].
    intros Hin%in_combine_r%(Forall_In (@Forall_chunk_length_le _ 64 ltac:(lia) _)).
    unshelve epose proof length_spec_chacha20_block key (le_split 4 (Z.of_nat n) ++ nonce) ltac:(auto) _.
    { rewrite app_length, length_le_split; lia. }
    lia.
  - rewrite <- map_map with (f := snd) (g := @length _).
    unfold enumerate; rewrite map_combine_snd by apply seq_length.
    rewrite <- length_concat_sum, concat_chunk; reflexivity.
Qed.

Lemma length_chacha20_encrypt key start nonce plaintext :
  (length key >= 32)%nat ->
  (length nonce >= 12)%nat ->
  (length nonce mod 4 = 0)%nat ->
  length (chacha20_encrypt key start nonce plaintext) = length plaintext.
Proof.
  intros; rewrite <- chacha20_encrypt_ok by assumption;
    apply length_spec_chacha20_encrypt; auto.
Qed.

Lemma padding_len_mod {A} (bs1 bs2: list A) n :
  (List.length bs1 mod n = List.length bs2 mod n)%nat ->
  padding_len bs1 n = padding_len bs2 n.
Proof. rewrite !padding_len_eqn by assumption; intros ->; reflexivity. Qed.

Lemma padding_len_round {A} (bs: list A) n :
  let rlen := (n * (length bs / n))%nat in
  padding_len (skipn rlen bs) n = padding_len bs n.
Proof.
  destruct (Nat.eq_dec n 0) as [->|]; intros.
  - reflexivity.
  - intros; apply padding_len_mod.
    rewrite skipn_length; subst rlen.
    rewrite <- Nat.mod_eq, Nat.mod_mod by assumption.
    reflexivity.
Qed.

Lemma chunk_split {A} (bs: list A) n:
  (n > 0)%nat ->
  let rlen := (n * (length bs / n))%nat in
  chunk n bs =
  if (length bs mod n =? 0)%nat then chunk n bs
  else chunk n (firstn rlen bs) ++ [skipn rlen bs].
Proof.
  intros.
  pose proof Nat.mod_le (length bs) n ltac:(lia).
  pose proof Nat.mod_upper_bound (length bs) n ltac:(lia).
  destruct (Nat.eqb_spec (length bs mod n) 0) as [Hz|Hnz].
  - reflexivity.
  - rewrite <- (firstn_skipn rlen bs) at 1.
    rewrite !chunk_app; try lia.
    f_equal; rewrite chunk_small; [reflexivity|].
    all: subst rlen.
    + rewrite skipn_length, <- Nat.mod_eq; lia.
    + rewrite firstn_length_le, Nat.mul_comm, Nat.mod_mul; [..| apply Nat.mul_div_le]; lia.
Qed.

Lemma chunk_pad bs n:
  (n > 0)%nat ->
  let rlen := (n * (length bs / n))%nat in
  chunk n (pad bs n) =
  if (length bs mod n =? 0)%nat then chunk n bs
  else chunk n (firstn rlen bs) ++ [pad (skipn rlen bs) n].
Proof.
  intros; unfold pad; rewrite <- (firstn_skipn (n * (length bs / n))%nat bs), <- !app_assoc.
  unshelve erewrite !(chunk_app _ _ (firstn _ _)), !firstn_skipn; try lia.
  subst rlen; rewrite padding_len_round, padding_len_eqn, !Nat_mod_eq'' by lia.
  2-3: rewrite firstn_length_le, Nat.mul_comm, Nat.mod_mul; try lia; apply Nat.mul_div_le; lia.
  destruct (Nat.eqb_spec (length bs mod n) 0) as [->|Hnz]; f_equal.
  - simpl; rewrite app_nil_r; reflexivity.
  - rewrite chunk_small; [reflexivity|].
    rewrite app_length, skipn_length, repeat_length by lia.
    pose proof Nat.mod_le (length bs) n ltac:(lia).
    pose proof Nat.mod_upper_bound (length bs) n ltac:(lia).
    lia.
Qed.

Lemma poly1305_loop_pad z z' msg :
  poly1305_loop z z' msg true =
  poly1305_loop z z' (pad msg 16) false.
Proof.
  unfold poly1305_loop, nlet; autounfold with poly;
    unfold pad, buf_pad; cbn [List.app].

  pose proof Nat.div_mod (length msg) 16 ltac:(lia).

  unfold enumerate; rewrite <- !fold_left_combine_fst by (rewrite seq_length; lia).
  match goal with
  | [  |- fold_left ?f _ _ = fold_left ?f' _ _ ] =>
    erewrite (fold_left_Proper f' f); [ | reflexivity.. | ]; cycle 1
  end. {
    intros * Hin;
      pose proof (Forall_In (Forall_chunk_length_mod 16 ltac:(lia) _) Hin) as Hmod;
      pose proof (Forall_In (Forall_chunk_length_le 16 ltac:(lia) _) Hin) as Hle;
      cbv beta in *.
    unfold padding_len, padded_len in *.
    rewrite (length_padded_mod 16 msg x00) in * by lia.
    destruct Hmod as [ -> | ]; [ | lia].
    simpl repeat; rewrite app_nil_r.
    reflexivity.
  }

  change (msg ++ repeat _ _) with (pad msg 16);
    rewrite (chunk_split msg) by lia; rewrite (chunk_pad msg) by lia.
  unfold pad; rewrite padding_len_eqn, skipn_length, <- Nat.mod_eq, Nat.mod_mod by lia.
  destruct (Nat.eqb_spec (length msg mod 16) 0) as [Hz|Hnz].
  - reflexivity.
  - rewrite !fold_left_app.
    set (fold_left _ (chunk 16 (firstn _ _)) _) as prefix.
    cbn [fold_left List.app]; rewrite <- !app_assoc.
    rewrite app_length, skipn_length, repeat_length; do 3 f_equal.
    symmetry.
    erewrite (app_assoc (repeat _ _) (repeat _ _)).
    rewrite
      <- repeat_app.
    do 4 f_equal.
    lia.
Qed.

Lemma poly1305_pad_header key header message footer pad_message pad_footer tag:
  poly1305 key (pad header 16) message footer false pad_message pad_footer tag =
  poly1305 key header message footer true pad_message pad_footer tag.
Proof.
  unfold poly1305, nlet; destruct array_split_at; destruct buf_split.
  rewrite <- poly1305_loop_pad; reflexivity.
Qed.

Lemma poly1305_pad_message key header message footer pad_header pad_footer tag:
  poly1305 key header (pad message 16) footer pad_header false pad_footer tag =
  poly1305 key header message footer pad_header true pad_footer tag.
Proof.
  unfold poly1305, nlet; destruct array_split_at; destruct buf_split.
  rewrite <- poly1305_loop_pad; reflexivity.
Qed.

Lemma poly1305_pad_footer key header message footer pad_header pad_message tag:
  poly1305 key header message (pad footer 16) pad_header pad_message false tag =
  poly1305 key header message footer pad_header pad_message true tag.
Proof.
  unfold poly1305, nlet; destruct array_split_at; destruct buf_split.
  rewrite <- poly1305_loop_pad; reflexivity.
Qed.

Lemma chacha20poly1305_aead_encrypt_ok' aad key iv constant plaintext tag:
  (length key >= 32)%nat ->
  (length (constant ++ iv) >= 12)%nat ->
  (length constant mod 4 = 0)%nat ->
  (length (constant ++ iv) mod 4 = 0)%nat ->
  0 <= Z.of_nat (length aad) < 2 ^ 32 ->
  0 <= Z.of_nat (length plaintext) < 2 ^ 32 ->
  Spec.chacha20poly1305_aead_encrypt aad key iv constant plaintext =
  chacha20poly1305_aead_encrypt aad key iv constant plaintext tag.
Proof.
  unfold Spec.chacha20poly1305_aead_encrypt, chacha20poly1305_aead_encrypt, nlet, copy;
    autounfold with poly; intros.

  cbn [List.app List.map List.flat_map].
  rewrite !map_app, !map_map with (f := word.of_Z).
  pose proof map_unsigned_of_Z_le_combine as P. cbn zeta in P. rewrite !P. clear P.
  rewrite <- !map_app.
  rewrite <- !chunk_app, flat_map_le_split_combine_chunk;
    [ | solve[eauto] || (try (cbn; lia)) ..].
  rewrite chacha20_encrypt_ok, chacha20_block_ok by eauto.

  apply f_equal2; [ reflexivity | ]. (* FIXME why does f_equal not work? *)

  rewrite !(le_split_zeroes 4 4), <- !app_assoc.
  eassert (?[aad] ++ ?[aad_pad] ++ ?[ciphertext] ++ ?[ciphertext_pad] ++ ?[rest] =
           (?aad ++ ?aad_pad) ++ (?ciphertext ++ ?ciphertext_pad) ++ ?rest) as ->
      by (rewrite <- !app_assoc; reflexivity).

  (* FIXME no need for msg to have length multiple of 16: real thm is that padding message is same as without padding *)
  rewrite poly1305_ok' with (output := tag).
  rewrite !word.unsigned_of_Z_0, !word.unsigned_of_Z_nowrap.
  repeat change (?x ++ repeat x00 _) with (pad x 16).
  rewrite poly1305_pad_header.
  rewrite poly1305_pad_message.
  reflexivity.

  all: try apply length_padded_mod.
  all: try rewrite length_chacha20_encrypt.
  all: eassumption || reflexivity || lia.
Qed.

Lemma chacha20poly1305_aead_encrypt_ok aad key iv constant plaintext tag:
  length key = 32%nat ->
  length constant = 4%nat ->
  length iv = 8%nat ->
  0 <= Z.of_nat (length aad) < 2 ^ 32 ->
  0 <= Z.of_nat (length plaintext) < 2 ^ 32 ->
  Spec.chacha20poly1305_aead_encrypt aad key iv constant plaintext =
  chacha20poly1305_aead_encrypt aad key iv constant plaintext tag.
Proof.
  intros; apply chacha20poly1305_aead_encrypt_ok'.
  all: try rewrite app_length by lia.
  all: try replace (length key); try replace (length constant); try replace (length iv).
  all: eauto.
Qed.

(* Print Assumptions poly1305_ok. *)
(* Print Assumptions chacha20poly1305_aead_encrypt_ok. *)
