(* Rewritten versions of poly1305 and chacha20 that you can compile with Rupicola *)
Require Import Coq.Unicode.Utf8.
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Loops.
(*TODO: move this file to Rupicola.Lib*)
Require Import Crypto.Bedrock.End2End.RupicolaCrypto.Broadcast.
Require Crypto.Bedrock.End2End.RupicolaCrypto.Spec.
Import coqutil.Word.LittleEndianList (le_combine, le_split).
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require coqutil.Word.Naive.
Require Import bedrock2.FE310CSemantics.
Require Import coqutil.Map.SortedListWord.
Import Syntax.Coercions ProgramLogic.Coercions.
Import Datatypes.
Import Lists.List.

Import Loops.
Import LoopCompiler.


Require Import Crypto.Bedrock.End2End.RupicolaCrypto.AbstractLength.
Require Import Crypto.Bedrock.End2End.RupicolaCrypto.LocalsBroadcast.

Notation word := (Naive.word 32).
Notation locals := (FE310CSemantics.locals (word:=word)).
Notation mem :=(@SortedListWord.map 32 (Naive.word 32) Naive.word32_ok Init.Byte.byte).
Notation predicate := (predicate (word:=word) (locals:=locals) (mem:=mem)).

Local Instance locals_ok : map.ok locals := (FE310CSemantics.locals_ok (word:=word)).



Section Bedrock2.

  Declare Scope word_scope.
  Delimit Scope word_scope with word.
  Local Infix "+" := word.add : word_scope.
  Local Infix "*" := word.mul : word_scope.
  
  Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).
  Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").


  (* copied from Low.v, anticipating its removal *)
  Section Low.    

Local Notation "a + b" := (word.add (word := word) a b).
Local Notation "a ^ b" := (word.xor (word := word) a b).
Local Notation "a <<< b" := (word.slu a b + word.sru a (word.sub (word.of_Z 32) b)) (at level 30).

Definition quarter_gallina a b c d : \<< word, word, word, word \>> :=
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
  let '\<a', b', c', d'\> := quarter_gallina a b c d in
  (word.unsigned a', word.unsigned b', word.unsigned c', word.unsigned d').
Proof.
  unfold Spec.quarter.
  repeat rewrite ?word.Z_land_ones_word_add, <- ?word.unsigned_xor_nowrap,
    ?word.Z_land_ones_rotate by (split; reflexivity).
  reflexivity.
Qed.

Lemma quarter_ok a b c d:
  in_bounds 32 a -> in_bounds 32 b -> in_bounds 32 c -> in_bounds 32 d ->
  quarter_gallina (word.of_Z (word:=word) a) (word.of_Z b) (word.of_Z c) (word.of_Z d) =
  let '(a', b', c', d') := Spec.quarter (a, b, c, d) in
  \< word.of_Z a', word.of_Z b', word.of_Z c', word.of_Z d' \>.
Proof.
  unfold in_bounds; intros.
  set (wa := word.of_Z a); set (wb := word.of_Z b); set (wc := word.of_Z c); set (wd := word.of_Z d).
  rewrite <- (word.unsigned_of_Z_nowrap (word:=word)  a),
    <- (word.unsigned_of_Z_nowrap (word:=word) b) by assumption.
  rewrite <- (word.unsigned_of_Z_nowrap (word:=word)  c),
    <- (word.unsigned_of_Z_nowrap (word:=word) d) by assumption.
  rewrite quarter_ok0; subst wa wb wc wd; destruct (quarter_gallina _ _ _ _) as (?&?&?&?); cbn -[word.of_Z word.unsigned].
  rewrite !word.of_Z_unsigned; reflexivity.
Qed.


Lemma quarter_in_bounds a b c d:
  in_bounds 32 a -> in_bounds 32 b -> in_bounds 32 c -> in_bounds 32 d ->
  let '(a', b', c', d') := Spec.quarter (a, b, c, d) in
  in_bounds 32 a' /\ in_bounds 32 b' /\ in_bounds 32 c' /\ in_bounds 32 d'.
Proof.
  unfold in_bounds; intros.
  rewrite <- (word.unsigned_of_Z_nowrap (word:=word)  a),
    <- (word.unsigned_of_Z_nowrap (word:=word) b) by assumption.
  rewrite <- (word.unsigned_of_Z_nowrap (word:=word)  c),
    <- (word.unsigned_of_Z_nowrap (word:=word) d) by assumption.
  rewrite <- (word.unsigned_of_Z_nowrap (word:=word)  a),
    <- (word.unsigned_of_Z_nowrap (word:=word) b) by assumption.
  rewrite <- (word.unsigned_of_Z_nowrap (word:=word)  c),
    <- (word.unsigned_of_Z_nowrap (word:=word) d) by assumption.
  rewrite quarter_ok0; destruct (quarter_gallina _ _ _ _) as (?&?&?&?); cbn -[word.of_Z word.unsigned Z.pow].
  repeat (split; try apply word.unsigned_range).
Qed.

  End Low.
  
Definition quarterround x y z t (st : list word) :=
  let '\<a,b,c,d\> := quarter_gallina (nth x st (word.of_Z 0))
                        (nth y st (word.of_Z 0))
                        (nth z st (word.of_Z 0))
                        (nth t st (word.of_Z 0)) in
  upd (upd (upd (upd st x a) y b) z c) t d.



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
                    let/n (qv0, qv4, qv8,qv12) := quarter_gallina qv0  qv4  qv8 qv12 in
                    let/n (qv1, qv5, qv9,qv13) := quarter_gallina qv1  qv5  qv9 qv13 in
                    let/n (qv2, qv6, qv10,qv14) := quarter_gallina qv2  qv6 qv10 qv14 in
                    let/n (qv3, qv7, qv11,qv15) := quarter_gallina qv3  qv7 qv11 qv15 in
                    let/n (qv0, qv5, qv10,qv15) := quarter_gallina qv0  qv5 qv10 qv15 in
                    let/n (qv1, qv6, qv11,qv12) := quarter_gallina qv1  qv6 qv11 qv12 in
                    let/n (qv2, qv7, qv8,qv13) := quarter_gallina qv2  qv7  qv8 qv13 in
                    let/n (qv3, qv4, qv9,qv14) := quarter_gallina qv3  qv4  qv9 qv14 in
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

  (*TODO: don't hardcode 0*)
  #[export] Instance spec_of_chacha20 : spec_of "chacha20_block" :=
    fnspec! "chacha20_block" out key nonce / (pt k n : list Byte.byte) (R Rk Rn : mem -> Prop),
      { requires t m :=
          m =* pt$@out * R /\ length pt = 64%nat /\
            m =* k$@key * Rk /\ length k = 32%nat /\
            (*TODO: account for difference in nonce length*)
            m =* n$@nonce * Rn /\ length n = 12%nat;
        ensures T m := T = t /\ exists ct, m =* ct$@out * R /\ length ct = 64%nat /\
                                             ct = Spec.chacha20_block k (le_split 4 (word.of_Z 0) ++ n) }.


Lemma word_add_pair_eqn st:
  (let '(s, t) := st in Z.land (s + t) (Z.ones 32)) =
  word.unsigned (word.of_Z (word:=word) (fst st) + word.of_Z (snd st))%word.
Proof.
  destruct st.
  rewrite Z.land_ones, <- word.ring_morph_add, word.unsigned_of_Z by lia.
  reflexivity.
Qed.

(*Copied from Derive anticipating its removal*)
Section Derive.

  Instance spec_of_quarter : spec_of "quarter" :=
    fnspec! "quarter" (a b c d : word) ~> (a' b' c' d' : word),
    { requires tr m := True;
      ensures tr' m' :=
        tr = tr' /\
        (m = m' :> mem) /\
        let '\<w, x, y, z\> := quarter_gallina a b c d in
        (a' = w /\ b' = x /\ c' = y /\ d' = z)}.

  Derive quarter SuchThat
         (defn! "quarter" ("a", "b", "c", "d") ~> "a", "b", "c", "d" { quarter },
          implements (quarter_gallina) using [])
         As quarter_body_correct.
  Proof.
    compile.
  Qed.
  
Lemma compile_quarter : forall {tr mem locals functions} a b c d,
      let v := quarter_gallina a b c d in

      forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
             a_var b_var c_var d_var,

        spec_of_quarter functions ->
        
        map.get locals a_var = Some a ->
        map.get locals b_var = Some b ->
        map.get locals c_var = Some c ->
        map.get locals d_var = Some d ->

        (let v := v in
           let '\<w, x, y, z\> := v in
        (<{ Trace := tr;
            Memory := mem;
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

End Derive.


  
  Existing Instance spec_of_quarter.

  Existing Instance word_ac_ok.

  
  Lemma nat_iter_rel {A B} (R : A -> B -> Prop) acca accb fa fb n
    : R acca accb ->
      (forall acca accb, R acca accb -> R (fa acca) (fb accb)) ->
      R (Nat.iter n fa acca) (Nat.iter n fb accb).
  Proof.
    intros.
    induction n; simpl; eauto.
  Qed.

  
  Lemma nat_iter_pred {A} (R : A -> Prop) f acc n
    : R acc ->
      (forall acc, R acc -> R (f acc)) ->
      R (Nat.iter n f acc).
  Proof.
    intros.
    induction n; simpl; eauto.
  Qed.
  
  Lemma length_quarterround a b c d l
    : length (Spec.quarterround a b c d l) = length l.
  Proof.
    unfold Spec.quarterround.
    generalize (Spec.quarter (nth a l 0, nth b l 0, nth c l 0, nth d l 0)) as p.
    intro p; destruct p as [[[? ?] ?] ?].
    simplify_len.
    reflexivity.
  Qed.
  
    #[refine]
      Instance abstr_quarterround x y z t l llen `{Abstractable _ _ (@length _) l llen}
      : Abstractable (@length _) (Spec.quarterround x y z t l) llen := Abstr _.
    Proof.
      rewrite (length_quarterround _ _).
      f_equal.
      apply H.
    Qed.

    (*TODO: move to the right place*)
     Hint Extern 1 (Abstractable (@length _) (Spec.quarterround _ _ _ _ _) _) =>
      apply abstr_quarterround;shelve : abstraction.
  
Lemma quarterround_ok x y z t st :
  Forall (in_bounds 32) st ->
  List.map word.of_Z (Spec.quarterround x y z t st) =
  quarterround x y z t (List.map word.of_Z st).
Proof.
  unfold Spec.quarterround, quarterround, nlet; intros H.
  rewrite forall_in_bounds in H by lia.
  rewrite !map_nth, !quarter_ok by auto.
  destruct (Spec.quarter _) as (((?&?)&?)&?).
  rewrite !map_upd; reflexivity.
Qed.


Lemma nth_upd {A} (l: list A) (a d: A) (i k: nat):
  ((i >= length l)%nat /\ nth i (upd l k a) d = d) \/
  (i = k /\ nth i (upd l k a) d = a) \/
  (i <> k /\ nth i (upd l k a) d = nth i l d).
Proof.
  destruct (Nat.lt_ge_cases i (length l)); cycle 1; [ left | right ].
  - unfold upd; rewrite nth_overflow; try simplify_len; auto.
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

Lemma quarterround_in_bounds x y z t a:
  Forall (in_bounds 32) a ->
  Forall (in_bounds 32) (Spec.quarterround x y z t a).
Proof.
  unfold Spec.quarterround, nlet; intros Ha.
  pose proof Ha as Ha'; rewrite forall_in_bounds in Ha by lia.
  pose proof quarter_in_bounds (nth x a 0) (nth y a 0) (nth z a 0) (nth t a 0)
       ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(eauto) as Hb.
  destruct (Spec.quarter _) as (((?&?)&?)&?).
  destruct Hb as (?&?&?&?).
  repeat (apply Forall_upd; auto).
Qed.


  Definition list_to_tuple_16 (l : list word) :=
    match l with
    | [car; car0; car1; car2; car3; car4; car5; car6; car7; car8; car9; car10; car11; car12; car13; x0] =>
        \< car, car0, car1, car2, car3, car4, car5, car6, car7, car8, car9, car10, car11, car12, car13, x0 \>
    | _ => \< word.of_Z 0,word.of_Z 0,word.of_Z 0,word.of_Z 0,
             word.of_Z 0,word.of_Z 0,word.of_Z 0,word.of_Z 0,
             word.of_Z 0,word.of_Z 0,word.of_Z 0,word.of_Z 0,
             word.of_Z 0,word.of_Z 0,word.of_Z 0,word.of_Z 0 \>
    end.

  Lemma list_to_tuple_16_injective l1 l2
    :  length l1 = 16%nat ->
       length l2 = 16%nat ->
       list_to_tuple_16 l1 = list_to_tuple_16 l2 -> l1 = l2.
  Proof.
    repeat (destruct l1 as [|? l1]; cbn [length]; try lia).

    repeat (destruct l2 as [|? l2]; cbn [length]; try lia).
    cbv.
    intros _ _ H; inversion H; reflexivity.
  Qed.

  Strategy 10 [list_to_tuple_16 nlet].
  Strategy 20 [quarterround Spec.quarterround].
  Strategy opaque [quarter_gallina Spec.quarter Nat.iter].


  Lemma destruct_16 {A} P
          : (forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x0 : A),
                 P \<x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x0\>) ->
            forall a, P a.
  Proof.
    do 15 destruct a as [? a].
    eauto.
  Qed.

  Lemma chacha20_block_ok key nonce
    : length key = 32%nat ->
      length nonce = 12%nat ->
      Spec.chacha20_block key ((le_split 4 (word.of_Z 0))++nonce) = chacha20_block' key nonce.
  Proof.
    intros Hlenk Hlenn.
  unfold Spec.chacha20_block, chacha20_block'.
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
  
  revert dependent x0;  intro x0; simple apply destruct_16 with (a:=x0); intros.
  
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
  

  lazymatch goal with |- map word.of_Z ?lhs = _ => set lhs end.
  assert (length l = 16%nat) as Hlen.
  {
    subst l.
    apply nat_iter_pred.
    { repeat simplify_len; reflexivity. }
    { intros. simplify_len; reflexivity. }
  }

  apply list_to_tuple_16_injective.
  { repeat simplify_len; reflexivity. }
  {
    reflexivity.
  }
  cbn [list_to_tuple_16].

  subst l; rewrite Heqx0; clear Heqx0.
  eapply Nat_iter_rew_inv
    with (g:=fun l => list_to_tuple_16 (map word.of_Z l))
         (P := fun l => Forall (in_bounds 32) l /\ length l = 16%nat); intros.
  {
    destruct H.
    split.
    1:repeat apply quarterround_in_bounds; auto.
    simplify_len; reflexivity.
  }
  
  {
    destruct H.
    repeat rewrite quarterround_ok.
    2-9:repeat apply quarterround_in_bounds; auto.
    repeat (destruct a as [|? a]; cbn [length] in H0; try (exfalso;lia)).
    cbn [list_to_tuple_16 map].


    do 4 (lazymatch goal with
      |- context ctx [(quarterround ?a ?b ?c ?d (?e1::?lst))] =>
        set (quarterround a b c d (e1::lst)) as l1;
        let g := context ctx [l1] in
        change g
    end;
    remember l1 eqn:Heql;
      subst l1;
      unfold quarterround in Heql;
    cbn [nth] in Heql;
    revert Heql;
    set (quarter_gallina _ _ _ _) as l2;
    destruct l2 as [? [? [? ?]]];
    intro Heql;
    cbn-[word.of_Z] in Heql;
          subst l).

    unfold nlet.
    do 4 (lazymatch goal with
      |- context ctx [(quarterround ?a ?b ?c ?d (?e1::?lst))] =>
        set (quarterround a b c d (e1::lst)) as l1;
        let g := context ctx [l1] in
        change g
    end;
    remember l1 eqn:Heql;
      subst l1;
      unfold quarterround in Heql;
    cbn [nth] in Heql;
    revert Heql;
    set (quarter_gallina _ _ _ _) as l2;
    destruct l2 as [? [? [? ?]]];
    intro Heql;
    cbn-[word.of_Z] in Heql;
          subst l).
    reflexivity.
  }
  {
    split.
    {
      rewrite !Forall_app.
      repeat split.
      all: change 32 with (8 * Z.of_nat 4).
      all: apply Forall_le_combine_in_bounds.
      all: lia.
    }
    { repeat simplify_len; reflexivity. }
  }
  {
    rewrite !map_app, !map_map.
    change  (λ x : list Init.Byte.byte, word.of_Z (LittleEndianList.le_combine x)) with le_combine.
    rewrite chunk_app_chunk; try lia.
    2:{ simplify_len; lia. }
    cbn [map].
    change (le_combine (LittleEndianList.le_split 4 (word.unsigned (word.of_Z 0)))) with (word.of_Z (word:=word) 0).
    remember ((map le_combine (chunk 4 (list_byte_of_string "expand 32-byte k")) ++
                 map le_combine (chunk 4 key) ++ word.of_Z 0 :: map le_combine (chunk 4 nonce))).
    assert (length l = 16%nat) by (repeat simplify_len; reflexivity).
    clear Heql Hlen.
    repeat (destruct l as [|? l]; cbn [length] in H; try lia).
    reflexivity.
  }
  Qed.


  (*TODO: continue from here*)
  
  (*used because concrete computation on maps seems to be slow here*)
  Ltac eval_map_get :=
    repeat rewrite ?map.remove_put_same,
      ?map.remove_put_diff,
      ?map.get_put_diff,
      ?map.remove_empty by (compute;congruence);
    rewrite map.get_put_same; reflexivity.

  
  
  Ltac dedup s :=
    repeat rewrite map.put_put_diff with (k1:=s) by congruence;
    rewrite ?map.put_put_same with (k:=s).
  

Ltac cmd_step lem :=
  try simple eapply compile_nlet_as_nlet_eq;
  simple eapply lem.

Ltac solve_NoDup :=
  lazymatch goal with
  | |- NoDup _ =>
      repeat constructor; simpl;
      intuition congruence
  | |- _ => fail "Not a NoDup"
  end.

Hint Extern 1 (locals_array_expr _ _ _ _ (_::_)) =>
       constructor; shelve : compiler.
Hint Extern 1 (locals_array_expr _ _ _ _ (_++_)) =>
         simple apply locals_array_expr_app; shelve : compiler.
Hint Extern 5 (locals_array_expr _ _ _ _ (map le_combine (chunk 4 _))) =>
         simple eapply expr_load_word_of_byte_array; shelve : compiler. 
Ltac greedy_eauto db := unshelve eauto 1 with db; shelve_unifiable.

Ltac deduce_map_key :=
  let v := lazymatch goal with |- _ = Some ?v => v end in
  let k := lazymatch goal with |- map.get _ ?k = Some _ => k end in
  lazymatch goal with
    |- context [ map.put _ ?k' v] =>
      unify k k'
  end.

Derive chacha20_block SuchThat
  (defn! "chacha20_block" ("st", "key", "nonce") { chacha20_block },
    implements (Spec.chacha20_block) using [ "quarter" ])
  As chacha20_block_body_correct.
Proof.
  compile_setup.
  replace (pred _) with (pred (Spec.chacha20_block k (le_split 4 (word.of_Z 0) ++ n))) by reflexivity.
  rewrite chacha20_block_ok by intuition.
  unfold chacha20_block'.
  compile_step.

  
  cmd_step @compile_set_locals_array; [| solve_NoDup| ..].
  {
    
    cbn -[combine le_combine word.of_Z].
    repeat (greedy_eauto compiler || compile_step).
    all: repeat simplify_len.
    2: compute; reflexivity.
    now compile_step.
    {
      cbn -[combine le_combine].
      eapply expr_compile_var.
      deduce_map_key.      
      eval_map_get.
    }    
    cbn -[combine le_combine word.of_Z].
    repeat (greedy_eauto compiler || compile_step).
    all: repeat simplify_len.
    all: repeat compile_step.
    all: cbn -[combine le_combine].
    eapply expr_compile_var.
    deduce_map_key.      
    eval_map_get.
  }
  compile_step.
  let l' := eval cbn in l in
    change l with l'.
  rewrite Nat_iter_as_nd_ranged_for_all with (i:=0).
  change (0 + Z.of_nat 10) with 10%Z.

  compile_step.
  compile_step.
  assert (m = m) by reflexivity.
  compile_step; [ now compile_step
                | now compile_step
                | now repeat compile_step 
                | now repeat compile_step 
                | now repeat compile_step
                | lia
                | .. ].
  {
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

        Ltac concrete_maps_equal :=
          eapply map.map_ext;
          intro;
          repeat (rewrite ?map.get_put_diff by assumption;
                  lazymatch goal with
                    |- _ = map.get (map.put _ ?k2 _) ?k1 =>
                      destruct (String.eqb_spec k1 k2);
                      [subst; rewrite ?map.get_put_diff, ?map.get_put_same by congruence; now auto
                      | rewrite map.get_put_diff with (k:=k1) (k':=k2) by assumption]
                  end);
          reflexivity.
        concrete_maps_equal.
      }
      ecancel_assumption.
  }
  }
  Optimize Proof.
  Optimize Heap.
  
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  
  (*TODO: need to strengthen this a la broadcast
    so that it allows other vars to change, doesn't need fresh names
   *)
  cmd_step @compile_set_locals_array.
  {
   (* cbn -[combine le_combine word.of_Z word.add]. *)
    
    Hint Extern 5 (locals_array_expr _ _ _ _ (map (fun '(_,_) => word.add _ _) _)) =>
           simple eapply array_expr_compile_word_add; shelve : compiler.
    (*repeat (greedy_eauto compiler || compile_step).*)
    
    greedy_eauto compiler.
    {
      repeat (greedy_eauto compiler || compile_step).
      all:apply expr_compile_var.
      all: deduce_map_key.
      all: eval_map_get.
    }
    {
      let l := constr:(chunk 4 (list_byte_of_string "expand 32-byte k")) in
      let l' := eval compute in l in
        change l with l'.
      cbn [map app].
      repeat (greedy_eauto compiler || compile_step).
      all:  repeat simplify_len.
      2: { compute; reflexivity. }
      { reflexivity. }
      {
        apply expr_compile_var.
        deduce_map_key.
        cbn.
        eval_map_get.
      }
      
      repeat (greedy_eauto compiler || compile_step).
      all:  repeat simplify_len; try reflexivity.
      
      apply expr_compile_var.
      deduce_map_key.
      cbn.
      eval_map_get.
    }
  }
  {
    solve_NoDup.
  }
  compile_step.
  cbv [le_split].
  let l' := open_constr:(_) in
  replace l0 with l'; cycle 1.
  {
    subst l0.
    change (array_locs ?a ?b ?c) with (array_locs a b v1).
    set (array_locs _ _ _) as l0.
    let l' := eval cbn -[v1 combine word.of_Z] in l0 in change l0 with l'.
    clear l0.
    cbv [map.putmany_of_list gs].
    Ltac dedup_all keys :=
      lazymatch keys with
      | ?k :: ?keys => dedup k; dedup_all keys
      | _ => idtac
      end.
    let m := match goal with |- _ = ?m => m end in
    let keys := eval compute in (map.keys m) in
      dedup_all keys.
    reflexivity.
  }  
  
  Optimize Proof.
  Optimize Heap.
  
  (*TODO: earlier in derivation: why is key counted to 32? definitely wrong*)
  (*TODO: do I need to eval the combine?*)
  rewrite <- ListUtil.flat_map_map.
  (*change (flat_map _ (map _ v1)) with (bytes_of_w32s v1).*)
  
  simple eapply compile_nlet_as_nlet_eq.
  change (pred (let/n x as "st" eq:_ := _ in x))
    with (pred (let/n v1 as "st" eq:_ := v1 in
                let/n x as "st" eq:_ := flat_map (LittleEndianList.le_split 4) (map word.unsigned v1) in x)).
  simple eapply compile_store_locals_array.
  {
    rewrite unroll_len with (l:=v1) (a:= word.of_Z 0) at 1.
    replace (length v1) with 16%nat.
    cbn [unroll app].
    {
      repeat constructor; repeat compile_step.
      all: apply expr_compile_var; cbn [word word.rep Naive.gen_word word.of_Z].
     (* TODO: remove need for the above cbn*)
      all: deduce_map_key;eval_map_get.
    }
    {
      simplify_len.
      reflexivity.
    }
  }
  2:{
    eapply expr_compile_var.
    eval_map_get.
  }
  2:{
    compile_step.
  }
  {
    repeat simplify_len.
    reflexivity.
  }
  compile_step.
  unfold nlet_eq.
  
  (*TODO: compile_step takes too long (related to computations on maps?)*)
  unshelve refine (compile_unsets _ _ _); [ shelve | intros |  ]; cycle 1.
  simple apply compile_skip.
  2: exact [].
  cbv beta delta [wp_bind_retvars pred].
  eexists; intuition eauto.
  eexists; split.
  {
    pose proof (bytes_of_words (width:=32) v2 out) as H'.
    cbn [id] in H'.
    change  (Z.of_nat (Memory.bytes_per (width:=32) access_size.word)) with 4 in H'.
    lazymatch goal with
      [ H : _ ?m |- _ ?m] => seprewrite_in H' H
    end.
    now compile_step.
  }
  compile_step.
  {
    simplify_len.
    reflexivity.
  }
  auto.
Qed.



(*
Local Open Scope string_scope.
Import Syntax Syntax.Coercions.
Require Import bedrock2.NotationsCustomEntry.
Import ListNotations.
Import Coq.Init.Byte.
Set Printing Depth 150.
Compute chacha20_block.
Print Assumptions chacha20_block_body_correct.
*)

End Bedrock2.
