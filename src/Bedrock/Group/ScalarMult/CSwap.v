From Coq.Program Require Import Tactics.
Require Import coqutil.Word.Bitwidth.
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Loops.
Require Import bedrock2.Semantics.
Require Import coqutil.Byte.
Local Open Scope Z_scope.
Require Import Rupicola.Lib.Arrays.


Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Alloc.
Require Import Rupicola.Lib.SepLocals.
Require Import Rupicola.Lib.ControlFlow.DownTo.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Util.NumTheoryUtil.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import bedrock2.ZnWords.


(*TODO: modified from rupicola example; unify?*)
Section __.

  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}.
  Context {field_representaton : FieldRepresentation}.
  Context {field_representation_ok : FieldRepresentation_ok}.
  (*TODO: move this requirement to the right place,
    or find a way to discharge it
    Should this go in FieldReprsentation_ok?
   *)
  Context (felem_size_in_words_small
    : Z.of_nat felem_size_in_words < 2^width).
  Hint Resolve relax_bounds : compiler.


  Notation all_1s := (bits.of_Z _ (-1) : word).

  Section Gallina.


    Definition is_mask mask : Prop :=
      mask = all_1s \/ mask = bits.of_Z _ 0.

    Definition mask_of_bool (b : bool) :=
      if b then all_1s else bits.of_Z _ 0.


    Instance HasDefault_word : HasDefault word :=
      bits.of_Z _ 0.

    Instance: HasDefault (word * word) := (default, default).
    Existing Instance Convertible_Z_nat.

    Definition cswap_low mask
               (a1: ListArray.t word)
               (a2: ListArray.t word) :=
      let from := 0%Z in
      let to := (Z.of_nat felem_size_in_words) in
      let/n nmask := Zmod.sub (bits.of_Z _ 0) mask in
      let/n mask := Zmod.not nmask in
      let/n (a1, a2) :=
         nd_ranged_for_all
           from to
           (fun '\<a1,a2\> idx =>
              let/n v1 := ListArray.get a1 idx in
              let/n v2 := ListArray.get a2 idx in
              let/n r1 := Zmod.or (Zmod.and mask v1)
                                 (Zmod.and nmask v2) in
              let/n r2 := Zmod.or (Zmod.and mask v2)
                                 (Zmod.and nmask v1) in
              let/n a1 := ListArray.put a1 idx r1 in
              let/n a2 := ListArray.put a2 idx r2 in
              \<a1, a2\>) \<a1, a2\> in
      \<a1, a2\>.


    Definition cswap_word1 (mask nmask a b : word) :=
      Zmod.or (Zmod.and mask a)
              (Zmod.and nmask b).
    Definition cswap_word2 (mask nmask a b : word) :=
      Zmod.or (Zmod.and mask b)
              (Zmod.and nmask a).

    Definition cswap_combine (mask : word)
               (a1: ListArray.t word)
               (a2: ListArray.t word) :=
      let/n from := 0%Z in
      let/n to := (Z.of_nat felem_size_in_words) in
      let/n nmask := Zmod.sub (bits.of_Z _ 0) mask in
      let/n mask := Zmod.not nmask in
      let/n (a1, a2) :=
         List.split
         (nd_ranged_for_all from to
            (fun ab (idx : Z) =>
             let/d xab := ListArray.get ab idx in
             let/d yab :=
               (cswap_word1 mask nmask (fst xab) (snd xab),
               cswap_word2 mask nmask (fst xab) (snd xab)) in
             let/d ab1 := ListArray.put ab idx yab in
             ab1) (combine a1 a2)) in
      \<a1, a2\>.

    Definition cswap {T} (swap: bool) (a b: T) :=
      if swap then \<b, a\> else \<a, b\>.

  End Gallina.


  Lemma foldl_dep'_funext {A B} l (a : A) (f1 f2 : A -> forall (x : B), In x l -> A) l' subl (exit : A-> bool)
    : (forall a (x : B) (pf : In x l), f1 a x pf = f2 a x pf) ->
      foldl_dep' l f1 exit l' subl a
      = foldl_dep' l f2 exit l' subl a.
  Proof using Type.
    revert subl a.
    induction l';
      simpl; intros; auto.
    destruct (exit a0); auto.
    rewrite IHl'; auto.
    rewrite H.
    reflexivity.
  Qed.

  Lemma ranged_for_fequal {A} from1 to1 f1 (init1 : A) from2 to2 f2 init2
    : from1 = from2 ->
       to1 = to2 ->
       (forall a t idx p1 p2, f1 a t idx p1 = f2 a t idx p2) ->
       init1 = init2 ->
       ranged_for from1 to1 f1 init1
       = ranged_for from2 to2 f2 init2.
  Proof using Type.
    intros; subst.
    unfold ranged_for,ranged_for', ranged_for_break.
    f_equal.
    apply foldl_dep'_funext.
    eauto.
  Qed.


  Lemma wrap_felem_size_in_words_small
    : (Z.of_nat felem_size_in_words) mod 2 ^ width = (Z.of_nat felem_size_in_words).
  Proof using felem_size_in_words_small.

    pose proof felem_size_in_words_small.
    rewrite Z.mod_small; lia.
  Qed.


Section __.
  Context {A B: Type}.

  Open Scope Z_scope.

  Context from to
          (body: forall (acc: A) (tok: ExitToken.t) (idx: Z),
              from - 1 < idx < to ->
              (ExitToken.t * (ListArray.t A * ListArray.t  B)))
          (a0: (ListArray.t A * ListArray.t  B)).

  Context `{HasDefault A} `{HasDefault B}.
  Instance: HasDefault (A * B) := (default, default).

  Instance Convertible_Z_nat : Convertible Z nat := Z.to_nat.


  Lemma replace_nth_combine  n (la: list A) (lb: list B) a b
    :  (replace_nth n (combine la lb) (a,b))
       = combine (replace_nth n la a) (replace_nth n lb b).
  Proof using Type.
    revert lb n; induction la; destruct lb; simpl; auto;
      destruct n; simpl; auto.
    f_equal.
    eauto.
  Qed.

  Lemma fst_nth_combine n (la: list A) (lb: list B)
    : length la = length lb ->
      (fst (nth n (combine la lb) default))
      = (nth n la default).
  Proof using a0 body field_representaton.
    revert lb n; induction la; destruct lb; simpl; auto;
      destruct n; simpl; try tauto; try lia.
    intro H'; inversion H'; clear H'; subst.
    eauto.
  Qed.

  Lemma snd_nth_combine n (la: list A) (lb: list B)
    : length la = length lb ->
      (snd (nth n (combine la lb) default))
      = (nth n lb default).
  Proof using a0 body field_representaton.
    revert lb n; induction la; destruct lb; simpl; auto;
      destruct n; simpl; try tauto; try lia.
    intro H'; inversion H'; clear H'; subst.
    eauto.
  Qed.

  Lemma nd_ranged_for_combine: forall n (lA: list A) (lB: list B) fA fB,
      length lA = length lB ->
    let '\<x,y\> := nd_ranged_for_all
      0%Z (Z.of_nat n)
      (fun ab idx =>
         let/d xa := ListArray.get (P2.car ab) idx in
         let/d xb := ListArray.get (P2.cdr ab) idx in
         let/d ya := fA xa xb in
         let/d yb := fB xa xb in
         let/d a := ListArray.put (P2.car ab) idx ya in
         let/d b := ListArray.put (P2.cdr ab) idx yb in
         \<a, b\>)
      \<lA, lB\>
  in (x,y) =
    List.split
      (nd_ranged_for_all
         0 (Z.of_nat n)
         (fun ab idx =>
            let/d xab := ListArray.get ab idx in
            let/d yab := (fA (fst xab) (snd xab), fB (fst xab) (snd xab)) in
            let/d ab := ListArray.put ab idx yab in
            ab)
         (combine lA lB)).
  Proof using a0 body field_representaton.
    intros n la lb fa fb leq.
    rewrite <- !fold_left_as_nd_ranged_for_all.
    generalize (z_range 0 (Z.of_nat n)).
    intro l.
    revert la lb leq.
    induction l.
    {
      intros.
      simpl.
      rewrite combine_split by auto.
      reflexivity.
    }
    {
      intros.
      unfold ListArray.get, ListArray.put, dlet in *.
      subst x0 y.
      simpl in *.
      rewrite replace_nth_combine.
      rewrite <- IHl.
      rewrite fst_nth_combine, snd_nth_combine by auto.
      reflexivity.
      rewrite !replace_nth_length.
      auto.
    }
  Qed.

  End __.

  Lemma cswap_low_combine_eq mask a1 a2
    : length a1 = length a2 ->
      cswap_low mask a1 a2 = cswap_combine mask a1 a2.
  Proof using Type.
    intros.
    unfold cswap_low.
    unfold cswap_combine.
    unfold nlet.

    set (List.split _).
    set (nd_ranged_for_all _ _ _ _).
    enough (p = (P2.car y, P2.cdr y)).
    rewrite H0; reflexivity.
    etransitivity.
    symmetry.
    (* use [rapply] instead of [eapply] to work around [eapply] inferring over-tight universe constraints :-( *)
    rapply (@nd_ranged_for_combine); eauto.
    reflexivity.
    Unshelve.
    all: eauto.
  Qed.

  Lemma split_map_combine {A B C D} (f : A * B -> C * D) a1 a2
    : List.split (List.map f (combine a1 a2))
      = (List.map (fun p => fst (f p)) (combine a1 a2), List.map (fun p => snd (f p)) (combine a1 a2)).
  Proof using Type.
    revert a2; induction a1; destruct a2; intros; simpl in *; auto.
    rewrite (surjective_pairing (f (a,b))).
    rewrite (surjective_pairing (List.split _)).
    simpl.
    specialize (IHa1 a2).
    rewrite (surjective_pairing (List.split _)) in IHa1.
    congruence.
  Qed.


  Lemma z_lt_width : (0 <= width)%Z.
  Proof using field_representaton.
    destruct width_cases; lia.
  Qed.



  Lemma all_1s_and : forall x, Zmod.and all_1s x = x.
  Proof using field_representaton.
    intros.
    rewrite Zmod.of_Z_m1, word.and_comm.
    apply word.and_m1_r, width_pos.
  Qed.

  Lemma word_not_all1s : Zmod.not all_1s = bits.of_Z _ 0.
  Proof using field_representaton.
    rewrite Zmod.of_Z_m1. apply bits.not_m1.
  Qed.


  Lemma word_not_impl (x : word)
    : Zmod.not x = Zmod.sub (bits.of_Z _ (-1)) x.
  Proof using field_representaton.
    rewrite <- (Zmod.of_Z_signed (Zmod.not x)).
    rewrite (word.signed_not_nowrap _ width_pos).
    rewrite <- (Zmod.of_Z_signed x).
    rewrite <- Zmod.of_Z_sub.
    f_equal.
    rewrite (Zmod.of_Z_signed x).
    unfold Z.lnot.
    lia.
  Qed.


  Lemma word_not_zero : Zmod.not (bits.of_Z _ 0) = all_1s.
  Proof using field_representaton.
    rewrite word_not_impl.
    rewrite <- (Zmod.of_Z_unsigned (Zmod.sub _ _)).
    rewrite <- Zmod.of_Z_sub.
    rewrite Zmod.of_Z_unsigned.
    reflexivity.
  Qed.

  Lemma zero_and (x : word)
    : Zmod.and (bits.of_Z _ 0) x = bits.of_Z _ 0.
  Proof using.
    rewrite word.and_comm. apply word.and_0_r.
  Qed.


  Lemma sub_zero (a : word) : Zmod.sub a (bits.of_Z _ 0) = a.
  Proof using field_representaton.
    rewrite <- (Zmod.of_Z_signed a).
    rewrite <-Zmod.of_Z_sub.
    replace (Zmod.signed a - 0) with (Zmod.signed a) by lia.
    reflexivity.
  Qed.


  Lemma zero_minus_one
    : (Zmod.sub (bits.of_Z _ 0) (bits.of_Z _ 1)) = all_1s.
  Proof using.
    rewrite <- Zmod.of_Z_sub.
    reflexivity.
  Qed.

  Lemma cswap_combine_eq mask a1 a2
    : (mask = bits.of_Z _ 0) \/ (mask = bits.of_Z _ 1) ->
      felem_size_in_words = length a1 ->
      felem_size_in_words = length a2 ->
      cswap_combine mask a1 a2 = cswap (Zmod.eqb mask (bits.of_Z _ 1)) a1 a2.
  Proof using.
    unfold cswap,cswap_combine, nlet; intros.
    assert (felem_size_in_words = (length (combine a1 a2))).
    {
      rewrite H0.
      rewrite combine_length.
      lia.
    }
    rewrite H2.
    rewrite <- map_as_nd_ranged_for_all
    with (f := fun p=> if Zmod.eqb mask (bits.of_Z _ 1) then ((snd p), (fst p)) else ((fst p), (snd p))).
    {
      destruct H; subst;
        [ rewrite word.eqb_ne | rewrite Zmod.eqb_refl].
      2:{
        intro H3.
        apply (f_equal Zmod.unsigned) in H3.
        rewrite Zmod.unsigned_0, bits.unsigned_1 in H3 by (pose proof width_pos; lia).
        lia.
      }
      all: rewrite split_map_combine;
        simpl;
        repeat change (fun a => ?f a) with f;
        rewrite ListUtil.map_fst_combine, ListUtil.map_snd_combine;
        rewrite <- H0, H1;
        rewrite firstn_all;
        rewrite <- H1, H0;
        rewrite firstn_all;
        reflexivity.
    }
    {
      unfold acts_as_replace_nth.
      intros.
      unfold dlet.
      unfold ListArray.put.
      unfold cast, Core.Convertible_Z_nat.
      rewrite Nat2Z.id.
      rewrite replace_nth_app2; eauto.
      f_equal.
      rewrite Nat.sub_diag.
      simpl.

      destruct a.
      unfold ListArray.get.
      unfold cast, Core.Convertible_Z_nat;
        rewrite !Nat2Z.id.
      rewrite !app_nth2; eauto.
      rewrite !Nat.sub_diag.
      simpl.
      f_equal.

      unfold cswap_word1, cswap_word2.

      destruct H; subst;
        [rewrite word.eqb_ne | rewrite Zmod.eqb_refl ];
        f_equal.

      all: rewrite ?sub_zero.
      all: rewrite ?zero_minus_one.
      all: rewrite ?word_not_all1s.
      all: rewrite ?word_not_zero.
      all: rewrite ?all_1s_and.
      all: rewrite ?zero_and.
      all: rewrite ?Zmod.of_Z_0, ?word.or_0_l, ?word.or_0_r.
      all: try reflexivity.

      {
        intro H3.
        apply (f_equal Zmod.unsigned) in H3.
        rewrite Zmod.unsigned_0, bits.unsigned_1 in H3 by (pose proof width_pos; lia).
        lia.
      }
    }
  Qed.


  (*TODO: move to NoExprReflection.v*)
  Lemma compile_word_not
        {tr m l functions} x :
    let v := Zmod.not x in
    forall P (pred: P v -> predicate)
      (k: nlet_eq_k P v) k_impl
      x_var var,
      map.get l x_var = Some x ->
      (let v := v in
       <{ Trace := tr;
          Memory := m;
          Locals := map.put l var v;
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := m;
         Locals := l;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.op1 op1.not (expr.var x_var)))
              k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof using field_representaton.
    repeat (eexists; split; eauto).
  Qed.
  Hint Extern 10 => simple eapply compile_word_not; shelve : compiler.

  Import SizedListArrayCompiler.
  Import LoopCompiler.
  Hint Extern 10 (_ < _) => lia: compiler_side_conditions.

    Instance spec_of_cswap : spec_of "felem_cswap" :=
      fnspec! "felem_cswap" mask ptr1 ptr2 / c1 c2 R,
        (*TODO: if b then bw should be all 1s*)
        { requires tr mem :=
            (mask = bits.of_Z _ 0 \/ mask = bits.of_Z _ 1) /\
            (sizedlistarray_value AccessWord felem_size_in_words ptr1 c1
             * sizedlistarray_value AccessWord felem_size_in_words ptr2 c2 * R)%sep mem;
          ensures tr' mem' :=
          tr' = tr /\
            let/d p := cswap_low mask c1 c2 in
            let (c1,c2) := p in
            (sizedlistarray_value AccessWord felem_size_in_words ptr1 c1
             * sizedlistarray_value AccessWord felem_size_in_words ptr2 c2 * R)%sep mem' }.

  Import LoopCompiler.
  Derive felem_cswap SuchThat
           (defn! "felem_cswap" ("mask", "a1", "a2") { felem_cswap },
             implements cswap_low)
           As cswap_body_correct.
  Proof.
    pose proof felem_size_in_words_small.
    compile.
    lia.
  Qed.

    Lemma compile_felem_cswap {tr m l functions} swap (lhs rhs : Zmod M) :
      let v := cswap swap lhs rhs in
      forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
             R mask_var bounds lhs_ptr lhs_var rhs_ptr rhs_var,

        spec_of_cswap functions ->

        map.get l mask_var = Some (bits.of_Z _ (Z.b2z swap)) ->

        map.get l lhs_var = Some lhs_ptr ->
        map.get l rhs_var = Some rhs_ptr ->

        (FElem bounds lhs_ptr lhs * FElem bounds rhs_ptr rhs * R)%sep m ->

        (let v := v in
         forall m',
           (FElem bounds lhs_ptr (P2.car v) * FElem bounds rhs_ptr (P2.cdr v) * R)%sep m' ->
           (<{ Trace := tr;
               Memory := m';
               Locals := l;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := m;
           Locals := l;
           Functions := functions }>
        cmd.seq
          (cmd.call [] "felem_cswap" [expr.var mask_var; expr.var lhs_var; expr.var rhs_var])
          k_impl
        <{ pred (nlet_eq [lhs_var; rhs_var] v k) }>.
  Proof using ext_spec_ok locals_ok mem_ok.
    unfold FElem.
    rewrite !FElem_as_array.
    repeat straightline' locals.
    sepsimpl.
    straightline_call.
    ssplit.
    { destruct swap; simpl; intuition fail. }
    unfold sizedlistarray_value.
    sepsimpl; try ecancel_assumption; try apply felem_length.
    repeat straightline' l.
    apply H4.
    sepsimpl.
    eexists.
    sepsimpl.
    {
      instantiate (1 := P2.car (cswap swap x x0)).
      destruct swap; assumption.
    }
    destruct swap; assumption.
    eexists.
    sepsimpl.
    {
      instantiate (1 := P2.cdr (cswap swap x x0)).
      destruct swap; assumption.
    }
    destruct swap; assumption.
    rewrite cswap_low_combine_eq in H11.
    assert (felem_size_in_words = length x
            /\ felem_size_in_words = length x0).
    {
      clear H11 H4 a0.
      auto using felem_length.
    }
    destruct H9.
    rewrite cswap_combine_eq in H11;
      try intuition congruence;
      try solve [destruct swap; intuition congruence];[].
    replace ((Zmod.eqb (bits.of_Z _ (Z.b2z swap)) (bits.of_Z _ 1))) with swap in H11.
    unfold dlet in H11.
    destruct x, x0, swap;
    cbv [sizedlistarray_value felem_to_list proj1_sig cswap] in *;
    sepsimpl; simpl; ecancel_assumption.
    {
      destruct swap; simpl;
        [ rewrite Zmod.eqb_refl | rewrite word.eqb_ne ];
        try reflexivity.
      intro H13.
      apply (f_equal Zmod.unsigned) in H13.
      rewrite Zmod.unsigned_0, bits.unsigned_1 in H13 by (pose proof width_pos; lia).
      lia.
    }
    rewrite !felem_length; reflexivity.
  Qed.
  Hint Resolve compile_felem_cswap : compiler.

End __.

#[global]
Hint Resolve compile_felem_cswap : compiler.

(* TODO: why doesn't `Existing Instance` work? *)
#[global]
Hint Extern 1 (spec_of felem_cswap) =>
       (simple refine (spec_of_cswap)) : typeclass_instances.