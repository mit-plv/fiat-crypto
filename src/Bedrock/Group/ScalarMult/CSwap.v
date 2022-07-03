Require Import Coq.Program.Tactics.
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Loops.
Require Import bedrock2.Semantics.
Require Import coqutil.Word.Interface coqutil.Byte.
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

  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
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
  Hint Resolve @relax_bounds : compiler.


  Notation all_1s := (word.of_Z (-1) : word).

  Section Gallina.


    Definition is_mask mask : Prop :=
      mask = all_1s \/ mask = word.of_Z 0.

    Definition mask_of_bool (b : bool) :=
      if b then all_1s else word.of_Z 0.


    Instance HasDefault_word : HasDefault word :=
      word.of_Z 0.

    Instance: HasDefault (word * word) := (default, default).
    Existing Instance Convertible_Z_nat.

    Definition cswap_low mask
               (a1: ListArray.t word.rep)
               (a2: ListArray.t word.rep) :=
      let from := 0%Z in
      let to := (Z.of_nat felem_size_in_words) in
      let/n nmask := word.sub (word.of_Z 0) mask in
      let/n mask := word.not nmask in
      let/n (a1, a2) :=
         nd_ranged_for_all
           from to
           (fun '\<a1,a2\> idx =>
              let/n v1 := ListArray.get a1 idx in
              let/n v2 := ListArray.get a2 idx in
              let/n r1 := word.or (word.and mask v1)
                                 (word.and nmask v2) in
              let/n r2 := word.or (word.and mask v2)
                                 (word.and nmask v1) in
              let/n a1 := ListArray.put a1 idx r1 in
              let/n a2 := ListArray.put a2 idx r2 in
              \<a1, a2\>) \<a1, a2\> in
      \<a1, a2\>.


    Definition cswap_word1 (mask nmask a b : word) :=
      word.or (word.and mask a)
              (word.and nmask b).
    Definition cswap_word2 (mask nmask a b : word) :=
      word.or (word.and mask b)
              (word.and nmask a).

    Definition cswap_combine (mask : word)
               (a1: ListArray.t word.rep)
               (a2: ListArray.t word.rep) :=
      let/n from := 0%Z in
      let/n to := (Z.of_nat felem_size_in_words) in
      let/n nmask := word.sub (word.of_Z 0) mask in
      let/n mask := word.not nmask in
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
    : word.wrap (Z.of_nat felem_size_in_words) = (Z.of_nat felem_size_in_words).
  Proof using felem_size_in_words_small.
    unfold word.wrap.
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



  Lemma all_1s_and : forall x, word.and all_1s x = x.
  Proof using field_representaton word_ok.
    intros.
    rewrite <- (word.of_Z_unsigned (word.of_Z (-1))).
    rewrite -> word.unsigned_of_Z_minus1.
    rewrite <- (word.of_Z_unsigned x) at 1.
    rewrite <- word.morph_and.
    rewrite Z.land_comm.
    rewrite Z.land_ones.
    rewrite word.wrap_unsigned.
    rewrite word.of_Z_unsigned.
    reflexivity.
    apply z_lt_width.
  Qed.

  Lemma word_not_all1s : word.not all_1s = word.of_Z 0.
  Proof using field_representaton word_ok.
    rewrite <- (word.of_Z_signed (word.not all_1s)).
    rewrite word.signed_not.
    rewrite word.signed_of_Z.
    rewrite !word.swrap_inrange.
    change (-1)%Z with (-(1))%Z.
    rewrite Z.lnot_m1; reflexivity.
    destruct width_cases as [H|H]; rewrite !H; lia.
    {
      rewrite word.swrap_inrange.
      let x := eval compute in ( Z.lnot (-1)) in
          change ( Z.lnot (-1)) with x.
      destruct width_cases as [H|H]; rewrite !H; lia.
      destruct width_cases as [H|H]; rewrite !H; lia.
    }
  Qed.


  Lemma word_not_impl (x : word)
    : word.not x = word.sub (word.of_Z (-1)) x.
  Proof using field_representaton word_ok.
    rewrite <- (word.of_Z_signed (word.not x)).
    rewrite word.signed_not_nowrap.
    rewrite <- (word.of_Z_signed x).
    rewrite <- word.ring_morph_sub.
    f_equal.
    rewrite (word.of_Z_signed x).
    unfold Z.lnot.
    lia.
  Qed.


  Lemma word_not_zero : word.not (word.of_Z 0) = all_1s.
  Proof using field_representaton word_ok.
    rewrite word_not_impl.
    rewrite <- (word.of_Z_unsigned (word.sub _ _)).
    rewrite <- word.ring_morph_sub.
    rewrite word.of_Z_unsigned.
    reflexivity.
  Qed.

  Lemma zero_and (x : word)
    : word.and (word.of_Z 0) x = word.of_Z 0.
  Proof using word_ok.
    rewrite <- (word.of_Z_unsigned x) at 1.
    rewrite <- word.morph_and.
    rewrite Z.land_0_l.
    reflexivity.
  Qed.


  Lemma zero_or (x : word)
    : word.or (word.of_Z 0) x = x.
  Proof using word_ok.
    rewrite <- (word.of_Z_unsigned x) at 1.
    rewrite <- word.morph_or.
    rewrite Z.lor_0_l.
    rewrite word.of_Z_unsigned.
    reflexivity.
  Qed.

  Lemma or_comm (a b : word) : word.or a b = word.or b a.
  Proof using word_ok.
    rewrite <- (word.of_Z_signed a).
    rewrite <- (word.of_Z_signed b).
    rewrite <-word.morph_or.
    rewrite Z.lor_comm.
    rewrite word.morph_or.
    reflexivity.
  Qed.

  Lemma sub_zero (a : word) : word.sub a (word.of_Z 0) = a.
  Proof using field_representaton word_ok.
    rewrite <- (word.of_Z_signed a).
    rewrite <-word.ring_morph_sub.
    replace (word.signed a - 0) with (word.signed a) by lia.
    reflexivity.
  Qed.


  Lemma zero_minus_one
    : (word.sub (word.of_Z 0) (word.of_Z 1)) = all_1s.
  Proof using word_ok.
    rewrite <- word.ring_morph_sub.
    reflexivity.
  Qed.

  Lemma cswap_combine_eq mask a1 a2
    : (mask = word.of_Z 0) \/ (mask = word.of_Z 1) ->
      felem_size_in_words = length a1 ->
      felem_size_in_words = length a2 ->
      cswap_combine mask a1 a2 = cswap (word.eqb mask (word.of_Z 1)) a1 a2.
  Proof using word_ok.
    unfold cswap,cswap_combine, nlet; intros.
    assert (felem_size_in_words = (length (combine a1 a2))).
    {
      rewrite H0.
      rewrite combine_length.
      lia.
    }
    rewrite H2.
    rewrite <- map_as_nd_ranged_for_all
    with (f := fun p=> if word.eqb mask (word.of_Z 1) then ((snd p), (fst p)) else ((fst p), (snd p))).
    {
      destruct H; subst;
        [ rewrite word.eqb_ne | rewrite word.eqb_eq by reflexivity].
      2:{
        intro.
        pose proof word.unsigned_of_Z_0.
        rewrite H in H3.
        rewrite word.unsigned_of_Z_1 in H3.
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
        [rewrite word.eqb_ne | rewrite word.eqb_eq by reflexivity ];
        f_equal.

      all: rewrite ?sub_zero.
      all: rewrite ?zero_minus_one.
      all: rewrite ?word_not_all1s.
      all: rewrite ?word_not_zero.
      all: rewrite ?all_1s_and.
      all: rewrite ?zero_and.
      all: rewrite ?zero_or.
      all: try rewrite or_comm, ?zero_or.
      all: try reflexivity.

      {
        intro.
        pose proof word.unsigned_of_Z_0.
        rewrite H in H3.
        rewrite word.unsigned_of_Z_1 in H3.
        lia.
      }
    }
  Qed.


  (*TODO: move to NoExprReflection.v*)
  Lemma compile_word_not
        {tr m l functions} x :
    let v := word.not x in
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
      cmd.seq (cmd.set var (expr.op bopname.sub (expr.literal (-1)) (expr.var x_var)))
              k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof using field_representaton word_ok.
    repeat (eexists; split; eauto).
    apply word_not_impl.
  Qed.
  Hint Extern 10 => simple eapply compile_word_not; shelve : compiler.

  Import SizedListArrayCompiler.
  Import LoopCompiler.
  Hint Extern 10 (_ < _) => lia: compiler_side_conditions.

  Definition felem_cswap := "felem_cswap".

    Instance spec_of_cswap : spec_of felem_cswap :=
      fnspec! felem_cswap mask ptr1 ptr2 / c1 c2 R,
        (*TODO: if b then bw should be all 1s*)
        { requires tr mem :=
            (mask = word.of_Z 0 \/ mask = word.of_Z 1) /\
            (sizedlistarray_value AccessWord felem_size_in_words ptr1 c1
             * sizedlistarray_value AccessWord felem_size_in_words ptr2 c2 * R)%sep mem;
          ensures tr' mem' :=
          tr' = tr /\
            let/d p := cswap_low mask c1 c2 in
            let (c1,c2) := p in
            (sizedlistarray_value AccessWord felem_size_in_words ptr1 c1
             * sizedlistarray_value AccessWord felem_size_in_words ptr2 c2 * R)%sep mem' }.

  Import LoopCompiler.
  Derive cswap_body SuchThat
           (defn! felem_cswap ("mask", "a1", "a2") { cswap_body },
             implements cswap_low)
           As cswap_body_correct.
  Proof.
    pose proof felem_size_in_words_small.
    compile.
    lia.
  Qed.

  Lemma Bignum_as_array
    : @Bignum.Bignum width word _ = sizedlistarray_value AccessWord.
  Proof using field_representaton.
    unfold Bignum.Bignum, sizedlistarray_value.
    unfold listarray_value.
    simpl.
    rewrite Z2Nat.id.
    reflexivity.
    unfold bytes_per_word.
    pose proof z_lt_width.
    apply Z.div_pos; try lia.
  Qed.

    Lemma compile_felem_cswap {tr m l functions} swap (lhs rhs : F M_pos) :
      let v := cswap swap lhs rhs in
      forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
             R mask_var bounds lhs_ptr lhs_var rhs_ptr rhs_var,

        spec_of_cswap functions ->

        map.get l mask_var = Some (word.of_Z (Z.b2z swap)) ->

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
          (cmd.call [] felem_cswap [expr.var mask_var; expr.var lhs_var; expr.var rhs_var])
          k_impl
        <{ pred (nlet_eq [lhs_var; rhs_var] v k) }>.
  Proof using env_ok ext_spec_ok locals_ok mem_ok word_ok.
    unfold FElem, Field.FElem.
    rewrite !Bignum_as_array.
    repeat straightline' locals.
    sepsimpl.
    straightline_call.
    ssplit.
    { destruct swap; simpl; intuition fail. }
    ecancel_assumption.
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
      unfold sizedlistarray_value in H7; sepsimpl; auto.
      seprewrite_in (sep_emp_2 R) H7.
      sepsimpl.
      auto.
    }
    destruct H9.
    rewrite cswap_combine_eq in H11;
      try intuition congruence;
      try solve [destruct swap; intuition congruence];[].
    replace ((word.eqb (word.of_Z (Z.b2z swap)) (word.of_Z 1))) with swap in H11.
    unfold dlet in H11.
    use_sep_assumption.
    cancel.
    apply sep_comm.
    {
      destruct swap; simpl;
        [ rewrite word.eqb_eq | rewrite word.eqb_ne ];
        try reflexivity.
      intro.
      pose proof word.unsigned_of_Z_1.
      rewrite <- H12 in H13.
      rewrite word.unsigned_of_Z_0 in H13.
      lia.
    }
    {
      assert (Datatypes.length x0 = felem_size_in_words) as Heqsz;[|rewrite Heqsz; clear Heqsz].
      {
        revert H7.
        unfold sizedlistarray_value.
        intros; sepsimpl.
        intuition.
      }
      assert (Datatypes.length x = felem_size_in_words) as Heqsz;[|apply Heqsz].
      {
        revert H7.
        unfold sizedlistarray_value.
        intros.
        sepsimpl.
        intuition.
        repeat destruct H9 as [? H9].
        sepsimpl.
        assumption.
      }
    }
  Qed.
  Hint Resolve compile_felem_cswap : compiler.

End __.


Hint Resolve compile_felem_cswap : compiler.

(* TODO: why doesn't `Existing Instance` work? *)
Hint Extern 1 (spec_of felem_cswap) =>
       (simple refine (spec_of_cswap)) : typeclass_instances.
