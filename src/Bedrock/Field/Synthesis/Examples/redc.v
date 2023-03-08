Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
From coqutil.Word Require Import Interface Properties.

From bedrock2 Require Import WeakestPrecondition WeakestPreconditionProperties
  Syntax Semantics BasicC64Semantics ProgramLogic Scalars Array Loops ZnWords.
From bedrock2.Map Require Import Separation SeparationLogic.
Require Import coqutil.Map.Interface.


From coqutil.Tactics Require Import Tactics letexists eabstract.
Require Import Coq.ZArith.ZArith.
From coqutil.Z Require Import div_mod_to_equations Lia.
Require Import Coq.Program.Tactics.

Require Import Crypto.Arithmetic.WordByWordMontgomery.
Import Markers.

Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.



Section WithParameters.

  Import coqutil.Datatypes.List.
  Import WordByWordMontgomery.

  Context {prime: Z} (r := 64) {ri : Z}.
  Context {ri_correct: (ri * 2^r) mod prime = 1} {prime_reasonable: 1 < prime}.
  (* prime is the modulus; r is the word size; ri is the inverse of 2^r mod prime *)

  Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).

  (* redc_alt ought to take in small arrays A and B, and output an array S *)
  (* S should be small, and should evaluate mod the prime to the same thing as
     A * B * ri *)

  Instance spec_of_redc_alt : spec_of "redc_alt" :=
    fnspec! "redc_alt" Astart Bstart Sstart len / A (aval: Z) B (bval: Z) S R,
    { requires t m :=
        m =* array scalar (word.of_Z 8) Astart A *
                  array scalar (word.of_Z 8) Bstart B *
                  array scalar (word.of_Z 8) Sstart S * R /\
        word.unsigned len = Z.of_nat (List.length A)  /\
        word.unsigned len = Z.of_nat (List.length B)  /\
        word.unsigned len = Z.of_nat (List.length S) /\
        @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned A) = aval /\
        @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned B) = bval;
      ensures t' m' :=  t=t' /\ exists S',
          m' =*
             array scalar (word.of_Z 8) Astart A *
             array scalar (word.of_Z 8) Bstart B *
            array scalar (word.of_Z 8) Sstart S' * R /\
          ( aval * bval * ri^(word.unsigned len) ) mod prime =
            @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned S') mod prime
    }.

  (* redc_step ought to take in small arrays B and S, and value a, and output an array S' *)
  (* S' should be small, and should eval to the same as (a * B + S) * ri modulo the prime *)

  Instance spec_of_redc_step : spec_of "redc_step" :=
    fnspec! "redc_step" a Bstart Sstart len / B (bval: Z) S (sval: Z) R,
      { requires t m :=
          m =* array scalar (word.of_Z 8) Bstart B *
                    array scalar (word.of_Z 8) Sstart S * R /\
          word.unsigned len = Z.of_nat (List.length B) /\
          word.unsigned len = Z.of_nat (List.length S) /\
          @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned B) = bval /\
          @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned S) = sval;
        ensures t' m' := t=t' /\ exists S',
            m' =* array scalar (word.of_Z 8) Bstart B *
              array scalar (word.of_Z 8) Sstart S' * R /\
              word.unsigned len = Z.of_nat (List.length S') /\
              ((word.unsigned a) * bval + sval) * ri mod prime =
                @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned S') mod prime
      }.

  Definition redc_alt :=
    func! (Astart, Bstart, Sstart, len) {
    i = $0;
    while (i < len) {
         store(Sstart + $8*i, $0);
         i = i + $1
      };
    i = $0;
    while (i < len) {
         redc_step ( load(Astart + $8*i), Bstart, Sstart, len );
          i = i + $1
      }
    }.

  Import Coq.Lists.List.

  Let zeros (n: Z) :=
        repeat (@word.of_Z _ word 0) (Z.to_nat n).

  Theorem eval_firstn:
    forall modulus depth number,
      @Core.Positional.eval (UniformWeight.uweight modulus) depth number = @Core.Positional.eval (UniformWeight.uweight modulus) depth (firstn depth number) .
    Proof.
      intros. cbv [Core.Positional.eval Core.Positional.to_associational Core.Associational.eval].
      rewrite combine_firstn_l. rewrite map_length. rewrite seq_length. reflexivity.
    Qed.

    Theorem eval_single:
      forall modulus x,
        Core.Positional.eval (UniformWeight.uweight modulus) (length [x]) [x] = x.
    Proof.
      intros. cbv [length].
      cbv [Core.Positional.eval Core.Positional.to_associational Core.Associational.eval].
      cbv [seq map UniformWeight.uweight ModOps.weight]. simpl.
      rewrite Z.mul_0_r. rewrite Zdiv_0_l. replace (-0) with 0 by Lia.lia.
      rewrite Z.pow_0_r. Lia.lia.
    Qed.

  Theorem eval_one_further:
    forall modulus depth number,  Z.of_nat (length number) > Z.of_nat depth -> 0 <= modulus ->
                                  @eval modulus (depth + 1) number =
                                  @eval modulus depth number + ((2 ^ modulus) ^ Z.of_nat depth) * hd 0 (skipn depth number).
  Proof.
    intros. cbv [eval].
    assert ((firstn depth number ++ skipn depth number) = number) by (apply firstn_skipn).
    destruct (skipn depth number) as [|new junk].
    - assert (length (firstn depth number ++ []) = length number) by (rewrite H1; reflexivity).
      rewrite app_length in H2. simpl in H2. assert ((length (firstn depth number)) <= depth)%nat by apply firstn_le_length. Lia.lia.
    - cbv [hd]. replace (Core.Positional.eval (UniformWeight.uweight modulus) (depth + 1) number) with (Core.Positional.eval (UniformWeight.uweight modulus) (depth + 1) (firstn depth number ++ [new])).
      2: {
        symmetry. rewrite eval_firstn. rewrite <- H1.
        replace (firstn (depth + 1) (firstn depth number ++ new :: junk)) with (firstn depth (firstn depth number ++ new :: junk) ++ [new]).
        1: { reflexivity. }
        replace (depth + 1)%nat with (S depth) by Lia.lia.
        rewrite <- firstn_nth with (d := 0).
        2: { rewrite app_length. replace (length (firstn depth number)) with depth.
             - assert (length (new::junk) = S (length junk)) by apply ListUtil.cons_length. Lia.lia.
             - rewrite ListUtil.List.firstn_length_le; Lia.lia.
        }
        f_equal. assert (depth = length (firstn depth number)) by (rewrite ListUtil.List.firstn_length_le; Lia.lia).
        remember (firstn depth number) as plz_dont_rewrite_me.
        rewrite H2. rewrite nth_middle. reflexivity.
      }
      rewrite UniformWeight.uweight_eval_app with (n := depth).
      + rewrite <- eval_firstn. f_equal. rewrite eval_single. f_equal.
        cbv [UniformWeight.uweight ModOps.weight]. rewrite Z.div_1_r.
        rewrite <- Z.pow_mul_r; try Lia.lia.
        f_equal. Lia.lia.
    + Lia.lia.
    + rewrite ListUtil.List.firstn_length_le; Lia.lia.
    + reflexivity.
 Qed.

  Theorem array_small:
  forall start arr R m,
    m =* array scalar (word.of_Z 8) start arr * R  ->
   Z.of_nat (@length (@word.rep 64 word) arr) * 8 < 2 ^ 64
  .
  Proof.
    Admitted.

 Theorem redc_alt_ok :
      program_logic_goal_for_function! redc_alt.
 Proof.
   repeat straightline.
      (*after the first loop, our output array is full of zeros*)
      refine ( tailrec (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ HList.polymorphic_list.nil))))))))
               ("Astart":: "Bstart" :: "Sstart" :: "len" :: "i" :: nil)
               (fun l A aval B bval S Ra Rb R t m Astart Bstart Sstart len i => PrimitivePair.pair.mk
                                    (m =* array scalar (word.of_Z 8) (word.add Sstart (word.mul (word.of_Z 8) i)) S * R /\
                                       word.unsigned len - word.unsigned i = Z.of_nat (List.length S) /\


                                    l = List.length S )
                                    (fun t' m' Astart' Bstart' Sstart' len' i' =>
                                       (
                                     t = t' /\ Astart = Astart' /\ Bstart = Bstart' /\ Sstart = Sstart' /\ len = len' /\
                                     m' =* array scalar (word.of_Z 8) (word.add Sstart (word.mul (word.of_Z 8) i)) (zeros (word.unsigned len - word.unsigned i)) * R
                                     )
                                    )
               )
               lt _ _ _ _ _ _ _ _ _ _ _ _ _);
        cbn [reconstruct map.putmany_of_list HList.tuple.to_list
         HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

      { repeat straightline. }
      { exact Wf_nat.lt_wf. }
      { repeat straightline.
        subst i.
        replace (word.add Sstart (word.mul (word.of_Z 8) (word.of_Z 0))) with (Sstart) by ring.
        repeat split; try eauto.
        - ecancel_assumption.
        - rewrite word.unsigned_of_Z_0. Lia.lia. }

      { repeat straightline. eexists. split. { repeat straightline. } repeat straightline. split.

        (*loop exits properly*)
        2: {
          repeat straightline; repeat split.
          rename x3 into S'; rename x9 into Sstart'; rename x10 into len'; rename x11 into i'; rename x6 into R'.

          destruct (word.ltu i' len') eqn: Hbreak.
          - rewrite word.unsigned_of_Z_1 in H8; try inversion H8; clear H8.
          - destruct (length S') eqn: HS.
          (*length cannot be nonzero*)
          2: { rewrite word.unsigned_ltu in Hbreak. Lia.lia. }
          (*if length is zero, all arrays are the same*)
          cbv [Z.of_nat] in H7. rewrite H7; clear H7 Hbreak.
          apply ListUtil.length0_nil in HS.
          subst S'. apply H6.
        }


        (*loop body is good*)
        repeat straightline.
        rename x3 into S'; rename x9 into Sstart'; rename x10 into len'; rename x11 into i'; rename x6 into R'.
        destruct S'.
        - cbv [length Z.of_nat] in H7.
          destruct (word.ltu i' len') eqn: Hbreak; try (rewrite word.unsigned_of_Z_0 in H8; exfalso; apply H8; trivial).
          rewrite word.unsigned_ltu in Hbreak. Lia.lia.
        - cbn [array] in H6. repeat straightline.
          repeat split; try trivial. exists (S'). repeat split; try trivial. exists ( (scalar (word.add Sstart' (word.mul (word.of_Z 8) i')) (word.of_Z 0)) * R')%sep. exists (length S').
          repeat split; subst v0 a.
          all: try (repeat (destruct H10 as [solver H10]; try assumption; clear solver)); subst i.
          + replace (word.mul (word.of_Z 8) (word.add i' (word.of_Z 1))) with (word.add (word.mul (word.of_Z 8) i') (word.of_Z 8)) by ring. rewrite word.add_assoc. apply sep_comm. apply sep_assoc. ecancel_assumption.
          + destruct (word.unsigned i' + 1 <? 2^64) eqn: Hisize.
            2: { assert (2^64 - 1 <= word.unsigned i') by Lia.lia; clear Hisize.
                 assert (word.unsigned i' < 2^64) by apply word.unsigned_range.
                 assert (Hi': word.unsigned i' = 2^64 - 1) by Lia.lia; clear H10 H11.
                 assert (Hlen': word.unsigned len' < 2^64) by apply word.unsigned_range.
                 assert (Hneg: word.unsigned len' - word.unsigned i' < 1) by Lia.lia; clear Hi' Hlen'.
                 simpl in H7; simpl in Hneg. rewrite Zpos_P_of_succ_nat in H7.
                 assert (0 <= (Z.of_nat(length S'))) by apply Zle_0_nat.
                 Lia.lia.
            }

            rewrite word.unsigned_add. rewrite word.unsigned_of_Z_1. cbv [word.wrap].
            assert (Hsmall: (word.unsigned i' + 1) mod 2^64 = word.unsigned i' + 1).
            {  apply Z.mod_small. assert (0 <= word.unsigned i') by apply word.unsigned_range. Lia.lia. }
            rewrite Hsmall; clear Hisize Hsmall.

            simpl in H7; simpl. rewrite Zpos_P_of_succ_nat in H7.
            assert (0 <= (Z.of_nat(length S'))) by apply Zle_0_nat.
            Lia.lia.
          + subst v.  auto.
          + assert (Hhead: zeros (word.unsigned len' - word.unsigned i') = word.of_Z 0 :: zeros (word.unsigned len' - word.unsigned (word.add i' (word.of_Z 1))) ).
            {
            destruct (word.unsigned i' + 1 <? 2^64) eqn: Hisize.
            2: { assert (2^64 - 1 <= word.unsigned i') by Lia.lia; clear Hisize.
                 assert (word.unsigned i' < 2^64) by apply word.unsigned_range.
                 assert (Hi': word.unsigned i' = 2^64 - 1) by Lia.lia; clear H10 H11.
                 assert (Hlen': word.unsigned len' < 2^64) by apply word.unsigned_range.
                 assert (Hneg: word.unsigned len' - word.unsigned i' < 1) by Lia.lia; clear Hi' Hlen'.
                 simpl in H7; simpl in Hneg. rewrite Zpos_P_of_succ_nat in H7.
                 assert (0 <= (Z.of_nat(length S'))) by apply Zle_0_nat.
                 Lia.lia.
            }

            rewrite word.unsigned_add. rewrite word.unsigned_of_Z_1. cbv [word.wrap].
            assert (Hsmall: (word.unsigned i' + 1) mod 2^64 = word.unsigned i' + 1).
            {  apply Z.mod_small. assert (0 <= word.unsigned i') by apply word.unsigned_range. Lia.lia. }
            rewrite Hsmall; clear Hisize Hsmall.
            assert (Hpos: 0 <= word.unsigned len' - (word.unsigned i' + 1)). {
              simpl in H7; simpl. rewrite Zpos_P_of_succ_nat in H7.
              assert (0 <= (Z.of_nat(length S'))) by apply Zle_0_nat.
              Lia.lia.
            }
            replace (word.unsigned len' - word.unsigned i') with (Z.succ (word.unsigned len' - (word.unsigned i' + 1)) ) by Lia.lia.
            cbv [zeros]. rewrite Z2Nat.inj_succ; try assumption. cbn [repeat]. trivial.
            }
            rewrite Hhead; clear Hhead.
            cbn [array].
            replace (word.add (word.add Sstart' (word.mul (word.of_Z 8) i')) (word.of_Z 8)) with  (word.add Sstart' (word.mul (word.of_Z 8) (word.add i' (word.of_Z 1)))) by ring. ecancel_assumption.
        }

        {
          repeat straightline.
          (*then, the second loop does the multiplication properly*)
          refine ( tailrec (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ HList.polymorphic_list.nil))))))))
               ("Astart":: "Bstart" :: "Sstart" :: "len" :: "i" :: nil)
               (fun l A aval B bval S Ra Rb R t m Astart Bstart Sstart len i => PrimitivePair.pair.mk
                                           (
                                            m =* array scalar (word.of_Z 8) Astart A *
                                              array scalar (word.of_Z 8) Bstart B *
                                              array scalar (word.of_Z 8) Sstart S * R /\
                                            word.unsigned len = Z.of_nat (List.length A)  /\
                                            word.unsigned len = Z.of_nat (List.length B)  /\
                                            word.unsigned len = Z.of_nat (List.length S) /\
                                            @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned A) = aval /\
                                            @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned B) = bval /\
                                            @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned S) mod prime =
                                            @eval r (Z.to_nat (word.unsigned i)) (List.map word.unsigned A)
                                            * bval * ri^(word.unsigned i) mod prime /\
                                             0 <= word.unsigned i <= word.unsigned len /\
                                             l = Z.to_nat (word.unsigned len - word.unsigned i)
                                           )
                                    (fun t' m' Astart' Bstart' Sstart' len' i' =>
                                     (
                                     t = t' /\ Astart = Astart' /\ Bstart = Bstart' /\ Sstart = Sstart' /\ len = len' /\
                                     exists S',
                                       m' =* array scalar (word.of_Z 8) Astart A *
                                              array scalar (word.of_Z 8) Bstart B *
                                              array scalar (word.of_Z 8) Sstart S' * R /\
                                       @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned S') mod prime =
                                       aval * bval * ri^(word.unsigned len) mod prime
                                     )
                                    )
               )
               lt _ _ _ _ _ _ _ _ _ _ _ _ _);
        cbn [reconstruct map.putmany_of_list HList.tuple.to_list
         HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

          { repeat straightline. }

          { exact Wf_nat.lt_wf. }

          { repeat straightline; subst_words.
            replace (word.add x1 (word.mul (word.of_Z 8) (word.of_Z 0))) with (x1) in H11 by ring.
            rewrite word.unsigned_of_Z_0 in H11. replace (word.unsigned x2 - 0) with (word.unsigned x2) in H11 by ring.
            repeat split.
            - ecancel_assumption.
            - assumption.
            - assumption.
            - cbv [zeros]. rewrite repeat_length. rewrite H3. rewrite Nat2Z.id. trivial.
            - rewrite word.unsigned_of_Z_0.

              assert (eval_zero: forall beep boop,  @eval r beep (map word.unsigned (zeros boop)) = 0 ).
              { clear; intros.
                cbv [zeros eval Core.Positional.eval Core.Associational.eval Core.Positional.to_associational].
                generalize dependent (map (UniformWeight.uweight r) (seq 0 beep)).
                induction (Z.to_nat boop).
                - simpl. destruct l; trivial.
                - intros l'. cbn [repeat map]. rewrite word.unsigned_of_Z_0. destruct l'; trivial.
                  cbn [combine map fst snd fold_right]. rewrite IHn. ring.
              }

              rewrite eval_zero.

              assert (eval_in_name_only: forall xs, @eval r 0 xs = 0).
              {  clear; intros.
                cbv [eval Core.Positional.eval Core.Associational.eval Core.Positional.to_associational].
                reflexivity.
              }
              rewrite eval_in_name_only. eexists.

            - rewrite word.unsigned_of_Z_0. reflexivity.


            - rewrite word.unsigned_of_Z_0. rewrite H3. apply Nat2Z.is_nonneg.

          }

          { repeat straightline. eexists. split. { repeat straightline. } repeat straightline. split.

            (*loop exits properly*)
            2: {
              repeat straightline; repeat split; eauto. eexists. split.
              1: { ecancel_assumption. }
              destruct (word.ltu x16 x15) eqn: Hbreak.
              - rewrite word.unsigned_of_Z_1 in H15; inversion H15.
              - subst x5.  rewrite word.unsigned_ltu in Hbreak.
                assert (word.unsigned x15 = word.unsigned x16) by Lia.lia.
                rewrite H10 in *. assumption.

            }

            (*loop body good*)
            repeat (repeat eexists; straightline).

            - eapply load_word_of_sep. seprewrite_in @array_address_inbounds H6.

              4: { ecancel_assumption. }

               { destruct (word.ltu x16 x15) eqn: Hbreak; try (rewrite word.unsigned_of_Z_0 in H15; contradiction);
              rewrite word.unsigned_ltu in Hbreak; assert (Hiupper : word.unsigned x16 < Z.of_nat (length x4)) by Lia.lia;
                clear H14 H15 Hbreak.
                 assert (Hilower: 0 <= word.unsigned x16) by apply word.unsigned_range.
                 ZnWords. }

               { clear. ZnWords. }


               {
                 replace (word.sub (word.add x12 (word.mul (word.of_Z 8) x16)) x12)
                   with (word.mul (word.of_Z 8) x16) by ring.
                 eexists. }

            - straightline_call.
              { repeat split.
                - ecancel_assumption.
                - assumption.
                - assumption.
              }
              repeat straightline.

              rename x4 into A'; rename x6 into B'; rename x8 into S'.
              rename x12 into Astart'; rename x13 into Bstart'; rename x14 into Sstart'.
              rename x5 into aval'; rename x7 into bval'; rename x15 into len; rename x16 into i'.
              rename x11 into R'. rename x17 into Snew.

              exists A'. exists aval'. exists B'. exists bval'. exists Snew.
              exists "duopus".
              exists "voltaire".
              eexists.
              exists (Z.to_nat (word.unsigned len - word.unsigned i)).
              split.
              { destruct (word.ltu i' len) eqn: Hbreak; try (rewrite word.unsigned_of_Z_0 in H15; contradiction);
                     rewrite word.unsigned_ltu in Hbreak; assert (Hiupper : word.unsigned i' < word.unsigned len) by Lia.lia;
                  subst i.
                split. {  ecancel_assumption. } repeat split; eauto.
                2: { clear - Hiupper. ZnWords. }
                {
                  rewrite <- H21.

                  assert ( no_overflow: (Z.of_nat (length Snew))*8 < 2^64).
                  2: {

                  rename H7 into HAlen; rename H8 into HBlen; rename H9 into HSoldlen;
                  rename H19 into HSnewlen; rename H13 into Holdeval.

                  assert (Hivalid: word.unsigned (word.add i' (word.of_Z 1)) = word.unsigned i' + 1) by
                    (clear - Hiupper; ZnWords).

                  rewrite Hivalid. assert (8*(word.unsigned i') < 2^64) by Lia.lia.

                  replace (@word.unsigned 64 word (@word.mul 64 word (@word.of_Z 64 word 8) i') /
                             @word.unsigned 64 word (@word.of_Z 64 word 8)) with (@word.unsigned 64 word i').

                  2:{
                    rewrite word.unsigned_mul.
                    rewrite word.unsigned_of_Z. cbv [word.wrap].
                    replace (8 mod 2^64) with 8 by reflexivity.
                    replace ((8 * word.unsigned i') mod 2 ^ 64) with (8 * word.unsigned i') by
                        (symmetry; apply Z.mod_small; Lia.lia).
                    rewrite Z.mul_comm.
                    symmetry; apply Z_div_mult. reflexivity.
                  }

                  rewrite H12.

                  instantiate (1 := (word.of_Z 0)).

                  rewrite Z2Nat.inj_add; try Lia.lia.

                  rewrite eval_one_further.

                  2: { rewrite map_length. rewrite Z2Nat.id; Lia.lia. }
                  2: { Lia.lia. }

                  rewrite Z.mul_mod_l. rewrite Z.add_mod_r. rewrite Holdeval.
                  rewrite <- Z.add_mod_r. rewrite <- Z.mul_mod_l.
                  rewrite Z2Nat.id; try Lia.lia.
                  rewrite Z.mul_add_distr_r.
                  repeat rewrite <- Z.mul_assoc.
                  replace (ri ^ word.unsigned i' * ri) with (ri * ri ^ word.unsigned i') by apply Z.mul_comm.
                  rewrite Pow.Z.pow_mul_base; try Lia.lia.
                  repeat rewrite Z.mul_assoc.
                  rewrite ListUtil.skipn_map. rewrite <- hd_map. rewrite word.unsigned_of_Z_0.

                  pose (Abig := hd 0 (map word.unsigned (skipn (Z.to_nat (word.unsigned i')) A')) ).
                  replace (hd 0 (map word.unsigned (skipn (Z.to_nat (word.unsigned i')) A'))) with Abig; try trivial.
                  pose (Arest := @eval r (Z.to_nat (@word.unsigned 64 word i')) (@map (@word.rep 64 word) Z (@word.unsigned 64 word) A')).
                  replace (@eval r (Z.to_nat (@word.unsigned 64 word i')) (@map (@word.rep 64 word) Z (@word.unsigned 64 word) A')) with Arest; try trivial.

                  rewrite Z.mul_add_distr_r. rewrite Z.mul_add_distr_r. rewrite Z.add_comm.

                  repeat rewrite <- Z.mul_assoc.
                  replace ((2^r) ^ word.unsigned i' * (Abig * (bval' * ri ^ (word.unsigned i' + 1)))) with ((Abig * (bval' * ri ^ (word.unsigned i' + 1)))*(2^r)^word.unsigned i') by apply Z.mul_comm.
                  repeat rewrite <- Z.mul_assoc.

                  replace ((ri ^ (word.unsigned i' + 1) * (2^r) ^ word.unsigned i')) with ( ri * (ri*(2^r)) ^ (word.unsigned i')).
                  2: {
                    rewrite <- Pow.Z.pow_mul_base; try rewrite Z.pow_mul_l; Lia.lia.
                  }

                  rewrite Z.add_mod_r. symmetry. rewrite Z.add_mod_r.

                  replace ((Abig * (bval' * (ri * (ri * (2^r)) ^ word.unsigned i'))) mod prime) with ((Abig * (bval' * ri)) mod prime).
                  1: { trivial. }

                    rewrite Z.mul_mod_r. symmetry. rewrite Z.mul_mod_r.

                  replace (((bval' * (ri * (ri * (2^r)) ^ word.unsigned i')) mod prime)) with ((bval' * ri) mod prime).
                  1: { trivial. }

                  rewrite Z.mul_mod_r. symmetry. rewrite Z.mul_mod_r.

                  replace ((ri * (ri * (2^r)) ^ word.unsigned i') mod prime) with (ri mod prime).
                  1: {trivial. }

                  rewrite Z.mul_mod_r. replace ((ri * (2^r)) ^ word.unsigned i' mod prime) with 1.
                  1: { rewrite Z.mul_1_r. reflexivity. }

                  rewrite Z.mod_pow_full. rewrite ri_correct. rewrite Z.pow_1_l; try Lia.lia. rewrite Zmod_1_l; try Lia.lia.

                  }
                  assert (exists Rsnew, a0 =* array scalar (word.of_Z 8) Sstart' Snew * Rsnew).
                  2: {
                    destruct H17 as [Rsnew H17]. apply array_small with (start := Sstart') (m := a0) (R := Rsnew). apply H17.
                  }
                  eexists. ecancel_assumption.
              }

              {
                clear -Hbreak.
                assert (word.unsigned i' < word.unsigned len) by Lia.lia.
                ZnWords.
              }

              }

              {
                 destruct (word.ltu i' len) eqn: Hbreak; try (rewrite word.unsigned_of_Z_0 in H15; contradiction);
                     rewrite word.unsigned_ltu in Hbreak; assert (Hiupper : word.unsigned i' < word.unsigned len) by Lia.lia;
                  subst i.
                repeat split.
                 - clear -Hiupper H14. ZnWords.
                 - repeat (destruct H17 as [maybewin H17]; try trivial; clear maybewin).
                 - repeat (destruct H17 as [maybewin H17]; try trivial; clear maybewin).
                 - repeat (destruct H17 as [maybewin H17]; try trivial; clear maybewin).
                 - repeat (destruct H17 as [maybewin H17]; try trivial; clear maybewin).
                 - repeat (destruct H17 as [maybewin H17]; try trivial; clear maybewin).
                 - destruct H17 as [_ H17]. destruct H17 as [_ H17]. destruct H17 as [_ H17].
                   destruct H17 as [_ H17]. destruct H17 as [_ H17]. destruct H17 as [Ssss H17].
                   destruct H17 as [Hmem Heval]. exists Ssss. split.
                   + ecancel_assumption.
                   + trivial.

              }
              }
              repeat straightline. repeat split; trivial. exists x9. split.
          - ecancel_assumption.
          - symmetry. subst aval. subst bval. trivial.
        }
        Unshelve.
   - eauto.
   - eauto.
   - eauto.
   - eauto.
   - eauto.
   - eauto.
   - exact String.HelloWorld.
   - exact " :) ".

    Qed.

End WithParameters.
