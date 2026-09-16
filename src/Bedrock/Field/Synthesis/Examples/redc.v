Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
From coqutil.Word Require Import Properties.

From bedrock2 Require Import WeakestPrecondition WeakestPreconditionProperties
  Syntax Semantics BasicC64Semantics ProgramLogic Scalars Array Loops ZnWords.
From bedrock2.Map Require Import Separation SeparationLogic.
Require Import coqutil.Map.Interface.


From coqutil.Tactics Require Import Tactics letexists eabstract.
From Coq Require Import ZArith.
From coqutil.Z Require Import Lia.
From Coq.Program Require Import Tactics.

Require Import Crypto.Arithmetic.WordByWordMontgomery.
Import Markers.

Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.



Section WithParameters.

  Import List coqutil.Datatypes.List.
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
        m =* array scalar (bits.of_Z _ 8) Astart A *
                  array scalar (bits.of_Z _ 8) Bstart B *
                  array scalar (bits.of_Z _ 8) Sstart S * R /\
        Zmod.unsigned len = Z.of_nat (List.length A)  /\
        Zmod.unsigned len = Z.of_nat (List.length B)  /\
        Zmod.unsigned len = Z.of_nat (List.length S) /\
        @eval r (Z.to_nat (Zmod.unsigned len)) (List.map Zmod.unsigned A) = aval /\
        @eval r (Z.to_nat (Zmod.unsigned len)) (List.map Zmod.unsigned B) = bval;
      ensures t' m' :=  t=t' /\ exists S',
          m' =*
             array scalar (bits.of_Z _ 8) Astart A *
             array scalar (bits.of_Z _ 8) Bstart B *
            array scalar (bits.of_Z _ 8) Sstart S' * R /\
          ( aval * bval * ri^(Zmod.unsigned len) ) mod prime =
            @eval r (Z.to_nat (Zmod.unsigned len)) (List.map Zmod.unsigned S') mod prime
    }.

  (* redc_step ought to take in small arrays B and S, and value a, and output an array S' *)
  (* S' should be small, and should eval to the same as (a * B + S) * ri modulo the prime *)

  Instance spec_of_redc_step : spec_of "redc_step" :=
    fnspec! "redc_step" a Bstart Sstart len / B (bval: Z) S (sval: Z) R,
      { requires t m :=
          m =* array scalar (bits.of_Z _ 8) Bstart B *
                    array scalar (bits.of_Z _ 8) Sstart S * R /\
          Zmod.unsigned len = Z.of_nat (List.length B) /\
          Zmod.unsigned len = Z.of_nat (List.length S) /\
          @eval r (Z.to_nat (Zmod.unsigned len)) (List.map Zmod.unsigned B) = bval /\
          @eval r (Z.to_nat (Zmod.unsigned len)) (List.map Zmod.unsigned S) = sval;
        ensures t' m' := t=t' /\ exists S',
            m' =* array scalar (bits.of_Z _ 8) Bstart B *
              array scalar (bits.of_Z _ 8) Sstart S' * R /\
              Zmod.unsigned len = Z.of_nat (List.length S') /\
              ((Zmod.unsigned a) * bval + sval) * ri mod prime =
                @eval r (Z.to_nat (Zmod.unsigned len)) (List.map Zmod.unsigned S') mod prime
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
        repeat (bits.of_Z 64 0) (Z.to_nat n).

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
    m =* array scalar (bits.of_Z _ 8) start arr * R  ->
   Z.of_nat (@length (word) arr) * 8 < 2 ^ 64
  .
  Proof.
    Admitted.

  Local Ltac no_call :=
    lazymatch goal with
    | |- Semantics.call _ _ _ _ _ _ => fail
    | |- _ => idtac
    end.

  Local Ltac original_eexists := eexists.
  Local Tactic Notation "eexists" := no_call; original_eexists.

 Theorem redc_alt_ok :
      program_logic_goal_for_function! redc_alt.
 Proof.
   repeat straightline.
      (*after the first loop, our output array is full of zeros*)
      refine ( tailrec (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ HList.polymorphic_list.nil))))))))
               ("Astart":: "Bstart" :: "Sstart" :: "len" :: "i" :: nil)
               (fun l A aval B bval S Ra Rb R t m Astart Bstart Sstart len i => PrimitivePair.pair.mk
                                    (m =* array scalar (bits.of_Z _ 8) (Zmod.add Sstart (Zmod.mul (bits.of_Z _ 8) i)) S * R /\
                                       Zmod.unsigned len - Zmod.unsigned i = Z.of_nat (List.length S) /\


                                    l = List.length S )
                                    (fun t' m' Astart' Bstart' Sstart' len' i' =>
                                       (
                                     t = t' /\ Astart = Astart' /\ Bstart = Bstart' /\ Sstart = Sstart' /\ len = len' /\
                                     m' =* array scalar (bits.of_Z _ 8) (Zmod.add Sstart (Zmod.mul (bits.of_Z _ 8) i)) (zeros (Zmod.unsigned len - Zmod.unsigned i)) * R
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
        replace (Zmod.add Sstart (Zmod.mul (bits.of_Z _ 8) (bits.of_Z _ 0))) with (Sstart) by ring.
        repeat split; try eauto.
        - ecancel_assumption.
        - rewrite Zmod.unsigned_0. Lia.lia. }

      { repeat straightline.
        (* Backwards compatibility: on Rocq < 9.3 (before rocq-prover/rocq#22182),
           [repeat straightline] cannot make progress on the loop-invariant goal
           [Markers.unique (Markers.left _)] (its [unshelve]-based case fails when
           an evar on the shelf gets restricted), so we do the corresponding steps
           manually.  On Rocq >= 9.3 the automation already went past this goal,
           making this a no-op; it can be removed once Rocq < 9.3 support is
           dropped. *)
        all: try lazymatch goal with
             | |- Markers.unique (Markers.left _) =>
               eexists; split; [ repeat straightline | repeat straightline; split ]
             end.
        (* On Rocq >= 9.3 (rocq-prover/rocq#22182), the loop-condition witness is
           introduced by [letexists] (inside [straightline]) as a context-local
           definition [br := if Z.ltb ... then ... else ...] which hypotheses
           mention by name, whereas on Rocq < 9.3 it is a plain evar whose
           instantiation leaves the conditional inlined in the hypotheses.  The
           [destruct (Z.ltb ...)]/[rewrite ... in H*] steps below need the
           inlined form, so inline the definition; no-op on Rocq < 9.3. *)
        all: try match goal with
             | br := (if Z.ltb _ _ then _ else _) |- _ => unfold br in *; try clear br
             end.

        (*loop exits properly*)
        2: {
          repeat straightline; repeat split.
          rename x3 into S'; rename x9 into Sstart'; rename x10 into len'; rename x11 into i'; rename x6 into R'.

          destruct (Zmod.unsigned i' <? Zmod.unsigned len') eqn: Hbreak.
          - rewrite bits.unsigned_1 in H8 by lia; try inversion H8; clear H8.
          - destruct (length S') eqn: HS.
          (*length cannot be nonzero*)
          2: { Lia.lia. }
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
          destruct (Zmod.unsigned i' <? Zmod.unsigned len') eqn: Hbreak; try (rewrite Zmod.unsigned_0 in H8; exfalso; apply H8; trivial).
          Lia.lia.
        - cbn [array] in H6. repeat straightline.
          repeat split; try trivial. exists (S'). repeat split; try trivial. exists ( (scalar (Zmod.add Sstart' (Zmod.mul (bits.of_Z _ 8) i')) (bits.of_Z _ 0)) * R')%sep. exists (length S').
          repeat split; subst v0 a.
          all: try (repeat (destruct H10 as [solver H10]; try assumption; clear solver)); subst i.
          + replace (Zmod.mul (bits.of_Z _ 8) (Zmod.add i' (bits.of_Z _ 1))) with (Zmod.add (Zmod.mul (bits.of_Z _ 8) i') (bits.of_Z _ 8)) by ring. rewrite Zmod.add_assoc. apply sep_comm. apply sep_assoc. ecancel_assumption.
          + destruct (Zmod.unsigned i' + 1 <? 2^64) eqn: Hisize.
            2: { assert (2^64 - 1 <= Zmod.unsigned i') by Lia.lia; clear Hisize.
                 assert (Zmod.unsigned i' < 2^64) by apply (bits.unsigned_range _ width_nonneg).
                 assert (Hi': Zmod.unsigned i' = 2^64 - 1) by Lia.lia; clear H10 H11.
                 assert (Hlen': Zmod.unsigned len' < 2^64) by apply (bits.unsigned_range _ width_nonneg).
                 assert (Hneg: Zmod.unsigned len' - Zmod.unsigned i' < 1) by Lia.lia; clear Hi' Hlen'.
                 simpl in H7; simpl in Hneg. rewrite Zpos_P_of_succ_nat in H7.
                 assert (0 <= (Z.of_nat(length S'))) by apply Zle_0_nat.
                 Lia.lia.
            }

            rewrite Zmod.unsigned_add. rewrite bits.unsigned_1 by lia.
            assert (Hsmall: (Zmod.unsigned i' + 1) mod 2^64 = Zmod.unsigned i' + 1).
            {  apply Z.mod_small. assert (0 <= Zmod.unsigned i') by apply (bits.unsigned_range _ width_nonneg). Lia.lia. }
            rewrite Hsmall; clear Hisize Hsmall.

            simpl in H7; simpl. rewrite Zpos_P_of_succ_nat in H7.
            assert (0 <= (Z.of_nat(length S'))) by apply Zle_0_nat.
            Lia.lia.
          + subst v.  auto.
          + assert (Hhead: zeros (Zmod.unsigned len' - Zmod.unsigned i') = bits.of_Z _ 0 :: zeros (Zmod.unsigned len' - Zmod.unsigned (Zmod.add i' (bits.of_Z _ 1))) ).
            {
            destruct (Zmod.unsigned i' + 1 <? 2^64) eqn: Hisize.
            2: { assert (2^64 - 1 <= Zmod.unsigned i') by Lia.lia; clear Hisize.
                 assert (Zmod.unsigned i' < 2^64) by apply (bits.unsigned_range _ width_nonneg).
                 assert (Hi': Zmod.unsigned i' = 2^64 - 1) by Lia.lia; clear H10 H11.
                 assert (Hlen': Zmod.unsigned len' < 2^64) by apply (bits.unsigned_range _ width_nonneg).
                 assert (Hneg: Zmod.unsigned len' - Zmod.unsigned i' < 1) by Lia.lia; clear Hi' Hlen'.
                 simpl in H7; simpl in Hneg. rewrite Zpos_P_of_succ_nat in H7.
                 assert (0 <= (Z.of_nat(length S'))) by apply Zle_0_nat.
                 Lia.lia.
            }

            rewrite Zmod.unsigned_add. rewrite bits.unsigned_1 by lia.
            assert (Hsmall: (Zmod.unsigned i' + 1) mod 2^64 = Zmod.unsigned i' + 1).
            {  apply Z.mod_small. assert (0 <= Zmod.unsigned i') by apply (bits.unsigned_range _ width_nonneg). Lia.lia. }
            rewrite Hsmall; clear Hisize Hsmall.
            assert (Hpos: 0 <= Zmod.unsigned len' - (Zmod.unsigned i' + 1)). {
              simpl in H7; simpl. rewrite Zpos_P_of_succ_nat in H7.
              assert (0 <= (Z.of_nat(length S'))) by apply Zle_0_nat.
              Lia.lia.
            }
            replace (Zmod.unsigned len' - Zmod.unsigned i') with (Z.succ (Zmod.unsigned len' - (Zmod.unsigned i' + 1)) ) by Lia.lia.
            cbv [zeros]. rewrite Z2Nat.inj_succ; try assumption. cbn [repeat]. trivial.
            }
            rewrite Hhead; clear Hhead.
            cbn [array].
            replace (Zmod.add (Zmod.add Sstart' (Zmod.mul (bits.of_Z _ 8) i')) (bits.of_Z _ 8)) with  (Zmod.add Sstart' (Zmod.mul (bits.of_Z _ 8) (Zmod.add i' (bits.of_Z _ 1)))) by ring. ecancel_assumption.
        }

        {
          repeat straightline.
          (*then, the second loop does the multiplication properly*)
          refine ( tailrec (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ HList.polymorphic_list.nil))))))))
               ("Astart":: "Bstart" :: "Sstart" :: "len" :: "i" :: nil)
               (fun l A aval B bval S Ra Rb R t m Astart Bstart Sstart len i => PrimitivePair.pair.mk
                                           (
                                            m =* array scalar (bits.of_Z _ 8) Astart A *
                                              array scalar (bits.of_Z _ 8) Bstart B *
                                              array scalar (bits.of_Z _ 8) Sstart S * R /\
                                            Zmod.unsigned len = Z.of_nat (List.length A)  /\
                                            Zmod.unsigned len = Z.of_nat (List.length B)  /\
                                            Zmod.unsigned len = Z.of_nat (List.length S) /\
                                            @eval r (Z.to_nat (Zmod.unsigned len)) (List.map Zmod.unsigned A) = aval /\
                                            @eval r (Z.to_nat (Zmod.unsigned len)) (List.map Zmod.unsigned B) = bval /\
                                            @eval r (Z.to_nat (Zmod.unsigned len)) (List.map Zmod.unsigned S) mod prime =
                                            @eval r (Z.to_nat (Zmod.unsigned i)) (List.map Zmod.unsigned A)
                                            * bval * ri^(Zmod.unsigned i) mod prime /\
                                             0 <= Zmod.unsigned i <= Zmod.unsigned len /\
                                             l = Z.to_nat (Zmod.unsigned len - Zmod.unsigned i)
                                           )
                                    (fun t' m' Astart' Bstart' Sstart' len' i' =>
                                     (
                                     t = t' /\ Astart = Astart' /\ Bstart = Bstart' /\ Sstart = Sstart' /\ len = len' /\
                                     exists S',
                                       m' =* array scalar (bits.of_Z _ 8) Astart A *
                                              array scalar (bits.of_Z _ 8) Bstart B *
                                              array scalar (bits.of_Z _ 8) Sstart S' * R /\
                                       @eval r (Z.to_nat (Zmod.unsigned len)) (List.map Zmod.unsigned S') mod prime =
                                       aval * bval * ri^(Zmod.unsigned len) mod prime
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
            replace (Zmod.add x1 (Zmod.mul (bits.of_Z _ 8) (bits.of_Z _ 0))) with (x1) in H11 by ring.
            rewrite Zmod.unsigned_0 in H11. replace (Zmod.unsigned x2 - 0) with (Zmod.unsigned x2) in H11 by ring.
            repeat split.
            - ecancel_assumption.
            - assumption.
            - assumption.
            - cbv [zeros]. rewrite repeat_length. rewrite H3. rewrite Nat2Z.id. trivial.
            - rewrite Zmod.unsigned_0.

              assert (eval_zero: forall beep boop,  @eval r beep (map Zmod.unsigned (zeros boop)) = 0 ).
              { clear; intros.
                cbv [zeros eval Core.Positional.eval Core.Associational.eval Core.Positional.to_associational].
                generalize dependent (map (UniformWeight.uweight r) (seq 0 beep)).
                induction (Z.to_nat boop).
                - simpl. destruct l; trivial.
                - intros l'. cbn [repeat map]. rewrite Zmod.unsigned_0. destruct l'; trivial.
                  cbn [combine map fst snd fold_right]. rewrite IHn. ring.
              }

              rewrite eval_zero.

              assert (eval_in_name_only: forall xs, @eval r 0 xs = 0).
              {  clear; intros.
                cbv [eval Core.Positional.eval Core.Associational.eval Core.Positional.to_associational].
                reflexivity.
              }
              rewrite eval_in_name_only. eexists.

            - rewrite Zmod.unsigned_0. reflexivity.


            - rewrite Zmod.unsigned_0. rewrite H3. apply Nat2Z.is_nonneg.

          }

          { repeat straightline.
            (* Same two compatibility steps as in the first loop above:
               the [lazymatch] is a no-op on Rocq >= 9.3 (rocq-prover/rocq#22182)
               and can be removed once Rocq < 9.3 support is dropped; the
               [match] inlining the [br := if Z.ltb ...] local definition is
               a no-op on Rocq < 9.3. *)
            all: try lazymatch goal with
                 | |- Markers.unique (Markers.left _) =>
                   eexists; split; [ repeat straightline | repeat straightline; split ]
                 end.
            all: try match goal with
                 | br := (if Z.ltb _ _ then _ else _) |- _ => unfold br in *; try clear br
                 end.

            (*loop exits properly*)
            2: {
              repeat straightline; repeat split; eauto. eexists. split.
              1: { ecancel_assumption. }
              destruct (Zmod.unsigned x16 <? Zmod.unsigned x15) eqn: Hbreak.
              - rewrite bits.unsigned_1 in H15 by lia; inversion H15.
              - subst x5.
                assert (Zmod.unsigned x15 = Zmod.unsigned x16) by Lia.lia.
                rewrite H10 in *. assumption.

            }

            (*loop body good*)
            (* This was [repeat (repeat eexists; straightline)], which is not
               robust: [t1; t2] is discarded entirely when [t2] fails on any goal
               produced by [t1], and on Rocq >= 9.3 (rocq-prover/rocq#22182) this
               point is reached with [straightline] already at a fixpoint, so
               [straightline] fails on the [call ...] goal produced by
               [repeat eexists] and the whole loop was a no-op.  Decoupling the
               two keeps the [repeat eexists] progress on all versions. *)
            repeat eexists. all: repeat straightline.

            - eapply load_word_of_sep. seprewrite_in @array_address_inbounds H6.

              4: { ecancel_assumption. }

               { destruct (Zmod.unsigned x16 <? Zmod.unsigned x15) eqn: Hbreak; try (rewrite Zmod.unsigned_0 in H15; contradiction);
              assert (Hiupper : Zmod.unsigned x16 < Z.of_nat (length x4)) by Lia.lia;
                clear H14 H15 Hbreak.
                 assert (Hilower: 0 <= Zmod.unsigned x16) by apply (bits.unsigned_range _ width_nonneg).
                 ZnWords. }

               { clear. ZnWords. }


               {
                 replace (Zmod.sub (Zmod.add x12 (Zmod.mul (bits.of_Z _ 8) x16)) x12)
                   with (Zmod.mul (bits.of_Z _ 8) x16) by ring.
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
              exists (Z.to_nat (Zmod.unsigned len - Zmod.unsigned i)).
              split.
              { destruct (Zmod.unsigned i' <? Zmod.unsigned len) eqn: Hbreak; try (rewrite Zmod.unsigned_0 in H15; contradiction);
                     assert (Hiupper : Zmod.unsigned i' < Zmod.unsigned len) by Lia.lia;
                  subst i.
                split. {  ecancel_assumption. } repeat split; eauto.
                2: { clear - Hiupper. ZnWords. }
                {
                  rewrite <- H21.

                  assert ( no_overflow: (Z.of_nat (length Snew))*8 < 2^64).
                  2: {

                  rename H7 into HAlen; rename H8 into HBlen; rename H9 into HSoldlen;
                  rename H19 into HSnewlen; rename H13 into Holdeval.

                  assert (Hivalid: Zmod.unsigned (Zmod.add i' (bits.of_Z _ 1)) = Zmod.unsigned i' + 1) by
                    (clear - Hiupper; ZnWords).

                  rewrite Hivalid. assert (8*(Zmod.unsigned i') < 2^64) by Lia.lia.

                  replace (Zmod.unsigned (Zmod.mul (bits.of_Z _ 8) i') /
                             Zmod.unsigned (bits.of_Z _ 8)) with (Zmod.unsigned i').

                  2:{
                    rewrite Zmod.unsigned_mul.
                    rewrite bits.unsigned_of_Z.
                    replace (8 mod 2^64) with 8 by reflexivity.
                    replace ((8 * Zmod.unsigned i') mod 2 ^ 64) with (8 * Zmod.unsigned i') by
                        (symmetry; apply Z.mod_small; Lia.lia).
                    rewrite Z.mul_comm.
                    symmetry; apply Z_div_mult. reflexivity.
                  }

                  rewrite H12.

                  instantiate (1 := (bits.of_Z _ 0)).

                  rewrite Z2Nat.inj_add; try Lia.lia.

                  rewrite eval_one_further.

                  2: { rewrite map_length. rewrite Z2Nat.id; Lia.lia. }
                  2: { Lia.lia. }

                  rewrite Z.mul_mod_l. rewrite Z.add_mod_r. rewrite Holdeval.
                  rewrite <- Z.add_mod_r. rewrite <- Z.mul_mod_l.
                  rewrite Z2Nat.id; try Lia.lia.
                  rewrite Z.mul_add_distr_r.
                  repeat rewrite <- Z.mul_assoc.
                  replace (ri ^ Zmod.unsigned i' * ri) with (ri * ri ^ Zmod.unsigned i') by apply Z.mul_comm.
                  rewrite Pow.Z.pow_mul_base; try Lia.lia.
                  repeat rewrite Z.mul_assoc.
                  rewrite ListUtil.skipn_map. rewrite <- hd_map. rewrite Zmod.unsigned_0.

                  pose (Abig := hd 0 (map Zmod.unsigned (skipn (Z.to_nat (Zmod.unsigned i')) A')) ).
                  replace (hd 0 (map Zmod.unsigned (skipn (Z.to_nat (Zmod.unsigned i')) A'))) with Abig; try trivial.
                  pose (Arest := @eval r (Z.to_nat (Zmod.unsigned i')) (@map (word) Z (Zmod.unsigned) A')).
                  replace (@eval r (Z.to_nat (Zmod.unsigned i')) (@map (word) Z (Zmod.unsigned) A')) with Arest; try trivial.

                  rewrite Z.mul_add_distr_r. rewrite Z.mul_add_distr_r. rewrite Z.add_comm.

                  repeat rewrite <- Z.mul_assoc.
                  replace ((2^r) ^ Zmod.unsigned i' * (Abig * (bval' * ri ^ (Zmod.unsigned i' + 1)))) with ((Abig * (bval' * ri ^ (Zmod.unsigned i' + 1)))*(2^r)^Zmod.unsigned i') by apply Z.mul_comm.
                  repeat rewrite <- Z.mul_assoc.

                  replace ((ri ^ (Zmod.unsigned i' + 1) * (2^r) ^ Zmod.unsigned i')) with ( ri * (ri*(2^r)) ^ (Zmod.unsigned i')).
                  2: {
                    rewrite <- Pow.Z.pow_mul_base; try rewrite Z.pow_mul_l; Lia.lia.
                  }

                  rewrite Z.add_mod_r. symmetry. rewrite Z.add_mod_r.

                  replace ((Abig * (bval' * (ri * (ri * (2^r)) ^ Zmod.unsigned i'))) mod prime) with ((Abig * (bval' * ri)) mod prime).
                  1: { trivial. }

                    rewrite Z.mul_mod_r. symmetry. rewrite Z.mul_mod_r.

                  replace (((bval' * (ri * (ri * (2^r)) ^ Zmod.unsigned i')) mod prime)) with ((bval' * ri) mod prime).
                  1: { trivial. }

                  rewrite Z.mul_mod_r. symmetry. rewrite Z.mul_mod_r.

                  replace ((ri * (ri * (2^r)) ^ Zmod.unsigned i') mod prime) with (ri mod prime).
                  1: {trivial. }

                  rewrite Z.mul_mod_r. replace ((ri * (2^r)) ^ Zmod.unsigned i' mod prime) with 1.
                  1: { rewrite Z.mul_1_r. reflexivity. }

                  rewrite Z.mod_pow_full. rewrite ri_correct. rewrite Z.pow_1_l; try Lia.lia. rewrite Zmod_1_l; try Lia.lia.

                  }
                  assert (exists Rsnew, a0 =* array scalar (bits.of_Z _ 8) Sstart' Snew * Rsnew).
                  2: {
                    destruct H17 as [Rsnew H17]. apply array_small with (start := Sstart') (m := a0) (R := Rsnew). apply H17.
                  }
                  eexists. ecancel_assumption.
              }

              {
                clear -Hbreak.
                assert (Zmod.unsigned i' < Zmod.unsigned len) by Lia.lia.
                ZnWords.
              }

              }

              {
                 destruct (Zmod.unsigned i' <? Zmod.unsigned len) eqn: Hbreak; try (rewrite Zmod.unsigned_0 in H15; contradiction);
                     assert (Hiupper : Zmod.unsigned i' < Zmod.unsigned len) by Lia.lia;
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
        (* Positional bullets here would depend on the shelf order, which changes
           in Rocq 9.3 (rocq-prover/rocq#22182: a restricted shelved evar now
           keeps its position instead of moving to the end), so solve these
           order-independently. *)
        all: eauto.
   - exact String.HelloWorld.
   - exact " :) ".

    Qed.

End WithParameters.
