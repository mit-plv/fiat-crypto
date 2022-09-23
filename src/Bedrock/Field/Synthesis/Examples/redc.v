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
  
  Import List.
  Import WordByWordMontgomery.
  
  Context {prime: Z} (r := 64) {ri : Z}.
  Context {ri_correct: (ri * r) mod prime = 1}.
  (* prime is the modulus; r is the word size; ri is the inverse of r mod prime *)
  (*Context {word: word.word r} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.*)
  
  Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).

  (* redc_alt ought to take in small arrays A and B, and output an array S *)
  (* S should be small, and should evaluate mod the prime to the same thing as 
     A * B * R^-1 *)
  
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
          m' =* array scalar (word.of_Z 8) Sstart S' * R /\
          ( aval * bval * ri^(word.unsigned len) ) mod prime =
            @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned S') mod prime
    }.

  (* redc_step ought to take in small arrays B and S, and value a, and output an array S' *)
  (* S' should be small, and should eval to the same as (a * B + S) * R^-1 modulo the prime *)
  
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

  Definition redc_alt : func :=
    let redc_step : String.string := "redc_step" in 
    ("redc_alt", (["Astart"; "Bstart"; "Sstart"; "len"], [], bedrock_func_body:(
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
    ))).

  Require Import Coq.Lists.List.

  Let zeros (n: Z) :=
        repeat (@word.of_Z _ word 0) (Z.to_nat n).

  Ltac nathans_handy_wordhammer :=
    match goal with
    | [H : 1 = 0 |- _ ] => inversion H
    | _ => try rewrite word.unsigned_of_Z_0 in *; try rewrite word.unsigned_of_Z_1 in *; try rewrite word.of_Z_unsigned in *
    end.

  (*stolen from insertionsort*)

  Lemma ptsto_nonaliasing: forall addr b1 b2 m (R: mem -> Prop),
      (ptsto addr b1 * ptsto addr b2 * R)%sep m ->
      False.
  Proof.
    intros. unfold ptsto, sep, map.split, map.disjoint in *.
    repeat match goal with
           | H: exists _, _ |- _ => destruct H
           | H: _ /\ _ |- _ => destruct H
           end.
    subst.
    specialize (H4 addr b1 b2). rewrite ?map.get_put_same in H4. auto.
  Qed.

      Lemma scalar_nonoverlapping: forall addr x1 x2 (R: mem -> Prop) m,
          (scalar addr x1 * scalar addr x2 * R)%sep m -> False.
      Proof.
        clear; intros.
        unfold scalar in *.
        unfold truncated_word in *.
        unfold truncated_scalar in *.
        unfold littleendian in *.
        unfold LittleEndianList.le_split in *.
        unfold ptsto_bytes.ptsto_bytes in *.
        rewrite !HList.tuple.to_list_of_list in H.
        simpl in H.
        assert (exists (R': mem -> Prop), (ptsto addr ((Byte.byte.of_Z (Naive.unsigned x1))) * ptsto addr ((Byte.byte.of_Z (Naive.unsigned x2))) * R')%sep m).
        { eexists. ecancel_assumption. }
        apply ptsto_nonaliasing in H.


        
        clear. intros. unfold sep, map.split, map.disjoint in H.
        repeat match goal with
           | H: exists _, _ |- _ => destruct H
           | H: _ /\ _ |- _ => destruct H
           end.
        subst.
        specialize (H4 addr x1 x2).
        unfold scalar, truncated_word, truncated_scalar in *.
    specialize (H4 addr x1 x2). rewrite ?map.get_put_same in H4. auto.
      Qed.

      
    Lemma array_scalar64_max_size: forall addr xs (R: mem -> Prop) m,
      (array scalar (word.of_Z 8) addr xs * R)%sep m ->
      8 * Z.of_nat (Datatypes.length xs) <= 2 ^ 64.
  Proof.
    intros.
    assert (8 * Z.of_nat (Datatypes.length xs) <= 2 ^ 64 \/ 2 ^ 64 < 8 * Z.of_nat (Datatypes.length xs))
      as C by Lia.lia. destruct C as [C | C]; [exact C | exfalso].
    pose proof (List.firstn_skipn (Z.to_nat (2 ^ 64 / 8)) xs) as E.
    pose proof @List.firstn_length_le _ xs (Z.to_nat (2 ^ 64 / 8)) as A.
    assert (Z.to_nat (2 ^ 64 / 8) <= Datatypes.length xs)%nat as B by ZnWords.
    specialize (A B). clear B.
    destruct (List.firstn (Z.to_nat (2 ^ 64 / 8)) xs) as [|h1 t1] eqn: E1. {
      cbv [length] in A. ZnWords. 
    }
    destruct (List.skipn (Z.to_nat (2 ^ 64 / 8)) xs) as [|h2 t2] eqn: E2. {
      pose proof @List.skipn_length _ (Z.to_nat (2 ^ 64 / 8)) xs as B.
      rewrite E2 in B. cbn [List.length] in B. ZnWords.
    }
    rewrite <- E in H.
    SeparationLogic.seprewrite_in @array_append H.
    SeparationLogic.seprewrite_in @array_cons H.
    SeparationLogic.seprewrite_in @array_cons H.
    replace (word.add addr (word.of_Z (word.unsigned (word.of_Z 8) * Z.of_nat (Datatypes.length (h1 :: t1)))))
      with addr in H by ZnWords.
    (*
    assert (exists R', (scalar addr h1 * scalar addr h2 * R')%sep m).
    { exists (fun m' => ((array scalar (word.of_Z 8) (word.add addr (word.of_Z 8)) t2)
       ⋆  (array scalar (word.of_Z 8) (word.add addr (word.of_Z 8)) t1) ⋆ R)%sep m'). ecancel_assumption. }
     *)
    
    unfold scalar at 1 3 in H.
    unfold truncated_word in H.
    unfold truncated_scalar in H.
    unfold littleendian in H.
    unfold ptsto_bytes.ptsto_bytes in H.
    cbn in H. rewrite !HList.tuple.to_list_of_list in H.
    eapply (ptsto_nonaliasing addr (List.hd Byte.x00 (LittleEndianList.le_split (Pos.to_nat 8) (word.unsigned h2))) (List.hd Byte.x00 (LittleEndianList.le_split (Pos.to_nat 8) (word.unsigned h1))) m).
    unfold List.hd.
    unfold LittleEndianList.le_split.
    unfold List.hd.
    unfold LittleEndianList.le_split in H. unfold List.hd in H.
    unfold array at 1 3 in H.


    unfold truncated_word, truncated_scalar, littleendian, ptsto_bytes.ptsto_bytes in H.
    cbn in H.
    rewrite !HList.tuple.to_list_of_list in H.
    eapply (ptsto_nonaliasing addr (List.hd Byte.x00 (LittleEndianList.le_split 8 (word.unsigned h2))) (List.hd Byte.x00 (LittleEndianList.le_split 8 (word.unsigned h1))) m).
    unfold LittleEndianList.le_split, List.hd, array in *.
    ecancel_assumption.
  Qed.
   *)


  
 Lemma array_scalar_max_size: forall wordsize arrwidth addr xs (R: mem -> Prop) m,
                      (array scalar arrwidth addr xs * R)%sep m ->
                      (word.unsigned arrwidth) * Z.of_nat (Datatypes.length xs) <= wordsize.
 Proof.
   clear; intros.
   assert ((word.unsigned arrwidth) * Z.of_nat (Datatypes.length xs) <= wordsize \/ wordsize < (word.unsigned arrwidth) * Z.of_nat (Datatypes.length xs))
     as C by Lia.lia. destruct C as [C | C]; [exact C | exfalso].
    pose proof (List.firstn_skipn (Z.to_nat (wordsize / (word.unsigned arrwidth))) xs) as E.
    pose proof @List.firstn_length_le _ xs (Z.to_nat (wordsize / word.unsigned arrwidth)) as A.
    assert (Z.to_nat (wordsize / word.unsigned arrwidth) <= Datatypes.length xs)%nat as B by ZnWords.
    specialize (A B). clear B.
    destruct (List.firstn (Z.to_nat (2 ^ 64 / 8)) xs) as [|h1 t1] eqn: E1. {
      ZnWordsL.
    }
    destruct (List.skipn (Z.to_nat (2 ^ 64 / 8)) xs) as [|h2 t2] eqn: E2. {
      pose proof @List.skipn_length _ (Z.to_nat (2 ^ 64 / 8)) xs as B.
      rewrite E2 in B. cbn [List.length] in B. ZnWords.
    }
 Qed.
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
                                             word.unsigned i <= word.unsigned len /\
                                             l = Z.to_nat (word.unsigned len - word.unsigned i)
                                           )
                                    (fun t' m' Astart' Bstart' Sstart' len' i' =>
                                     (
                                     t = t' /\ Astart = Astart' /\ Bstart = Bstart' /\ Sstart = Sstart' /\ len = len' /\
                                     exists S',
                                       m' =* array scalar (word.of_Z 8) Astart A *
                                              array scalar (word.of_Z 8) Bstart B *
                                              array scalar (word.of_Z 8) Sstart S * R /\
                                       @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned S) mod prime =
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

          { repeat straightline.
            subst i i0. replace (word.add x1 (word.mul (word.of_Z 8) (word.of_Z 0))) with (x1) in H11 by ring. 
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

            - rewrite word.unsigned_of_Z_0. rewrite H3. apply Nat2Z.is_nonneg.
              
          }

          { repeat straightline. eexists. split. { repeat straightline. } repeat straightline. split.

            (*loop exits properly*)
            2: { 
              repeat straightline; repeat split; eauto.
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
                 ZnWords. (*why does ZnWords take so much longer the first time??*)  }
               
               { ZnWords. }

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
              exists "what is this".
              exists "o_O".
              eexists. 
              exists (Z.to_nat (word.unsigned len - word.unsigned i)).
              split.
              { destruct (word.ltu i' len) eqn: Hbreak; try (rewrite word.unsigned_of_Z_0 in H15; contradiction);
                     rewrite word.unsigned_ltu in Hbreak; assert (Hiupper : word.unsigned i' < word.unsigned len) by Lia.lia;
                  subst i.
                split. {  ecancel_assumption. } repeat split; eauto.
                2: { clear - Hiupper. ZnWords. }
                {
                  rewrite <- H20.
                  
                  clear - H19 Hiupper.
                  clear H0 H1 H2 H3 H4 H5 A aval B bval S R m m0 m1 H11 zeros functions
                  H x3 x2 x1 x0 x x9 x10  i1 i0 R' H14. subst. 

                  rename H7 into HAlen; rename H8 into HBlen; rename H9 into HSoldlen;
                  rename H19 into HSnewlen; rename H13 into Holdeval.

                  assert (Hivalid: word.unsigned (word.add i' (word.of_Z 1)) = word.unsigned i' + 1) by
                    (clear - Hiupper; ZnWords).

                  rewrite Hivalid.
                  
                  (*rewrite <-  Pow.Z.pow_mul_base by ZnWords. *)

                  Set Printing Implicit.
                  
                  assert (
                         (@eval r (Z.to_nat (@word.unsigned 64 word i' + 1))
                         (@map (@word.rep 64 word) Z (@word.unsigned 64 word) A')) * ri
                       =

                         (@word.unsigned 64 word
                            (@hd (@word.rep 64 word)
                               ?default@{x4:=A';
                           x5:=@eval r (Z.to_nat (@word.unsigned 64 word len))
                         (@map (@word.rep 64 word) Z (@word.unsigned 64 word) A'); x6:=B';
                   x7:=@eval r (Z.to_nat (@word.unsigned 64 word len))
                         (@map (@word.rep 64 word) Z (@word.unsigned 64 word) B'); x8:=S'; x12:=Astart';
                   x13:=Bstart'; x14:=Sstart'; x15:=len; x16:=i'; H7:=HAlen; H8:=HBlen; H9:=HSoldlen;
                   H13:=Holdeval}
         (@skipn (@word.rep 64 word)
            (Z.to_nat
               (@word.unsigned 64 word (@word.mul 64 word (@word.of_Z 64 word 8) i') /
                @word.unsigned 64 word (@word.of_Z 64 word 8))) A')) 

                         +
                           (@eval r (Z.to_nat (@word.unsigned 64 word i'))
                              (@map (@word.rep 64 word) Z (@word.unsigned 64 word) A'))
                    ).
                              
                              
                  cbv [eval Core.Positional.eval Core.Associational.eval Core.Positional.to_associational].
                  
                  assert ((word.unsigned (word.mul (word.of_Z 8) i') / word.unsigned (word.of_Z 8)) =  word.unsigned i').
                  
                }

              }
              
              {


              }
              
        }

          {  }
          
        }
    Qed.
    
    End WithParameters.
