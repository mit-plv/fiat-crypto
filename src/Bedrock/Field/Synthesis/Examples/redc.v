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
    fnspec! "redc_alt" Astart Bstart Sstart len / A (aval: Z) B (bval: Z) S Ra Rb R,
    { requires t m :=
        m =* array scalar (word.of_Z 8) Astart A * Ra /\
        m =* array scalar (word.of_Z 8) Bstart B * Rb /\
        m =* array scalar (word.of_Z 8) Sstart S * R /\
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
    fnspec! "redc_step" a Bstart Sstart len / B (bval: Z) S (sval: Z) R Rb,
      { requires t m :=
          m =* array scalar (word.of_Z 8) Bstart B * Rb /\
          m =* array scalar (word.of_Z 8) Sstart S * R /\
          word.unsigned len = Z.of_nat (List.length B) /\
          word.unsigned len = Z.of_nat (List.length S) /\
          @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned B) = bval /\
          @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned S) = sval;
        ensures t' m' := t=t' /\ exists S',
            m' =* array scalar (word.of_Z 8) Sstart S' * R /\
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
        repeat split; try eauto. rewrite word.unsigned_of_Z_0. Lia.lia. }

      { repeat straightline. eexists. split. { repeat straightline. } repeat straightline. split.

        (*loop exits properly*)
        2: {
          repeat straightline; repeat split.
          rename x3 into S'; rename x9 into Sstart'; rename x10 into len'; rename x11 into i'; rename x6 into R'.

          destruct (word.ltu i' len') eqn: Hbreak.
          - rewrite word.unsigned_of_Z_1 in H10; try inversion H10; clear H10.
          - destruct (length S') eqn: HS.
          (*length cannot be nonzero*)
          2: { rewrite word.unsigned_ltu in Hbreak. Lia.lia. }
          (*if length is zero, all arrays are the same*)
          cbv [Z.of_nat] in H9. rewrite H9; clear H9 Hbreak.
          apply ListUtil.length0_nil in HS.
          subst S'. apply H8.
        }

          
        (*loop body is good*)
        repeat straightline.
        rename x3 into S'; rename x9 into Sstart'; rename x10 into len'; rename x11 into i'; rename x6 into R'.
        destruct S'.
        - cbv [length Z.of_nat] in H9. 
          destruct (word.ltu i' len') eqn: Hbreak; try (rewrite word.unsigned_of_Z_0 in H10; exfalso; apply H10; trivial).
          rewrite word.unsigned_ltu in Hbreak. Lia.lia. 
        - cbn [array] in H8. repeat straightline.
          repeat split; try trivial. exists (S'). repeat split; try trivial. exists ( (scalar (word.add Sstart' (word.mul (word.of_Z 8) i')) (word.of_Z 0)) * R')%sep. exists (length S').
          repeat split; subst v0 a.
          all: try (repeat (destruct H12 as [solver H12]; try assumption; clear solver)); subst i.
          + replace (word.mul (word.of_Z 8) (word.add i' (word.of_Z 1))) with (word.add (word.mul (word.of_Z 8) i') (word.of_Z 8)) by ring. rewrite word.add_assoc. apply sep_comm. apply sep_assoc. ecancel_assumption.
          + destruct (word.unsigned i' + 1 <? 2^64) eqn: Hisize.
            2: { assert (2^64 - 1 <= word.unsigned i') by Lia.lia; clear Hisize.
                 assert (word.unsigned i' < 2^64) by apply word.unsigned_range.
                 assert (Hi': word.unsigned i' = 2^64 - 1) by Lia.lia; clear H12 H13.
                 assert (Hlen': word.unsigned len' < 2^64) by apply word.unsigned_range.
                 assert (Hneg: word.unsigned len' - word.unsigned i' < 1) by Lia.lia; clear Hi' Hlen'.
                 simpl in H9; simpl in Hneg. rewrite Zpos_P_of_succ_nat in H9.
                 assert (0 <= (Z.of_nat(length S'))) by apply Zle_0_nat.
                 Lia.lia.
            }
                        
            rewrite word.unsigned_add. rewrite word.unsigned_of_Z_1. cbv [word.wrap].
            assert (Hsmall: (word.unsigned i' + 1) mod 2^64 = word.unsigned i' + 1).
            {  apply Z.mod_small. assert (0 <= word.unsigned i') by apply word.unsigned_range. Lia.lia. }
            rewrite Hsmall; clear Hisize Hsmall.

            simpl in H9; simpl. rewrite Zpos_P_of_succ_nat in H9.
            assert (0 <= (Z.of_nat(length S'))) by apply Zle_0_nat.
            Lia.lia.
          + subst v.  auto.
          + assert (Hhead: zeros (word.unsigned len' - word.unsigned i') = word.of_Z 0 :: zeros (word.unsigned len' - word.unsigned (word.add i' (word.of_Z 1))) ).
            {
            destruct (word.unsigned i' + 1 <? 2^64) eqn: Hisize.
            2: { assert (2^64 - 1 <= word.unsigned i') by Lia.lia; clear Hisize.
                 assert (word.unsigned i' < 2^64) by apply word.unsigned_range.
                 assert (Hi': word.unsigned i' = 2^64 - 1) by Lia.lia; clear H12 H13.
                 assert (Hlen': word.unsigned len' < 2^64) by apply word.unsigned_range.
                 assert (Hneg: word.unsigned len' - word.unsigned i' < 1) by Lia.lia; clear Hi' Hlen'.
                 simpl in H9; simpl in Hneg. rewrite Zpos_P_of_succ_nat in H9.
                 assert (0 <= (Z.of_nat(length S'))) by apply Zle_0_nat.
                 Lia.lia.
            }
                        
            rewrite word.unsigned_add. rewrite word.unsigned_of_Z_1. cbv [word.wrap].
            assert (Hsmall: (word.unsigned i' + 1) mod 2^64 = word.unsigned i' + 1).
            {  apply Z.mod_small. assert (0 <= word.unsigned i') by apply word.unsigned_range. Lia.lia. }
            rewrite Hsmall; clear Hisize Hsmall.
            assert (Hpos: 0 <= word.unsigned len' - (word.unsigned i' + 1)). {
              simpl in H9; simpl. rewrite Zpos_P_of_succ_nat in H9.
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
                                            (*m =* array scalar (word.of_Z 8) Astart A * Ra /\
                                            m =* array scalar (word.of_Z 8) Bstart B * Rb /\*)
                                            m =* array scalar (word.of_Z 8) Sstart S * R /\
                                            (*word.unsigned len = Z.of_nat (List.length A)  /\
                                            word.unsigned len = Z.of_nat (List.length B)  /\*)
                                            word.unsigned len = Z.of_nat (List.length S) /\
                                            @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned A) = aval /\ 
                                            (*@eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned B) = bval /\*)
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
                                       m' =* array scalar (word.of_Z 8) Sstart S' * R /\
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
            subst i i0. replace (word.add x1 (word.mul (word.of_Z 8) (word.of_Z 0))) with (x1) in H13 by ring. 
            rewrite word.unsigned_of_Z_0 in H13. replace (word.unsigned x2 - 0) with (word.unsigned x2) in H13 by ring.
            repeat split; eauto. 
            - cbv [zeros]. rewrite repeat_length. rewrite H5. rewrite Nat2Z.id. trivial. 
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

            - rewrite word.unsigned_of_Z_0. rewrite H5. apply Nat2Z.is_nonneg.
              
          }

          { repeat straightline. eexists. split. { repeat straightline. } repeat straightline. split.

            (*loop exits properly*)
            2: {
              repeat straightline; repeat split. exists x8; split; trivial.
              destruct (word.ltu x16 x15) eqn: Hbreak.
              - rewrite word.unsigned_of_Z_1 in H14; inversion H14.
              - subst x5.  rewrite word.unsigned_ltu in Hbreak.
                assert (word.unsigned x15 = word.unsigned x16) by Lia.lia.
                rewrite H10 in *. apply H11.              
            }

            (*loop body good*)
            repeat straightline.


            (*at this point, straightline doesn't go any farther, but we're left with*)
            (*something with this whole "exists args" thing at the beginning that I*)
            (*don't know how to deal with*)

(* exists args : list word.rep,
    dexprs m1 localsmap
      [bedrock_expr:(load($(expr.var "Astart") + $(expr.literal 8) * $(expr.var "i"))); 
      expr.var "Bstart"; expr.var "Sstart"; expr.var "len"] args /\
    call functions "redc_step" t m1 args
      (fun (t0 : trace) (m2 : map.rep) (rets : list word.rep) =>
       exists l : map.rep,
         map.putmany_of_list_zip [] rets localsmap = Some l /\
         WeakestPrecondition.cmd (call functions) bedrock_func_body:(
             $"i" = $(expr.var "i") + $(expr.literal 1)) t0 m2 l
           (fun (t' : trace) (m' localsmap' : map.rep) =>
            unique
              (left
                 (exists x17 x18 x19 x20 x21 : word.rep,
                    Markers.split
                      (enforce ["Astart"; "Bstart"; "Sstart"; "len"; "i"]
                         {|
                           PrimitivePair.pair._1 := x17;
                           PrimitivePair.pair._2 :=
                             {|
                               PrimitivePair.pair._1 := x18;
                               PrimitivePair.pair._2 :=
                                 {|
                                   PrimitivePair.pair._1 := x19;
                                   PrimitivePair.pair._2 :=
                                     {|
                                       PrimitivePair.pair._1 := x20;
                                       PrimitivePair.pair._2 :=
                                         {| PrimitivePair.pair._1 := x21; PrimitivePair.pair._2 := tt |}
                                     |}
                                 |}
                             |}
                         |} localsmap' /\
                       right
                         (unique
                            (left
                               (exists
                                  (x22 : list word.rep) (x23 : Z) (_ : ?Goal12) 
                                (x25 : Z) (x26 : list word.rep) (_ : ?Goal13) 
                                (_ : ?Goal14) (x29 : map.rep -> Prop) (v' : nat),
                                  Markers.split
                                    (((array scalar (word.of_Z 8) x19 x26 ⋆ x29)%sep m' /\
                                      word.unsigned x20 = Z.of_nat (length x26) /\
                                      eval r (map word.unsigned x22) = x23 /\
                                      eval r (map word.unsigned x26) mod prime =
                                      (eval r (map word.unsigned x22) * x25 * ri ^ word.unsigned x21)
                                      mod prime /\
                                      word.unsigned x21 <= word.unsigned x20 /\
                                      v' = Z.to_nat (word.unsigned x20 - word.unsigned x21)) /\
                                     right
                                       (Markers.split
                                          ((v' < v)%nat /\
                                           (forall (T : trace) (M : map.rep) (x30 x31 x32 x33 : word.rep),
                                            word.rep ->
                                            t' = T /\
                                            x17 = x30 /\
                                            x18 = x31 /\ x19 = x32 /\ x20 = x33 /\ (exists ..., ...) ->
                                            t = T /\
                                            x12 = x30 /\
                                            x13 = x31 /\ x14 = x32 /\ x15 = x33 /\ (exists ..., ...))))))))))))) *)
        }

          {  }
          
        }
    Qed.
    
    End WithParameters.
