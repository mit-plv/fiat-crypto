Require Export Bedrock.Word Bedrock.Nomega.
Require Import NArith List.
Require Import Pseudo State Wordize.

Module Conversion.
  Import Pseudo ListNotations StateCommon.

  Definition run {n m w s} (prog: @Pseudo w s n m) (inList: list (word w)) : list (word w) :=  
    match (pseudoEval prog (inList, TripleM.empty N, None)) with
    | Some (outList, _, _) => outList
    | _ => []
    end.

  Lemma pseudo_plus: forall {w s n} (p0 p1: @Pseudo w s n 1) x out0 out1 b,
      (b <= Npow2 w)%N
    -> ((&out0)%w < b)%N
    -> ((&out1)%w < (Npow2 w - b))%N
    -> run p0 x = [out0]
    -> run p1 x = [out1]
    -> run (p0 :+: p1)%p x = [out0 ^+ out1].
  Proof.
    intros; unfold run in *; simpl.
    destruct (pseudoEval p0 _) as [r0|], (pseudoEval p1 _) as [r1|].
    destruct r0 as [r0 rc0], r1 as [r1 rc1].
    destruct r0 as [r0 rm0], r1 as [r1 rm1].

    - subst; simpl.
      destruct ((& out0)%w + (& out1)%w ?= Npow2 w)%N; simpl;
        rewrite (wordize_plus out0 out1 b); try assumption;
        rewrite NToWord_wordToN; intuition.

    - inversion H3.

    - inversion H2.

    - inversion H2.
  Qed.

  Program Definition ex0: Program Unary32 := ($0 :-: $0)%p.

  Eval vm_compute in (run ex0 [natToWord _ 7]).

End Conversion.

