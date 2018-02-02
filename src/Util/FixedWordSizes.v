Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.BinNat.
Require Import Coq.Arith.Arith.
Require Import bbv.WordScope.

Definition word32 := word 32. (* 2^5 *)
Definition word64 := word 64. (* 2^6 *)
Definition word128 := word 128. (* 2^7 *)

Definition word_case {T : nat -> Type} (logsz : nat)
           (case32 : T 5)
           (case64 : T 6)
           (case128 : T 7)
           (default : forall k, T k)
  : T logsz
  := match logsz return T logsz with
     | 5 => case32
     | 6 => case64
     | 7 => case128
     | logsz' => default _
     end.

Definition wordT logsz := word_case (T:=fun _ => Set) logsz word32 word64 word128 (fun logsz => word (2^logsz)).

Definition word_case_dep {T : nat -> Set -> Type} (logsz : nat)
           (case32 : T 5 word32)
           (case64 : T 6 word64)
           (case128 : T 7 word128)
           (default : forall k, T k (word (2^k)))
  : T logsz (wordT logsz)
  := match logsz return T logsz (wordT logsz) with
     | 5 => case32
     | 6 => case64
     | 7 => case128
     | logsz' => default _
     end.

Definition ZToWord_gen {sz} (v : Z) : word sz := NToWord _ (Z.to_N v).
Definition wordToZ_gen {sz} (v : word sz) : Z := Z.of_N (wordToN v).

Definition ZToSignedWord_gen {sz} (v : Z) : word sz := Word.ZToWord _ v.
Definition signedWordToZ_gen {sz} (v : word sz) : Z := Word.wordToZ v.

Definition ZToWord32 : Z -> word32 := @ZToWord_gen _.
Definition word32ToZ : word32 -> Z := @wordToZ_gen _.
Definition ZToSignedWord32 : Z -> word32 := @ZToSignedWord_gen _.
Definition signedWord32ToZ : word32 -> Z := @signedWordToZ_gen _.
Definition wadd32 : word32 -> word32 -> word32 := @wplus _.
Definition wsub32 : word32 -> word32 -> word32 := @wminus _.
Definition wmul32 : word32 -> word32 -> word32 := @wmult _.
Definition wshl32 : word32 -> word32 -> word32 := @wordBin N.shiftl _.
Definition wshr32 : word32 -> word32 -> word32 := @wordBin N.shiftr _.
Definition wland32 : word32 -> word32 -> word32 := @wand _.
Definition wlor32 : word32 -> word32 -> word32 := @wor _.

Definition ZToWord64 : Z -> word64 := @ZToWord_gen _.
Definition word64ToZ : word64 -> Z := @wordToZ_gen _.
Definition ZToSignedWord64 : Z -> word64 := @ZToSignedWord_gen _.
Definition signedWord64ToZ : word64 -> Z := @signedWordToZ_gen _.
Definition wadd64 : word64 -> word64 -> word64 := @wplus _.
Definition wsub64 : word64 -> word64 -> word64 := @wminus _.
Definition wmul64 : word64 -> word64 -> word64 := @wmult _.
Definition wshl64 : word64 -> word64 -> word64 := @wordBin N.shiftl _.
Definition wshr64 : word64 -> word64 -> word64 := @wordBin N.shiftr _.
Definition wland64 : word64 -> word64 -> word64 := @wand _.
Definition wlor64 : word64 -> word64 -> word64 := @wor _.

Definition ZToWord128 : Z -> word128 := @ZToWord_gen _.
Definition word128ToZ : word128 -> Z := @wordToZ_gen _.
Definition ZToSignedWord128 : Z -> word128 := @ZToSignedWord_gen _.
Definition signedWord128ToZ : word128 -> Z := @signedWordToZ_gen _.
Definition wadd128 : word128 -> word128 -> word128 := @wplus _.
Definition wsub128 : word128 -> word128 -> word128 := @wminus _.
Definition wmul128 : word128 -> word128 -> word128 := @wmult _.
Definition wshl128 : word128 -> word128 -> word128 := @wordBin N.shiftl _.
Definition wshr128 : word128 -> word128 -> word128 := @wordBin N.shiftr _.
Definition wland128 : word128 -> word128 -> word128 := @wand _.
Definition wlor128 : word128 -> word128 -> word128 := @wor _.

Definition ZToWord {logsz}
  := word_case_dep (T:=fun _ word => Z -> word)
                   logsz ZToWord32 ZToWord64 ZToWord128 (fun _ => @ZToWord_gen _).
Definition wordToZ {logsz}
  := word_case_dep (T:=fun _ word => word -> Z)
                   logsz word32ToZ word64ToZ word128ToZ (fun _ => @wordToZ_gen _).
Definition ZToSignedWord {logsz}
  := word_case_dep (T:=fun _ word => Z -> word)
                   logsz ZToSignedWord32 ZToSignedWord64 ZToSignedWord128 (fun _ => @ZToSignedWord_gen _).
Definition signedWordToZ {logsz}
  := word_case_dep (T:=fun _ word => word -> Z)
                   logsz signedWord32ToZ signedWord64ToZ signedWord128ToZ (fun _ => @signedWordToZ_gen _).
Definition wadd {logsz}
  := word_case_dep (T:=fun _ word => word -> word -> word)
                   logsz wadd32 wadd64 wadd128 (fun _ => @wplus _).
Definition wsub {logsz}
  := word_case_dep (T:=fun _ word => word -> word -> word)
                   logsz wsub32 wsub64 wsub128 (fun _ => @wminus _).
Definition wmul {logsz}
  := word_case_dep (T:=fun _ word => word -> word -> word)
                   logsz wmul32 wmul64 wmul128 (fun _ => @wmult _).
Definition wshl {logsz}
  := word_case_dep (T:=fun _ word => word -> word -> word)
                   logsz wshl32 wshl64 wshl128 (fun _ => @wordBin N.shiftl _).
Definition wshr {logsz}
  := word_case_dep (T:=fun _ word => word -> word -> word)
                   logsz wshr32 wshr64 wshr128 (fun _ => @wordBin N.shiftr _).
Definition wland {logsz}
  := word_case_dep (T:=fun _ word => word -> word -> word)
                   logsz wland32 wland64 wland128 (fun _ => @wand _).
Definition wlor {logsz}
  := word_case_dep (T:=fun _ word => word -> word -> word)
                   logsz wlor32 wlor64 wlor128 (fun _ => @wor _).

Create HintDb fixed_size_constants discriminated.
Hint Unfold word32 word64 word128
     wadd wadd32 wadd64 wadd128
     wsub wsub32 wsub64 wsub128
     wmul wmul32 wmul64 wmul128
     wshl wshl32 wshl64 wshl128
     wshr wshr32 wshr64 wshr128
     wland wland32 wland64 wland128
     wlor wlor32 wlor64 wlor128 : fixed_size_constants.
