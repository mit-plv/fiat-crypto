Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.BinNat.
Require Import Coq.Arith.Arith.
Require Import Bedrock.Word.

Definition word32 := word 32. (* 2^5 *)
Definition word64 := word 64. (* 2^6 *)
Definition word128 := word 128. (* 2^7 *)

Definition word_case {T : nat -> Type} (logsz : nat)
           (case32 : T 32)
           (case64 : T 64)
           (case128 : T 128)
           (default : forall k, T (2^k))
  : T (2^logsz)
  := match logsz return T (2^logsz) with
     | 5 => case32
     | 6 => case64
     | 7 => case128
     | logsz' => default _
     end.

Definition ZToWord32 (v : Z) : word32 := NToWord _ (Z.to_N v).
Definition word32ToZ (v : word32) : Z := Z.of_N (wordToN v).
Definition wadd32 : word32 -> word32 -> word32 := @wplus _.
Definition wsub32 : word32 -> word32 -> word32 := @wminus _.
Definition wmul32 : word32 -> word32 -> word32 := @wmult _.
Definition wshl32 : word32 -> word32 -> word32 := @wordBin N.shiftl _.
Definition wshr32 : word32 -> word32 -> word32 := @wordBin N.shiftr _.
Definition wland32 : word32 -> word32 -> word32 := @wand _.
Definition wlor32 : word32 -> word32 -> word32 := @wor _.

Definition ZToWord64 (v : Z) : word64 := NToWord _ (Z.to_N v).
Definition word64ToZ (v : word64) : Z := Z.of_N (wordToN v).
Definition wadd64 : word64 -> word64 -> word64 := @wplus _.
Definition wsub64 : word64 -> word64 -> word64 := @wminus _.
Definition wmul64 : word64 -> word64 -> word64 := @wmult _.
Definition wshl64 : word64 -> word64 -> word64 := @wordBin N.shiftl _.
Definition wshr64 : word64 -> word64 -> word64 := @wordBin N.shiftr _.
Definition wland64 : word64 -> word64 -> word64 := @wand _.
Definition wlor64 : word64 -> word64 -> word64 := @wor _.

Definition ZToWord128 (v : Z) : word128 := NToWord _ (Z.to_N v).
Definition word128ToZ (v : word128) : Z := Z.of_N (wordToN v).
Definition wadd128 : word128 -> word128 -> word128 := @wplus _.
Definition wsub128 : word128 -> word128 -> word128 := @wminus _.
Definition wmul128 : word128 -> word128 -> word128 := @wmult _.
Definition wshl128 : word128 -> word128 -> word128 := @wordBin N.shiftl _.
Definition wshr128 : word128 -> word128 -> word128 := @wordBin N.shiftr _.
Definition wland128 : word128 -> word128 -> word128 := @wand _.
Definition wlor128 : word128 -> word128 -> word128 := @wor _.

Definition ZToWord {logsz}
  := word_case (T:=fun sz => Z -> word sz)
               logsz ZToWord32 ZToWord64 ZToWord128 (fun _ v => NToWord _ (Z.to_N v)).
Definition wordToZ {logsz}
  := word_case (T:=fun sz => word sz -> Z)
               logsz word32ToZ word64ToZ word128ToZ (fun _ v => Z.of_N (wordToN v)).
Definition wadd {logsz}
  := word_case (T:=fun sz => word sz -> word sz -> word sz)
               logsz wadd32 wadd64 wadd128 (fun _ => @wplus _).
Definition wsub {logsz}
  := word_case (T:=fun sz => word sz -> word sz -> word sz)
               logsz wsub32 wsub64 wsub128 (fun _ => @wminus _).
Definition wmul {logsz}
  := word_case (T:=fun sz => word sz -> word sz -> word sz)
               logsz wmul32 wmul64 wmul128 (fun _ => @wmult _).
Definition wshl {logsz}
  := word_case (T:=fun sz => word sz -> word sz -> word sz)
               logsz wshl32 wshl64 wshl128 (fun _ => @wordBin N.shiftl _).
Definition wshr {logsz}
  := word_case (T:=fun sz => word sz -> word sz -> word sz)
               logsz wshr32 wshr64 wshr128 (fun _ => @wordBin N.shiftr _).
Definition wland {logsz}
  := word_case (T:=fun sz => word sz -> word sz -> word sz)
               logsz wland32 wland64 wland128 (fun _ => @wand _).
Definition wlor {logsz}
  := word_case (T:=fun sz => word sz -> word sz -> word sz)
               logsz wlor32 wlor64 wlor128 (fun _ => @wor _).
