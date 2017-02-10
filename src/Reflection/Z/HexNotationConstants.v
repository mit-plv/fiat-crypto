Require Import Coq.ZArith.ZArith.
Require Export Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Z.Syntax.
Require Export Bedrock.Word.
Require Export Crypto.Util.Notations.

Notation Const x := (Op (OpConst x) TT).
(* python:
<<
print('\n'.join('''Notation "'%s'" (* %d (%s) *)\n  := (Const %s%%Z).''' % (h, d, h, d)
 for d, h, b, i in sorted([(eval(bv), hex(eval(bv)), bv, i)
 for (bv, i) in (('0b' + i[2:].replace('~', ''), i)
 for i in r"""WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0
WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
WO~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0
WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~0
WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
WO~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~1~0~0~1~1
WO~0~0~0~1~1~0~0~1
WO~0~0~0~1~1~0~1~0
WO~0~0~0~1~1~0~1~1
WO~0~0~0~1~1~1~0~0
WO~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~0
WO~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
WO~0~0~1~1~0~0~1~1
WO~1~0
WO~1~0~0~1
WO~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~1~0~0~0~1
WO~0~0~0~1~0~1~1~1
WO~1~1""".split('\n'))])))
>>
 *)
Notation "'0x2'" (* 2 (0x2) *)
  := (Const 2%Z).
Notation "'0x3'" (* 3 (0x3) *)
  := (Const 3%Z).
Notation "'0x9'" (* 9 (0x9) *)
  := (Const 9%Z).
Notation "'0x11'" (* 17 (0x11) *)
  := (Const 17%Z).
Notation "'0x13'" (* 19 (0x13) *)
  := (Const 19%Z).
Notation "'0x17'" (* 23 (0x17) *)
  := (Const 23%Z).
Notation "'0x19'" (* 25 (0x19) *)
  := (Const 25%Z).
Notation "'0x1a'" (* 26 (0x1a) *)
  := (Const 26%Z).
Notation "'0x1b'" (* 27 (0x1b) *)
  := (Const 27%Z).
Notation "'0x1c'" (* 28 (0x1c) *)
  := (Const 28%Z).
Notation "'0x33'" (* 51 (0x33) *)
  := (Const 51%Z).
Notation "'0x7fffff'" (* 8388607 (0x7fffff) *)
  := (Const 8388607%Z).
Notation "'0x1ffffff'" (* 33554431 (0x1ffffff) *)
  := (Const 33554431%Z).
Notation "'0x3fffffe'" (* 67108862 (0x3fffffe) *)
  := (Const 67108862%Z).
Notation "'0x3ffffff'" (* 67108863 (0x3ffffff) *)
  := (Const 67108863%Z).
Notation "'0x7ffffda'" (* 134217690 (0x7ffffda) *)
  := (Const 134217690%Z).
Notation "'0x7ffffee'" (* 134217710 (0x7ffffee) *)
  := (Const 134217710%Z).
Notation "'0x7fffffe'" (* 134217726 (0x7fffffe) *)
  := (Const 134217726%Z).
Notation "'0x7ffffff'" (* 134217727 (0x7ffffff) *)
  := (Const 134217727%Z).
Notation "'0xffffffe'" (* 268435454 (0xffffffe) *)
  := (Const 268435454%Z).
Notation "'0xfffffff'" (* 268435455 (0xfffffff) *)
  := (Const 268435455%Z).
Notation "'0x1ffffffa'" (* 536870906 (0x1ffffffa) *)
  := (Const 536870906%Z).
Notation "'0x1ffffffe'" (* 536870910 (0x1ffffffe) *)
  := (Const 536870910%Z).
Notation "'0x7ffffffffffff'" (* 2251799813685247 (0x7ffffffffffff) *)
  := (Const 2251799813685247%Z).
Notation "'0xfffffffffffda'" (* 4503599627370458 (0xfffffffffffda) *)
  := (Const 4503599627370458%Z).
Notation "'0xffffffffffffe'" (* 4503599627370494 (0xffffffffffffe) *)
  := (Const 4503599627370494%Z).
