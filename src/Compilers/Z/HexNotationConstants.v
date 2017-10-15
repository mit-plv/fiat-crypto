Require Import Coq.ZArith.ZArith.
Require Export Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Export Bedrock.Word.
Require Export Crypto.Util.Notations.

Notation Const x := (Op (OpConst x) TT).
(* python:
<<
#!/usr/bin/env python
from __future__ import with_statement
import math

nums = tuple(list(range(128)) + [
    187,
    189,
    255,
    317,
    481,
    569,
    765,
    1023,
    65535,
    65536,
    114687,
    121665,
    130307,
    131039,
    131067,
    131071,
    261167,
    261575,
    262131,
    262139,
    262143,
    523807,
    524101,
    524263,
    524269,
    524271,
    524279,
    524287,
    1048471,
    1048549,
    1048557,
    1048559,
    1048573,
    1048575,
    2096128,
    2097127,
    2097135,
    2097143,
    2097151,
    4193987,
    4194115,
    4194275,
    4194279,
    4194285,
    4194287,
    4194293,
    4194303,
    8388491,
    8388577,
    8388581,
    8388591,
    8388599,
    8388605,
    8388606,
    8388607,
    16711679,
    16776959,
    16777191,
    16777199,
    16777201,
    16777213,
    16777215,
    33554413,
    33554417,
    33554429,
    33554431,
    67108833,
    67108855,
    67108859,
    67108861,
    67108862,
    67108863,
    134217690,
    134217710,
    134217726,
    134217727,
    268431360,
    268435454,
    268435455,
    536870893,
    536870906,
    536870910,
    536870911,
    1073741822,
    1073741823,
    4294967107,
    4294967294,
    4294967295,
    8589934559,
    8589934567,
    8589934575,
    8589934587,
    8589934591,
    17179869183,
    34359738341,
    34359738349,
    34359738355,
    34359738367,
    68719476707,
    68719476727,
    68719476733,
    68719476735,
    137436856320,
    137438952991,
    137438953285,
    137438953355,
    137438953471,
    274877906927,
    274877906933,
    274877906939,
    274877906941,
    274877906943,
    274877906944,
    549755813783,
    549755813869,
    549755813887,
    1099511627761,
    1099511627775,
    2199023255543,
    2199023255551,
    4398046511079,
    4398046511099,
    4398046511103,
    8796090925055,
    8796093021443,
    8796093022189,
    8796093022193,
    8796093022207,
    17592186044399,
    17592186044413,
    17592186044415,
    35184372088829,
    35184372088831,
    70368735789055,
    70368744177637,
    70368744177647,
    70368744177659,
    70368744177661,
    70368744177663,
    140737488355303,
    140737488355313,
    140737488355327,
    281470681743359,
    281474976645119,
    281474976710339,
    281474976710639,
    281474976710647,
    281474976710653,
    281474976710655,
    562949953421293,
    562949953421311,
    1125899873288191,
    1125899906842593,
    1125899906842607,
    1125899906842623,
    2251799813160960,
    2251799813685210,
    2251799813685217,
    2251799813685229,
    2251799813685247,
    4503599627370458,
    4503599627370479,
    4503599627370494,
    4503599627370495,
    9007199187632127,
    9007199254740991,
    18014398509481983,
    72057594037927934,
    72057594037927935,
    72057594037927936,
    18446744069414584321,
    18446744073709551614,
    18446744073709551615,
    18446744073709551616,
    38685626227668133590597631,
    77371252455336267181195254,
    77371252455336267181195262,
    79228162514264337593543950335,
    79228162514264337593543950337,
    340282366841710300967557013911933812736,
    340282366920938463463374607431768211455,
    340282366920938463463374607431768211456,
    26959946667150639794667015087019630673637144422540572481103610249216,
])

def log2_up(i):
    return int(math.ceil(math.log(i, 2)))

def word(i, width=None):
    assert(i >= 0)
    if width is None:
        if i == 0: return word(i, width=1)
        return word(i, width=2**log2_up(log2_up(i + 1)))
    return 'WO~' + '~'.join(bin(i)[2:].rjust(width, '0'))

word_formats = tuple(sorted([(n, hex(n), bin(n), word(n)) for n in nums]))

def header():
    return (r"""Require Import Coq.ZArith.ZArith.
Require Export Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Export Bedrock.Word.
Require Export Crypto.Util.Notations.

Notation Const x := (Op (OpConst x) TT).
(""" + r"""* python:
<<
""" +
            open(__file__).read() +
            r""">>
 *""" + r""")""")


def hex_nots():
    return ('\n'.join('''Notation "'%s'" (* %d (%s) *)\n  := (Const %s%%Z).\nNotation "'%s'" (* %d (%s) *)\n  := (Const %s).''' % (h, d, h, d, h, d, h, w)
                      for d, h, b, w in word_formats))
def bin_nots():
    return ('\n'.join('''Notation "'%s'" (* %d (%s) *)\n  := (Const %s).''' % (b, d, h, w)
                      for d, h, b, w in word_formats))

with open('HexNotationConstants.v', 'w') as f:
    f.write(header() + '\n' + hex_nots())

with open('BinaryNotationConstants.v', 'w') as f:
    f.write(header() + '\n' + bin_nots())
>>
 *)
Notation "'0x0'" (* 0 (0x0) *)
  := (Const 0%Z).
Notation "'0x0'" (* 0 (0x0) *)
  := (Const WO~0).
Notation "'0x1'" (* 1 (0x1) *)
  := (Const 1%Z).
Notation "'0x1'" (* 1 (0x1) *)
  := (Const WO~1).
Notation "'0x2'" (* 2 (0x2) *)
  := (Const 2%Z).
Notation "'0x2'" (* 2 (0x2) *)
  := (Const WO~1~0).
Notation "'0x3'" (* 3 (0x3) *)
  := (Const 3%Z).
Notation "'0x3'" (* 3 (0x3) *)
  := (Const WO~1~1).
Notation "'0x4'" (* 4 (0x4) *)
  := (Const 4%Z).
Notation "'0x4'" (* 4 (0x4) *)
  := (Const WO~0~1~0~0).
Notation "'0x5'" (* 5 (0x5) *)
  := (Const 5%Z).
Notation "'0x5'" (* 5 (0x5) *)
  := (Const WO~0~1~0~1).
Notation "'0x6'" (* 6 (0x6) *)
  := (Const 6%Z).
Notation "'0x6'" (* 6 (0x6) *)
  := (Const WO~0~1~1~0).
Notation "'0x7'" (* 7 (0x7) *)
  := (Const 7%Z).
Notation "'0x7'" (* 7 (0x7) *)
  := (Const WO~0~1~1~1).
Notation "'0x8'" (* 8 (0x8) *)
  := (Const 8%Z).
Notation "'0x8'" (* 8 (0x8) *)
  := (Const WO~1~0~0~0).
Notation "'0x9'" (* 9 (0x9) *)
  := (Const 9%Z).
Notation "'0x9'" (* 9 (0x9) *)
  := (Const WO~1~0~0~1).
Notation "'0xa'" (* 10 (0xa) *)
  := (Const 10%Z).
Notation "'0xa'" (* 10 (0xa) *)
  := (Const WO~1~0~1~0).
Notation "'0xb'" (* 11 (0xb) *)
  := (Const 11%Z).
Notation "'0xb'" (* 11 (0xb) *)
  := (Const WO~1~0~1~1).
Notation "'0xc'" (* 12 (0xc) *)
  := (Const 12%Z).
Notation "'0xc'" (* 12 (0xc) *)
  := (Const WO~1~1~0~0).
Notation "'0xd'" (* 13 (0xd) *)
  := (Const 13%Z).
Notation "'0xd'" (* 13 (0xd) *)
  := (Const WO~1~1~0~1).
Notation "'0xe'" (* 14 (0xe) *)
  := (Const 14%Z).
Notation "'0xe'" (* 14 (0xe) *)
  := (Const WO~1~1~1~0).
Notation "'0xf'" (* 15 (0xf) *)
  := (Const 15%Z).
Notation "'0xf'" (* 15 (0xf) *)
  := (Const WO~1~1~1~1).
Notation "'0x10'" (* 16 (0x10) *)
  := (Const 16%Z).
Notation "'0x10'" (* 16 (0x10) *)
  := (Const WO~0~0~0~1~0~0~0~0).
Notation "'0x11'" (* 17 (0x11) *)
  := (Const 17%Z).
Notation "'0x11'" (* 17 (0x11) *)
  := (Const WO~0~0~0~1~0~0~0~1).
Notation "'0x12'" (* 18 (0x12) *)
  := (Const 18%Z).
Notation "'0x12'" (* 18 (0x12) *)
  := (Const WO~0~0~0~1~0~0~1~0).
Notation "'0x13'" (* 19 (0x13) *)
  := (Const 19%Z).
Notation "'0x13'" (* 19 (0x13) *)
  := (Const WO~0~0~0~1~0~0~1~1).
Notation "'0x14'" (* 20 (0x14) *)
  := (Const 20%Z).
Notation "'0x14'" (* 20 (0x14) *)
  := (Const WO~0~0~0~1~0~1~0~0).
Notation "'0x15'" (* 21 (0x15) *)
  := (Const 21%Z).
Notation "'0x15'" (* 21 (0x15) *)
  := (Const WO~0~0~0~1~0~1~0~1).
Notation "'0x16'" (* 22 (0x16) *)
  := (Const 22%Z).
Notation "'0x16'" (* 22 (0x16) *)
  := (Const WO~0~0~0~1~0~1~1~0).
Notation "'0x17'" (* 23 (0x17) *)
  := (Const 23%Z).
Notation "'0x17'" (* 23 (0x17) *)
  := (Const WO~0~0~0~1~0~1~1~1).
Notation "'0x18'" (* 24 (0x18) *)
  := (Const 24%Z).
Notation "'0x18'" (* 24 (0x18) *)
  := (Const WO~0~0~0~1~1~0~0~0).
Notation "'0x19'" (* 25 (0x19) *)
  := (Const 25%Z).
Notation "'0x19'" (* 25 (0x19) *)
  := (Const WO~0~0~0~1~1~0~0~1).
Notation "'0x1a'" (* 26 (0x1a) *)
  := (Const 26%Z).
Notation "'0x1a'" (* 26 (0x1a) *)
  := (Const WO~0~0~0~1~1~0~1~0).
Notation "'0x1b'" (* 27 (0x1b) *)
  := (Const 27%Z).
Notation "'0x1b'" (* 27 (0x1b) *)
  := (Const WO~0~0~0~1~1~0~1~1).
Notation "'0x1c'" (* 28 (0x1c) *)
  := (Const 28%Z).
Notation "'0x1c'" (* 28 (0x1c) *)
  := (Const WO~0~0~0~1~1~1~0~0).
Notation "'0x1d'" (* 29 (0x1d) *)
  := (Const 29%Z).
Notation "'0x1d'" (* 29 (0x1d) *)
  := (Const WO~0~0~0~1~1~1~0~1).
Notation "'0x1e'" (* 30 (0x1e) *)
  := (Const 30%Z).
Notation "'0x1e'" (* 30 (0x1e) *)
  := (Const WO~0~0~0~1~1~1~1~0).
Notation "'0x1f'" (* 31 (0x1f) *)
  := (Const 31%Z).
Notation "'0x1f'" (* 31 (0x1f) *)
  := (Const WO~0~0~0~1~1~1~1~1).
Notation "'0x20'" (* 32 (0x20) *)
  := (Const 32%Z).
Notation "'0x20'" (* 32 (0x20) *)
  := (Const WO~0~0~1~0~0~0~0~0).
Notation "'0x21'" (* 33 (0x21) *)
  := (Const 33%Z).
Notation "'0x21'" (* 33 (0x21) *)
  := (Const WO~0~0~1~0~0~0~0~1).
Notation "'0x22'" (* 34 (0x22) *)
  := (Const 34%Z).
Notation "'0x22'" (* 34 (0x22) *)
  := (Const WO~0~0~1~0~0~0~1~0).
Notation "'0x23'" (* 35 (0x23) *)
  := (Const 35%Z).
Notation "'0x23'" (* 35 (0x23) *)
  := (Const WO~0~0~1~0~0~0~1~1).
Notation "'0x24'" (* 36 (0x24) *)
  := (Const 36%Z).
Notation "'0x24'" (* 36 (0x24) *)
  := (Const WO~0~0~1~0~0~1~0~0).
Notation "'0x25'" (* 37 (0x25) *)
  := (Const 37%Z).
Notation "'0x25'" (* 37 (0x25) *)
  := (Const WO~0~0~1~0~0~1~0~1).
Notation "'0x26'" (* 38 (0x26) *)
  := (Const 38%Z).
Notation "'0x26'" (* 38 (0x26) *)
  := (Const WO~0~0~1~0~0~1~1~0).
Notation "'0x27'" (* 39 (0x27) *)
  := (Const 39%Z).
Notation "'0x27'" (* 39 (0x27) *)
  := (Const WO~0~0~1~0~0~1~1~1).
Notation "'0x28'" (* 40 (0x28) *)
  := (Const 40%Z).
Notation "'0x28'" (* 40 (0x28) *)
  := (Const WO~0~0~1~0~1~0~0~0).
Notation "'0x29'" (* 41 (0x29) *)
  := (Const 41%Z).
Notation "'0x29'" (* 41 (0x29) *)
  := (Const WO~0~0~1~0~1~0~0~1).
Notation "'0x2a'" (* 42 (0x2a) *)
  := (Const 42%Z).
Notation "'0x2a'" (* 42 (0x2a) *)
  := (Const WO~0~0~1~0~1~0~1~0).
Notation "'0x2b'" (* 43 (0x2b) *)
  := (Const 43%Z).
Notation "'0x2b'" (* 43 (0x2b) *)
  := (Const WO~0~0~1~0~1~0~1~1).
Notation "'0x2c'" (* 44 (0x2c) *)
  := (Const 44%Z).
Notation "'0x2c'" (* 44 (0x2c) *)
  := (Const WO~0~0~1~0~1~1~0~0).
Notation "'0x2d'" (* 45 (0x2d) *)
  := (Const 45%Z).
Notation "'0x2d'" (* 45 (0x2d) *)
  := (Const WO~0~0~1~0~1~1~0~1).
Notation "'0x2e'" (* 46 (0x2e) *)
  := (Const 46%Z).
Notation "'0x2e'" (* 46 (0x2e) *)
  := (Const WO~0~0~1~0~1~1~1~0).
Notation "'0x2f'" (* 47 (0x2f) *)
  := (Const 47%Z).
Notation "'0x2f'" (* 47 (0x2f) *)
  := (Const WO~0~0~1~0~1~1~1~1).
Notation "'0x30'" (* 48 (0x30) *)
  := (Const 48%Z).
Notation "'0x30'" (* 48 (0x30) *)
  := (Const WO~0~0~1~1~0~0~0~0).
Notation "'0x31'" (* 49 (0x31) *)
  := (Const 49%Z).
Notation "'0x31'" (* 49 (0x31) *)
  := (Const WO~0~0~1~1~0~0~0~1).
Notation "'0x32'" (* 50 (0x32) *)
  := (Const 50%Z).
Notation "'0x32'" (* 50 (0x32) *)
  := (Const WO~0~0~1~1~0~0~1~0).
Notation "'0x33'" (* 51 (0x33) *)
  := (Const 51%Z).
Notation "'0x33'" (* 51 (0x33) *)
  := (Const WO~0~0~1~1~0~0~1~1).
Notation "'0x34'" (* 52 (0x34) *)
  := (Const 52%Z).
Notation "'0x34'" (* 52 (0x34) *)
  := (Const WO~0~0~1~1~0~1~0~0).
Notation "'0x35'" (* 53 (0x35) *)
  := (Const 53%Z).
Notation "'0x35'" (* 53 (0x35) *)
  := (Const WO~0~0~1~1~0~1~0~1).
Notation "'0x36'" (* 54 (0x36) *)
  := (Const 54%Z).
Notation "'0x36'" (* 54 (0x36) *)
  := (Const WO~0~0~1~1~0~1~1~0).
Notation "'0x37'" (* 55 (0x37) *)
  := (Const 55%Z).
Notation "'0x37'" (* 55 (0x37) *)
  := (Const WO~0~0~1~1~0~1~1~1).
Notation "'0x38'" (* 56 (0x38) *)
  := (Const 56%Z).
Notation "'0x38'" (* 56 (0x38) *)
  := (Const WO~0~0~1~1~1~0~0~0).
Notation "'0x39'" (* 57 (0x39) *)
  := (Const 57%Z).
Notation "'0x39'" (* 57 (0x39) *)
  := (Const WO~0~0~1~1~1~0~0~1).
Notation "'0x3a'" (* 58 (0x3a) *)
  := (Const 58%Z).
Notation "'0x3a'" (* 58 (0x3a) *)
  := (Const WO~0~0~1~1~1~0~1~0).
Notation "'0x3b'" (* 59 (0x3b) *)
  := (Const 59%Z).
Notation "'0x3b'" (* 59 (0x3b) *)
  := (Const WO~0~0~1~1~1~0~1~1).
Notation "'0x3c'" (* 60 (0x3c) *)
  := (Const 60%Z).
Notation "'0x3c'" (* 60 (0x3c) *)
  := (Const WO~0~0~1~1~1~1~0~0).
Notation "'0x3d'" (* 61 (0x3d) *)
  := (Const 61%Z).
Notation "'0x3d'" (* 61 (0x3d) *)
  := (Const WO~0~0~1~1~1~1~0~1).
Notation "'0x3e'" (* 62 (0x3e) *)
  := (Const 62%Z).
Notation "'0x3e'" (* 62 (0x3e) *)
  := (Const WO~0~0~1~1~1~1~1~0).
Notation "'0x3f'" (* 63 (0x3f) *)
  := (Const 63%Z).
Notation "'0x3f'" (* 63 (0x3f) *)
  := (Const WO~0~0~1~1~1~1~1~1).
Notation "'0x40'" (* 64 (0x40) *)
  := (Const 64%Z).
Notation "'0x40'" (* 64 (0x40) *)
  := (Const WO~0~1~0~0~0~0~0~0).
Notation "'0x41'" (* 65 (0x41) *)
  := (Const 65%Z).
Notation "'0x41'" (* 65 (0x41) *)
  := (Const WO~0~1~0~0~0~0~0~1).
Notation "'0x42'" (* 66 (0x42) *)
  := (Const 66%Z).
Notation "'0x42'" (* 66 (0x42) *)
  := (Const WO~0~1~0~0~0~0~1~0).
Notation "'0x43'" (* 67 (0x43) *)
  := (Const 67%Z).
Notation "'0x43'" (* 67 (0x43) *)
  := (Const WO~0~1~0~0~0~0~1~1).
Notation "'0x44'" (* 68 (0x44) *)
  := (Const 68%Z).
Notation "'0x44'" (* 68 (0x44) *)
  := (Const WO~0~1~0~0~0~1~0~0).
Notation "'0x45'" (* 69 (0x45) *)
  := (Const 69%Z).
Notation "'0x45'" (* 69 (0x45) *)
  := (Const WO~0~1~0~0~0~1~0~1).
Notation "'0x46'" (* 70 (0x46) *)
  := (Const 70%Z).
Notation "'0x46'" (* 70 (0x46) *)
  := (Const WO~0~1~0~0~0~1~1~0).
Notation "'0x47'" (* 71 (0x47) *)
  := (Const 71%Z).
Notation "'0x47'" (* 71 (0x47) *)
  := (Const WO~0~1~0~0~0~1~1~1).
Notation "'0x48'" (* 72 (0x48) *)
  := (Const 72%Z).
Notation "'0x48'" (* 72 (0x48) *)
  := (Const WO~0~1~0~0~1~0~0~0).
Notation "'0x49'" (* 73 (0x49) *)
  := (Const 73%Z).
Notation "'0x49'" (* 73 (0x49) *)
  := (Const WO~0~1~0~0~1~0~0~1).
Notation "'0x4a'" (* 74 (0x4a) *)
  := (Const 74%Z).
Notation "'0x4a'" (* 74 (0x4a) *)
  := (Const WO~0~1~0~0~1~0~1~0).
Notation "'0x4b'" (* 75 (0x4b) *)
  := (Const 75%Z).
Notation "'0x4b'" (* 75 (0x4b) *)
  := (Const WO~0~1~0~0~1~0~1~1).
Notation "'0x4c'" (* 76 (0x4c) *)
  := (Const 76%Z).
Notation "'0x4c'" (* 76 (0x4c) *)
  := (Const WO~0~1~0~0~1~1~0~0).
Notation "'0x4d'" (* 77 (0x4d) *)
  := (Const 77%Z).
Notation "'0x4d'" (* 77 (0x4d) *)
  := (Const WO~0~1~0~0~1~1~0~1).
Notation "'0x4e'" (* 78 (0x4e) *)
  := (Const 78%Z).
Notation "'0x4e'" (* 78 (0x4e) *)
  := (Const WO~0~1~0~0~1~1~1~0).
Notation "'0x4f'" (* 79 (0x4f) *)
  := (Const 79%Z).
Notation "'0x4f'" (* 79 (0x4f) *)
  := (Const WO~0~1~0~0~1~1~1~1).
Notation "'0x50'" (* 80 (0x50) *)
  := (Const 80%Z).
Notation "'0x50'" (* 80 (0x50) *)
  := (Const WO~0~1~0~1~0~0~0~0).
Notation "'0x51'" (* 81 (0x51) *)
  := (Const 81%Z).
Notation "'0x51'" (* 81 (0x51) *)
  := (Const WO~0~1~0~1~0~0~0~1).
Notation "'0x52'" (* 82 (0x52) *)
  := (Const 82%Z).
Notation "'0x52'" (* 82 (0x52) *)
  := (Const WO~0~1~0~1~0~0~1~0).
Notation "'0x53'" (* 83 (0x53) *)
  := (Const 83%Z).
Notation "'0x53'" (* 83 (0x53) *)
  := (Const WO~0~1~0~1~0~0~1~1).
Notation "'0x54'" (* 84 (0x54) *)
  := (Const 84%Z).
Notation "'0x54'" (* 84 (0x54) *)
  := (Const WO~0~1~0~1~0~1~0~0).
Notation "'0x55'" (* 85 (0x55) *)
  := (Const 85%Z).
Notation "'0x55'" (* 85 (0x55) *)
  := (Const WO~0~1~0~1~0~1~0~1).
Notation "'0x56'" (* 86 (0x56) *)
  := (Const 86%Z).
Notation "'0x56'" (* 86 (0x56) *)
  := (Const WO~0~1~0~1~0~1~1~0).
Notation "'0x57'" (* 87 (0x57) *)
  := (Const 87%Z).
Notation "'0x57'" (* 87 (0x57) *)
  := (Const WO~0~1~0~1~0~1~1~1).
Notation "'0x58'" (* 88 (0x58) *)
  := (Const 88%Z).
Notation "'0x58'" (* 88 (0x58) *)
  := (Const WO~0~1~0~1~1~0~0~0).
Notation "'0x59'" (* 89 (0x59) *)
  := (Const 89%Z).
Notation "'0x59'" (* 89 (0x59) *)
  := (Const WO~0~1~0~1~1~0~0~1).
Notation "'0x5a'" (* 90 (0x5a) *)
  := (Const 90%Z).
Notation "'0x5a'" (* 90 (0x5a) *)
  := (Const WO~0~1~0~1~1~0~1~0).
Notation "'0x5b'" (* 91 (0x5b) *)
  := (Const 91%Z).
Notation "'0x5b'" (* 91 (0x5b) *)
  := (Const WO~0~1~0~1~1~0~1~1).
Notation "'0x5c'" (* 92 (0x5c) *)
  := (Const 92%Z).
Notation "'0x5c'" (* 92 (0x5c) *)
  := (Const WO~0~1~0~1~1~1~0~0).
Notation "'0x5d'" (* 93 (0x5d) *)
  := (Const 93%Z).
Notation "'0x5d'" (* 93 (0x5d) *)
  := (Const WO~0~1~0~1~1~1~0~1).
Notation "'0x5e'" (* 94 (0x5e) *)
  := (Const 94%Z).
Notation "'0x5e'" (* 94 (0x5e) *)
  := (Const WO~0~1~0~1~1~1~1~0).
Notation "'0x5f'" (* 95 (0x5f) *)
  := (Const 95%Z).
Notation "'0x5f'" (* 95 (0x5f) *)
  := (Const WO~0~1~0~1~1~1~1~1).
Notation "'0x60'" (* 96 (0x60) *)
  := (Const 96%Z).
Notation "'0x60'" (* 96 (0x60) *)
  := (Const WO~0~1~1~0~0~0~0~0).
Notation "'0x61'" (* 97 (0x61) *)
  := (Const 97%Z).
Notation "'0x61'" (* 97 (0x61) *)
  := (Const WO~0~1~1~0~0~0~0~1).
Notation "'0x62'" (* 98 (0x62) *)
  := (Const 98%Z).
Notation "'0x62'" (* 98 (0x62) *)
  := (Const WO~0~1~1~0~0~0~1~0).
Notation "'0x63'" (* 99 (0x63) *)
  := (Const 99%Z).
Notation "'0x63'" (* 99 (0x63) *)
  := (Const WO~0~1~1~0~0~0~1~1).
Notation "'0x64'" (* 100 (0x64) *)
  := (Const 100%Z).
Notation "'0x64'" (* 100 (0x64) *)
  := (Const WO~0~1~1~0~0~1~0~0).
Notation "'0x65'" (* 101 (0x65) *)
  := (Const 101%Z).
Notation "'0x65'" (* 101 (0x65) *)
  := (Const WO~0~1~1~0~0~1~0~1).
Notation "'0x66'" (* 102 (0x66) *)
  := (Const 102%Z).
Notation "'0x66'" (* 102 (0x66) *)
  := (Const WO~0~1~1~0~0~1~1~0).
Notation "'0x67'" (* 103 (0x67) *)
  := (Const 103%Z).
Notation "'0x67'" (* 103 (0x67) *)
  := (Const WO~0~1~1~0~0~1~1~1).
Notation "'0x68'" (* 104 (0x68) *)
  := (Const 104%Z).
Notation "'0x68'" (* 104 (0x68) *)
  := (Const WO~0~1~1~0~1~0~0~0).
Notation "'0x69'" (* 105 (0x69) *)
  := (Const 105%Z).
Notation "'0x69'" (* 105 (0x69) *)
  := (Const WO~0~1~1~0~1~0~0~1).
Notation "'0x6a'" (* 106 (0x6a) *)
  := (Const 106%Z).
Notation "'0x6a'" (* 106 (0x6a) *)
  := (Const WO~0~1~1~0~1~0~1~0).
Notation "'0x6b'" (* 107 (0x6b) *)
  := (Const 107%Z).
Notation "'0x6b'" (* 107 (0x6b) *)
  := (Const WO~0~1~1~0~1~0~1~1).
Notation "'0x6c'" (* 108 (0x6c) *)
  := (Const 108%Z).
Notation "'0x6c'" (* 108 (0x6c) *)
  := (Const WO~0~1~1~0~1~1~0~0).
Notation "'0x6d'" (* 109 (0x6d) *)
  := (Const 109%Z).
Notation "'0x6d'" (* 109 (0x6d) *)
  := (Const WO~0~1~1~0~1~1~0~1).
Notation "'0x6e'" (* 110 (0x6e) *)
  := (Const 110%Z).
Notation "'0x6e'" (* 110 (0x6e) *)
  := (Const WO~0~1~1~0~1~1~1~0).
Notation "'0x6f'" (* 111 (0x6f) *)
  := (Const 111%Z).
Notation "'0x6f'" (* 111 (0x6f) *)
  := (Const WO~0~1~1~0~1~1~1~1).
Notation "'0x70'" (* 112 (0x70) *)
  := (Const 112%Z).
Notation "'0x70'" (* 112 (0x70) *)
  := (Const WO~0~1~1~1~0~0~0~0).
Notation "'0x71'" (* 113 (0x71) *)
  := (Const 113%Z).
Notation "'0x71'" (* 113 (0x71) *)
  := (Const WO~0~1~1~1~0~0~0~1).
Notation "'0x72'" (* 114 (0x72) *)
  := (Const 114%Z).
Notation "'0x72'" (* 114 (0x72) *)
  := (Const WO~0~1~1~1~0~0~1~0).
Notation "'0x73'" (* 115 (0x73) *)
  := (Const 115%Z).
Notation "'0x73'" (* 115 (0x73) *)
  := (Const WO~0~1~1~1~0~0~1~1).
Notation "'0x74'" (* 116 (0x74) *)
  := (Const 116%Z).
Notation "'0x74'" (* 116 (0x74) *)
  := (Const WO~0~1~1~1~0~1~0~0).
Notation "'0x75'" (* 117 (0x75) *)
  := (Const 117%Z).
Notation "'0x75'" (* 117 (0x75) *)
  := (Const WO~0~1~1~1~0~1~0~1).
Notation "'0x76'" (* 118 (0x76) *)
  := (Const 118%Z).
Notation "'0x76'" (* 118 (0x76) *)
  := (Const WO~0~1~1~1~0~1~1~0).
Notation "'0x77'" (* 119 (0x77) *)
  := (Const 119%Z).
Notation "'0x77'" (* 119 (0x77) *)
  := (Const WO~0~1~1~1~0~1~1~1).
Notation "'0x78'" (* 120 (0x78) *)
  := (Const 120%Z).
Notation "'0x78'" (* 120 (0x78) *)
  := (Const WO~0~1~1~1~1~0~0~0).
Notation "'0x79'" (* 121 (0x79) *)
  := (Const 121%Z).
Notation "'0x79'" (* 121 (0x79) *)
  := (Const WO~0~1~1~1~1~0~0~1).
Notation "'0x7a'" (* 122 (0x7a) *)
  := (Const 122%Z).
Notation "'0x7a'" (* 122 (0x7a) *)
  := (Const WO~0~1~1~1~1~0~1~0).
Notation "'0x7b'" (* 123 (0x7b) *)
  := (Const 123%Z).
Notation "'0x7b'" (* 123 (0x7b) *)
  := (Const WO~0~1~1~1~1~0~1~1).
Notation "'0x7c'" (* 124 (0x7c) *)
  := (Const 124%Z).
Notation "'0x7c'" (* 124 (0x7c) *)
  := (Const WO~0~1~1~1~1~1~0~0).
Notation "'0x7d'" (* 125 (0x7d) *)
  := (Const 125%Z).
Notation "'0x7d'" (* 125 (0x7d) *)
  := (Const WO~0~1~1~1~1~1~0~1).
Notation "'0x7e'" (* 126 (0x7e) *)
  := (Const 126%Z).
Notation "'0x7e'" (* 126 (0x7e) *)
  := (Const WO~0~1~1~1~1~1~1~0).
Notation "'0x7f'" (* 127 (0x7f) *)
  := (Const 127%Z).
Notation "'0x7f'" (* 127 (0x7f) *)
  := (Const WO~0~1~1~1~1~1~1~1).
Notation "'0xbb'" (* 187 (0xbb) *)
  := (Const 187%Z).
Notation "'0xbb'" (* 187 (0xbb) *)
  := (Const WO~1~0~1~1~1~0~1~1).
Notation "'0xbd'" (* 189 (0xbd) *)
  := (Const 189%Z).
Notation "'0xbd'" (* 189 (0xbd) *)
  := (Const WO~1~0~1~1~1~1~0~1).
Notation "'0xff'" (* 255 (0xff) *)
  := (Const 255%Z).
Notation "'0xff'" (* 255 (0xff) *)
  := (Const WO~1~1~1~1~1~1~1~1).
Notation "'0x13d'" (* 317 (0x13d) *)
  := (Const 317%Z).
Notation "'0x13d'" (* 317 (0x13d) *)
  := (Const WO~0~0~0~0~0~0~0~1~0~0~1~1~1~1~0~1).
Notation "'0x1e1'" (* 481 (0x1e1) *)
  := (Const 481%Z).
Notation "'0x1e1'" (* 481 (0x1e1) *)
  := (Const WO~0~0~0~0~0~0~0~1~1~1~1~0~0~0~0~1).
Notation "'0x239'" (* 569 (0x239) *)
  := (Const 569%Z).
Notation "'0x239'" (* 569 (0x239) *)
  := (Const WO~0~0~0~0~0~0~1~0~0~0~1~1~1~0~0~1).
Notation "'0x2fd'" (* 765 (0x2fd) *)
  := (Const 765%Z).
Notation "'0x2fd'" (* 765 (0x2fd) *)
  := (Const WO~0~0~0~0~0~0~1~0~1~1~1~1~1~1~0~1).
Notation "'0x3ff'" (* 1023 (0x3ff) *)
  := (Const 1023%Z).
Notation "'0x3ff'" (* 1023 (0x3ff) *)
  := (Const WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1).
Notation "'0xffff'" (* 65535 (0xffff) *)
  := (Const 65535%Z).
Notation "'0xffff'" (* 65535 (0xffff) *)
  := (Const WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x10000'" (* 65536 (0x10000) *)
  := (Const 65536%Z).
Notation "'0x10000'" (* 65536 (0x10000) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).
Notation "'0x1bfff'" (* 114687 (0x1bfff) *)
  := (Const 114687%Z).
Notation "'0x1bfff'" (* 114687 (0x1bfff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x1db41'" (* 121665 (0x1db41) *)
  := (Const 121665%Z).
Notation "'0x1db41'" (* 121665 (0x1db41) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~0~1~1~0~1~1~0~1~0~0~0~0~0~1).
Notation "'0x1fd03'" (* 130307 (0x1fd03) *)
  := (Const 130307%Z).
Notation "'0x1fd03'" (* 130307 (0x1fd03) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~0~1~0~0~0~0~0~0~1~1).
Notation "'0x1ffdf'" (* 131039 (0x1ffdf) *)
  := (Const 131039%Z).
Notation "'0x1ffdf'" (* 131039 (0x1ffdf) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1~1).
Notation "'0x1fffb'" (* 131067 (0x1fffb) *)
  := (Const 131067%Z).
Notation "'0x1fffb'" (* 131067 (0x1fffb) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1).
Notation "'0x1ffff'" (* 131071 (0x1ffff) *)
  := (Const 131071%Z).
Notation "'0x1ffff'" (* 131071 (0x1ffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x3fc2f'" (* 261167 (0x3fc2f) *)
  := (Const 261167%Z).
Notation "'0x3fc2f'" (* 261167 (0x3fc2f) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~0~0~0~0~1~0~1~1~1~1).
Notation "'0x3fdc7'" (* 261575 (0x3fdc7) *)
  := (Const 261575%Z).
Notation "'0x3fdc7'" (* 261575 (0x3fdc7) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~0~1~1~1~0~0~0~1~1~1).
Notation "'0x3fff3'" (* 262131 (0x3fff3) *)
  := (Const 262131%Z).
Notation "'0x3fff3'" (* 262131 (0x3fff3) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~1~1).
Notation "'0x3fffb'" (* 262139 (0x3fffb) *)
  := (Const 262139%Z).
Notation "'0x3fffb'" (* 262139 (0x3fffb) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1).
Notation "'0x3ffff'" (* 262143 (0x3ffff) *)
  := (Const 262143%Z).
Notation "'0x3ffff'" (* 262143 (0x3ffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x7fe1f'" (* 523807 (0x7fe1f) *)
  := (Const 523807%Z).
Notation "'0x7fe1f'" (* 523807 (0x7fe1f) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~0~0~0~0~1~1~1~1~1).
Notation "'0x7ff45'" (* 524101 (0x7ff45) *)
  := (Const 524101%Z).
Notation "'0x7ff45'" (* 524101 (0x7ff45) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~0~1~0~0~0~1~0~1).
Notation "'0x7ffe7'" (* 524263 (0x7ffe7) *)
  := (Const 524263%Z).
Notation "'0x7ffe7'" (* 524263 (0x7ffe7) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~1~1~1).
Notation "'0x7ffed'" (* 524269 (0x7ffed) *)
  := (Const 524269%Z).
Notation "'0x7ffed'" (* 524269 (0x7ffed) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1).
Notation "'0x7ffef'" (* 524271 (0x7ffef) *)
  := (Const 524271%Z).
Notation "'0x7ffef'" (* 524271 (0x7ffef) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1).
Notation "'0x7fff7'" (* 524279 (0x7fff7) *)
  := (Const 524279%Z).
Notation "'0x7fff7'" (* 524279 (0x7fff7) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1).
Notation "'0x7ffff'" (* 524287 (0x7ffff) *)
  := (Const 524287%Z).
Notation "'0x7ffff'" (* 524287 (0x7ffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0xfff97'" (* 1048471 (0xfff97) *)
  := (Const 1048471%Z).
Notation "'0xfff97'" (* 1048471 (0xfff97) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~1~0~1~1~1).
Notation "'0xfffe5'" (* 1048549 (0xfffe5) *)
  := (Const 1048549%Z).
Notation "'0xfffe5'" (* 1048549 (0xfffe5) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~1~0~1).
Notation "'0xfffed'" (* 1048557 (0xfffed) *)
  := (Const 1048557%Z).
Notation "'0xfffed'" (* 1048557 (0xfffed) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1).
Notation "'0xfffef'" (* 1048559 (0xfffef) *)
  := (Const 1048559%Z).
Notation "'0xfffef'" (* 1048559 (0xfffef) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1).
Notation "'0xffffd'" (* 1048573 (0xffffd) *)
  := (Const 1048573%Z).
Notation "'0xffffd'" (* 1048573 (0xffffd) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1).
Notation "'0xfffff'" (* 1048575 (0xfffff) *)
  := (Const 1048575%Z).
Notation "'0xfffff'" (* 1048575 (0xfffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x1ffc00'" (* 2096128 (0x1ffc00) *)
  := (Const 2096128%Z).
Notation "'0x1ffc00'" (* 2096128 (0x1ffc00) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0).
Notation "'0x1fffe7'" (* 2097127 (0x1fffe7) *)
  := (Const 2097127%Z).
Notation "'0x1fffe7'" (* 2097127 (0x1fffe7) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~1~1~1).
Notation "'0x1fffef'" (* 2097135 (0x1fffef) *)
  := (Const 2097135%Z).
Notation "'0x1fffef'" (* 2097135 (0x1fffef) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1).
Notation "'0x1ffff7'" (* 2097143 (0x1ffff7) *)
  := (Const 2097143%Z).
Notation "'0x1ffff7'" (* 2097143 (0x1ffff7) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1).
Notation "'0x1fffff'" (* 2097151 (0x1fffff) *)
  := (Const 2097151%Z).
Notation "'0x1fffff'" (* 2097151 (0x1fffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x3ffec3'" (* 4193987 (0x3ffec3) *)
  := (Const 4193987%Z).
Notation "'0x3ffec3'" (* 4193987 (0x3ffec3) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~0~0~0~1~1).
Notation "'0x3fff43'" (* 4194115 (0x3fff43) *)
  := (Const 4194115%Z).
Notation "'0x3fff43'" (* 4194115 (0x3fff43) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~0~0~0~0~1~1).
Notation "'0x3fffe3'" (* 4194275 (0x3fffe3) *)
  := (Const 4194275%Z).
Notation "'0x3fffe3'" (* 4194275 (0x3fffe3) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~1~1).
Notation "'0x3fffe7'" (* 4194279 (0x3fffe7) *)
  := (Const 4194279%Z).
Notation "'0x3fffe7'" (* 4194279 (0x3fffe7) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~1~1~1).
Notation "'0x3fffed'" (* 4194285 (0x3fffed) *)
  := (Const 4194285%Z).
Notation "'0x3fffed'" (* 4194285 (0x3fffed) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1).
Notation "'0x3fffef'" (* 4194287 (0x3fffef) *)
  := (Const 4194287%Z).
Notation "'0x3fffef'" (* 4194287 (0x3fffef) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1).
Notation "'0x3ffff5'" (* 4194293 (0x3ffff5) *)
  := (Const 4194293%Z).
Notation "'0x3ffff5'" (* 4194293 (0x3ffff5) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~0~1).
Notation "'0x3fffff'" (* 4194303 (0x3fffff) *)
  := (Const 4194303%Z).
Notation "'0x3fffff'" (* 4194303 (0x3fffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x7fff8b'" (* 8388491 (0x7fff8b) *)
  := (Const 8388491%Z).
Notation "'0x7fff8b'" (* 8388491 (0x7fff8b) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~1~0~1~1).
Notation "'0x7fffe1'" (* 8388577 (0x7fffe1) *)
  := (Const 8388577%Z).
Notation "'0x7fffe1'" (* 8388577 (0x7fffe1) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~1).
Notation "'0x7fffe5'" (* 8388581 (0x7fffe5) *)
  := (Const 8388581%Z).
Notation "'0x7fffe5'" (* 8388581 (0x7fffe5) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~1~0~1).
Notation "'0x7fffef'" (* 8388591 (0x7fffef) *)
  := (Const 8388591%Z).
Notation "'0x7fffef'" (* 8388591 (0x7fffef) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1).
Notation "'0x7ffff7'" (* 8388599 (0x7ffff7) *)
  := (Const 8388599%Z).
Notation "'0x7ffff7'" (* 8388599 (0x7ffff7) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1).
Notation "'0x7ffffd'" (* 8388605 (0x7ffffd) *)
  := (Const 8388605%Z).
Notation "'0x7ffffd'" (* 8388605 (0x7ffffd) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1).
Notation "'0x7ffffe'" (* 8388606 (0x7ffffe) *)
  := (Const 8388606%Z).
Notation "'0x7ffffe'" (* 8388606 (0x7ffffe) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0x7fffff'" (* 8388607 (0x7fffff) *)
  := (Const 8388607%Z).
Notation "'0x7fffff'" (* 8388607 (0x7fffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0xfeffff'" (* 16711679 (0xfeffff) *)
  := (Const 16711679%Z).
Notation "'0xfeffff'" (* 16711679 (0xfeffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0xfffeff'" (* 16776959 (0xfffeff) *)
  := (Const 16776959%Z).
Notation "'0xfffeff'" (* 16776959 (0xfffeff) *)
  := (Const WO~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1~1~1~1~1).
Notation "'0xffffe7'" (* 16777191 (0xffffe7) *)
  := (Const 16777191%Z).
Notation "'0xffffe7'" (* 16777191 (0xffffe7) *)
  := (Const WO~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~1~1~1).
Notation "'0xffffef'" (* 16777199 (0xffffef) *)
  := (Const 16777199%Z).
Notation "'0xffffef'" (* 16777199 (0xffffef) *)
  := (Const WO~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1).
Notation "'0xfffff1'" (* 16777201 (0xfffff1) *)
  := (Const 16777201%Z).
Notation "'0xfffff1'" (* 16777201 (0xfffff1) *)
  := (Const WO~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~1).
Notation "'0xfffffd'" (* 16777213 (0xfffffd) *)
  := (Const 16777213%Z).
Notation "'0xfffffd'" (* 16777213 (0xfffffd) *)
  := (Const WO~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1).
Notation "'0xffffff'" (* 16777215 (0xffffff) *)
  := (Const 16777215%Z).
Notation "'0xffffff'" (* 16777215 (0xffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x1ffffed'" (* 33554413 (0x1ffffed) *)
  := (Const 33554413%Z).
Notation "'0x1ffffed'" (* 33554413 (0x1ffffed) *)
  := (Const WO~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1).
Notation "'0x1fffff1'" (* 33554417 (0x1fffff1) *)
  := (Const 33554417%Z).
Notation "'0x1fffff1'" (* 33554417 (0x1fffff1) *)
  := (Const WO~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~1).
Notation "'0x1fffffd'" (* 33554429 (0x1fffffd) *)
  := (Const 33554429%Z).
Notation "'0x1fffffd'" (* 33554429 (0x1fffffd) *)
  := (Const WO~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1).
Notation "'0x1ffffff'" (* 33554431 (0x1ffffff) *)
  := (Const 33554431%Z).
Notation "'0x1ffffff'" (* 33554431 (0x1ffffff) *)
  := (Const WO~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x3ffffe1'" (* 67108833 (0x3ffffe1) *)
  := (Const 67108833%Z).
Notation "'0x3ffffe1'" (* 67108833 (0x3ffffe1) *)
  := (Const WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~1).
Notation "'0x3fffff7'" (* 67108855 (0x3fffff7) *)
  := (Const 67108855%Z).
Notation "'0x3fffff7'" (* 67108855 (0x3fffff7) *)
  := (Const WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1).
Notation "'0x3fffffb'" (* 67108859 (0x3fffffb) *)
  := (Const 67108859%Z).
Notation "'0x3fffffb'" (* 67108859 (0x3fffffb) *)
  := (Const WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1).
Notation "'0x3fffffd'" (* 67108861 (0x3fffffd) *)
  := (Const 67108861%Z).
Notation "'0x3fffffd'" (* 67108861 (0x3fffffd) *)
  := (Const WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1).
Notation "'0x3fffffe'" (* 67108862 (0x3fffffe) *)
  := (Const 67108862%Z).
Notation "'0x3fffffe'" (* 67108862 (0x3fffffe) *)
  := (Const WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0x3ffffff'" (* 67108863 (0x3ffffff) *)
  := (Const 67108863%Z).
Notation "'0x3ffffff'" (* 67108863 (0x3ffffff) *)
  := (Const WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x7ffffda'" (* 134217690 (0x7ffffda) *)
  := (Const 134217690%Z).
Notation "'0x7ffffda'" (* 134217690 (0x7ffffda) *)
  := (Const WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0).
Notation "'0x7ffffee'" (* 134217710 (0x7ffffee) *)
  := (Const 134217710%Z).
Notation "'0x7ffffee'" (* 134217710 (0x7ffffee) *)
  := (Const WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~0).
Notation "'0x7fffffe'" (* 134217726 (0x7fffffe) *)
  := (Const 134217726%Z).
Notation "'0x7fffffe'" (* 134217726 (0x7fffffe) *)
  := (Const WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0x7ffffff'" (* 134217727 (0x7ffffff) *)
  := (Const 134217727%Z).
Notation "'0x7ffffff'" (* 134217727 (0x7ffffff) *)
  := (Const WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0xffff000'" (* 268431360 (0xffff000) *)
  := (Const 268431360%Z).
Notation "'0xffff000'" (* 268431360 (0xffff000) *)
  := (Const WO~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0).
Notation "'0xffffffe'" (* 268435454 (0xffffffe) *)
  := (Const 268435454%Z).
Notation "'0xffffffe'" (* 268435454 (0xffffffe) *)
  := (Const WO~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0xfffffff'" (* 268435455 (0xfffffff) *)
  := (Const 268435455%Z).
Notation "'0xfffffff'" (* 268435455 (0xfffffff) *)
  := (Const WO~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x1fffffed'" (* 536870893 (0x1fffffed) *)
  := (Const 536870893%Z).
Notation "'0x1fffffed'" (* 536870893 (0x1fffffed) *)
  := (Const WO~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1).
Notation "'0x1ffffffa'" (* 536870906 (0x1ffffffa) *)
  := (Const 536870906%Z).
Notation "'0x1ffffffa'" (* 536870906 (0x1ffffffa) *)
  := (Const WO~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~0).
Notation "'0x1ffffffe'" (* 536870910 (0x1ffffffe) *)
  := (Const 536870910%Z).
Notation "'0x1ffffffe'" (* 536870910 (0x1ffffffe) *)
  := (Const WO~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0x1fffffff'" (* 536870911 (0x1fffffff) *)
  := (Const 536870911%Z).
Notation "'0x1fffffff'" (* 536870911 (0x1fffffff) *)
  := (Const WO~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x3ffffffe'" (* 1073741822 (0x3ffffffe) *)
  := (Const 1073741822%Z).
Notation "'0x3ffffffe'" (* 1073741822 (0x3ffffffe) *)
  := (Const WO~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0x3fffffff'" (* 1073741823 (0x3fffffff) *)
  := (Const 1073741823%Z).
Notation "'0x3fffffff'" (* 1073741823 (0x3fffffff) *)
  := (Const WO~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0xffffff43'" (* 4294967107 (0xffffff43) *)
  := (Const 4294967107%Z).
Notation "'0xffffff43'" (* 4294967107 (0xffffff43) *)
  := (Const WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~0~0~0~0~1~1).
Notation "'0xfffffffe'" (* 4294967294 (0xfffffffe) *)
  := (Const 4294967294%Z).
Notation "'0xfffffffe'" (* 4294967294 (0xfffffffe) *)
  := (Const WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0xffffffff'" (* 4294967295 (0xffffffff) *)
  := (Const 4294967295%Z).
Notation "'0xffffffff'" (* 4294967295 (0xffffffff) *)
  := (Const WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x1ffffffdf'" (* 8589934559 (0x1ffffffdf) *)
  := (Const 8589934559%Z).
Notation "'0x1ffffffdf'" (* 8589934559 (0x1ffffffdf) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1~1).
Notation "'0x1ffffffe7'" (* 8589934567 (0x1ffffffe7) *)
  := (Const 8589934567%Z).
Notation "'0x1ffffffe7'" (* 8589934567 (0x1ffffffe7) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~1~1~1).
Notation "'0x1ffffffef'" (* 8589934575 (0x1ffffffef) *)
  := (Const 8589934575%Z).
Notation "'0x1ffffffef'" (* 8589934575 (0x1ffffffef) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1).
Notation "'0x1fffffffb'" (* 8589934587 (0x1fffffffb) *)
  := (Const 8589934587%Z).
Notation "'0x1fffffffb'" (* 8589934587 (0x1fffffffb) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1).
Notation "'0x1ffffffff'" (* 8589934591 (0x1ffffffff) *)
  := (Const 8589934591%Z).
Notation "'0x1ffffffff'" (* 8589934591 (0x1ffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x3ffffffff'" (* 17179869183 (0x3ffffffff) *)
  := (Const 17179869183%Z).
Notation "'0x3ffffffff'" (* 17179869183 (0x3ffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x7ffffffe5'" (* 34359738341 (0x7ffffffe5) *)
  := (Const 34359738341%Z).
Notation "'0x7ffffffe5'" (* 34359738341 (0x7ffffffe5) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~1~0~1).
Notation "'0x7ffffffed'" (* 34359738349 (0x7ffffffed) *)
  := (Const 34359738349%Z).
Notation "'0x7ffffffed'" (* 34359738349 (0x7ffffffed) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1).
Notation "'0x7fffffff3'" (* 34359738355 (0x7fffffff3) *)
  := (Const 34359738355%Z).
Notation "'0x7fffffff3'" (* 34359738355 (0x7fffffff3) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~1~1).
Notation "'0x7ffffffff'" (* 34359738367 (0x7ffffffff) *)
  := (Const 34359738367%Z).
Notation "'0x7ffffffff'" (* 34359738367 (0x7ffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0xfffffffe3'" (* 68719476707 (0xfffffffe3) *)
  := (Const 68719476707%Z).
Notation "'0xfffffffe3'" (* 68719476707 (0xfffffffe3) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~1~1).
Notation "'0xffffffff7'" (* 68719476727 (0xffffffff7) *)
  := (Const 68719476727%Z).
Notation "'0xffffffff7'" (* 68719476727 (0xffffffff7) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1).
Notation "'0xffffffffd'" (* 68719476733 (0xffffffffd) *)
  := (Const 68719476733%Z).
Notation "'0xffffffffd'" (* 68719476733 (0xffffffffd) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1).
Notation "'0xfffffffff'" (* 68719476735 (0xfffffffff) *)
  := (Const 68719476735%Z).
Notation "'0xfffffffff'" (* 68719476735 (0xfffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x1fffe00000'" (* 137436856320 (0x1fffe00000) *)
  := (Const 137436856320%Z).
Notation "'0x1fffe00000'" (* 137436856320 (0x1fffe00000) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).
Notation "'0x1ffffffe1f'" (* 137438952991 (0x1ffffffe1f) *)
  := (Const 137438952991%Z).
Notation "'0x1ffffffe1f'" (* 137438952991 (0x1ffffffe1f) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~1~1~1~1~1).
Notation "'0x1fffffff45'" (* 137438953285 (0x1fffffff45) *)
  := (Const 137438953285%Z).
Notation "'0x1fffffff45'" (* 137438953285 (0x1fffffff45) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~0~0~0~1~0~1).
Notation "'0x1fffffff8b'" (* 137438953355 (0x1fffffff8b) *)
  := (Const 137438953355%Z).
Notation "'0x1fffffff8b'" (* 137438953355 (0x1fffffff8b) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~1~0~1~1).
Notation "'0x1fffffffff'" (* 137438953471 (0x1fffffffff) *)
  := (Const 137438953471%Z).
Notation "'0x1fffffffff'" (* 137438953471 (0x1fffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x3fffffffef'" (* 274877906927 (0x3fffffffef) *)
  := (Const 274877906927%Z).
Notation "'0x3fffffffef'" (* 274877906927 (0x3fffffffef) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1).
Notation "'0x3ffffffff5'" (* 274877906933 (0x3ffffffff5) *)
  := (Const 274877906933%Z).
Notation "'0x3ffffffff5'" (* 274877906933 (0x3ffffffff5) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~0~1).
Notation "'0x3ffffffffb'" (* 274877906939 (0x3ffffffffb) *)
  := (Const 274877906939%Z).
Notation "'0x3ffffffffb'" (* 274877906939 (0x3ffffffffb) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1).
Notation "'0x3ffffffffd'" (* 274877906941 (0x3ffffffffd) *)
  := (Const 274877906941%Z).
Notation "'0x3ffffffffd'" (* 274877906941 (0x3ffffffffd) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1).
Notation "'0x3fffffffff'" (* 274877906943 (0x3fffffffff) *)
  := (Const 274877906943%Z).
Notation "'0x3fffffffff'" (* 274877906943 (0x3fffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x4000000000'" (* 274877906944 (0x4000000000) *)
  := (Const 274877906944%Z).
Notation "'0x4000000000'" (* 274877906944 (0x4000000000) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).
Notation "'0x7fffffff97'" (* 549755813783 (0x7fffffff97) *)
  := (Const 549755813783%Z).
Notation "'0x7fffffff97'" (* 549755813783 (0x7fffffff97) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~1~0~1~1~1).
Notation "'0x7fffffffed'" (* 549755813869 (0x7fffffffed) *)
  := (Const 549755813869%Z).
Notation "'0x7fffffffed'" (* 549755813869 (0x7fffffffed) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1).
Notation "'0x7fffffffff'" (* 549755813887 (0x7fffffffff) *)
  := (Const 549755813887%Z).
Notation "'0x7fffffffff'" (* 549755813887 (0x7fffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0xfffffffff1'" (* 1099511627761 (0xfffffffff1) *)
  := (Const 1099511627761%Z).
Notation "'0xfffffffff1'" (* 1099511627761 (0xfffffffff1) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~1).
Notation "'0xffffffffff'" (* 1099511627775 (0xffffffffff) *)
  := (Const 1099511627775%Z).
Notation "'0xffffffffff'" (* 1099511627775 (0xffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x1fffffffff7'" (* 2199023255543 (0x1fffffffff7) *)
  := (Const 2199023255543%Z).
Notation "'0x1fffffffff7'" (* 2199023255543 (0x1fffffffff7) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1).
Notation "'0x1ffffffffff'" (* 2199023255551 (0x1ffffffffff) *)
  := (Const 2199023255551%Z).
Notation "'0x1ffffffffff'" (* 2199023255551 (0x1ffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x3ffffffffe7'" (* 4398046511079 (0x3ffffffffe7) *)
  := (Const 4398046511079%Z).
Notation "'0x3ffffffffe7'" (* 4398046511079 (0x3ffffffffe7) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~1~1~1).
Notation "'0x3fffffffffb'" (* 4398046511099 (0x3fffffffffb) *)
  := (Const 4398046511099%Z).
Notation "'0x3fffffffffb'" (* 4398046511099 (0x3fffffffffb) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1).
Notation "'0x3ffffffffff'" (* 4398046511103 (0x3ffffffffff) *)
  := (Const 4398046511103%Z).
Notation "'0x3ffffffffff'" (* 4398046511103 (0x3ffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x7ffffdfffff'" (* 8796090925055 (0x7ffffdfffff) *)
  := (Const 8796090925055%Z).
Notation "'0x7ffffdfffff'" (* 8796090925055 (0x7ffffdfffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x7fffffffd03'" (* 8796093021443 (0x7fffffffd03) *)
  := (Const 8796093021443%Z).
Notation "'0x7fffffffd03'" (* 8796093021443 (0x7fffffffd03) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~0~0~0~0~0~0~1~1).
Notation "'0x7ffffffffed'" (* 8796093022189 (0x7ffffffffed) *)
  := (Const 8796093022189%Z).
Notation "'0x7ffffffffed'" (* 8796093022189 (0x7ffffffffed) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1).
Notation "'0x7fffffffff1'" (* 8796093022193 (0x7fffffffff1) *)
  := (Const 8796093022193%Z).
Notation "'0x7fffffffff1'" (* 8796093022193 (0x7fffffffff1) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~1).
Notation "'0x7ffffffffff'" (* 8796093022207 (0x7ffffffffff) *)
  := (Const 8796093022207%Z).
Notation "'0x7ffffffffff'" (* 8796093022207 (0x7ffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0xfffffffffef'" (* 17592186044399 (0xfffffffffef) *)
  := (Const 17592186044399%Z).
Notation "'0xfffffffffef'" (* 17592186044399 (0xfffffffffef) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1).
Notation "'0xffffffffffd'" (* 17592186044413 (0xffffffffffd) *)
  := (Const 17592186044413%Z).
Notation "'0xffffffffffd'" (* 17592186044413 (0xffffffffffd) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1).
Notation "'0xfffffffffff'" (* 17592186044415 (0xfffffffffff) *)
  := (Const 17592186044415%Z).
Notation "'0xfffffffffff'" (* 17592186044415 (0xfffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x1ffffffffffd'" (* 35184372088829 (0x1ffffffffffd) *)
  := (Const 35184372088829%Z).
Notation "'0x1ffffffffffd'" (* 35184372088829 (0x1ffffffffffd) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1).
Notation "'0x1fffffffffff'" (* 35184372088831 (0x1fffffffffff) *)
  := (Const 35184372088831%Z).
Notation "'0x1fffffffffff'" (* 35184372088831 (0x1fffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x3fffff7fffff'" (* 70368735789055 (0x3fffff7fffff) *)
  := (Const 70368735789055%Z).
Notation "'0x3fffff7fffff'" (* 70368735789055 (0x3fffff7fffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x3fffffffffe5'" (* 70368744177637 (0x3fffffffffe5) *)
  := (Const 70368744177637%Z).
Notation "'0x3fffffffffe5'" (* 70368744177637 (0x3fffffffffe5) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~1~0~1).
Notation "'0x3fffffffffef'" (* 70368744177647 (0x3fffffffffef) *)
  := (Const 70368744177647%Z).
Notation "'0x3fffffffffef'" (* 70368744177647 (0x3fffffffffef) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1).
Notation "'0x3ffffffffffb'" (* 70368744177659 (0x3ffffffffffb) *)
  := (Const 70368744177659%Z).
Notation "'0x3ffffffffffb'" (* 70368744177659 (0x3ffffffffffb) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1).
Notation "'0x3ffffffffffd'" (* 70368744177661 (0x3ffffffffffd) *)
  := (Const 70368744177661%Z).
Notation "'0x3ffffffffffd'" (* 70368744177661 (0x3ffffffffffd) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1).
Notation "'0x3fffffffffff'" (* 70368744177663 (0x3fffffffffff) *)
  := (Const 70368744177663%Z).
Notation "'0x3fffffffffff'" (* 70368744177663 (0x3fffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x7fffffffffe7'" (* 140737488355303 (0x7fffffffffe7) *)
  := (Const 140737488355303%Z).
Notation "'0x7fffffffffe7'" (* 140737488355303 (0x7fffffffffe7) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~1~1~1).
Notation "'0x7ffffffffff1'" (* 140737488355313 (0x7ffffffffff1) *)
  := (Const 140737488355313%Z).
Notation "'0x7ffffffffff1'" (* 140737488355313 (0x7ffffffffff1) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~1).
Notation "'0x7fffffffffff'" (* 140737488355327 (0x7fffffffffff) *)
  := (Const 140737488355327%Z).
Notation "'0x7fffffffffff'" (* 140737488355327 (0x7fffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0xfffeffffffff'" (* 281470681743359 (0xfffeffffffff) *)
  := (Const 281470681743359%Z).
Notation "'0xfffeffffffff'" (* 281470681743359 (0xfffeffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0xfffffffeffff'" (* 281474976645119 (0xfffffffeffff) *)
  := (Const 281474976645119%Z).
Notation "'0xfffffffeffff'" (* 281474976645119 (0xfffffffeffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0xfffffffffec3'" (* 281474976710339 (0xfffffffffec3) *)
  := (Const 281474976710339%Z).
Notation "'0xfffffffffec3'" (* 281474976710339 (0xfffffffffec3) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~0~0~0~1~1).
Notation "'0xffffffffffef'" (* 281474976710639 (0xffffffffffef) *)
  := (Const 281474976710639%Z).
Notation "'0xffffffffffef'" (* 281474976710639 (0xffffffffffef) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1).
Notation "'0xfffffffffff7'" (* 281474976710647 (0xfffffffffff7) *)
  := (Const 281474976710647%Z).
Notation "'0xfffffffffff7'" (* 281474976710647 (0xfffffffffff7) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1).
Notation "'0xfffffffffffd'" (* 281474976710653 (0xfffffffffffd) *)
  := (Const 281474976710653%Z).
Notation "'0xfffffffffffd'" (* 281474976710653 (0xfffffffffffd) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1).
Notation "'0xffffffffffff'" (* 281474976710655 (0xffffffffffff) *)
  := (Const 281474976710655%Z).
Notation "'0xffffffffffff'" (* 281474976710655 (0xffffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x1ffffffffffed'" (* 562949953421293 (0x1ffffffffffed) *)
  := (Const 562949953421293%Z).
Notation "'0x1ffffffffffed'" (* 562949953421293 (0x1ffffffffffed) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1).
Notation "'0x1ffffffffffff'" (* 562949953421311 (0x1ffffffffffff) *)
  := (Const 562949953421311%Z).
Notation "'0x1ffffffffffff'" (* 562949953421311 (0x1ffffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x3fffffdffffff'" (* 1125899873288191 (0x3fffffdffffff) *)
  := (Const 1125899873288191%Z).
Notation "'0x3fffffdffffff'" (* 1125899873288191 (0x3fffffdffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x3ffffffffffe1'" (* 1125899906842593 (0x3ffffffffffe1) *)
  := (Const 1125899906842593%Z).
Notation "'0x3ffffffffffe1'" (* 1125899906842593 (0x3ffffffffffe1) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~1).
Notation "'0x3ffffffffffef'" (* 1125899906842607 (0x3ffffffffffef) *)
  := (Const 1125899906842607%Z).
Notation "'0x3ffffffffffef'" (* 1125899906842607 (0x3ffffffffffef) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1).
Notation "'0x3ffffffffffff'" (* 1125899906842623 (0x3ffffffffffff) *)
  := (Const 1125899906842623%Z).
Notation "'0x3ffffffffffff'" (* 1125899906842623 (0x3ffffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x7fffffff80000'" (* 2251799813160960 (0x7fffffff80000) *)
  := (Const 2251799813160960%Z).
Notation "'0x7fffffff80000'" (* 2251799813160960 (0x7fffffff80000) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).
Notation "'0x7ffffffffffda'" (* 2251799813685210 (0x7ffffffffffda) *)
  := (Const 2251799813685210%Z).
Notation "'0x7ffffffffffda'" (* 2251799813685210 (0x7ffffffffffda) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0).
Notation "'0x7ffffffffffe1'" (* 2251799813685217 (0x7ffffffffffe1) *)
  := (Const 2251799813685217%Z).
Notation "'0x7ffffffffffe1'" (* 2251799813685217 (0x7ffffffffffe1) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~1).
Notation "'0x7ffffffffffed'" (* 2251799813685229 (0x7ffffffffffed) *)
  := (Const 2251799813685229%Z).
Notation "'0x7ffffffffffed'" (* 2251799813685229 (0x7ffffffffffed) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1).
Notation "'0x7ffffffffffff'" (* 2251799813685247 (0x7ffffffffffff) *)
  := (Const 2251799813685247%Z).
Notation "'0x7ffffffffffff'" (* 2251799813685247 (0x7ffffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0xfffffffffffda'" (* 4503599627370458 (0xfffffffffffda) *)
  := (Const 4503599627370458%Z).
Notation "'0xfffffffffffda'" (* 4503599627370458 (0xfffffffffffda) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0).
Notation "'0xfffffffffffef'" (* 4503599627370479 (0xfffffffffffef) *)
  := (Const 4503599627370479%Z).
Notation "'0xfffffffffffef'" (* 4503599627370479 (0xfffffffffffef) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1).
Notation "'0xffffffffffffe'" (* 4503599627370494 (0xffffffffffffe) *)
  := (Const 4503599627370494%Z).
Notation "'0xffffffffffffe'" (* 4503599627370494 (0xffffffffffffe) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0xfffffffffffff'" (* 4503599627370495 (0xfffffffffffff) *)
  := (Const 4503599627370495%Z).
Notation "'0xfffffffffffff'" (* 4503599627370495 (0xfffffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x1ffffffbffffff'" (* 9007199187632127 (0x1ffffffbffffff) *)
  := (Const 9007199187632127%Z).
Notation "'0x1ffffffbffffff'" (* 9007199187632127 (0x1ffffffbffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x1fffffffffffff'" (* 9007199254740991 (0x1fffffffffffff) *)
  := (Const 9007199254740991%Z).
Notation "'0x1fffffffffffff'" (* 9007199254740991 (0x1fffffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x3fffffffffffff'" (* 18014398509481983 (0x3fffffffffffff) *)
  := (Const 18014398509481983%Z).
Notation "'0x3fffffffffffff'" (* 18014398509481983 (0x3fffffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0xfffffffffffffe'" (* 72057594037927934 (0xfffffffffffffe) *)
  := (Const 72057594037927934%Z).
Notation "'0xfffffffffffffe'" (* 72057594037927934 (0xfffffffffffffe) *)
  := (Const WO~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0xffffffffffffff'" (* 72057594037927935 (0xffffffffffffff) *)
  := (Const 72057594037927935%Z).
Notation "'0xffffffffffffff'" (* 72057594037927935 (0xffffffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x100000000000000'" (* 72057594037927936 (0x100000000000000) *)
  := (Const 72057594037927936%Z).
Notation "'0x100000000000000'" (* 72057594037927936 (0x100000000000000) *)
  := (Const WO~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).
Notation "'0xffffffff00000001L'" (* 18446744069414584321 (0xffffffff00000001L) *)
  := (Const 18446744069414584321%Z).
Notation "'0xffffffff00000001L'" (* 18446744069414584321 (0xffffffff00000001L) *)
  := (Const WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1).
Notation "'0xfffffffffffffffeL'" (* 18446744073709551614 (0xfffffffffffffffeL) *)
  := (Const 18446744073709551614%Z).
Notation "'0xfffffffffffffffeL'" (* 18446744073709551614 (0xfffffffffffffffeL) *)
  := (Const WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0xffffffffffffffffL'" (* 18446744073709551615 (0xffffffffffffffffL) *)
  := (Const 18446744073709551615%Z).
Notation "'0xffffffffffffffffL'" (* 18446744073709551615 (0xffffffffffffffffL) *)
  := (Const WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x10000000000000000L'" (* 18446744073709551616 (0x10000000000000000L) *)
  := (Const 18446744073709551616%Z).
Notation "'0x10000000000000000L'" (* 18446744073709551616 (0x10000000000000000L) *)
  := (Const WO~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).
Notation "'0x1fffffffffffffffffffffL'" (* 38685626227668133590597631 (0x1fffffffffffffffffffffL) *)
  := (Const 38685626227668133590597631%Z).
Notation "'0x1fffffffffffffffffffffL'" (* 38685626227668133590597631 (0x1fffffffffffffffffffffL) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x3ffffffffffffffffffff6L'" (* 77371252455336267181195254 (0x3ffffffffffffffffffff6L) *)
  := (Const 77371252455336267181195254%Z).
Notation "'0x3ffffffffffffffffffff6L'" (* 77371252455336267181195254 (0x3ffffffffffffffffffff6L) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0).
Notation "'0x3ffffffffffffffffffffeL'" (* 77371252455336267181195262 (0x3ffffffffffffffffffffeL) *)
  := (Const 77371252455336267181195262%Z).
Notation "'0x3ffffffffffffffffffffeL'" (* 77371252455336267181195262 (0x3ffffffffffffffffffffeL) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0xffffffffffffffffffffffffL'" (* 79228162514264337593543950335 (0xffffffffffffffffffffffffL) *)
  := (Const 79228162514264337593543950335%Z).
Notation "'0xffffffffffffffffffffffffL'" (* 79228162514264337593543950335 (0xffffffffffffffffffffffffL) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x1000000000000000000000001L'" (* 79228162514264337593543950337 (0x1000000000000000000000001L) *)
  := (Const 79228162514264337593543950337%Z).
Notation "'0x1000000000000000000000001L'" (* 79228162514264337593543950337 (0x1000000000000000000000001L) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1).
Notation "'0xffffffff000000010000000000000000L'" (* 340282366841710300967557013911933812736 (0xffffffff000000010000000000000000L) *)
  := (Const 340282366841710300967557013911933812736%Z).
Notation "'0xffffffff000000010000000000000000L'" (* 340282366841710300967557013911933812736 (0xffffffff000000010000000000000000L) *)
  := (Const WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).
Notation "'0xffffffffffffffffffffffffffffffffL'" (* 340282366920938463463374607431768211455 (0xffffffffffffffffffffffffffffffffL) *)
  := (Const 340282366920938463463374607431768211455%Z).
Notation "'0xffffffffffffffffffffffffffffffffL'" (* 340282366920938463463374607431768211455 (0xffffffffffffffffffffffffffffffffL) *)
  := (Const WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x100000000000000000000000000000000L'" (* 340282366920938463463374607431768211456 (0x100000000000000000000000000000000L) *)
  := (Const 340282366920938463463374607431768211456%Z).
Notation "'0x100000000000000000000000000000000L'" (* 340282366920938463463374607431768211456 (0x100000000000000000000000000000000L) *)
  := (Const WO~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).
Notation "'0x100000000000000000000000000000000000000000000000000000000L'" (* 26959946667150639794667015087019630673637144422540572481103610249216 (0x100000000000000000000000000000000000000000000000000000000L) *)
  := (Const 26959946667150639794667015087019630673637144422540572481103610249216%Z).
Notation "'0x100000000000000000000000000000000000000000000000000000000L'" (* 26959946667150639794667015087019630673637144422540572481103610249216 (0x100000000000000000000000000000000000000000000000000000000L) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).