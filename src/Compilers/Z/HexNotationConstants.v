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
    121665,
    8388607,
    33554431,
    67108862,
    67108863,
    134217690,
    134217710,
    134217726,
    134217727,
    268435454,
    268435455,
    536870906,
    536870910,
    4294967295,
    2251799813685210,
    2251799813685229,
    2251799813685247,
    4503599627370458,
    4503599627370494,
    4503599627370495,
    72057594037927935,
    72057594037927936,
    18446744069414584321,
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
    26959946667150639794667015087019630673637144422540572481103610249216
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
Notation "'0x1db41'" (* 121665 (0x1db41) *)
  := (Const 121665%Z).
Notation "'0x1db41'" (* 121665 (0x1db41) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~0~1~1~0~1~1~0~1~0~0~0~0~0~1).
Notation "'0x7fffff'" (* 8388607 (0x7fffff) *)
  := (Const 8388607%Z).
Notation "'0x7fffff'" (* 8388607 (0x7fffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x1ffffff'" (* 33554431 (0x1ffffff) *)
  := (Const 33554431%Z).
Notation "'0x1ffffff'" (* 33554431 (0x1ffffff) *)
  := (Const WO~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
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
Notation "'0xffffffe'" (* 268435454 (0xffffffe) *)
  := (Const 268435454%Z).
Notation "'0xffffffe'" (* 268435454 (0xffffffe) *)
  := (Const WO~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0xfffffff'" (* 268435455 (0xfffffff) *)
  := (Const 268435455%Z).
Notation "'0xfffffff'" (* 268435455 (0xfffffff) *)
  := (Const WO~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x1ffffffa'" (* 536870906 (0x1ffffffa) *)
  := (Const 536870906%Z).
Notation "'0x1ffffffa'" (* 536870906 (0x1ffffffa) *)
  := (Const WO~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~0).
Notation "'0x1ffffffe'" (* 536870910 (0x1ffffffe) *)
  := (Const 536870910%Z).
Notation "'0x1ffffffe'" (* 536870910 (0x1ffffffe) *)
  := (Const WO~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0xffffffff'" (* 4294967295 (0xffffffff) *)
  := (Const 4294967295%Z).
Notation "'0xffffffff'" (* 4294967295 (0xffffffff) *)
  := (Const WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0x7ffffffffffda'" (* 2251799813685210 (0x7ffffffffffda) *)
  := (Const 2251799813685210%Z).
Notation "'0x7ffffffffffda'" (* 2251799813685210 (0x7ffffffffffda) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0).
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
Notation "'0xffffffffffffe'" (* 4503599627370494 (0xffffffffffffe) *)
  := (Const 4503599627370494%Z).
Notation "'0xffffffffffffe'" (* 4503599627370494 (0xffffffffffffe) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0xfffffffffffff'" (* 4503599627370495 (0xfffffffffffff) *)
  := (Const 4503599627370495%Z).
Notation "'0xfffffffffffff'" (* 4503599627370495 (0xfffffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
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