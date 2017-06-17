Require Export Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Export Bedrock.Word.
Require Export Crypto.Util.Notations.

Local Notation Const x := (Op (OpConst x) TT).
(* python:
<<
#!/usr/bin/env python
print(r"""Require Export Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Export Bedrock.Word.
Require Export Crypto.Util.Notations.

Local Notation Const x := (Op (OpConst x) TT).
(""" + r"""* python:
<<""")
print(open(__file__).read())
print(r""">>
 *""" + r""")""")
print('\n'.join('''Notation "'%s'" (* %d (%s) *)\n  := (Const %s).''' % (b, d, h, i)
 for d, h, b, i in sorted([(eval(bv), hex(eval(bv)), bv, i)
 for (bv, i) in (('0b' + i[2:].replace('~', ''), i)
 for i in r"""WO~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0
WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1
WO~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0
WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1
WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0
WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~0~1~1~0~1~1~0~1~0~0~0~0~0~1
WO~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0
WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~0
WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
WO~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~0
WO~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~1~0~0~0~1
WO~0~0~0~1~0~0~1~1
WO~0~0~0~1~0~1~1~1
WO~0~0~0~1~1~0~0~1
WO~0~0~0~1~1~0~1~0
WO~0~0~0~1~1~0~1~1
WO~0~0~0~1~1~1~0~0
WO~0~0~1~1~0~0~1~1
WO~0~1~0~1~0~1~0~1
WO~1~1~1~0~0~0
WO~0~1~0~1
WO~1~0~0~1
WO~1~0
WO~1~1
WO~0
WO~1""".split('\n'))])))

>>
 *)
Notation "'0b0'" (* 0 (0x0) *)
  := (Const WO~0).
Notation "'0b1'" (* 1 (0x1) *)
  := (Const WO~1).
Notation "'0b10'" (* 2 (0x2) *)
  := (Const WO~1~0).
Notation "'0b11'" (* 3 (0x3) *)
  := (Const WO~1~1).
Notation "'0b0101'" (* 5 (0x5) *)
  := (Const WO~0~1~0~1).
Notation "'0b1001'" (* 9 (0x9) *)
  := (Const WO~1~0~0~1).
Notation "'0b00010001'" (* 17 (0x11) *)
  := (Const WO~0~0~0~1~0~0~0~1).
Notation "'0b00010011'" (* 19 (0x13) *)
  := (Const WO~0~0~0~1~0~0~1~1).
Notation "'0b00010111'" (* 23 (0x17) *)
  := (Const WO~0~0~0~1~0~1~1~1).
Notation "'0b00011001'" (* 25 (0x19) *)
  := (Const WO~0~0~0~1~1~0~0~1).
Notation "'0b00011010'" (* 26 (0x1a) *)
  := (Const WO~0~0~0~1~1~0~1~0).
Notation "'0b00011011'" (* 27 (0x1b) *)
  := (Const WO~0~0~0~1~1~0~1~1).
Notation "'0b00011100'" (* 28 (0x1c) *)
  := (Const WO~0~0~0~1~1~1~0~0).
Notation "'0b00110011'" (* 51 (0x33) *)
  := (Const WO~0~0~1~1~0~0~1~1).
Notation "'0b111000'" (* 56 (0x38) *)
  := (Const WO~1~1~1~0~0~0).
Notation "'0b01010101'" (* 85 (0x55) *)
  := (Const WO~0~1~0~1~0~1~0~1).
Notation "'0b00000000000000011101101101000001'" (* 121665 (0x1db41) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~0~1~1~0~1~1~0~1~0~0~0~0~0~1).
Notation "'0b00000000011111111111111111111111'" (* 8388607 (0x7fffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b00000001111111111111111111111111'" (* 33554431 (0x1ffffff) *)
  := (Const WO~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b00000011111111111111111111111110'" (* 67108862 (0x3fffffe) *)
  := (Const WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0b00000011111111111111111111111111'" (* 67108863 (0x3ffffff) *)
  := (Const WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b00000111111111111111111111011010'" (* 134217690 (0x7ffffda) *)
  := (Const WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0).
Notation "'0b00000111111111111111111111101110'" (* 134217710 (0x7ffffee) *)
  := (Const WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~0).
Notation "'0b00000111111111111111111111111110'" (* 134217726 (0x7fffffe) *)
  := (Const WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0b00000111111111111111111111111111'" (* 134217727 (0x7ffffff) *)
  := (Const WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b00001111111111111111111111111110'" (* 268435454 (0xffffffe) *)
  := (Const WO~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0b00001111111111111111111111111111'" (* 268435455 (0xfffffff) *)
  := (Const WO~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b00011111111111111111111111111010'" (* 536870906 (0x1ffffffa) *)
  := (Const WO~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~0).
Notation "'0b00011111111111111111111111111110'" (* 536870910 (0x1ffffffe) *)
  := (Const WO~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0b11111111111111111111111111111111'" (* 4294967295 (0xffffffff) *)
  := (Const WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b0000000000000111111111111111111111111111111111111111111111011010'" (* 2251799813685210 (0x7ffffffffffda) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0).
Notation "'0b0000000000000111111111111111111111111111111111111111111111101101'" (* 2251799813685229 (0x7ffffffffffed) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1).
Notation "'0b0000000000000111111111111111111111111111111111111111111111111111'" (* 2251799813685247 (0x7ffffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b0000000000001111111111111111111111111111111111111111111111011010'" (* 4503599627370458 (0xfffffffffffda) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0).
Notation "'0b0000000000001111111111111111111111111111111111111111111111111110'" (* 4503599627370494 (0xffffffffffffe) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0b0000000000001111111111111111111111111111111111111111111111111111'" (* 4503599627370495 (0xfffffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b0000000011111111111111111111111111111111111111111111111111111111'" (* 72057594037927935 (0xffffffffffffff) *)
  := (Const WO~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b1111111111111111111111111111111100000000000000000000000000000001'" (* 18446744069414584321 (0xffffffff00000001L) *)
  := (Const WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1).
Notation "'0b1111111111111111111111111111111111111111111111111111111111111111'" (* 18446744073709551615 (0xffffffffffffffffL) *)
  := (Const WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000'" (* 18446744073709551616 (0x10000000000000000L) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).
Notation "'0b00000000000000000000000000000000000000000001111111111111111111111111111111111111111111111111111111111111111111111111111111111111'" (* 38685626227668133590597631 (0x1fffffffffffffffffffffL) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b00000000000000000000000000000000000000000011111111111111111111111111111111111111111111111111111111111111111111111111111111110110'" (* 77371252455336267181195254 (0x3ffffffffffffffffffff6L) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0).
Notation "'0b00000000000000000000000000000000000000000011111111111111111111111111111111111111111111111111111111111111111111111111111111111110'" (* 77371252455336267181195262 (0x3ffffffffffffffffffffeL) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0b100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'" (* 26959946667150639794667015087019630673637144422540572481103610249216 (0x100000000000000000000000000000000000000000000000000000000L) *)
  := (Const WO~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).
