(** * Extraction Directives for [nat] in Haskell *)
(** [nat] is really complicated, so we jump through many hoops to get
    code that compiles in 8.4 and 8.5 at the same time. *)
Require Coq.Numbers.Natural.Peano.NPeano.
Require Coq.Arith.Compare_dec Coq.Arith.EqNat Coq.Arith.Peano_dec.

Extract Inductive nat => "Prelude.Integer" [ "0" "Prelude.succ" ]
  "(\fO fS n -> {- match_on_nat -} if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".


(** We rely on the fact that Coq forbids masking absolute names.  Hopefully we can drop support for 8.4 before this is changed. *)
Module Coq.
  Module M. Export NPeano.Nat. End M.
  Module Init.
    Module Nat.
      Export M.
    End Nat.
  End Init.
  Module Numbers.
    Module Natural.
      Module Peano.
        Module NPeano.
          Module Nat.
            Export M.
          End Nat.
        End NPeano.
      End Peano.
    End Natural.
  End Numbers.
  Module Arith.
    Module PeanoNat.
      Module Nat.
        Export M.
      End Nat.
    End PeanoNat.
  End Arith.
End Coq.

Module Export Import_NPeano_Nat.
  Import Coq.Numbers.Natural.Peano.NPeano.Nat.

  Extract Inlined Constant add => "(Prelude.+)".
  Extract Inlined Constant mul => "(Prelude.*)".
  Extract Inlined Constant pow => "(Prelude.^)".
  Extract Inlined Constant max => "Prelude.max".
  Extract Inlined Constant min => "Prelude.min".
  Extract Inlined Constant gcd => "Prelude.gcd".
  Extract Inlined Constant lcm => "Prelude.lcm".
  Extract Inlined Constant land => "(Data.Bits..&.)".
  Extract Inlined Constant compare => "Prelude.compare".
  Extract Inlined Constant ltb => "(Prelude.<)".
  Extract Inlined Constant leb => "(Prelude.<=)".
  Extract Inlined Constant eqb => "(Prelude.==)".
  Extract Inlined Constant odd => "Prelude.odd".
  Extract Inlined Constant even => "Prelude.even".
  Extract Constant pred => "(\n -> Prelude.max 0 (Prelude.pred n))".
  Extract Constant sub => "(\n m -> Prelude.max 0 (n Prelude.- m))".
  Extract Constant div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
  Extract Constant modulo => "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".
End Import_NPeano_Nat.


Module Export Import_Init_Nat.
  Import Coq.Init.Nat.

  Extract Inlined Constant add => "(Prelude.+)".
  Extract Inlined Constant mul => "(Prelude.*)".
  Extract Inlined Constant max => "Prelude.max".
  Extract Inlined Constant min => "Prelude.min".
  Extract Constant pred => "(\n -> Prelude.max 0 (Prelude.pred n))".
  Extract Constant sub => "(\n m -> Prelude.max 0 (n Prelude.- m))".

  Extract Constant div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
  Extract Constant modulo => "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".
End Import_Init_Nat.


Module Export Import_PeanoNat_Nat.
  Import Coq.Arith.PeanoNat.Nat.

  Extract Inlined Constant add => "(Prelude.+)".
  Extract Inlined Constant mul => "(Prelude.*)".
  Extract Inlined Constant max => "Prelude.max".
  Extract Inlined Constant min => "Prelude.min".
  Extract Inlined Constant compare => "Prelude.compare".
End Import_PeanoNat_Nat.

Extract Inlined Constant Compare_dec.nat_compare_alt => "Prelude.compare".
Extract Inlined Constant Compare_dec.lt_dec => "(Prelude.<)".
Extract Inlined Constant Compare_dec.leb => "(Prelude.<=)".
Extract Inlined Constant Compare_dec.le_lt_dec => "(Prelude.<=)".
Extract Inlined Constant EqNat.beq_nat => "(Prelude.==)".
Extract Inlined Constant EqNat.eq_nat_decide => "(Prelude.==)".
Extract Inlined Constant Peano_dec.eq_nat_dec => "(Prelude.==)".
