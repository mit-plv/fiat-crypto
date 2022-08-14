(** * Push-Button Synthesis of Solinas Reduction: Reification Cache *)
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.SolinasReduction.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Local Open Scope Z_scope.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Import
  Language.API.Compilers
  Language.Wf.Compilers.

Module Export SolinasReductionCache.

  Import SolinasReduction.SolinasReduction.

  Strategy -500 [Crypto.Arithmetic.SolinasReduction.SolinasReduction.is_bounded_by
                   Crypto.Arithmetic.Saturated.Columns.cons_to_nth
                   Coq.ZArith.BinInt.Z.to_hex_int
                   Crypto.Arithmetic.Saturated.Rows.extract_row
                   Crypto.Arithmetic.Saturated.Associational.sat_multerm
                   Crypto.Arithmetic.Saturated.Rows.flatten'
                   Coq.Init.Nat.to_hex_uint
                   Coq.ZArith.BinInt.Z.to_int
                   Coq.Init.Nat.to_little_hex_uint
                   Crypto.Arithmetic.Saturated.Rows.from_columns
                   Crypto.Arithmetic.Saturated.Rows.adjust_s
                   Crypto.Arithmetic.SolinasReduction.SolinasReduction.fold_andb_map'
                   Coq.Init.Nat.to_uint
                   Crypto.Arithmetic.Core.Associational.split
                   Coq.Init.Decimal.rev
                   Coq.Init.Hexadecimal.revapp
                   Crypto.Arithmetic.Saturated.Columns.from_associational
                   Crypto.Arithmetic.SolinasReduction.SolinasReduction.sat_reduce
                   Coq.Init.Datatypes.andb
                   Coq.PArith.BinPos.Pos.to_little_hex_uint
                   Coq.PArith.BinPos.Pos.to_little_uint
                   Crypto.Arithmetic.SolinasReduction.SolinasReduction.mulmod
                   Coq.Init.Decimal.Little.double
                   Coq.Lists.List.tl
                   Crypto.Arithmetic.Core.Positional.place
                   Crypto.Arithmetic.Saturated.Rows.sum_rows'
                   Crypto.Arithmetic.Core.Positional.add_to_nth
                   Coq.Init.Decimal.Little.succ
                   Crypto.Arithmetic.Core.Positional.to_associational
                   Coq.Init.Nat.to_num_uint
                   Coq.Init.Hexadecimal.Little.succ
                   Coq.Init.Nat.to_num_hex_uint
                   Crypto.Arithmetic.SolinasReduction.SolinasReduction.dual_map
                   Crypto.Arithmetic.Saturated.Rows.from_columns'
                   Coq.Init.Hexadecimal.Little.double
                   Crypto.Arithmetic.UniformWeight.uweight
                   Crypto.Arithmetic.Saturated.Associational.sat_mul
                   Coq.Init.Datatypes.nat_rect
                   Coq.Init.Nat.to_little_uint
                   Crypto.Arithmetic.Saturated.Associational.sat_multerm_const
                   Crypto.Arithmetic.Saturated.Columns.nils
                   Crypto.Arithmetic.Saturated.Rows.max_column_size
                   Crypto.Arithmetic.Saturated.Rows.sum_rows
                   Crypto.Arithmetic.ModOps.weight
                   Coq.Init.Decimal.revapp
                   Crypto.Arithmetic.Saturated.Associational.sat_mul_const
                   Coq.Lists.List.hd
                   Coq.ZArith.BinInt.Z.to_num_int
                   Crypto.Arithmetic.Saturated.Rows.from_associational
                   Coq.PArith.BinPos.Pos.to_uint
                   Rewriter.Util.LetIn.Let_In
                   Crypto.Arithmetic.Core.Positional.zeros
                   Coq.PArith.BinPos.Pos.to_hex_uint
                   Coq.ZArith.BinInt.Z.to_num_hex_int
                   Coq.Init.Hexadecimal.rev
                   Crypto.Arithmetic.Saturated.Rows.flatten].

  Derive reified_solmul_gen
         SuchThat (is_reification_of reified_solmul_gen mulmod)
         As reified_solmul_gen_correct.
  Proof. Time cache_reify (). Time Qed.

#[global]
  Hint Extern 1 (_ = _) => apply_cached_reification mulmod (proj1 reified_solmul_gen) : reify_cache_gen.
#[global]
  Hint Immediate (proj2 reified_solmul_gen_correct) : wf_gen_cache.
#[global]
  Hint Rewrite (proj1 reified_solmul_gen_correct) : interp_gen_cache.
  Local Opaque reified_solmul_gen. (* needed for making [autorewrite] not take a very long time *)
End SolinasReductionCache.
