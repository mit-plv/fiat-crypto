(** * Push-Button Synthesis of Solinas Reduction: Reification Cache *)
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.BinInt.
Require Import Coq.derive.Derive.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.SolinasReduction.
Require Import Crypto.PushButtonSynthesis.ReificationCache.

Require Import Crypto.Language.IdentifierParameters.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Language.PreExtra.

Local Open Scope Z_scope.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Import
  Language.API.Compilers
  Language.Wf.Compilers.
Import SolinasReduction.SolinasReduction.

(* Set Debug Cbv. *)
(* Eval cbv delta -[ident.literal *)
(*                    (* ident.comment *) *)
(*                    (* ident.comment_no_keep *) *)
(*                    Z.value_barrier *)
(*                    Nat.succ *)
(*                    Nat.pred *)
(*                    Nat.max *)
(*                    Nat.mul *)
(*                    Nat.add *)
(*                    Nat.sub *)
(*                    Nat.eqb *)
(*                    (* Datatypes.nil *) *)
(*                    (* Datatypes.cons *) *)
(*                    (* Datatypes.tt *) *)
(*                    (* Datatypes.pair *) *)
(*                    Datatypes.fst *)
(*                    Datatypes.snd *)
(*                    prod_rect_nodep *)
(*                    Thunked.bool_rect *)
(*                    bool_rect_nodep *)
(*                    Thunked.nat_rect *)
(*                    Thunked.nat_rect *)
(*                    nat_rect_arrow_nodep *)
(*                    nat_rect_arrow_nodep *)
(*                    Thunked.list_rect *)
(*                    Thunked.list_rect *)
(*                    list_rect_arrow_nodep *)
(*                    list_rect_arrow_nodep *)
(*                    Thunked.list_case *)
(*                    List.length *)
(*                    List.seq *)
(*                    List.firstn *)
(*                    List.skipn *)
(*                    repeat *)
(*                    List.combine *)
(*                    List.map *)
(*                    List.app *)
(*                    List.rev *)
(*                    List.flat_map *)
(*                    List.partition *)
(*                    List.fold_right *)
(*                    update_nth *)
(*                    nth_default *)
(*                    nth_default *)
(*                    Z.add *)
(*                    Z.mul *)
(*                    Z.pow *)
(*                    Z.sub *)
(*                    Z.opp *)
(*                    Z.div *)
(*                    Z.modulo *)
(*                    Z.eqb *)
(*                    Z.leb *)
(*                    Z.ltb *)
(*                    Z.geb *)
(*                    Z.gtb *)
(*                    Z.log2 *)
(*                    Z.log2_up *)
(*                    Z.of_nat *)
(*                    Z.to_nat *)
(*                    Z.shiftr *)
(*                    Z.shiftl *)
(*                    Z.land *)
(*                    Z.lor *)
(*                    Z.min *)
(*                    Z.max *)
(*                    Z.mul_split *)
(*                    Z.mul_high *)
(*                    Z.add_get_carry_full *)
(*                    Z.add_with_carry *)
(*                    Z.add_with_get_carry_full *)
(*                    Z.sub_get_borrow_full *)
(*                    Z.sub_with_get_borrow_full *)
(*                    Z.ltz *)
(*                    Z.zselect *)
(*                    Z.add_modulo *)
(*                    Z.truncating_shiftl *)
(*                    Z.bneg *)
(*                    Z.lnot_modulo *)
(*                    Z.lxor *)
(*                    Z.rshi *)
(*                    Z.cc_m *)
(*                    Z.combine_at_bitwidth *)
(*                    (* ident.cast *) *)
(*                    (* ident.cast2 *) *)
(*                    (* Datatypes.Some *) *)
(*                    (* Datatypes.None *) *)
(*                    Thunked.option_rect *)
(*                    (* ZRange.Build_zrange *) *)
(*                    ZRange.zrange_rect_nodep *)
(*                    ident.fancy.add *)
(*                    ident.fancy.addc *)
(*                    ident.fancy.sub *)
(*                    ident.fancy.subb *)
(*                    ident.fancy.mulll *)
(*                    ident.fancy.mullh *)
(*                    ident.fancy.mulhl *)
(*                    ident.fancy.mulhh *)
(*                    ident.fancy.rshi *)
(*                    ident.fancy.selc *)
(*                    ident.fancy.selm *)
(*                    ident.fancy.sell *)
(*                    ident.fancy.addm] in SolinasReduction.mulmod. *)

Strategy -500 [Crypto.Arithmetic.Core.Positional.add_to_nth
                 Coq.Init.Datatypes.andb
                 Coq.ZArith.BinInt.Z.to_int
                 Crypto.Arithmetic.SolinasReduction.SolinasReduction.dual_map
                 Coq.PArith.BinPos.Pos.to_uint
                 Coq.Init.Decimal.revapp
                 Coq.Init.Datatypes.nat_rect
                 Crypto.Arithmetic.Saturated.Rows.max_column_size
                 Crypto.Arithmetic.Saturated.Rows.sum_rows'
                 Crypto.Arithmetic.Core.Associational.split
                 Coq.PArith.BinPos.Pos.to_little_uint
                 Coq.Init.Nat.to_uint
                 Crypto.Arithmetic.SolinasReduction.SolinasReduction.mulmod
                 Crypto.Arithmetic.ModOps.weight
                 Crypto.Arithmetic.SolinasReduction.SolinasReduction.sat_reduce
                 Coq.Lists.List.tl
                 Crypto.Arithmetic.Saturated.Rows.adjust_s
                 Crypto.Arithmetic.Core.Positional.to_associational
                 Coq.Init.Nat.to_little_uint
                 Crypto.Arithmetic.Saturated.Columns.cons_to_nth
                 Crypto.Arithmetic.Saturated.Rows.extract_row
                 Crypto.Arithmetic.Saturated.Rows.from_columns
                 Crypto.Arithmetic.Saturated.Associational.sat_multerm_const
                 Coq.Init.Decimal.rev
                 Crypto.Arithmetic.Saturated.Associational.sat_mul
                 Crypto.Arithmetic.Saturated.Rows.from_columns'
                 Crypto.Arithmetic.Core.Positional.place
                 Crypto.Arithmetic.Core.Positional.zeros
                 Crypto.Arithmetic.Saturated.Rows.flatten'
                 Crypto.Arithmetic.Saturated.Rows.sum_rows
                 Crypto.Arithmetic.Saturated.Associational.sat_mul_const
                 Coq.Lists.List.hd
                 Crypto.Arithmetic.Saturated.Associational.sat_multerm
                 Crypto.Arithmetic.SolinasReduction.SolinasReduction.is_bounded_by
                 Crypto.Arithmetic.Saturated.Columns.nils
                 Coq.Init.Decimal.Little.succ
                 Crypto.Arithmetic.UniformWeight.uweight
                 Crypto.Arithmetic.Saturated.Rows.flatten
                 (* Rewriter.Util.LetIn.Let_In *)
                 Crypto.Arithmetic.Saturated.Rows.from_associational
                 Crypto.Arithmetic.SolinasReduction.SolinasReduction.fold_andb_map'
                 Crypto.Arithmetic.Saturated.Columns.from_associational
                 Coq.Init.Decimal.Little.double].

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
