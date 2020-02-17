Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Translation.Func.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import bedrock2.Syntax.
Require Import bedrock2.BasicC64Semantics.
Require bedrock2.NotationsCustomEntry.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Import Language.Compilers.
Import Associational Positional.
Import Types.Notations.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

(* Curve25519 64-bit *)
Module X25519_64.
  Section __.
    Context (n : nat := 5%nat)
            (s : Z := 2^255)
            (c : list (Z * Z) := [(1,19)])
            (machine_wordsize : Z := 64).

    Local Existing Instance default_low_level_rewriter_method.
    Local Instance only_signed : only_signed_opt := false.
    Local Instance should_split_mul : should_split_mul_opt := true.
    Local Instance should_split_multiret : should_split_multiret_opt := true.
    Local Instance widen_carry : widen_carry_opt := true.
    Local Instance widen_bytes : widen_bytes_opt := true.

    Let limbwidth := (Z.log2_up (s - Associational.eval c) / Z.of_nat n)%Q.
    Let idxs := (List.seq 0 n ++ [0; 1])%list%nat.

    Definition possible_values_of_machine_wordsize
      := prefix_with_carry [machine_wordsize; 2 * machine_wordsize]%Z.

    Let possible_values := possible_values_of_machine_wordsize.

    Local Instance split_mul_to : split_mul_to_opt :=
      split_mul_to_of_should_split_mul machine_wordsize possible_values.
    Local Instance split_multiret_to : split_multiret_to_opt :=
      split_multiret_to_of_should_split_multiret machine_wordsize possible_values.

    Let prime_upperbound_list : list Z
      := encode_no_reduce (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
    Let tight_upperbounds : list Z
      := List.map
           (fun v : Z => Qceiling (11/10 * v))
           prime_upperbound_list.
    Definition tight_bounds : list (ZRange.type.option.interp (type.base (base.type.type_base base.type.Z)))
      := List.map (fun u => Some r[0~>u]%zrange) tight_upperbounds.
    Definition loose_bounds : list (ZRange.type.option.interp (type.base (base.type.type_base base.type.Z)))
      := List.map (fun u => Some r[0 ~> 3*u]%zrange) tight_upperbounds.

    Let limbwidth_num := Eval vm_compute in Qnum limbwidth.
    Let limbwidth_den := Eval vm_compute in QDen limbwidth.

    Set Printing Depth 100000.
    Local Open Scope string_scope.
    Local Notation "'uint64,uint64'" := (ident.Literal
                                           (r[0 ~> 18446744073709551615]%zrange,
                                            r[0 ~> 18446744073709551615]%zrange)%core) : expr_scope.
    Local Notation "'uint64'" :=
      (ident.Literal (t:=Compilers.zrange) r[0 ~> 18446744073709551615]%zrange) : expr_scope.
    Local Open Scope expr_scope.
    Local Open Scope core_scope.

    Definition mulmod_ : Pipeline.ErrorT (Expr _) :=
      Pipeline.BoundsPipeline
        false (* subst01 *)
        None (* fancy *)
        possible_values
        ltac:(let r := Reify ((carry_mulmod limbwidth_num limbwidth_den s c n idxs)) in
              exact r)
               (Some loose_bounds, (Some loose_bounds, tt))
               (Some tight_bounds).
    Definition mulmod := Eval vm_compute in mulmod_.

    Local Existing Instances Types.rep.Z Types.rep.listZ_mem.
    Let wordsize_bytes := Eval vm_compute in (machine_wordsize / 8)%Z.

    Local Instance p : Types.parameters :=
      {| semantics := BasicC64Semantics.parameters;
         varname_gen := fun i => String.append "x" (Decimal.decimal_string_of_Z (Z.of_nat i));
         error := expr.var "ERROR";
         word_size_in_bytes := wordsize_bytes;
      |}.

    Definition mulmod_bedrock : cmd :=
      match mulmod with
      | ErrorT.Success e =>
        snd (translate_func (e Types.ltype)
                            ("y0", ("y1", tt)) (* argument names *)
                            (n, (n, tt)) (* lengths for list arguments *)
                            "ret") (* return value name *)
      | ErrorT.Error _ => Syntax.cmd.skip
      end.

    Import NotationsCustomEntry.
    Local Set Printing Width 150.
    Redirect "Crypto.Bedrock.Test_X25519_64.mulmod_bedrock" Compute mulmod_bedrock.
  End __.
End X25519_64.
