From Coq Require Import ZArith String List.
From Crypto Require Import IR Stringification.Language Stringification.Zig.

Import ListNotations.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Import IR.Compilers.ToString.
Import Stringification.Language.Compilers.
Import Stringification.Language.Compilers.Options.
Import Stringification.Language.Compilers.ToString.
Import Stringification.Language.Compilers.ToString.int.Notations.
Import IR.Notations.
Import Zig.

Section CastTests.
  Local Instance naming : language_naming_conventions_opt := default_language_naming_conventions.

  Definition test_selection (out c : string) : IR.stmt :=
    IR.Call (IR.Z_zselect uint64 @@@
      (IR.Addr @@@ IR.Var IR.type.Z out,
       (IR.Var IR.type.Z c, IR.Var IR.type.Z "a", IR.Var IR.type.Z "b")))%Cexpr.

  Example adjacent_selections_share_mask :
    to_strings true "" [("c", Some _Bool); ("a", Some uint64); ("b", Some uint64)]
      [test_selection "x1" "c"; IR.DeclareVar IR.type.Z (Some uint64) "x2";
       test_selection "x2" "c"]
    = ["const x1_selection_mask = selection_mask_u64(c);";
       "x1 = a ^ ((a ^ b) & x1_selection_mask);";
       "var x2: u64 = undefined;";
       "x2 = a ^ ((a ^ b) & x1_selection_mask);"].
  Proof. reflexivity. Qed.

  Example writing_selector_invalidates_mask :
    to_strings true "" [("c", Some uint64); ("a", Some uint64); ("b", Some uint64)]
      [test_selection "c" "c"; test_selection "x2" "c"]
    = ["const c_selection_mask = selection_mask_u64(@truncate(c));";
       "c = a ^ ((a ^ b) & c_selection_mask);";
       "const x2_selection_mask = selection_mask_u64(@truncate(c));";
       "x2 = a ^ ((a ^ b) & x2_selection_mask);"].
  Proof. reflexivity. Qed.

  Example pointer_writes_invalidate_mask :
    List.nth 3
      (to_strings true "" [("c", Some _Bool); ("a", Some uint64); ("b", Some uint64)]
        [test_selection "x1" "c";
         IR.AssignZPtr "p" (Some uint64) (IR.Var IR.type.Z "a");
         test_selection "x2" "c"]) ""
    = "const x2_selection_mask = selection_mask_u64(c);".
  Proof. reflexivity. Qed.

  Example widened_api_carry_is_narrowed_at_call :
    boolean_argument_to_string (Some uint8) "c" = "@truncate(c)".
  Proof. reflexivity. Qed.

  Example bit_carry_needs_no_cast :
    boolean_argument_to_string (Some _Bool) "c" = "c".
  Proof. reflexivity. Qed.

  Example inferred_widening :
    cast_to_string (Some uint64) (Some uint32) uint64 "x" = "x".
  Proof. reflexivity. Qed.

  Example explicit_widening :
    cast_to_string None (Some uint32) uint64 "x" = "@as(u64, x)".
  Proof. reflexivity. Qed.

  Example inferred_truncation :
    cast_to_string (Some uint64) (Some uint128) uint64 "x" = "@truncate(x)".
  Proof. reflexivity. Qed.

  Example sign_extension_before_reinterpretation :
    cast_to_string (Some uint64) (Some (int.of_bitwidth true 1)) uint64 "x" = "@bitCast(@as(i64, x))".
  Proof. reflexivity. Qed.

  Example same_width_reinterpretation :
    cast_to_string (Some int64) (Some uint64) int64 "x" = "@bitCast(x)".
  Proof. reflexivity. Qed.

  Example boolean_negation :
    arith_to_string true "" [("x", Some uint64)] (Some _Bool)
      (IR.Z_bneg @@@ IR.Var IR.type.Z "x")%Cexpr = "@intFromBool(x == 0)".
  Proof. reflexivity. Qed.

  Example full_mask_is_redundant :
    arith_to_string true "" [("x", Some uint128)] (Some uint64)
      (IR.Z_static_cast uint64 @@@
        (IR.Z_land @@@ (IR.Var IR.type.Z "x",
          IR.Z_static_cast uint128 @@@ (IR.literal (2^64-1) @@@ IR.TT))))%Cexpr
    = "@truncate(x)".
  Proof. vm_compute. reflexivity. Qed.

  Example partial_mask_is_preserved :
    arith_to_string true "" [("x", Some uint128)] (Some uint64)
      (IR.Z_static_cast uint64 @@@
        (IR.Z_land @@@ (IR.Var IR.type.Z "x",
          IR.Z_static_cast uint128 @@@ (IR.literal 255 @@@ IR.TT))))%Cexpr
    = "@truncate((x & 0xff))".
  Proof. vm_compute. reflexivity. Qed.

  Example peer_infers_left_widening :
    arith_to_string true "" [("x", Some uint32); ("y", Some uint64)] (Some uint64)
      (IR.Z_add @@@ (IR.Z_static_cast uint64 @@@ IR.Var IR.type.Z "x",
                     IR.Var IR.type.Z "y"))%Cexpr = "(x + y)".
  Proof. vm_compute. reflexivity. Qed.

  Example peer_infers_right_widening :
    arith_to_string true "" [("x", Some uint64); ("y", Some uint32)] (Some uint64)
      (IR.Z_sub @@@ (IR.Var IR.type.Z "x",
                     IR.Z_static_cast uint64 @@@ IR.Var IR.type.Z "y"))%Cexpr = "(x - y)".
  Proof. vm_compute. reflexivity. Qed.

  Example wide_product_keeps_one_widening :
    arith_to_string true "" [("x", Some uint64); ("y", Some uint64)] (Some uint128)
      (IR.Z_mul @@@ (IR.Z_static_cast uint128 @@@ IR.Var IR.type.Z "x",
                     IR.Z_static_cast uint128 @@@ IR.Var IR.type.Z "y"))%Cexpr
    = "(@as(u128, x) * y)".
  Proof. vm_compute. reflexivity. Qed.

  Example peer_infers_literal_type :
    arith_to_string true "" [("x", Some uint64)] (Some uint64)
      (IR.Z_lxor @@@ (IR.Var IR.type.Z "x",
                      IR.Z_static_cast uint64 @@@ (IR.literal 255 @@@ IR.TT)))%Cexpr
    = "(x ^ 0xff)".
  Proof. vm_compute. reflexivity. Qed.

  Example peer_does_not_infer_truncation :
    arith_to_string true "" [("x", Some uint128); ("y", Some uint64)] (Some uint64)
      (IR.Z_add @@@ (IR.Z_static_cast uint64 @@@ IR.Var IR.type.Z "x",
                     IR.Var IR.type.Z "y"))%Cexpr
    = "(@as(u64, @truncate(x)) + y)".
  Proof. vm_compute. reflexivity. Qed.

  Example peer_does_not_infer_reinterpretation :
    arith_to_string true "" [("x", Some int64); ("y", Some uint64)] (Some uint64)
      (IR.Z_add @@@ (IR.Z_static_cast uint64 @@@ IR.Var IR.type.Z "x",
                     IR.Var IR.type.Z "y"))%Cexpr
    = "(@as(u64, @bitCast(x)) + y)".
  Proof. vm_compute. reflexivity. Qed.

  Example peer_preserves_out_of_range_literal_cast :
    peer_widens_cast [] (Some uint64) uint8
      (IR.literal 65535 @@@ IR.TT)%Cexpr = false.
  Proof. vm_compute. reflexivity. Qed.

  Example narrowing_masks_are_not_literals :
    literal_through_cast (IR.Z_static_cast uint8 @@@ (IR.literal 65535 @@@ IR.TT))%Cexpr = None.
  Proof. vm_compute. reflexivity. Qed.

  Example nonstandard_split_uses_generic_arithmetic : native_split 56 = false.
  Proof. reflexivity. Qed.
End CastTests.
