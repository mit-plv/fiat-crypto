Require Import Crypto.Language.Identifier.
Require Import Crypto.Language.IdentifiersGenerate.

Module Compilers.
  Import Identifier.Compilers.
  Export IdentifiersGenerate.Compilers.

  Module pattern.
    Export IdentifiersGenerate.Compilers.pattern.
    Notation type := (type Compilers.base).

    Module Raw.
      Export IdentifiersGenerate.Compilers.pattern.Raw.
      Module ident.
        Export IdentifiersGenerate.Compilers.pattern.Raw.ident.
        Module PrintIdent.
          Import Raw.ident.Tactics.MakeIdent.
          Import Identifier.Compilers.
          Local Unset Printing Notations.
          (*Goal True. print_ident Compilers.ident. Abort.*)
        End PrintIdent.

        Local Unset Decidable Equality Schemes.
        Local Unset Boolean Equality Schemes.
        Inductive ident :=
        | ident_Literal
        | ident_Nat_succ
        | ident_Nat_pred
        | ident_Nat_max
        | ident_Nat_mul
        | ident_Nat_add
        | ident_Nat_sub
        | ident_Nat_eqb
        | ident_nil
        | ident_cons
        | ident_tt
        | ident_pair
        | ident_fst
        | ident_snd
        | ident_prod_rect
        | ident_bool_rect
        | ident_nat_rect
        | ident_nat_rect_arrow
        | ident_eager_nat_rect
        | ident_eager_nat_rect_arrow
        | ident_list_rect
        | ident_list_rect_arrow
        | ident_eager_list_rect
        | ident_eager_list_rect_arrow
        | ident_list_case
        | ident_List_length
        | ident_List_seq
        | ident_List_firstn
        | ident_List_skipn
        | ident_List_repeat
        | ident_List_combine
        | ident_List_map
        | ident_List_app
        | ident_List_rev
        | ident_List_flat_map
        | ident_List_partition
        | ident_List_fold_right
        | ident_List_update_nth
        | ident_List_nth_default
        | ident_eager_List_nth_default
        | ident_Z_add
        | ident_Z_mul
        | ident_Z_pow
        | ident_Z_sub
        | ident_Z_opp
        | ident_Z_div
        | ident_Z_modulo
        | ident_Z_log2
        | ident_Z_log2_up
        | ident_Z_eqb
        | ident_Z_leb
        | ident_Z_ltb
        | ident_Z_geb
        | ident_Z_gtb
        | ident_Z_of_nat
        | ident_Z_to_nat
        | ident_Z_shiftr
        | ident_Z_shiftl
        | ident_Z_land
        | ident_Z_lor
        | ident_Z_min
        | ident_Z_max
        | ident_Z_bneg
        | ident_Z_lnot_modulo
        | ident_Z_truncating_shiftl
        | ident_Z_mul_split
        | ident_Z_add_get_carry
        | ident_Z_add_with_carry
        | ident_Z_add_with_get_carry
        | ident_Z_sub_get_borrow
        | ident_Z_sub_with_get_borrow
        | ident_Z_zselect
        | ident_Z_add_modulo
        | ident_Z_rshi
        | ident_Z_cc_m
        | ident_Z_combine_at_bitwidth
        | ident_Z_cast
        | ident_Z_cast2
        | ident_Some
        | ident_None
        | ident_option_rect
        | ident_Build_zrange
        | ident_zrange_rect
        | ident_fancy_add
        | ident_fancy_addc
        | ident_fancy_sub
        | ident_fancy_subb
        | ident_fancy_mulll
        | ident_fancy_mullh
        | ident_fancy_mulhl
        | ident_fancy_mulhh
        | ident_fancy_rshi
        | ident_fancy_selc
        | ident_fancy_selm
        | ident_fancy_sell
        | ident_fancy_addm
        .
      End ident.
      Notation ident := ident.ident.
    End Raw.

    Module ident.
      Export IdentifiersGenerate.Compilers.pattern.ident.
      Module PrintIdent.
        Import ident.Tactics.PrintIdent.
        Import Identifier.Compilers.
        Import Coq.Init.Datatypes.
        Import Coq.ZArith.BinInt.
        Import Crypto.Util.ZRange.
        Local Set Printing Coercions.
        Local Unset Printing Notations.
        Local Set Printing Width 10000.
        (*Goal True. print_ident Compilers.ident. Abort.*)
      End PrintIdent.
      Local Unset Decidable Equality Schemes.
      Inductive ident : type -> Type :=
      | ident_Literal : (forall t : base, ident (type.base (pattern.base.type.type_base t)))
      | ident_Nat_succ : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.base (pattern.base.type.type_base Compilers.nat))))
      | ident_Nat_pred : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.base (pattern.base.type.type_base Compilers.nat))))
      | ident_Nat_max : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.base (pattern.base.type.type_base Compilers.nat)))))
      | ident_Nat_mul : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.base (pattern.base.type.type_base Compilers.nat)))))
      | ident_Nat_add : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.base (pattern.base.type.type_base Compilers.nat)))))
      | ident_Nat_sub : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.base (pattern.base.type.type_base Compilers.nat)))))
      | ident_Nat_eqb : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.base (pattern.base.type.type_base Compilers.bool)))))
      | ident_nil : (forall t : pattern.base.type.type base, ident (type.base (pattern.base.type.list t)))
      | ident_cons : (forall t : pattern.base.type.type base, ident (type.arrow (type.base t) (type.arrow (type.base (pattern.base.type.list t)) (type.base (pattern.base.type.list t)))))
      | ident_tt : (ident (type.base pattern.base.type.unit))
      | ident_pair : (forall A B : pattern.base.type.type base, ident (type.arrow (type.base A) (type.arrow (type.base B) (type.base (pattern.base.type.prod A B)))))
      | ident_fst : (forall A B : pattern.base.type.type base, ident (type.arrow (type.base (pattern.base.type.prod A B)) (type.base A)))
      | ident_snd : (forall A B : pattern.base.type.type base, ident (type.arrow (type.base (pattern.base.type.prod A B)) (type.base B)))
      | ident_prod_rect : (forall A B T : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base A) (type.arrow (type.base B) (type.base T))) (type.arrow (type.base (pattern.base.type.prod A B)) (type.base T))))
      | ident_bool_rect : (forall T : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base pattern.base.type.unit) (type.base T)) (type.arrow (type.arrow (type.base pattern.base.type.unit) (type.base T)) (type.arrow (type.base (pattern.base.type.type_base Compilers.bool)) (type.base T)))))
      | ident_nat_rect : (forall P : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base pattern.base.type.unit) (type.base P)) (type.arrow (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.arrow (type.base P) (type.base P))) (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.base P)))))
      | ident_nat_rect_arrow : (forall P Q : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.base P) (type.base Q)))) (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.arrow (type.base P) (type.base Q))))))
      | ident_eager_nat_rect : (forall P : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base pattern.base.type.unit) (type.base P)) (type.arrow (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.arrow (type.base P) (type.base P))) (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.base P)))))
      | ident_eager_nat_rect_arrow : (forall P Q : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.base P) (type.base Q)))) (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.arrow (type.base P) (type.base Q))))))
      | ident_list_rect : (forall A P : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base pattern.base.type.unit) (type.base P)) (type.arrow (type.arrow (type.base A) (type.arrow (type.base (pattern.base.type.list A)) (type.arrow (type.base P) (type.base P)))) (type.arrow (type.base (pattern.base.type.list A)) (type.base P)))))
      | ident_list_rect_arrow : (forall A P Q : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.arrow (type.base A) (type.arrow (type.base (pattern.base.type.list A)) (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.base P) (type.base Q))))) (type.arrow (type.base (pattern.base.type.list A)) (type.arrow (type.base P) (type.base Q))))))
      | ident_eager_list_rect : (forall A P : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base pattern.base.type.unit) (type.base P)) (type.arrow (type.arrow (type.base A) (type.arrow (type.base (pattern.base.type.list A)) (type.arrow (type.base P) (type.base P)))) (type.arrow (type.base (pattern.base.type.list A)) (type.base P)))))
      | ident_eager_list_rect_arrow : (forall A P Q : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.arrow (type.base A) (type.arrow (type.base (pattern.base.type.list A)) (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.base P) (type.base Q))))) (type.arrow (type.base (pattern.base.type.list A)) (type.arrow (type.base P) (type.base Q))))))
      | ident_list_case : (forall A P : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base pattern.base.type.unit) (type.base P)) (type.arrow (type.arrow (type.base A) (type.arrow (type.base (pattern.base.type.list A)) (type.base P))) (type.arrow (type.base (pattern.base.type.list A)) (type.base P)))))
      | ident_List_length : (forall T : pattern.base.type.type base, ident (type.arrow (type.base (pattern.base.type.list T)) (type.base (pattern.base.type.type_base Compilers.nat))))
      | ident_List_seq : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.base (pattern.base.type.list (pattern.base.type.type_base Compilers.nat))))))
      | ident_List_firstn : (forall A : pattern.base.type.type base, ident (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.arrow (type.base (pattern.base.type.list A)) (type.base (pattern.base.type.list A)))))
      | ident_List_skipn : (forall A : pattern.base.type.type base, ident (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.arrow (type.base (pattern.base.type.list A)) (type.base (pattern.base.type.list A)))))
      | ident_List_repeat : (forall A : pattern.base.type.type base, ident (type.arrow (type.base A) (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.base (pattern.base.type.list A)))))
      | ident_List_combine : (forall A B : pattern.base.type.type base, ident (type.arrow (type.base (pattern.base.type.list A)) (type.arrow (type.base (pattern.base.type.list B)) (type.base (pattern.base.type.list (pattern.base.type.prod A B))))))
      | ident_List_map : (forall A B : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base A) (type.base B)) (type.arrow (type.base (pattern.base.type.list A)) (type.base (pattern.base.type.list B)))))
      | ident_List_app : (forall A : pattern.base.type.type base, ident (type.arrow (type.base (pattern.base.type.list A)) (type.arrow (type.base (pattern.base.type.list A)) (type.base (pattern.base.type.list A)))))
      | ident_List_rev : (forall A : pattern.base.type.type base, ident (type.arrow (type.base (pattern.base.type.list A)) (type.base (pattern.base.type.list A))))
      | ident_List_flat_map : (forall A B : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base A) (type.base (pattern.base.type.list B))) (type.arrow (type.base (pattern.base.type.list A)) (type.base (pattern.base.type.list B)))))
      | ident_List_partition : (forall A : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base A) (type.base (pattern.base.type.type_base Compilers.bool))) (type.arrow (type.base (pattern.base.type.list A)) (type.base (pattern.base.type.prod (pattern.base.type.list A) (pattern.base.type.list A))))))
      | ident_List_fold_right : (forall A B : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base B) (type.arrow (type.base A) (type.base A))) (type.arrow (type.base A) (type.arrow (type.base (pattern.base.type.list B)) (type.base A)))))
      | ident_List_update_nth : (forall T : pattern.base.type.type base, ident (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.arrow (type.arrow (type.base T) (type.base T)) (type.arrow (type.base (pattern.base.type.list T)) (type.base (pattern.base.type.list T))))))
      | ident_List_nth_default : (forall T : pattern.base.type.type base, ident (type.arrow (type.base T) (type.arrow (type.base (pattern.base.type.list T)) (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.base T)))))
      | ident_eager_List_nth_default : (forall T : pattern.base.type.type base, ident (type.arrow (type.base T) (type.arrow (type.base (pattern.base.type.list T)) (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.base T)))))
      | ident_Z_add : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z)))))
      | ident_Z_mul : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z)))))
      | ident_Z_pow : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z)))))
      | ident_Z_sub : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z)))))
      | ident_Z_opp : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z))))
      | ident_Z_div : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z)))))
      | ident_Z_modulo : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z)))))
      | ident_Z_log2 : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z))))
      | ident_Z_log2_up : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z))))
      | ident_Z_eqb : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.bool)))))
      | ident_Z_leb : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.bool)))))
      | ident_Z_ltb : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.bool)))))
      | ident_Z_geb : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.bool)))))
      | ident_Z_gtb : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.bool)))))
      | ident_Z_of_nat : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.nat)) (type.base (pattern.base.type.type_base Compilers.Z))))
      | ident_Z_to_nat : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.nat))))
      | ident_Z_shiftr : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z)))))
      | ident_Z_shiftl : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z)))))
      | ident_Z_land : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z)))))
      | ident_Z_lor : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z)))))
      | ident_Z_min : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z)))))
      | ident_Z_max : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z)))))
      | ident_Z_bneg : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z))))
      | ident_Z_lnot_modulo : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z)))))
      | ident_Z_truncating_shiftl : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z))))))
      | ident_Z_mul_split : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)))))))
      | ident_Z_add_get_carry : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)))))))
      | ident_Z_add_with_carry : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z))))))
      | ident_Z_add_with_get_carry : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z))))))))
      | ident_Z_sub_get_borrow : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)))))))
      | ident_Z_sub_with_get_borrow : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z))))))))
      | ident_Z_zselect : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z))))))
      | ident_Z_add_modulo : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z))))))
      | ident_Z_rshi : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z)))))))
      | ident_Z_cc_m : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z)))))
      | ident_Z_combine_at_bitwidth : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z))))))
      | ident_Z_cast : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.zrange)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.Z)))))
      | ident_Z_cast2 : (ident (type.arrow (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.zrange) (pattern.base.type.type_base Compilers.zrange))) (type.arrow (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z))) (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z))))))
      | ident_Some : (forall A : pattern.base.type.type base, ident (type.arrow (type.base A) (type.base (pattern.base.type.option A))))
      | ident_None : (forall A : pattern.base.type.type base, ident (type.base (pattern.base.type.option A)))
      | ident_option_rect : (forall A P : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base A) (type.base P)) (type.arrow (type.arrow (type.base pattern.base.type.unit) (type.base P)) (type.arrow (type.base (pattern.base.type.option A)) (type.base P)))))
      | ident_Build_zrange : (ident (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base (pattern.base.type.type_base Compilers.zrange)))))
      | ident_zrange_rect : (forall P : pattern.base.type.type base, ident (type.arrow (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.arrow (type.base (pattern.base.type.type_base Compilers.Z)) (type.base P))) (type.arrow (type.base (pattern.base.type.type_base Compilers.zrange)) (type.base P))))
      | ident_fancy_add : (ident (type.arrow (type.base (pattern.base.type.prod (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)) (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)))) (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)))))
      | ident_fancy_addc : (ident (type.arrow (type.base (pattern.base.type.prod (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)) (pattern.base.type.prod (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)) (pattern.base.type.type_base Compilers.Z)))) (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)))))
      | ident_fancy_sub : (ident (type.arrow (type.base (pattern.base.type.prod (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)) (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)))) (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)))))
      | ident_fancy_subb : (ident (type.arrow (type.base (pattern.base.type.prod (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)) (pattern.base.type.prod (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)) (pattern.base.type.type_base Compilers.Z)))) (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)))))
      | ident_fancy_mulll : (ident (type.arrow (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)))) (type.base (pattern.base.type.type_base Compilers.Z))))
      | ident_fancy_mullh : (ident (type.arrow (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)))) (type.base (pattern.base.type.type_base Compilers.Z))))
      | ident_fancy_mulhl : (ident (type.arrow (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)))) (type.base (pattern.base.type.type_base Compilers.Z))))
      | ident_fancy_mulhh : (ident (type.arrow (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)))) (type.base (pattern.base.type.type_base Compilers.Z))))
      | ident_fancy_rshi : (ident (type.arrow (type.base (pattern.base.type.prod (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)) (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)))) (type.base (pattern.base.type.type_base Compilers.Z))))
      | ident_fancy_selc : (ident (type.arrow (type.base (pattern.base.type.prod (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)) (pattern.base.type.type_base Compilers.Z))) (type.base (pattern.base.type.type_base Compilers.Z))))
      | ident_fancy_selm : (ident (type.arrow (type.base (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.prod (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)) (pattern.base.type.type_base Compilers.Z)))) (type.base (pattern.base.type.type_base Compilers.Z))))
      | ident_fancy_sell : (ident (type.arrow (type.base (pattern.base.type.prod (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)) (pattern.base.type.type_base Compilers.Z))) (type.base (pattern.base.type.type_base Compilers.Z))))
      | ident_fancy_addm : (ident (type.arrow (type.base (pattern.base.type.prod (pattern.base.type.prod (pattern.base.type.type_base Compilers.Z) (pattern.base.type.type_base Compilers.Z)) (pattern.base.type.type_base Compilers.Z))) (type.base (pattern.base.type.type_base Compilers.Z))))
      .

      Definition package : @GoalType.package Compilers.base Compilers.ident.
      Proof. Time Tactic.make_package Compilers.exprInfoAndExprExtraInfo Raw.ident.ident ident.ident. Defined.
    End ident.
  End pattern.
End Compilers.
