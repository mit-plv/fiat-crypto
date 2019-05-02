Require Import Crypto.Language.
Require Import Crypto.IdentifiersGenerate.

Module Compilers.
  Export Language.Compilers.
  Export IdentifiersGenerate.Compilers.

  Module pattern.
    Export IdentifiersGenerate.Compilers.pattern.

    Module Raw.
      Export IdentifiersGenerate.Compilers.pattern.Raw.
      Module ident.
        Export IdentifiersGenerate.Compilers.pattern.Raw.ident.
        Module PrintIdent.
          Import Raw.ident.Tactics.MakeIdent.
          Import Language.Compilers.ident.
          Local Unset Printing Notations.
          (*Goal True. print_ident. Abort.*)
        End PrintIdent.

        Local Unset Decidable Equality Schemes.
        Local Unset Boolean Equality Schemes.
        Inductive ident :=
        | Literal
        | Nat_succ
        | Nat_pred
        | Nat_max
        | Nat_mul
        | Nat_add
        | Nat_sub
        | Nat_eqb
        | nil
        | cons
        | pair
        | fst
        | snd
        | prod_rect
        | bool_rect
        | nat_rect
        | nat_rect_arrow
        | eager_nat_rect
        | eager_nat_rect_arrow
        | list_rect
        | list_rect_arrow
        | eager_list_rect
        | eager_list_rect_arrow
        | list_case
        | List_length
        | List_seq
        | List_firstn
        | List_skipn
        | List_repeat
        | List_combine
        | List_map
        | List_app
        | List_rev
        | List_flat_map
        | List_partition
        | List_fold_right
        | List_update_nth
        | List_nth_default
        | eager_List_nth_default
        | Z_add
        | Z_mul
        | Z_pow
        | Z_sub
        | Z_opp
        | Z_div
        | Z_modulo
        | Z_log2
        | Z_log2_up
        | Z_eqb
        | Z_leb
        | Z_ltb
        | Z_geb
        | Z_gtb
        | Z_of_nat
        | Z_to_nat
        | Z_shiftr
        | Z_shiftl
        | Z_land
        | Z_lor
        | Z_min
        | Z_max
        | Z_bneg
        | Z_lnot_modulo
        | Z_mul_split
        | Z_add_get_carry
        | Z_add_with_carry
        | Z_add_with_get_carry
        | Z_sub_get_borrow
        | Z_sub_with_get_borrow
        | Z_zselect
        | Z_add_modulo
        | Z_rshi
        | Z_cc_m
        | Z_combine_at_bitwidth
        | Z_cast
        | Z_cast2
        | option_Some
        | option_None
        | option_rect
        | Build_zrange
        | zrange_rect
        | fancy_add
        | fancy_addc
        | fancy_sub
        | fancy_subb
        | fancy_mulll
        | fancy_mullh
        | fancy_mulhl
        | fancy_mulhh
        | fancy_rshi
        | fancy_selc
        | fancy_selm
        | fancy_sell
        | fancy_addm
        .
      End ident.
      Notation ident := ident.ident.
    End Raw.

    Module ident.
      Export IdentifiersGenerate.Compilers.pattern.ident.
      Module PrintIdent.
        Import ident.Tactics.PrintIdent.
        Import Compilers.ident.
        Local Set Printing Coercions.
        Local Unset Printing Notations.
        Local Set Printing Width 10000.
        (*Goal True. print_ident. Abort.*)
      End PrintIdent.
      Local Unset Decidable Equality Schemes.
      Inductive ident : type -> Set :=
      | Literal : (forall t : base.type.base, ident (type.base (base.type.type_base t)))
      | Nat_succ : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.type_base base.type.nat))))
      | Nat_pred : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.type_base base.type.nat))))
      | Nat_max : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.type_base base.type.nat)))))
      | Nat_mul : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.type_base base.type.nat)))))
      | Nat_add : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.type_base base.type.nat)))))
      | Nat_sub : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.type_base base.type.nat)))))
      | Nat_eqb : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.type_base base.type.bool)))))
      | nil : (forall t : base.type.type, ident (type.base (base.type.list t)))
      | cons : (forall t : base.type.type, ident (type.arrow (type.base t) (type.arrow (type.base (base.type.list t)) (type.base (base.type.list t)))))
      | pair : (forall A B : base.type.type, ident (type.arrow (type.base A) (type.arrow (type.base B) (type.base (base.type.prod A B)))))
      | fst : (forall A B : base.type.type, ident (type.arrow (type.base (base.type.prod A B)) (type.base A)))
      | snd : (forall A B : base.type.type, ident (type.arrow (type.base (base.type.prod A B)) (type.base B)))
      | prod_rect : (forall A B T : base.type.type, ident (type.arrow (type.arrow (type.base A) (type.arrow (type.base B) (type.base T))) (type.arrow (type.base (base.type.prod A B)) (type.base T))))
      | bool_rect : (forall T : base.type.type, ident (type.arrow (type.arrow (type.base (base.type.type_base base.type.unit)) (type.base T)) (type.arrow (type.arrow (type.base (base.type.type_base base.type.unit)) (type.base T)) (type.arrow (type.base (base.type.type_base base.type.bool)) (type.base T)))))
      | nat_rect : (forall P : base.type.type, ident (type.arrow (type.arrow (type.base (base.type.type_base base.type.unit)) (type.base P)) (type.arrow (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base P) (type.base P))) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base P)))))
      | nat_rect_arrow : (forall P Q : base.type.type, ident (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.base P) (type.base Q)))) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base P) (type.base Q))))))
      | eager_nat_rect : (forall P : base.type.type, ident (type.arrow (type.arrow (type.base (base.type.type_base base.type.unit)) (type.base P)) (type.arrow (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base P) (type.base P))) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base P)))))
      | eager_nat_rect_arrow : (forall P Q : base.type.type, ident (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.base P) (type.base Q)))) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base P) (type.base Q))))))
      | list_rect : (forall A P : base.type.type, ident (type.arrow (type.arrow (type.base (base.type.type_base base.type.unit)) (type.base P)) (type.arrow (type.arrow (type.base A) (type.arrow (type.base (base.type.list A)) (type.arrow (type.base P) (type.base P)))) (type.arrow (type.base (base.type.list A)) (type.base P)))))
      | list_rect_arrow : (forall A P Q : base.type.type, ident (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.arrow (type.base A) (type.arrow (type.base (base.type.list A)) (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.base P) (type.base Q))))) (type.arrow (type.base (base.type.list A)) (type.arrow (type.base P) (type.base Q))))))
      | eager_list_rect : (forall A P : base.type.type, ident (type.arrow (type.arrow (type.base (base.type.type_base base.type.unit)) (type.base P)) (type.arrow (type.arrow (type.base A) (type.arrow (type.base (base.type.list A)) (type.arrow (type.base P) (type.base P)))) (type.arrow (type.base (base.type.list A)) (type.base P)))))
      | eager_list_rect_arrow : (forall A P Q : base.type.type, ident (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.arrow (type.base A) (type.arrow (type.base (base.type.list A)) (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.base P) (type.base Q))))) (type.arrow (type.base (base.type.list A)) (type.arrow (type.base P) (type.base Q))))))
      | list_case : (forall A P : base.type.type, ident (type.arrow (type.arrow (type.base (base.type.type_base base.type.unit)) (type.base P)) (type.arrow (type.arrow (type.base A) (type.arrow (type.base (base.type.list A)) (type.base P))) (type.arrow (type.base (base.type.list A)) (type.base P)))))
      | List_length : (forall T : base.type.type, ident (type.arrow (type.base (base.type.list T)) (type.base (base.type.type_base base.type.nat))))
      | List_seq : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.list (base.type.type_base base.type.nat))))))
      | List_firstn : (forall A : base.type.type, ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base (base.type.list A)) (type.base (base.type.list A)))))
      | List_skipn : (forall A : base.type.type, ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base (base.type.list A)) (type.base (base.type.list A)))))
      | List_repeat : (forall A : base.type.type, ident (type.arrow (type.base A) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.list A)))))
      | List_combine : (forall A B : base.type.type, ident (type.arrow (type.base (base.type.list A)) (type.arrow (type.base (base.type.list B)) (type.base (base.type.list (base.type.prod A B))))))
      | List_map : (forall A B : base.type.type, ident (type.arrow (type.arrow (type.base A) (type.base B)) (type.arrow (type.base (base.type.list A)) (type.base (base.type.list B)))))
      | List_app : (forall A : base.type.type, ident (type.arrow (type.base (base.type.list A)) (type.arrow (type.base (base.type.list A)) (type.base (base.type.list A)))))
      | List_rev : (forall A : base.type.type, ident (type.arrow (type.base (base.type.list A)) (type.base (base.type.list A))))
      | List_flat_map : (forall A B : base.type.type, ident (type.arrow (type.arrow (type.base A) (type.base (base.type.list B))) (type.arrow (type.base (base.type.list A)) (type.base (base.type.list B)))))
      | List_partition : (forall A : base.type.type, ident (type.arrow (type.arrow (type.base A) (type.base (base.type.type_base base.type.bool))) (type.arrow (type.base (base.type.list A)) (type.base (base.type.prod (base.type.list A) (base.type.list A))))))
      | List_fold_right : (forall A B : base.type.type, ident (type.arrow (type.arrow (type.base B) (type.arrow (type.base A) (type.base A))) (type.arrow (type.base A) (type.arrow (type.base (base.type.list B)) (type.base A)))))
      | List_update_nth : (forall T : base.type.type, ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.arrow (type.base T) (type.base T)) (type.arrow (type.base (base.type.list T)) (type.base (base.type.list T))))))
      | List_nth_default : (forall T : base.type.type, ident (type.arrow (type.base T) (type.arrow (type.base (base.type.list T)) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base T)))))
      | eager_List_nth_default : (forall T : base.type.type, ident (type.arrow (type.base T) (type.arrow (type.base (base.type.list T)) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base T)))))
      | Z_add : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_mul : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_pow : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_sub : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_opp : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))
      | Z_div : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_modulo : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_log2 : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))
      | Z_log2_up : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))
      | Z_eqb : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.bool)))))
      | Z_leb : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.bool)))))
      | Z_ltb : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.bool)))))
      | Z_geb : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.bool)))))
      | Z_gtb : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.bool)))))
      | Z_of_nat : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.type_base base.type.Z))))
      | Z_to_nat : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.nat))))
      | Z_shiftr : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_shiftl : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_land : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_lor : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_min : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_max : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_bneg : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))
      | Z_lnot_modulo : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_mul_split : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))))))
      | Z_add_get_carry : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))))))
      | Z_add_with_carry : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))))
      | Z_add_with_get_carry : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))))))))
      | Z_sub_get_borrow : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))))))
      | Z_sub_with_get_borrow : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))))))))
      | Z_zselect : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))))
      | Z_add_modulo : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))))
      | Z_rshi : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))))
      | Z_cc_m : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_combine_at_bitwidth : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))))
      | Z_cast : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))
      | Z_cast2 : (ident (type.arrow (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))))
      | option_Some : (forall A : base.type.type, ident (type.arrow (type.base A) (type.base (base.type.option A))))
      | option_None : (forall A : base.type.type, ident (type.base (base.type.option A)))
      | option_rect : (forall A P : base.type.type, ident (type.arrow (type.arrow (type.base A) (type.base P)) (type.arrow (type.arrow (type.base (base.type.type_base base.type.unit)) (type.base P)) (type.arrow (type.base (base.type.option A)) (type.base P)))))
      | Build_zrange : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.zrange)))))
      | zrange_rect : (forall P : base.type.type, ident (type.arrow (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base P))) (type.arrow (type.base (base.type.type_base base.type.zrange)) (type.base P))))
      | fancy_add : (ident (type.arrow (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))))
      | fancy_addc : (ident (type.arrow (type.base (base.type.prod (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)) (base.type.type_base base.type.Z))) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))))
      | fancy_sub : (ident (type.arrow (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))))
      | fancy_subb : (ident (type.arrow (type.base (base.type.prod (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)) (base.type.type_base base.type.Z))) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))))
      | fancy_mulll : (ident (type.arrow (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      | fancy_mullh : (ident (type.arrow (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      | fancy_mulhl : (ident (type.arrow (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      | fancy_mulhh : (ident (type.arrow (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      | fancy_rshi : (ident (type.arrow (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      | fancy_selc : (ident (type.arrow (type.base (base.type.prod (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      | fancy_selm : (ident (type.arrow (type.base (base.type.prod (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      | fancy_sell : (ident (type.arrow (type.base (base.type.prod (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      | fancy_addm : (ident (type.arrow (type.base (base.type.prod (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      .

      Definition package : GoalType.package.
      Proof. Time Tactic.make_package Raw.ident.ident ident.ident. Defined.
    End ident.
  End pattern.
End Compilers.
