Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Language.Pre.

Definition var_like_idents : GallinaIdentList.t
  := [@ident.literal
      ; @Datatypes.nil
      ; @Datatypes.cons
      ; @Datatypes.pair
      ; @Datatypes.fst
      ; @Datatypes.snd
      ; Z.opp
      ; ident.cast
      ; ident.cast2
      ; Z.combine_at_bitwidth]%gi_list.

Definition base_type_list_named : GallinaIdentList.t
  := [with_name Z BinInt.Z
      ; with_name bool Datatypes.bool
      ; with_name nat Datatypes.nat
      ; with_name zrange ZRange.zrange]%gi_list.

Definition all_ident_named_interped : GallinaIdentList.t
  := [with_name ident_Literal (@ident.literal)
      ; with_name ident_Nat_succ Nat.succ
      ; with_name ident_Nat_pred Nat.pred
      ; with_name ident_Nat_max Nat.max
      ; with_name ident_Nat_mul Nat.mul
      ; with_name ident_Nat_add Nat.add
      ; with_name ident_Nat_sub Nat.sub
      ; with_name ident_Nat_eqb Nat.eqb
      ; with_name ident_nil (@Datatypes.nil)
      ; with_name ident_cons (@Datatypes.cons)
      ; with_name ident_tt Datatypes.tt
      ; with_name ident_pair (@Datatypes.pair)
      ; with_name ident_fst (@Datatypes.fst)
      ; with_name ident_snd (@Datatypes.snd)
      ; with_name ident_prod_rect (@prod_rect_nodep)
      ; with_name ident_bool_rect (@ident.Thunked.bool_rect)
      ; with_name ident_nat_rect (@ident.Thunked.nat_rect)
      ; with_name ident_eager_nat_rect (ident.eagerly (@ident.Thunked.nat_rect))
      ; with_name ident_nat_rect_arrow (@nat_rect_arrow_nodep)
      ; with_name ident_eager_nat_rect_arrow (ident.eagerly (@nat_rect_arrow_nodep))
      ; with_name ident_list_rect (@ident.Thunked.list_rect)
      ; with_name ident_eager_list_rect (ident.eagerly (@ident.Thunked.list_rect))
      ; with_name ident_list_rect_arrow (@list_rect_arrow_nodep)
      ; with_name ident_eager_list_rect_arrow (ident.eagerly (@list_rect_arrow_nodep))
      ; with_name ident_list_case (@ident.Thunked.list_case)
      ; with_name ident_List_length (@List.length)
      ; with_name ident_List_seq (@List.seq)
      ; with_name ident_List_firstn (@List.firstn)
      ; with_name ident_List_skipn (@List.skipn)
      ; with_name ident_List_repeat (@repeat)
      ; with_name ident_List_combine (@List.combine)
      ; with_name ident_List_map (@List.map)
      ; with_name ident_List_app (@List.app)
      ; with_name ident_List_rev (@List.rev)
      ; with_name ident_List_flat_map (@List.flat_map)
      ; with_name ident_List_partition (@List.partition)
      ; with_name ident_List_fold_right (@List.fold_right)
      ; with_name ident_List_update_nth (@update_nth)
      ; with_name ident_List_nth_default (@nth_default)
      ; with_name ident_eager_List_nth_default (ident.eagerly (@nth_default))
      ; with_name ident_Z_add Z.add
      ; with_name ident_Z_mul Z.mul
      ; with_name ident_Z_pow Z.pow
      ; with_name ident_Z_sub Z.sub
      ; with_name ident_Z_opp Z.opp
      ; with_name ident_Z_div Z.div
      ; with_name ident_Z_modulo Z.modulo
      ; with_name ident_Z_eqb Z.eqb
      ; with_name ident_Z_leb Z.leb
      ; with_name ident_Z_ltb Z.ltb
      ; with_name ident_Z_geb Z.geb
      ; with_name ident_Z_gtb Z.gtb
      ; with_name ident_Z_log2 Z.log2
      ; with_name ident_Z_log2_up Z.log2_up
      ; with_name ident_Z_of_nat Z.of_nat
      ; with_name ident_Z_to_nat Z.to_nat
      ; with_name ident_Z_shiftr Z.shiftr
      ; with_name ident_Z_shiftl Z.shiftl
      ; with_name ident_Z_land Z.land
      ; with_name ident_Z_lor Z.lor
      ; with_name ident_Z_min Z.min
      ; with_name ident_Z_max Z.max
      ; with_name ident_Z_mul_split Z.mul_split
      ; with_name ident_Z_add_get_carry Z.add_get_carry_full
      ; with_name ident_Z_add_with_carry Z.add_with_carry
      ; with_name ident_Z_add_with_get_carry Z.add_with_get_carry_full
      ; with_name ident_Z_sub_get_borrow Z.sub_get_borrow_full
      ; with_name ident_Z_sub_with_get_borrow Z.sub_with_get_borrow_full
      ; with_name ident_Z_zselect Z.zselect
      ; with_name ident_Z_add_modulo Z.add_modulo
      ; with_name ident_Z_truncating_shiftl Z.truncating_shiftl
      ; with_name ident_Z_bneg Z.bneg
      ; with_name ident_Z_lnot_modulo Z.lnot_modulo
      ; with_name ident_Z_rshi Z.rshi
      ; with_name ident_Z_cc_m Z.cc_m
      ; with_name ident_Z_combine_at_bitwidth Z.combine_at_bitwidth
      ; with_name ident_Z_cast ident.cast
      ; with_name ident_Z_cast2 ident.cast2
      ; with_name ident_Some (@Datatypes.Some)
      ; with_name ident_None (@Datatypes.None)
      ; with_name ident_option_rect (@ident.Thunked.option_rect)
      ; with_name ident_Build_zrange ZRange.Build_zrange
      ; with_name ident_zrange_rect (@ZRange.zrange_rect_nodep)
      ; with_name ident_fancy_add ident.fancy.add
      ; with_name ident_fancy_addc ident.fancy.addc
      ; with_name ident_fancy_sub ident.fancy.sub
      ; with_name ident_fancy_subb ident.fancy.subb
      ; with_name ident_fancy_mulll ident.fancy.mulll
      ; with_name ident_fancy_mullh ident.fancy.mullh
      ; with_name ident_fancy_mulhl ident.fancy.mulhl
      ; with_name ident_fancy_mulhh ident.fancy.mulhh
      ; with_name ident_fancy_rshi ident.fancy.rshi
      ; with_name ident_fancy_selc ident.fancy.selc
      ; with_name ident_fancy_selm ident.fancy.selm
      ; with_name ident_fancy_sell ident.fancy.sell
      ; with_name ident_fancy_addm ident.fancy.addm
     ]%gi_list.

Definition scraped_data : ScrapedData.t
  := {| ScrapedData.base_type_list_named := base_type_list_named
        ; ScrapedData.all_ident_named_interped := all_ident_named_interped |}.
