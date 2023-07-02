Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Language.PreExtra.
Require Import Ltac2.Ltac2.
Require Import Ltac2.Printf.
Require Import Ltac2.Bool.
Import Ltac2.Constr.Unsafe.
Require Rewriter.Util.InductiveHList.
Require Rewriter.Util.LetIn.
Import InductiveHList.Notations.
Require Import Ltac2.Printf.

(* TODO: move to Util *)
Ltac2 mkApp (f : constr) (args : constr list) :=
  Constr.Unsafe.make (Constr.Unsafe.App f (Array.of_list args)).

Ltac2 Set reify_preprocess_extra :=
  fun ctx_tys term
  => lazy_match! term with
     | @Crypto.Util.LetIn.Let_In ?a ?b ?x ?f
       => mkApp '@Rewriter.Util.LetIn.Let_In [a; b; x; f]
     | ?term
       => (* kludge around COQBUG(https://github.com/coq/coq/issues/16421) *)
         (* match ?x with ZRange.Build_zrange a b => @?f a b end
            => let t := Constr.type term in
            '(@ZRange.zrange_rect_nodep $t $f $x) *)
         match Constr.Unsafe.kind term with
         | Constr.Unsafe.Case cinfo ret_ty cinv x branches
           => match Constr.Unsafe.kind ret_ty with
              | Constr.Unsafe.Lambda xb ret_ty
                => let ty := Constr.Unsafe.substnl [x] 0 ret_ty in
                   lazy_match! Constr.Binder.type xb with
                   | zrange
                     => mkApp '@ZRange.zrange_rect_nodep [ty; Array.get branches 0; x]
                   | _ => term
                   end
              | _ => printf "Warning: non-Lambda case return type %t in %t" ret_ty term;
                     term
              end
         | _ => term
         end
     end.

(* TODO: Move to util *)
Ltac2 eval_cbv_beta (c : constr) :=
  Std.eval_cbv { Std.rBeta := true; Std.rMatch := false;
                 Std.rFix := false; Std.rCofix := false;
                 Std.rZeta := false; Std.rDelta := false;
                 Std.rConst := [] }
               c.

Ltac2 Set reify_ident_preprocess_extra :=
  fun ctx_tys term
  => lazy_match! term with
     | @ZRange.zrange_rect ?t0
       => lazy_match! eval_cbv_beta t0 with
          | fun _ => ?t => mkApp '@ZRange.zrange_rect_nodep [t]
          | ?t' => if Constr.equal t0 t'
                   then term
                   else mkApp '@ZRange.zrange_rect [t']
          end
     | _ => term
     end.

Definition var_like_idents : InductiveHList.hlist
  := [@ident.literal
      ; @Datatypes.nil
      ; @Datatypes.cons
      ; @Datatypes.pair
      ; @Datatypes.fst
      ; @Datatypes.snd
      ; Datatypes.tt
      ; Z.opp
      ; ident.cast
      ; ident.cast2
      ; Z.combine_at_bitwidth]%hlist.

Definition base_type_list_named : InductiveHList.hlist
  := [with_name Z BinInt.Z
      ; with_name bool Datatypes.bool
      ; with_name nat Datatypes.nat
      ; with_name zrange ZRange.zrange
      ; with_name string String.string]%hlist.

Definition all_ident_named_interped : InductiveHList.hlist
  := [with_name ident_Literal (@ident.literal)
      ; with_name ident_comment (@ident.comment)
      ; with_name ident_comment_no_keep (@ident.comment_no_keep)
      ; with_name ident_value_barrier (@Z.value_barrier)
      ; with_name ident_Nat_succ Nat.succ
      ; with_name ident_Nat_pred Nat.pred
      ; with_name ident_Nat_max Nat.max
      ; with_name ident_Nat_mul Nat.mul
      ; with_name ident_Nat_add Nat.add
      ; with_name ident_Nat_sub Nat.sub
      ; with_name ident_Nat_eqb Nat.eqb
      (*; with_name ident_Nat_ltb Nat.ltb*)
      ; with_name ident_nil (@Datatypes.nil)
      ; with_name ident_cons (@Datatypes.cons)
      ; with_name ident_tt Datatypes.tt
      ; with_name ident_pair (@Datatypes.pair)
      ; with_name ident_fst (@Datatypes.fst)
      ; with_name ident_snd (@Datatypes.snd)
      ; with_name ident_prod_rect (@prod_rect_nodep)
      ; with_name ident_bool_rect (@Thunked.bool_rect)
      ; with_name ident_bool_rect_nodep (@bool_rect_nodep)
      ; with_name ident_nat_rect (@Thunked.nat_rect)
      ; with_name ident_eager_nat_rect (ident.eagerly (@Thunked.nat_rect))
      ; with_name ident_nat_rect_arrow (@nat_rect_arrow_nodep)
      ; with_name ident_eager_nat_rect_arrow (ident.eagerly (@nat_rect_arrow_nodep))
      ; with_name ident_list_rect (@Thunked.list_rect)
      ; with_name ident_eager_list_rect (ident.eagerly (@Thunked.list_rect))
      ; with_name ident_list_rect_arrow (@list_rect_arrow_nodep)
      ; with_name ident_eager_list_rect_arrow (ident.eagerly (@list_rect_arrow_nodep))
      ; with_name ident_list_case (@Thunked.list_case)
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
      ; with_name ident_List_filter (@List.filter)
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
      ; with_name ident_Z_mul_high Z.mul_high
      ; with_name ident_Z_add_get_carry Z.add_get_carry_full
      ; with_name ident_Z_add_with_carry Z.add_with_carry
      ; with_name ident_Z_add_with_get_carry Z.add_with_get_carry_full
      ; with_name ident_Z_sub_get_borrow Z.sub_get_borrow_full
      ; with_name ident_Z_sub_with_get_borrow Z.sub_with_get_borrow_full
      ; with_name ident_Z_ltz Z.ltz
      ; with_name ident_Z_zselect Z.zselect
      ; with_name ident_Z_add_modulo Z.add_modulo
      ; with_name ident_Z_truncating_shiftl Z.truncating_shiftl
      ; with_name ident_Z_bneg Z.bneg
      ; with_name ident_Z_lnot_modulo Z.lnot_modulo
      ; with_name ident_Z_lxor Z.lxor
      ; with_name ident_Z_rshi Z.rshi
      ; with_name ident_Z_cc_m Z.cc_m
      ; with_name ident_Z_combine_at_bitwidth Z.combine_at_bitwidth
      ; with_name ident_Z_cast ident.cast
      ; with_name ident_Z_cast2 ident.cast2
      ; with_name ident_Some (@Datatypes.Some)
      ; with_name ident_None (@Datatypes.None)
      ; with_name ident_option_rect (@Thunked.option_rect)
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
      (*; with_name ident_adk_mul pmul.adk_mul*)
     ]%hlist.

Definition scraped_data : ScrapedData.t
  := {| ScrapedData.base_type_list_named := base_type_list_named
        ; ScrapedData.all_ident_named_interped := all_ident_named_interped |}.
