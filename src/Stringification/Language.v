Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.Strings.HexString.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Prod.
Require Crypto.Util.Strings.String.
Require Import Crypto.Util.Structures.Equalities.Sum.
Require Import Crypto.Util.Structures.Equalities.Iso.
Require Import Crypto.Util.Structures.Orders.Sum.
Require Import Crypto.Util.Structures.Orders.Iso.
Require Import Crypto.Util.MSets.MSetIso.
Require Import Crypto.Util.MSets.MSetSum.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.Strings.NamingConventions.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.Show.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.MSets.MSetPositive.Show.
Require Import Crypto.Util.MSets.Show.
Require Import Crypto.Util.Level.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.Bool.Equality.
Require Import Crypto.Util.Notations.
Import Coq.Lists.List ListNotations. Local Open Scope zrange_scope. Local Open Scope Z_scope.

Module Compilers.
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  Export Language.Language.Compilers.
  Export Language.API.Compilers.
  Export AbstractInterpretation.ZRange.Compilers.
  Import invert_expr.
  Import Compilers.API.

  Local Notation tZ := (base.type.type_base base.type.Z).

  Module Export Options.
    Module PHOAS.
      (** Print casts in PHOAS? *)
      Class with_casts := with_castsv : bool.
      #[global] Typeclasses Opaque with_casts.

      (** Print all casts in PHOAS? *)
      Class with_all_casts := with_all_castsv : bool.
      #[global] Typeclasses Opaque with_all_casts.

      Definition default_with_casts : with_casts := true.
      Definition default_with_all_casts : with_all_casts := false.
    End PHOAS.
    #[global] Typeclasses Opaque PHOAS.with_casts PHOAS.with_all_casts.
    #[global] Existing Instances PHOAS.default_with_casts PHOAS.default_with_all_casts.

    (** How to relax zranges *)
    Class relax_zrange_opt := relax_zrange : zrange -> zrange.
#[global]
    Typeclasses Opaque relax_zrange_opt.
    (** What's the package name? *)
    Class package_name_opt := internal_package_name : option string.
#[global]
    Typeclasses Opaque package_name_opt.
    (** What's the class name? *)
    Class class_name_opt := internal_class_name : option string.
#[global]
    Typeclasses Opaque class_name_opt.
    (** Should we emit typedefs or not? *)
    Class skip_typedefs_opt := skip_typedefs : bool.
#[global]
    Typeclasses Opaque skip_typedefs_opt.
    (** Which adc/sbb bitwidth-split-carries should be relaxed to bitwidth *)
    Class relax_adc_sbb_return_carry_to_bitwidth_opt := relax_adc_sbb_return_carry_to_bitwidth : list Z.
#[global]
    Typeclasses Opaque relax_adc_sbb_return_carry_to_bitwidth_opt.
    (** Do language-specific cast adjustment *)
    Class language_specific_cast_adjustment_opt := language_specific_cast_adjustment : bool.
#[global]
    Typeclasses Opaque language_specific_cast_adjustment_opt.
    Class language_naming_conventions_opt :=
      { public_function_naming_convention : option capitalization_convention
        ; private_function_naming_convention : option capitalization_convention
        ; public_type_naming_convention : option capitalization_convention
        ; private_type_naming_convention : option capitalization_convention
        ; variable_naming_convention : option capitalization_convention
        ; package_naming_convention : option capitalization_convention
        ; class_naming_convention : option capitalization_convention
      }.
    Definition default_language_naming_conventions : language_naming_conventions_opt
      := {| public_function_naming_convention := None
            ; private_function_naming_convention := None
            ; public_type_naming_convention := None
            ; private_type_naming_convention := None
            ; variable_naming_convention := None
            ; package_naming_convention := None
            ; class_naming_convention := None
         |}.

    Definition convert_to_naming_convention (convention : option capitalization_convention) (s : string) : string
      := match convention with
         | Some convention => convert_case snake_case convention s
         | None => s
         end.
    Definition package_name {pkg_name : package_name_opt} {language_naming_conventions : language_naming_conventions_opt} (prefix : string) : string
      := match pkg_name with
         | Some name => name
         | None => convert_to_naming_convention
                     package_naming_convention
                     (if String.endswith "_" prefix then substring 0 (String.length prefix - 1) prefix else prefix)
         end.
    Definition class_name {cls_name : class_name_opt} {language_naming_conventions : language_naming_conventions_opt} (prefix : string) : string
      := match cls_name with
         | Some name => name
         | None => convert_to_naming_convention
                     class_naming_convention
                     (if String.endswith "_" prefix then substring 0 (String.length prefix - 1) prefix else prefix)
         end.

    Definition default_text_before_function_name : string := "The function ".
    Definition default_text_before_type_name : string := "The type ".

    Class documentation_options_opt :=
      {
        (** Text to insert before the function name *)
        text_before_function_name_opt : option string;
        text_before_function_name : string := Option.value text_before_function_name_opt default_text_before_function_name;
        (** Text to insert before the type name *)
        text_before_type_name_opt : option string;
        text_before_type_name : string := Option.value text_before_type_name_opt default_text_before_type_name;
        (** Stick an extra newline before the package declaration *)
        newline_before_package_declaration : bool;
        (** Stick a newline between the "Bounds:" and the bounds of typedefs *)
        newline_in_typedef_bounds : bool;
      }.

    Definition default_documentation_options : documentation_options_opt
      := {| text_before_function_name_opt := None
            ; text_before_type_name_opt := None
            ; newline_before_package_declaration := false
            ; newline_in_typedef_bounds := false
         |}.

    Class output_options_opt :=
      { #[global] skip_typedefs_ :: skip_typedefs_opt
      ; #[global] relax_adc_sbb_return_carry_to_bitwidth_ :: relax_adc_sbb_return_carry_to_bitwidth_opt
      ; #[global] language_specific_cast_adjustment_ :: language_specific_cast_adjustment_opt
      }.

    Definition default_output_options : output_options_opt
      := {| skip_typedefs_ := true
         ; relax_adc_sbb_return_carry_to_bitwidth_ := []
         ; language_specific_cast_adjustment_ := true
         |}.
  End Options.

  Module ToString.
    Local Open Scope string_scope.
    Local Open Scope Z_scope.

    Module Import ZRange.
      Module Export type.
        Module Export base.
          Fixpoint show_lvl_interp {t} : ShowLevel (ZRange.type.base.interp t)
            := match t return ShowLevel (ZRange.type.base.interp t) with
               | base.type.unit => @show_lvl unit _
               | base.type.type_base base.type.Z => @show_lvl zrange _
               | base.type.type_base base.type.positive => @show_lvl positive _
               | base.type.type_base base.type.bool => @show_lvl bool _
               | base.type.type_base base.type.nat => @show_lvl nat _
               | base.type.type_base base.type.zrange => @show_lvl zrange _
               | base.type.type_base base.type.string => @show_lvl string _
               | base.type.prod A B => @show_lvl (ZRange.type.base.interp A * ZRange.type.base.interp B) _
               | base.type.list A => @show_lvl (list (ZRange.type.base.interp A)) _
               | base.type.option A => @show_lvl (option (ZRange.type.base.interp A)) _
               end%string.
          Global Existing Instance show_lvl_interp.
          Global Instance show_interp {t} : Show (ZRange.type.base.interp t) := show_lvl_interp.
          Module Export option.
            Fixpoint show_lvl_interp {t} : ShowLevel (ZRange.type.base.option.interp t)
              := match t return ShowLevel (ZRange.type.base.option.interp t) with
                 | base.type.unit => @show_lvl unit _
                 | base.type.type_base _ as t => @show_lvl (option (ZRange.type.base.interp t)) _
                 | base.type.prod A B => @show_lvl (ZRange.type.base.option.interp A * ZRange.type.base.option.interp B) _
                 | base.type.list A => @show_lvl (option (list (ZRange.type.base.option.interp A))) _
                 | base.type.option A => @show_lvl (option (option (ZRange.type.base.option.interp A))) _
                 end.
            Global Existing Instance show_lvl_interp.
            Global Instance show_interp {t} : Show (ZRange.type.base.option.interp t) := show_lvl_interp.
          End option.
        End base.

        Module option.
          Global Instance show_lvl_interp {t} : ShowLevel (ZRange.type.option.interp t)
            := match t return ShowLevel (ZRange.type.option.interp t) with
               | type.base t => @show_lvl (ZRange.type.base.option.interp t) _
               | type.arrow s d => fun _ _ => "λ"
               end.
          Global Instance show_interp {t} : Show (ZRange.type.option.interp t) := show_lvl_interp.
        End option.
      End type.
    End ZRange.

    Module PHOAS.
      Module type.
        Module base.
          Global Instance show_base : Show base.type.base
            := fun t => match t with
                        | base.type.Z => "ℤ"
                        | base.type.positive => "ℤ⁺"
                        | base.type.bool => "𝔹"
                        | base.type.nat => "ℕ"
                        | base.type.zrange => "zrange"
                        | base.type.string => "string"
                        end.
          Global Instance show_lvl_base : ShowLevel base.type.base := show_base.
          Global Instance show_lvl_type : ShowLevel base.type
            := fix show_lvl_type (t : base.type) : Level.Level -> string
                 := match t with
                    | base.type.unit => fun _ => "()"
                    | base.type.type_base t => show_lvl t
                    | base.type.prod A B => show_lvl_binop
                                              mul_assoc mul_lvl
                                              (show_lvl_type A) " * " (show_lvl_type B)
                    | base.type.list A => fun _ => "[" ++ show_lvl_type A term_lvl ++ "]"
                    | base.type.option A
                      => show_lvl_app
                           (fun 'tt => "option") (show_lvl_type A)
                    end.
          Global Instance show_type : Show base.type := show_lvl_type.
          Global Instance show_lvl_base_interp {t} : ShowLevel (base.base_interp t)
            := match t with
               | base.type.Z => @show_lvl Z _
               | base.type.bool => @show_lvl bool _
               | base.type.positive => @show_lvl positive _
               | base.type.nat => @show_lvl nat _
               | base.type.zrange => @show_lvl zrange _
               | base.type.string => @show_lvl string _
               end.
          Global Instance show_base_interp {t} : Show (base.base_interp t) := show_lvl_base_interp.
          Fixpoint show_lvl_interp {t} : ShowLevel (base.interp t)
            := match t with
               | base.type.unit => @show_lvl unit _
               | base.type.type_base t => @show_lvl (base.base_interp t) _
               | base.type.prod A B => @show_lvl (base.interp A * base.interp B) _
               | base.type.list A => @show_lvl (list (base.interp A)) _
               | base.type.option A => @show_lvl (option (base.interp A)) _
               end.
          Global Existing Instance show_lvl_interp.
          Global Instance show_interp {t} : Show (base.interp t) := show_lvl_interp.
          Global Instance show_lvl : ShowLevel base.type := show_lvl_type.
          Global Instance show : Show base.type := show_type.
        End base.
        Fixpoint show_lvl_for_each_lhs_of_arrow {base_type} {f : type.type base_type -> Type} {show_f : forall t, ShowLevel (f t)} {t : type.type base_type} {struct t} : ShowLevel (type.for_each_lhs_of_arrow f t)
          := match t return ShowLevel (type.for_each_lhs_of_arrow f t) with
             | type.base t => @show_lvl unit _
             | type.arrow s d
               => Option.value
                    (match d with
                     | type.base _ => Some (fun '(x, _) => @show_lvl (f s) _ x)
                     | type.arrow _ _ => None
                     end)
                    (@show_lvl (f s * type.for_each_lhs_of_arrow f d) _)
             end.
        Global Existing Instance show_lvl_for_each_lhs_of_arrow.
        Definition show_for_each_lhs_of_arrow {base_type} {f : type.type base_type -> Type} {show_f : forall t, Show (f t)} {t : type.type base_type} : Show (type.for_each_lhs_of_arrow f t)
          := let _ := fun t => @ShowLevel_of_Show (f t) in
             show_lvl_for_each_lhs_of_arrow.

        Global Instance show_lvl_type : forall {base_type} {S : ShowLevel base_type}, ShowLevel (type.type base_type)
          := fix show_lvl_type {base_type} {S : ShowLevel base_type} (t : type.type base_type) : Level.Level -> string
               := match t with
                  | type.base t => show_lvl t
                  | type.arrow s d
                    => show_lvl_binop impl_assoc impl_lvl (show_lvl_type s) " → " (show_lvl_type d)
                  end.
        Global Instance show_lvl {base_type} {S : ShowLevel base_type} : ShowLevel (type.type base_type) := show_lvl_type.
        Global Instance show_type {base_type} {S : Show base_type} : Show (type.type base_type)
          := let _ := @ShowLevel_of_Show base_type in
             show_lvl_type.
        Global Instance show {base_type} {S : Show base_type} : Show (type.type base_type) := show_type.
      End type.

      Definition bitwidth_to_string (v : Z) : string
        := (if v =? 2^Z.log2 v then "2^" ++ Decimal.Z.to_string (Z.log2 v) else HexString.of_Z v).
      Definition show_range_or_ctype : Show zrange
        := fun v
           => if (v.(lower) =? 0) && (v.(upper) =? 2^(Z.log2 (v.(upper) + 1)) - 1)
              then ("uint" ++ Decimal.Z.to_string (Z.log2 (v.(upper) + 1)) ++ "_t")%string
              else let lg2 := 1 + Z.log2 (-v.(lower)) in
                   if (v.(lower) =? -2^(lg2-1)) && (v.(upper) =? 2^(lg2-1)-1)
                   then ("int" ++ Decimal.Z.to_string lg2 ++ "_t")%string
                   else show v.
      Definition show_lvl_compact_Z : ShowLevel Z
        := fun v
           => let is_neg := v <? 0 in
              (if is_neg then show_lvl_unop opp_lvl "-" else show_lvl)
                (let v := Z.abs v in
                 if v <=? 2^8
                 then Decimal.show_lvl_Z v
                 else if v =? 2^(Z.log2 v)
                      then show_lvl_binop pow_assoc pow_lvl 2 "^" (Decimal.show_lvl_Z (Z.log2 v))
                      else if v =? 2^(Z.log2_up v) - 1
                           then show_lvl_binop
                                  sub_assoc sub_lvl
                                  (show_lvl_binop pow_assoc pow_lvl 2 "^" (Decimal.show_lvl_Z (Z.log2_up v))) "-" 1
                           else Hex.show_lvl_Z v).
      Definition show_compact_Z : Show Z := show_lvl_compact_Z.

      Fixpoint make_castb {t} : ZRange.type.base.option.interp t -> option string
        := match t return ZRange.type.base.option.interp t -> option string with
           | base.type.type_base base.type.Z => option_map show_range_or_ctype
           | base.type.prod A B
             => fun '(r1, r2)
                => match @make_castb A r1, @make_castb B r2 with
                   | Some c1, Some c2 => Some (c1 ++ ", " ++ c2)
                   | None, Some c => Some ("??, " ++ c)
                   | Some c, None => Some (c ++ ", ??")
                   | None, None => None
                   end
           | base.type.list A
             => fun r
                => match r with
                   | None => None
                   | Some nil => Some "void[0]"
                   | Some ((r :: rs) as ls)
                     => let n := show (List.length ls) in
                        let c1 := @make_castb A r in
                        let all_same := List.forallb (ZRange.type.base.option.interp_beq r) rs in
                        Some
                          (match all_same, c1 with
                           | true, Some c1 => c1
                           | _, _ => "??"
                           end
                             ++ "[" ++ n ++ "]")
                   end
           | base.type.unit
           | base.type.type_base _
           | base.type.option _
             => fun _ => None
           end.

      Definition make_cast {t} : ZRange.type.option.interp t -> option string
        := match t with
           | type.base t => @make_castb t
           | type.arrow _ _ => fun _ => None
           end.

      Definition maybe_wrap_cast (with_cast : bool) {t} (xr : (Level.Level -> string) * ZRange.type.option.interp t) (lvl : Level.Level) : string
        := match with_cast, make_cast (snd xr) with
           | true, Some c => "(" ++ c ++ ")" ++ fst xr (Level.next app_lvl)
           | _, _ => fst xr lvl
           end.

      Section without_prod.
        Local Remove Hints show_lvl_prod : typeclass_instances.
        Definition show_application (with_casts : bool) {t : type} (f : Level.Level -> string) (args : type.for_each_lhs_of_arrow (fun t => (Level.Level -> string) * ZRange.type.option.interp t)%type t)
          : Level.Level -> string
          := match t return type.for_each_lhs_of_arrow (fun t => (Level.Level -> string) * ZRange.type.option.interp t)%type t -> Level.Level -> string with
             | type.base _ => fun 'tt lvl => f lvl
             | type.arrow s d
               => fun xs lvl
                  => let _ : forall t, Show ((Level.Level -> string) * ZRange.type.option.interp t)%type
                       := (fun t x => maybe_wrap_cast with_casts x app_lvl) in
                     let _ : forall t, ShowLevel ((Level.Level -> string) * ZRange.type.option.interp t)%type
                       := fun t => ShowLevel_of_Show in
                     maybe_wrap_parens (Level.ltb lvl (Level.prev app_lvl)) (f (Level.prev app_lvl) ++ show_lvl xs (-∞))
             end args.
      End without_prod.

      Module ident.
        Global Instance show_lvl_ident {t} : ShowLevel (ident.ident t)
          := fun idc
             => match idc with
                | ident.Literal base.type.Z v => show_lvl_compact_Z v
                | ident.Literal _t v => show_lvl v
                | ident.value_barrier => neg_wrap_parens "value_barrier"
                | ident.comment _ => neg_wrap_parens "comment"
                | ident.comment_no_keep _ => neg_wrap_parens "comment_no_keep"
                | ident.tt => fun _ => "()"
                | ident.Nat_succ => neg_wrap_parens "Nat.succ"
                | ident.Nat_pred => neg_wrap_parens "Nat.pred"
                | ident.Nat_max => neg_wrap_parens "Nat.max"
                | ident.Nat_mul => neg_wrap_parens "Nat.mul"
                | ident.Nat_add => neg_wrap_parens "Nat.add"
                | ident.Nat_sub => neg_wrap_parens "Nat.sub"
                | ident.Nat_eqb => neg_wrap_parens "Nat.eqb"
                | ident.Pos_mul => neg_wrap_parens "Pos.mul"
                | ident.Pos_add => neg_wrap_parens "Pos.add"
                | ident.nil t => neg_wrap_parens "[]"
                | ident.cons t => fun _ => "(::)"
                | ident.pair A B => fun _ => "(,)"
                | ident.fst A B => neg_wrap_parens "fst"
                | ident.snd A B => neg_wrap_parens "snd"
                | ident.prod_rect A B T => neg_wrap_parens "prod_rect"
                | ident.bool_rect T => neg_wrap_parens "bool_rect"
                | ident.bool_rect_nodep T => neg_wrap_parens "bool_rect_nodep"
                | ident.nat_rect P => neg_wrap_parens "nat_rect"
                | ident.eager_nat_rect P => neg_wrap_parens "eager_nat_rect"
                | ident.nat_rect_arrow P Q => neg_wrap_parens "nat_rect(→)"
                | ident.eager_nat_rect_arrow P Q => neg_wrap_parens "eager_nat_rect(→)"
                | @ident.nat_rect_fbb_b A B C => neg_wrap_parens "nat_rect_fbb_b"
                | @ident.nat_rect_fbb_b_b A B C D => neg_wrap_parens "nat_rect_fbb_b_b"
                | @ident.list_rect_fbb_b T A B C => neg_wrap_parens "list_rect_fbb_b"
                | @ident.list_rect_fbb_b_b T A B C D => neg_wrap_parens "list_rect_fbb_b_b"
                | @ident.list_rect_fbb_b_b_b T A B C D E => neg_wrap_parens "list_rect_fbb_b_b"
                | @ident.list_rect_fbb_b_b_b_b T A B C D E F => neg_wrap_parens "list_rect_fbb_b_b"
                | @ident.list_rect_fbb_b_b_b_b_b T A B C D E F G => neg_wrap_parens "list_rect_fbb_b_b"
                | ident.list_rect A P => neg_wrap_parens "list_rect"
                | ident.eager_list_rect A P => neg_wrap_parens "eager_list_rect"
                | ident.list_rect_arrow A P Q => neg_wrap_parens "list_rect(→)"
                | ident.eager_list_rect_arrow A P Q => neg_wrap_parens "eager_list_rect(→)"
                | ident.list_case A P => neg_wrap_parens "list_case"
                | ident.List_length T => neg_wrap_parens "length"
                | ident.List_seq => neg_wrap_parens "seq"
                | ident.List_repeat A => neg_wrap_parens "repeat"
                | ident.List_firstn A => neg_wrap_parens "firstn"
                | ident.List_skipn A => neg_wrap_parens "skipn"
                | ident.List_combine A B => neg_wrap_parens "combine"
                | ident.List_map A B => neg_wrap_parens "map"
                | ident.List_app A => fun _ => "(++)"
                | ident.List_rev A => neg_wrap_parens "rev"
                | ident.List_flat_map A B => neg_wrap_parens "flat_map"
                | ident.List_partition A => neg_wrap_parens "partition"
                | ident.List_filter A => neg_wrap_parens "filter"
                | ident.List_fold_right A B => neg_wrap_parens "fold_right"
                | ident.List_update_nth T => neg_wrap_parens "update_nth"
                | ident.List_nth_default T => neg_wrap_parens "nth"
                | ident.eager_List_nth_default T => neg_wrap_parens "eager_nth"
                | ident.Some _ => neg_wrap_parens "Some"
                | ident.None _ => neg_wrap_parens "None"
                | ident.option_rect _ _ => neg_wrap_parens "option_rect"
                | ident.Z_add => fun _ => "(+)"
                | ident.Z_mul => fun _ => "( * )"
                | ident.Z_pow => fun _ => "(^)"
                | ident.Z_sub => fun _ => "(-)"
                | ident.Z_opp => fun _ => "-"
                | ident.Z_div => fun _ => "(/)"
                | ident.Z_modulo => fun _ => "(mod)"
                | ident.Z_eqb => fun _ => "(=)"
                | ident.Z_leb => fun _ => "(≤)"
                | ident.Z_ltb => fun _ => "(<)"
                | ident.Z_geb => fun _ => "(≥)"
                | ident.Z_gtb => fun _ => "(>)"
                | ident.Z_min => neg_wrap_parens "min"
                | ident.Z_max => neg_wrap_parens "max"
                | ident.Z_abs => neg_wrap_parens "abs"
                | ident.Z_log2 => neg_wrap_parens "log₂"
                | ident.Z_log2_up => neg_wrap_parens "⌈log₂⌉"
                | ident.Z_of_nat => fun _ => "(ℕ→ℤ)"
                | ident.Z_to_nat => fun _ => "(ℤ→ℕ)"
                | ident.Z_pos => fun _ => "(ℤ⁺→ℤ)"
                | ident.Z_to_pos => fun _ => "(ℤ→ℤ⁺)"
                | ident.Z_shiftr => fun _ => "(>>)"
                | ident.Z_shiftl => fun _ => "(<<)"
                | ident.Z_land => fun _ => "(&)"
                | ident.Z_lor => fun _ => "(|)"
                | ident.Z_lnot_modulo => neg_wrap_parens "~"
                | ident.Z_lxor => neg_wrap_parens "⊕"
                | ident.Z_bneg => neg_wrap_parens "!"
                | ident.Z_mul_split => neg_wrap_parens "Z.mul_split"
                | ident.Z_mul_high => neg_wrap_parens "Z.mul_high"
                | ident.Z_add_get_carry => neg_wrap_parens "Z.add_get_carry"
                | ident.Z_add_with_carry => neg_wrap_parens "Z.add_with_carry"
                | ident.Z_add_with_get_carry => neg_wrap_parens "Z.add_with_get_carry"
                | ident.Z_sub_get_borrow => neg_wrap_parens "Z.sub_get_borrow"
                | ident.Z_sub_with_get_borrow => neg_wrap_parens "Z.sub_with_get_borrow"
                | ident.Z_ltz => neg_wrap_parens "Z.ltz"
                | ident.Z_zselect => neg_wrap_parens "Z.zselect"
                | ident.Z_add_modulo => neg_wrap_parens "Z.add_modulo"
                | ident.Z_truncating_shiftl => neg_wrap_parens "Z.truncating_shiftl"
                | ident.Z_rshi => neg_wrap_parens "Z.rshi"
                | ident.Z_cc_m => neg_wrap_parens "Z.cc_m"
                | ident.Z_combine_at_bitwidth => neg_wrap_parens "Z.combine_at_bitwidth"
                | ident.Z_cast => neg_wrap_parens "Z.cast"
                | ident.Z_cast2 => neg_wrap_parens "Z.cast2"
                | ident.Build_zrange => neg_wrap_parens "Build_zrange"
                | ident.zrange_rect _ => neg_wrap_parens "zrange_rect"
                | ident.fancy_add => neg_wrap_parens "fancy.add"
                | ident.fancy_addc => neg_wrap_parens "fancy.addc"
                | ident.fancy_sub => neg_wrap_parens "fancy.sub"
                | ident.fancy_subb => neg_wrap_parens "fancy.subb"
                | ident.fancy_mulll => neg_wrap_parens "fancy.mulll"
                | ident.fancy_mullh => neg_wrap_parens "fancy.mullh"
                | ident.fancy_mulhl => neg_wrap_parens "fancy.mulhl"
                | ident.fancy_mulhh => neg_wrap_parens "fancy.mulhh"
                | ident.fancy_rshi => neg_wrap_parens "fancy.rshi"
                | ident.fancy_selc => neg_wrap_parens "fancy.selc"
                | ident.fancy_selm => neg_wrap_parens "fancy.selm"
                | ident.fancy_sell => neg_wrap_parens "fancy.sell"
                | ident.fancy_addm => neg_wrap_parens "fancy.addm"
                end.
        Global Instance show_ident {t} : Show (ident.ident t) := show_lvl_ident.

        (** N.B. Even though we are nominally printing Gallina
             identifiers here, we parenthesize bitwise operators much
             more frequently.  See, e.g.,
             https://github.com/mit-plv/fiat-crypto/pull/792#issuecomment-627647069,
             where Andres makes the point that in C, [+] binds more
             tightly than [<<]. *)

        Definition conservative_binop_precedence_table : list (string * (Associativity * Level))
          := [("*ℕ", (mul_assoc, mul_lvl))
              ; ("+ℕ", (add_assoc, add_lvl))
              ; ("-ℕ", (sub_assoc, sub_lvl))
              ; ("=ℕ", (NoAssoc, Level.level 70))
              ; ("*ℤ⁺", (mul_assoc, mul_lvl))
              ; ("+ℤ⁺", (add_assoc, add_lvl))
              ; ("::", (RightAssoc, Level.level 60))
              ; ("++", (FullyAssoc, Level.level 60))
              ; ("*", (mul_assoc, mul_lvl))
              ; ("/", (div_assoc, div_lvl))
              ; ("+", (add_assoc, add_lvl))
              ; ("-", (sub_assoc, sub_lvl))
              ; ("^", (pow_assoc, pow_lvl))
              ; ("⊕", (LeftAssoc, Level.level 50))
              ; ("mod", (LeftAssoc, Level.level 40))
              ; ("=", (NoAssoc, Level.level 70))
              ; ("<", (NoAssoc, Level.level 70))
              ; ("≤", (NoAssoc, Level.level 70))
              ; (">", (NoAssoc, Level.level 70))
              ; ("≥", (NoAssoc, Level.level 70))
              ; (">>", (ExplicitAssoc 35 35, Level.level 55))
              ; ("<<", (ExplicitAssoc 35 35, Level.level 55))
              ; ("&", (ExplicitAssoc 35 35, Level.level 55))
              ; ("|", (ExplicitAssoc 35 35, Level.level 55))
              ; (", ", (pair_assoc, pair_lvl))
             ].
        Definition conservative_preop_precedence_table : list (string * (Associativity * Level))
          := [("-", (RightAssoc, opp_lvl))
              ; ("!", (RightAssoc, Level.level 75))
            ].
        Definition conservative_postop_precedence_table : list (string * (Associativity * Level))
          := [(".+1", (LeftAssoc, app_lvl))
              ; (".-1", (LeftAssoc, app_lvl))
              ; ("₁", (LeftAssoc, Level.level 0))
              ; ("₂", (LeftAssoc, Level.level 0))
             ].

        Inductive Not_found := not_found.

        Class with_space_opt := with_space : bool.
        Global Instance with_space_default : with_space_opt | 1000 := true.

        Definition lookup_lvl (table : list (string * (Associativity * Level))) (op : string)
          := match List.find (fun '(op', _) => String.eqb op op') table as x return if x then Level else Not_found with
             | Some (_, (assoc, lvl)) => lvl
             | None => not_found
             end.
        Definition lookup_assoc (table : list (string * (Associativity * Level))) (op : string)
          := match List.find (fun '(op', _) => String.eqb op op') table as x return if x then Associativity else Not_found with
             | Some (_, (assoc, lvl)) => assoc
             | None => not_found
             end.
        Definition lookup_show_lvl_binop {with_space : bool} (table : list (string * (Associativity * Level))) (binop : string)
          := match List.find (fun '(binop', _) => String.eqb binop binop') table as x return if x then (Level -> string) -> (Level -> string) -> (Level -> string) else Not_found with
             | Some (_, (binop_assoc, binop_lvl)) => fun x y => show_lvl_binop binop_assoc binop_lvl x (if with_space then " " ++ binop ++ " " else binop) y
             | None => not_found
             end.
        Definition lookup_show_lvl_preop (table : list (string * (Associativity * Level))) (preop : string)
          := match List.find (fun '(op', _) => String.eqb preop op') table as x return if x then (Level -> string) -> (Level -> string) else Not_found with
             | Some (op, (op_assoc, op_lvl)) => fun x => show_lvl_preop_assoc op_assoc op_lvl op x
             | None => not_found
             end.
        Definition lookup_show_lvl_postop (table : list (string * (Associativity * Level))) (postop : string)
          := match List.find (fun '(op', _) => String.eqb postop op') table as x return if x then (Level -> string) -> (Level -> string) else Not_found with
             | Some (op, (op_assoc, op_lvl)) => fun x => show_lvl_postop_assoc op_assoc op_lvl x op
             | None => not_found
             end.
        (** We give the ident type [a -> b] to force patterns like [|
            ident.Nat_mul as idc => ident_to_binop_string idc] to bind
            [ident.Nat_mul] rather than the discriminee *)
        Definition ident_to_op_string {a b} (idc : ident.ident (a -> b)) : string
          := match idc with
             | ident.Nat_mul => "*ℕ"
             | ident.Nat_add => "+ℕ"
             | ident.Nat_sub => "-ℕ"
             | ident.Nat_eqb => "=ℕ"
             | ident.Pos_mul => "*ℤ⁺"
             | ident.Pos_add => "+ℤ⁺"
             | ident.cons _ => "::"
             | ident.List_app _ => "++"
             | ident.Z_mul => "*"
             | ident.Z_add => "+"
             | ident.Z_sub => "-"
             | ident.Z_pow => "^"
             | ident.Z_lxor => "⊕"
             | ident.Z_div => "/"
             | ident.Z_modulo => "mod"
             | ident.Z_eqb => "="
             | ident.Z_ltb => "<"
             | ident.Z_leb => "≤"
             | ident.Z_gtb => ">"
             | ident.Z_geb => "≥"
             | ident.Z_shiftr => ">>"
             | ident.Z_shiftl => "<<"
             | ident.Z_land => "&"
             | ident.Z_lor => "|"
             | ident.pair _ _ => ", "
             | ident.Nat_succ => ".+1"
             | ident.Nat_pred => ".-1"
             | ident.fst _ _ => "₁"
             | ident.snd _ _ => "₂"
             | ident.Z_opp => "-"
             | ident.Z_bneg => "!"
             | _ => ""
             end.

        Local Notation show_lvl_binop_no_space idc := (lookup_show_lvl_binop (with_space:=false) conservative_binop_precedence_table (ident_to_op_string idc)).
        Local Notation show_lvl_binop idc := (lookup_show_lvl_binop (with_space:=true) conservative_binop_precedence_table (ident_to_op_string idc)).
        Local Notation show_lvl_preop idc := (lookup_show_lvl_preop conservative_preop_precedence_table (ident_to_op_string idc)).
        Local Notation show_lvl_postop idc := (lookup_show_lvl_postop conservative_postop_precedence_table (ident_to_op_string idc)).

        Definition show_ident_lvl (with_casts : bool) (with_all_casts : bool) {t} (idc : ident.ident t)
          : type.for_each_lhs_of_arrow (fun t => (Level.Level -> string) * ZRange.type.option.interp t)%type t -> (Level.Level -> string) * ZRange.type.base.option.interp (type.final_codomain t)
          := let with_casts := (with_casts && negb with_all_casts)%bool in
             match idc in ident.ident t return type.for_each_lhs_of_arrow (fun t => (Level.Level -> string) * ZRange.type.option.interp t)%type t -> (Level.Level -> string) * ZRange.type.base.option.interp (type.final_codomain t) with
             | ident.Literal base.type.Z v => fun 'tt => (show_lvl_compact_Z v, ZRange.type.base.option.None)
             | ident.Literal t v => fun 'tt => (show_lvl v, ZRange.type.base.option.Some (t:=t) v)
             | ident.tt => fun _ => (fun _ => "()", tt)
             | ident.Nat_max as idc
               => fun '((x, xr), ((y, yr), tt)) => (show_lvl_app2 (show_lvl_ident idc) x y, ZRange.type.base.option.None)
             | ident.Nat_succ as idc
             | ident.Nat_pred as idc
               => fun '((x, xr), tt) => (show_lvl_postop idc x, ZRange.type.base.option.None)
             | ident.Z_opp as idc
             | ident.Z_bneg as idc
               => fun '((x, xr), tt) => (show_lvl_preop idc x, ZRange.type.base.option.None)
             | ident.Nat_mul as idc
             | ident.Nat_add as idc
             | ident.Nat_sub as idc
             | ident.Nat_eqb as idc
             | ident.Pos_mul as idc
             | ident.Pos_add as idc
             | ident.cons _ as idc
             | ident.List_app _ as idc
             | ident.Z_mul as idc
             | ident.Z_add as idc
             | ident.Z_sub as idc
             | ident.Z_pow as idc
             | ident.Z_lxor as idc
             | ident.Z_div as idc
             | ident.Z_modulo as idc
             | ident.Z_shiftr as idc
             | ident.Z_shiftl as idc
             | ident.Z_land as idc
             | ident.Z_lor as idc
               => fun '((x, xr), ((y, yr), tt)) => (show_lvl_binop idc x y, ZRange.type.base.option.None)
             | ident.Z_eqb as idc
             | ident.Z_ltb as idc
             | ident.Z_leb as idc
             | ident.Z_gtb as idc
             | ident.Z_geb as idc
               => fun '(x, (y, tt)) => (show_lvl_binop idc (maybe_wrap_cast with_casts x) (maybe_wrap_cast with_casts y), ZRange.type.base.option.None)
             | ident.pair _ _ as idc => fun '((x, xr), ((y, yr), tt)) => (show_lvl_binop_no_space idc x y, (xr, yr))
             | ident.fst _ _ as idc
               => fun '((x, xr), tt) => (show_lvl_postop idc x, fst xr)
             | ident.snd _ _ as idc
               => fun '((x, xr), tt) => (show_lvl_postop idc x, snd xr)
             | ident.None _ => fun 'tt => (neg_wrap_parens "None", ZRange.type.base.option.None)
             | ident.nil t => fun 'tt => (neg_wrap_parens "[]", ZRange.type.base.option.None)
             | ident.prod_rect A B T => fun '((f, fr), ((p, pr), tt)) => (neg_wrap_parens ("match " ++ show_lvl p term_lvl ++ " with " ++ show_lvl f term_lvl ++ " end"), ZRange.type.base.option.None)
             | ident.bool_rect _
             | ident.bool_rect_nodep _
               => fun '(t, (f, ((b, br), tt))) => (fun lvl => maybe_wrap_parens (Level.ltb lvl term_lvl) ("if " ++ show_lvl b term_lvl ++ " then " ++ maybe_wrap_cast with_casts t term_lvl ++ " else " ++ maybe_wrap_cast with_casts f term_lvl), ZRange.type.base.option.None)
             | ident.eager_List_nth_default _
               => fun '((d, dr), ((ls, lsr), ((i, ir), tt))) => (fun lvl => maybe_wrap_parens (Level.ltb lvl app_lvl) (show_lvl ls app_lvl ++ "[[" ++ show_lvl i term_lvl ++ "]]"), ZRange.type.base.option.None)
             | ident.List_nth_default _
               => fun '((d, dr), ((ls, lsr), ((i, ir), tt))) => (fun lvl => maybe_wrap_parens (Level.ltb lvl app_lvl) (show_lvl ls app_lvl ++ "[" ++ show_lvl i term_lvl ++ "]"), ZRange.type.base.option.None)
             | ident.Z_lnot_modulo => fun '((x, xr), ((m, mr), tt)) => (fun lvl => maybe_wrap_parens (Level.ltb lvl 75) ("~" ++ show_lvl x 75 ++ (if with_casts then " (mod " ++ show_lvl m term_lvl ++ ")" else "")), ZRange.type.base.option.None)
             | ident.Z_cast as idc
             | ident.Z_cast2 as idc
               => fun '((srange, range), ((x, xr), tt))
                  => let t := (fun t (idc : ident.ident (_ -> t -> _)) => t) _ idc in
                     (* if we don't do the above, we pick up the wrong type in maybe_wrap_cast below *)
                     (if with_all_casts && Option.is_None (ZRange.type.base.option.lift_Some range)
                      then (fun _ => "(" ++ srange term_lvl ++ ")" ++ x 0)
                      else maybe_wrap_cast (t:=t) with_all_casts (x, range),
                       range)
             | ident.Build_zrange
               => fun '((x, xr), ((y, yr), tt))
                  => (neg_wrap_parens ("r[" ++ show_lvl x 60 ++ " ~> " ++ show_lvl y term_lvl),
                       match ZRange.ident.option.to_literal xr, ZRange.ident.option.to_literal yr with
                       | Some l, Some h => Some r[l ~> h]
                       | _, _ => (*ZRange.type.base.option.*)None
                       end)
             | ident.comment _ as idc
             | ident.comment_no_keep _ as idc
             | ident.value_barrier as idc
             | ident.Some _ as idc
             | ident.nat_rect _ as idc
             | ident.eager_nat_rect _ as idc
             | ident.eager_nat_rect_arrow _ _ as idc
             | ident.nat_rect_arrow _ _ as idc
             | @ident.nat_rect_fbb_b    _ _ _ as idc
             | @ident.nat_rect_fbb_b_b  _ _ _ _ as idc
             | @ident.list_rect_fbb_b   _ _ _ _ as idc
             | @ident.list_rect_fbb_b_b _ _ _ _ _ as idc
             | @ident.list_rect_fbb_b_b_b _ _ _ _ _ _ as idc
             | @ident.list_rect_fbb_b_b_b_b _ _ _ _ _ _ _ as idc
             | @ident.list_rect_fbb_b_b_b_b_b  _ _ _ _ _ _ _ _ as idc
             | ident.option_rect _ _ as idc
             | ident.list_rect _ _ as idc
             | ident.eager_list_rect _ _ as idc
             | ident.list_rect_arrow _ _ _ as idc
             | ident.eager_list_rect_arrow _ _ _ as idc
             | ident.list_case _ _ as idc
             | ident.List_length _ as idc
             | ident.List_seq as idc
             | ident.List_repeat _ as idc
             | ident.List_firstn _ as idc
             | ident.List_skipn _ as idc
             | ident.List_combine _ _ as idc
             | ident.List_map _ _ as idc
             | ident.List_rev _ as idc
             | ident.List_flat_map _ _ as idc
             | ident.List_partition _ as idc
             | ident.List_filter _ as idc
             | ident.List_fold_right _ _ as idc
             | ident.List_update_nth _ as idc
             | ident.Z_log2 as idc
             | ident.Z_log2_up as idc
             | ident.Z_of_nat as idc
             | ident.Z_to_nat as idc
             | ident.Z_pos as idc
             | ident.Z_to_pos as idc
             | ident.Z_min as idc
             | ident.Z_max as idc
             | ident.Z_abs as idc
             | ident.Z_mul_split as idc
             | ident.Z_mul_high as idc
             | ident.Z_add_get_carry as idc
             | ident.Z_add_with_carry as idc
             | ident.Z_add_with_get_carry as idc
             | ident.Z_sub_get_borrow as idc
             | ident.Z_sub_with_get_borrow as idc
             | ident.Z_ltz as idc
             | ident.Z_zselect as idc
             | ident.Z_add_modulo as idc
             | ident.Z_truncating_shiftl as idc
             | ident.Z_rshi as idc
             | ident.Z_cc_m as idc
             | ident.Z_combine_at_bitwidth as idc
             | ident.zrange_rect _ as idc
             | ident.fancy_add as idc
             | ident.fancy_addc as idc
             | ident.fancy_sub as idc
             | ident.fancy_subb as idc
             | ident.fancy_mulll as idc
             | ident.fancy_mullh as idc
             | ident.fancy_mulhl as idc
             | ident.fancy_mulhh as idc
             | ident.fancy_rshi as idc
             | ident.fancy_selc as idc
             | ident.fancy_selm as idc
             | ident.fancy_sell as idc
             | ident.fancy_addm as idc
               => fun args => (show_application with_casts (fun _ => show idc) args, ZRange.type.base.option.None)
             end.
      End ident.

      Module expr.
        Local Notation show_ident := ident.show_ident.
        Local Notation show_ident_lvl := ident.show_ident_lvl.
        Fixpoint get_eta_cps_args {A} (t : type) (idx : positive) {struct t}
          : (type.for_each_lhs_of_arrow (fun y => (Level -> string) * ZRange.type.option.interp y)%type t -> positive -> A) -> list string * A
          := match t with
             | type.arrow s d
               => fun k
                  => let n := "x" ++ Decimal.Pos.to_string idx in
                     let '(args, show_f) := @get_eta_cps_args A d (Pos.succ idx) (fun arglist => k (((fun _ => n), ZRange.type.option.None), arglist)) in
                     (n :: args, show_f)
             | type.base _
               => fun k => (nil, k tt idx)
             end.
        Section helper.
          Context {var}
                  (of_string : forall t, string -> option (var t))
                  (k : forall t, @API.expr var t -> type.for_each_lhs_of_arrow (fun t => (Level -> string) * ZRange.type.option.interp t)%type t -> positive -> (positive * (Level -> list string)) * ZRange.type.base.option.interp (type.final_codomain t)).
          Definition show_eta_abs_aux
              (aux : forall t (idx : positive) (e : @API.expr var t),
                     (positive * (list string * (Level -> list string))) * ZRange.type.base.option.interp (type.final_codomain t))
              s d (idx : positive) (f : var s -> @API.expr var d)
            : (positive * (list string * (Level -> list string))) * ZRange.type.base.option.interp (type.final_codomain d)
            := let n := match s with
                        | type.base base.type.unit => "()_" ++ Decimal.Pos.to_string idx
                        | _ => "x" ++ Decimal.Pos.to_string idx
                        end in
               match of_string s n with
               | Some n'
                 => let '(_, (args, show_f), r) := aux d (Pos.succ idx) (f n') in
                    (idx,
                     (n :: args, show_f),
                     r)
               | None
                 => (idx,
                     ([n], (fun _ => ["λ_(" ++ show s ++ ")"])),
                     ZRange.type.base.option.None)
               end.
          Fixpoint show_eta_abs_cps' {t} (idx : positive) (e : @API.expr var t)
            : (positive * (list string * (Level -> list string))) * ZRange.type.base.option.interp (type.final_codomain t)
            := match e in expr.expr t return (unit -> _ * ZRange.type.base.option.interp (type.final_codomain t)) -> _ * ZRange.type.base.option.interp (type.final_codomain t) with
               | expr.Abs s d f
                 => fun _
                    => show_eta_abs_aux (@show_eta_abs_cps') s d idx f
               | _
                 => fun default
                    => default tt
               end (fun _
                    => let '(args, (idx, show_f, r)) := get_eta_cps_args _ idx (@k _ e) in
                       ((idx, (args, show_f)), r)).
          Definition show_eta_abs_cps (with_casts : bool) {s d} (idx : positive) (f : var s -> @API.expr var d) (extraargs : type.for_each_lhs_of_arrow (fun t => (Level -> string) * ZRange.type.option.interp t)%type (s -> d))
            : (positive * (Level -> list string)) * ZRange.type.base.option.interp (type.final_codomain d)
            := let '(idx, (args, show_f), r) := show_eta_abs_aux (@show_eta_abs_cps') s d idx f in
               let argstr := String.concat " " args in
               (idx,
                fun lvl
                => match show_f lvl with
                   | nil => [show_application with_casts (fun _ => "(λ " ++ argstr ++ ", (* NOTHING‽ *))") extraargs (Level.prev app_lvl)]%string
                   | show_f::nil
                     => [show_application with_casts (fun _ => "(λ " ++ argstr ++ ", " ++ show_f ++ ")") extraargs (Level.prev app_lvl)]%string
                   | show_f
                     => ["(λ " ++ argstr ++ ","]%string ++ (List.map (fun v => String " " (String " " v)) show_f) ++ [")" ++ show_application with_casts (fun _ => "") extraargs (Level.prev app_lvl)]%string
                   end%list,
                   r).
          Definition show_eta_cps {t} (idx : positive) (e : @API.expr var t)
            : (positive * (Level -> list string)) * ZRange.type.option.interp t
            := let '(idx, (args, show_f), r) := @show_eta_abs_cps' t idx e in
               let argstr := String.concat " " args in
               (idx,
                (fun lvl
                 => match args, show_f lvl with
                    | nil, show_f => show_f
                    | _, nil => ["(λ " ++ argstr ++ ", (* NOTHING‽ *))"]%string
                    | _, show_f::nil
                      => ["(λ " ++ argstr ++ ", " ++ show_f ++ ")"]%string
                    | _, show_f
                      => ["(λ " ++ argstr ++ ","]%string ++ (List.map (fun v => String " " (String " " v)) show_f) ++ [")"]
                    end%list),
                match t return ZRange.type.base.option.interp (type.final_codomain t) -> ZRange.type.option.interp t with
                | type.base _ => fun r => r
                | type.arrow _ _ => fun _ => ZRange.type.option.None
                end r).
        End helper.

        Fixpoint show_expr_lines_gen (with_casts : bool) (with_all_casts : bool) {var} (to_string : forall t, var t -> string) (of_string : forall t, string -> option (var t)) {t} (e : @API.expr var t) (args : type.for_each_lhs_of_arrow (fun t => (Level -> string) * ZRange.type.option.interp t)%type t) (idx : positive) {struct e} : (positive * (Level -> list string)) * ZRange.type.base.option.interp (type.final_codomain t)
          := let show_expr_lines_gen := @show_expr_lines_gen with_casts with_all_casts var to_string of_string in
             match e in expr.expr t return type.for_each_lhs_of_arrow (fun t => (Level -> string) * ZRange.type.option.interp t)%type t -> (positive * (Level -> list string)) * ZRange.type.base.option.interp (type.final_codomain t) with
             | expr.Ident t idc
               => fun args => let '(v, r) := @show_ident_lvl with_casts with_all_casts t idc args in
                              (idx, fun lvl => [v lvl], r)
             | expr.Var t v
               => fun args => (idx, fun lvl => [show_application with_casts (fun _ => to_string _ v) args lvl], ZRange.type.base.option.None)
             | expr.Abs s d f
               => fun args
                  => show_eta_abs_cps of_string (fun t e args idx => let '(idx, v, r) := @show_expr_lines_gen t e args idx in (idx, fun _ => v term_lvl, r)) with_casts idx f args
             | expr.App s d f x
               => fun args
                  => let '(idx', x', xr) := show_eta_cps of_string (fun t e args idx => @show_expr_lines_gen t e args idx) idx x in
                     @show_expr_lines_gen
                       _ f
                       (((fun lvl => String.concat String.NewLine (x' lvl)), xr),
                         args)
                       idx
             | expr.LetIn A (type.base B) x f
               => fun 'tt
                  => let n := "x" ++ Decimal.Pos.to_string idx in
                     let '(_, show_x, xr) := show_eta_cps of_string (fun t e args idx => @show_expr_lines_gen t e args idx) idx x in
                     let '(idx, show_f, fr)
                       := match of_string A n with
                          | Some n' => show_eta_cps of_string (fun t e args idx => @show_expr_lines_gen t e args idx) (Pos.succ idx) (f n')
                          | None => (idx, (fun _ => ["_"]), ZRange.type.option.None)
                          end in
                     let '(ty_str, comment_ty_str, space_comment_ty_str)
                       := match make_cast xr with
                          | Some c => let ty_str := " : " ++ c in
                                      let comment_ty_str := "(*" ++ ty_str ++ " *)" in
                                      (ty_str, comment_ty_str, " " ++ comment_ty_str)
                          | None => ("", "", "")
                          end in
                     let expr_let_line := "let " ++ n ++ " := " in
                     (idx,
                       (fun lvl
                        => match show_x term_lvl with
                           | nil => [expr_let_line ++ "(* NOTHING‽ *)" ++ space_comment_ty_str ++ " in"]%string ++ show_f term_lvl
                          | show_x::nil => [expr_let_line ++ show_x ++ "" ++ space_comment_ty_str ++ " in"]%string ++ show_f term_lvl
                          | show_x::rest
                            => ([expr_let_line ++ show_x]%string)
                                 ++ (List.map (fun l => String.string_of_list_ascii (List.repeat " "%char (String.length expr_let_line)) ++ l)%string
                                              rest)
                                 ++ (if ty_str =? "" then ["(*" ++ ty_str ++ " *)"] else [])%string
                                 ++ ["in"]
                                 ++ show_f term_lvl
                          end%list),
                      fr)
             | expr.LetIn A B x f
               => fun args
                  => let n := "x" ++ Decimal.Pos.to_string idx in
                     let '(_, show_x, xr) := show_eta_cps of_string (fun t e args idx => @show_expr_lines_gen t e args idx) idx x in
                     let '(idx, show_f, fr)
                         := match of_string A n with
                            | Some n' => show_eta_cps of_string (fun t e args idx => @show_expr_lines_gen t e args idx) (Pos.succ idx) (f n')
                            | None => (idx, (fun _ => ["_"]), ZRange.type.option.None)
                            end in
                     let '(ty_str, comment_ty_str, space_comment_ty_str)
                         := match make_cast xr with
                            | Some c => let ty_str := " : " ++ c in
                                        let comment_ty_str := "(*" ++ ty_str ++ " *)" in
                                        (ty_str, comment_ty_str, " " ++ comment_ty_str)
                            | None => ("", "", "")
                            end in
                     let expr_let_line := "let " ++ n ++ " := " in
                     (idx,
                      (fun lvl
                       => (["("]
                             ++ (map
                                   (String " ")
                                   match show_x term_lvl with
                                   | nil => [expr_let_line ++ "(* NOTHING‽ *)" ++ space_comment_ty_str ++ " in"]%string ++ show_f term_lvl
                                   | show_x::nil => [expr_let_line ++ show_x ++ "" ++ space_comment_ty_str ++ " in"]%string ++ show_f term_lvl
                                   | show_x::rest
                                     => ([expr_let_line ++ show_x]%string)
                                          ++ (List.map (fun l => String.string_of_list_ascii (List.repeat " "%char (String.length expr_let_line)) ++ l)%string
                                                       rest)
                                          ++ (if ty_str =? "" then ["(*" ++ ty_str ++ " *)"] else [])%string
                                          ++ ["in"]
                                          ++ show_f term_lvl
                                   end%list)
                             ++ [")"; show_application with_casts (fun _ => "") args (Level.prev app_lvl)])%list),
                      ZRange.type.base.option.None)
             end args.
        Definition show_expr_lines (with_casts : bool) (with_all_casts : bool) {t} (e : @API.expr (fun _ => string) t) (args : type.for_each_lhs_of_arrow (fun t => (Level -> string) * ZRange.type.option.interp t)%type t) (idx : positive) : (positive * (Level -> list string)) * ZRange.type.base.option.interp (type.final_codomain t)
          := @show_expr_lines_gen with_casts with_all_casts (fun _ => string) (fun _ x => x) (fun _ x => Some x) t e args idx.
        Definition show_lvl_var_expr : forall {var t}, ShowLevel (@API.expr var t)
          := fix show_lvl_var_expr {var t} (e : @API.expr var t) : Level -> string
               := match e with
                  | expr.Ident t idc => show_lvl idc
                  | expr.Var t v => neg_wrap_parens ("VAR_" ++ show_lvl t 0)
                  | expr.Abs s d f => neg_wrap_parens ("λ_" ++ show_lvl t 0)
                  | expr.App s d f x => show_lvl_binop LeftAssoc app_lvl (show_lvl_var_expr f) " @ " (show_lvl_var_expr x)
                  | expr.LetIn A B x f
                    => fun lvl => maybe_wrap_parens (Level.ltb lvl term_lvl) ("expr_let _ := " ++ show_lvl_var_expr x term_lvl ++ " in _")
                  end%string.
        Definition show_var_expr {var t} : Show (@API.expr var t) := show_lvl_var_expr.
        Definition partially_show_expr {var t} : Show (@API.expr var t) := show_var_expr.
        Section Show_gen.
          Context {with_casts : PHOAS.with_casts}
                  {with_all_casts : PHOAS.with_all_casts}
                  {var : API.type -> Type}
                  (to_string : forall t, var t -> string)
                  (of_string : forall t, string -> option (var t)).

          Definition show_lines_expr_gen {t} : ShowLines (@API.expr var t)
            := fun e => let '(_, v, _) := show_eta_cps of_string (fun t e args idx => @show_expr_lines_gen with_casts with_all_casts var to_string of_string t e args idx) 1%positive e in v (Level.prev term_lvl).
          Definition show_expr_gen {t} : Show (@API.expr var t)
            := fun e => String.concat String.NewLine (show_lines_expr_gen e).
        End Show_gen.
        Global Instance show_lines_expr {with_casts : PHOAS.with_casts} {with_all_casts : PHOAS.with_all_casts} {t} : ShowLines (@API.expr (fun _ => string) t)
          := @show_lines_expr_gen with_casts with_all_casts (fun _ => string) (fun _ x => x) (fun _ x => Some x) t.
        Global Instance show_lines_Expr {with_casts : PHOAS.with_casts} {with_all_casts : PHOAS.with_all_casts} {t} : ShowLines (@API.Expr t)
          := fun e => show_lines (e _).
        Global Instance show_expr {with_casts : PHOAS.with_casts} {with_all_casts : PHOAS.with_all_casts} {t} : Show (@API.expr (fun _ => string) t)
          := fun e => String.concat String.NewLine (show_lines e).
        Global Instance show_Expr {with_casts : PHOAS.with_casts} {with_all_casts : PHOAS.with_all_casts} {t} : Show (@API.Expr t)
          := fun e => show (e _).
      End expr.
    End PHOAS.

    Definition LinesToString (lines : list string)
      : string
      := String.concat String.NewLine lines.

    Definition format_typedef_name
               {language_naming_conventions : language_naming_conventions_opt}
               (prefix : string)
               (private : bool)
               (name : string)
      : string
      := convert_to_naming_convention (if private then private_type_naming_convention else public_type_naming_convention) (prefix ++ name).

    Module int.
      Inductive type := signed (lgbitwidth : nat) | unsigned (lgbitwidth : nat).

      Definition lgbitwidth_of (t : type) : nat
        := match t with
           | signed lgbitwidth => lgbitwidth
           | unsigned lgbitwidth => lgbitwidth
           end.
      Definition of_lgbitwidth (is_signed : bool) (lgbitwidth : nat) : type
        := if is_signed then signed lgbitwidth else unsigned lgbitwidth.
      Definition bitwidth_of (t : type) : Z := 2^Z.of_nat (lgbitwidth_of t).
      Definition of_bitwidth (is_signed : bool) (bitwidth : Z) : type
        := of_lgbitwidth is_signed (Z.to_nat (Z.log2 bitwidth)).
      Definition of_bitwidth_up (is_signed : bool) (bitwidth : Z) : type
        := of_lgbitwidth is_signed (Z.to_nat (Z.log2_up bitwidth)).
      Definition is_signed (t : type) : bool := match t with signed _ => true | unsigned _ => false end.
      Definition is_unsigned (t : type) : bool := negb (is_signed t).
      Definition to_zrange (t : type) : zrange
        := let bw := bitwidth_of t in
           if is_signed t
           then r[-2^(bw-1) ~> 2^(bw-1) - 1]
           else r[0 ~> 2^bw - 1].
      Definition is_tighter_than (t1 t2 : type)
        := ZRange.is_tighter_than_bool (to_zrange t1) (to_zrange t2).
      Definition of_zrange_relaxed (r : zrange) : type
        := let lg2 := Z.log2_up ((upper r - lower r) + 1) in
           let lg2u := Z.log2_up (upper r + 1) in
           let lg2l := (if (lower r <? 0) then 1 + Z.log2_up (-lower r) else 0) in
           let lg2 := Z.max lg2 (Z.max lg2u lg2l) in
           let lg2lg2u := Z.log2_up lg2 in
           if (0 <=? lower r)
           then unsigned (Z.to_nat lg2lg2u)
           else signed (Z.to_nat lg2lg2u).
      Definition of_zrange (r : zrange) : option type
        := let t := of_zrange_relaxed r in
           let r' := to_zrange t in
           if (r' =? r)%zrange
           then Some t
           else None.
      Definition unsigned_counterpart_of (t : type) : type
        := unsigned (lgbitwidth_of t).
      Definition signed_counterpart_of (t : type) : type
        := signed (lgbitwidth_of t).

      Lemma bitwidth_of_pos v : 0 < bitwidth_of v.
      Proof. cbv [bitwidth_of]; apply Z.pow_pos_nonneg; lia. Qed.

      Lemma of_lgbitwidth_of v : of_lgbitwidth (is_signed v) (lgbitwidth_of v) = v.
      Proof. case v; reflexivity. Qed.

      Lemma lgbitwidth_of_lgbitwidth b v : lgbitwidth_of (of_lgbitwidth b v) = v.
      Proof. case b; reflexivity. Qed.

      Lemma is_signed_of_lgbitwidth b v : is_signed (of_lgbitwidth b v) = b.
      Proof. case b; reflexivity. Qed.

      Lemma of_bitwidth_of v : of_bitwidth (is_signed v) (bitwidth_of v) = v.
      Proof.
        cbv [of_bitwidth bitwidth_of].
        rewrite Z.log2_pow2, Nat2Z.id by lia.
        apply of_lgbitwidth_of.
      Qed.

      Lemma of_bitwidth_up_of v : of_bitwidth_up (is_signed v) (bitwidth_of v) = v.
      Proof.
        cbv [of_bitwidth_up bitwidth_of].
        rewrite Z.log2_up_pow2, Nat2Z.id by lia.
        apply of_lgbitwidth_of.
      Qed.

      Lemma is_signed_of_bitwidth b v : is_signed (of_bitwidth b v) = b.
      Proof. apply is_signed_of_lgbitwidth. Qed.

      Lemma is_signed_of_bitwidth_up b v : is_signed (of_bitwidth_up b v) = b.
      Proof. apply is_signed_of_lgbitwidth. Qed.

      Global Instance show_lvl_type : ShowLevel type
        := fun t => neg_wrap_parens ((if is_unsigned t then "u" else "") ++ "int" ++ Decimal.Z.to_string (bitwidth_of t)).
      Global Instance show_type : Show type := show_lvl_type.

      Definition to_string_gen
                 {language_naming_conventions : language_naming_conventions_opt}
                 (standard_bitwidths : list Z)
                 (unsigned_s signed_s : string)
                 (standard_postfix special_postfix : string)
                 (private : bool) (prefix : string)
                 (t : type)
        : string
        := let is_standard := existsb (Z.eqb (bitwidth_of t)) standard_bitwidths in
           (if is_standard
            then (fun s => s)
            else (fun s => convert_to_naming_convention
                             (if private then private_type_naming_convention else public_type_naming_convention)
                             (prefix ++ s)))
             ((if is_unsigned t then unsigned_s else signed_s)
                ++ Decimal.Z.to_string (ToString.int.bitwidth_of t)
                ++ (if is_standard then standard_postfix else special_postfix)).

      Definition to_string_gen_opt_typedef
                 {language_naming_conventions : language_naming_conventions_opt}
                 {skip_typedefs : skip_typedefs_opt}
                 (standard_bitwidths : list Z)
                 (unsigned_s signed_s : string)
                 (standard_postfix special_postfix : string)
                 (private : bool) (typedef_private : bool) (prefix : string)
                 (t : type)
                 (typedef : option string)
        : string
        := match (if skip_typedefs then None else typedef) with
           | Some typedef => format_typedef_name prefix typedef_private typedef
           | None => to_string_gen standard_bitwidths unsigned_s signed_s standard_postfix special_postfix private prefix t
           end.

      Definition union (t1 t2 : type) : type := of_zrange_relaxed (ZRange.union (to_zrange t1) (to_zrange t2)).

      Definition union_zrange (r : zrange) (t : type) : type
        := of_zrange_relaxed (ZRange.union r (to_zrange t)).

      Fixpoint base_interp (t : base.type) : Set
        := match t with
           | base.type.type_base base.type.Z => type
           | base.type.type_base _
           | base.type.unit
             => unit
           | base.type.prod A B => base_interp A * base_interp B
           | base.type.list A => list (base_interp A)
           | base.type.option A => option (base_interp A)
           end%type.

      Module base_interp.
        Fixpoint of_zrange_relaxed {t : base.type} : ZRange.type.base.interp t -> base_interp t
          := match t with
             | base.type.type_base base.type.Z => int.of_zrange_relaxed
             | base.type.type_base _
             | base.type.unit
               => fun _ => tt
             | base.type.prod A B => fun '(a, b) => (@of_zrange_relaxed A a, @of_zrange_relaxed B b)
             | base.type.list A => List.map (@of_zrange_relaxed A)
             | base.type.option A => option_map (@of_zrange_relaxed A)
             end.

        Fixpoint to_union {t : base.type} : base_interp t -> option type
          := match t with
             | base.type.type_base base.type.Z => fun r => Some r
             | base.type.type_base _
             | base.type.unit
               => fun 'tt => None
             | base.type.prod A B => fun '(a, b) => (a <- @to_union A a; b <- @to_union B b; Some (union a b))
             | base.type.list A
               => fun ls
                  => (ls <-- List.map (@to_union A) ls;
                     match ls with
                     | nil => None
                     | cons x xs => Some (List.fold_right union x xs)
                     end)
             | base.type.option A => fun x => (x <- option_map (@to_union A) x; x)
             end%option.
      End base_interp.

      Module option.
        Fixpoint interp (t : base.type) : Set
          := match t with
             | base.type.type_base base.type.Z => option type
             | base.type.type_base _
             | base.type.unit
               => unit
             | base.type.prod A B => interp A * interp B
             | base.type.list A => option (list (interp A))
             | base.type.option A => option (option (interp A))
             end%type.

        Module interp.
          Fixpoint to_zrange {t : base.type} : interp t -> ZRange.type.base.option.interp t
            := match t with
               | base.type.type_base base.type.Z => option_map int.to_zrange
               | base.type.type_base _
                 => fun 'tt => None
               | base.type.unit
                 => fun 'tt => tt
               | base.type.prod A B => fun '(a, b) => (@to_zrange A a, @to_zrange B b)
               | base.type.list A => option_map (List.map (@to_zrange A))
               | base.type.option A => option_map (option_map (@to_zrange A))
               end.
          Fixpoint of_zrange_relaxed {t : base.type} : ZRange.type.base.option.interp t -> interp t
            := match t with
               | base.type.type_base base.type.Z => option_map int.of_zrange_relaxed
               | base.type.type_base _
               | base.type.unit
                 => fun _ => tt
               | base.type.prod A B => fun '(a, b) => (@of_zrange_relaxed A a, @of_zrange_relaxed B b)
               | base.type.list A => option_map (List.map (@of_zrange_relaxed A))
               | base.type.option A => option_map (option_map (@of_zrange_relaxed A))
               end.
        Fixpoint to_union {t : base.type} : interp t -> option type
          := match t return interp t -> option type with
             | base.type.type_base base.type.Z => fun r => r
             | base.type.type_base _
             | base.type.unit
               => fun 'tt => None
             | base.type.prod A B => fun '(a, b) => (a <- @to_union A a; b <- @to_union B b; Some (union a b))
             | base.type.list A
               => fun ls
                  => (ls <- ls;
                     ls <-- List.map (@to_union A) ls;
                     match ls with
                     | nil => None
                     | cons x xs => Some (List.fold_right union x xs)
                     end)
             | base.type.option A => fun x => (x <- x; x <- option_map (@to_union A) x; x)
             end%option.
        End interp.
        Fixpoint None {t} : interp t
          := match t with
             | base.type.type_base base.type.Z => Datatypes.None
             | base.type.type_base _
             | base.type.unit
               => tt
             | base.type.prod A B => (@None A, @None B)
             | base.type.list A => Datatypes.None
             | base.type.option A => Datatypes.None
             end.
        Fixpoint Some {t} : base_interp t -> interp t
          := match t with
             | base.type.type_base base.type.Z => Datatypes.Some
             | base.type.type_base _
             | base.type.unit
               => fun tt => tt
             | base.type.prod A B => fun '(a, b) => (@Some A a, @Some B b)
             | base.type.list A => fun ls => Datatypes.Some (List.map (@Some A) ls)
             | base.type.option A => fun ls => Datatypes.Some (Option.map (@Some A) ls)
             end.
      End option.

      Module Export Notations.
        Notation _Bool := (unsigned 0).
        Notation uint8 := (unsigned 3).
        Notation int8 := (signed 3).
        Notation uint16 := (unsigned 4).
        Notation int16 := (signed 4).
        Notation uint32 := (unsigned 5).
        Notation int32 := (signed 5).
        Notation uint64 := (unsigned 6).
        Notation int64 := (signed 6).
        Notation uint128 := (unsigned 7).
        Notation int128 := (signed 7).
      End Notations.
    End int.
    Import int.Notations.

    Example of_zrange_int32 : int.of_zrange_relaxed r[-2^31 ~> 2^31-1] = int32 := eq_refl.
    Example of_zrange_int64 : int.of_zrange_relaxed r[-2^31-1 ~> 2^31-1] = int64 := eq_refl.
    Example of_zrange_int64' : int.of_zrange_relaxed r[-2^31 ~> 2^31] = int64 := eq_refl.
    Example of_zrange_uint32 : int.of_zrange_relaxed r[0 ~> 2^32-1] = uint32 := eq_refl.
    Example of_zrange_uint64 : int.of_zrange_relaxed r[0 ~> 2^32] = uint64 := eq_refl.

    Module SumPositiveSet := SumSets PositiveSet PositiveSet.

    Module IntAsDecidableType <: IsoDecidableType SumPositiveSet.E.
      Definition t := int.type.
      Definition eq : t -> t -> Prop := eq.
      Definition eq_equiv : Equivalence eq := _.
      Definition eq_dec := int.type_eq_dec.
      Definition to_ (v : t) : positive + positive
        := (if int.is_signed v then inl else inr)
             (Pos.of_succ_nat (int.lgbitwidth_of v)).
      Definition of_ (v : positive + positive) : t
        := let is_signed := match v with inl _ => true | inr _ => false end in
           let lgbitwidth := match v with inl v => v | inr v => v end in
           int.of_lgbitwidth is_signed (Nat.pred (Pos.to_nat lgbitwidth)).
      Lemma of_to v : of_ (to_ v) = v.
      Proof.
        destruct v; cbv [of_ to_]; cbn;
          now rewrite SuccNat2Pos.pred_id.
      Qed.
      Lemma to_of v : SumPositiveSet.E.eq (to_ (of_ v)) v.
      Proof.
        destruct v; cbv [of_ to_ SumPositiveSet.E.eq sumwise];
          rewrite int.lgbitwidth_of_lgbitwidth, int.is_signed_of_lgbitwidth;
          f_equal;
          lia.
      Qed.
      Global Instance Proper_to_ : Proper (eq ==> SumPositiveSet.E.eq) to_.
      Proof. cbv [eq]; intros ???; subst; reflexivity. Qed.
      Global Instance Proper_of_ : Proper (SumPositiveSet.E.eq ==> eq) of_.
      Proof. cbv [eq SumPositiveSet.E.eq sumwise]; intros [?|?] [?|?] ?; subst; tauto. Qed.
    End IntAsDecidableType.

    Module IntSet <: WSets := IsoWSets SumPositiveSet IntAsDecidableType.
    Module Import IntSetShow := ShowWSets IntSet.
    Global Instance show_IntSet : Show IntSet.t := _.
    Global Instance show_lines_IntSet : ShowLines IntSet.t := _.

    Notation typedef_info := (string (* name *) * (string -> string) (* description *) * option int.type * { t : base.type & ZRange.type.base.option.interp t } (* bounds *))%type.

    (* Work around COQBUG(https://github.com/coq/coq/issues/11942) *)
    Local Unset Decidable Equality Schemes.
    Record ident_infos :=
      { bitwidths_used : IntSet.t;
        addcarryx_lg_splits : PositiveSet.t;
        mulx_lg_splits : PositiveSet.t;
        cmovznz_bitwidths : IntSet.t;
        value_barrier_bitwidths : IntSet.t;
        typedefs_used : list string (* typedef name *);
      }.
    Local Set Decidable Equality Schemes.
    Global Instance show_lines_ident_infos : ShowLines ident_infos
      := fun v
         => ["{| bitwidths_used := " ++ show (bitwidths_used v)
             ; " ; addcarryx_lg_splits := " ++ show (addcarryx_lg_splits v)
             ; " ; mulx_lg_splits := " ++ show (mulx_lg_splits v)
             ; " ; cmovznz_bitwidths := " ++ show (cmovznz_bitwidths v)
             ; " ; value_barrier_bitwidths := " ++ show (value_barrier_bitwidths v)
             ; " ; typedefs_used := " ++ show (typedefs_used v) ++ " |}"].
    Global Instance show_ident_infos : Show ident_infos
      := fun v => String.concat "" (show_lines v).
    Global Instance show_lvl_ident_infos : ShowLevel ident_infos
      := fun v => neg_wrap_parens (show_ident_infos v).
    Local Notation typedef_beq := String.eqb (only parsing).
    Local Notation typedefs_diff x y := (List.filter (fun v => negb (existsb (typedef_beq v) y)) x).
    Definition ident_infos_equal (x y : ident_infos) : bool
      := let (x0, x1, x2, x3, x4, x5) := x in
         let (y0, y1, y2, y3, y4, y5) := y in
         List.fold_right
           andb true
           [IntSet.equal x0 y0
            ; PositiveSet.equal x1 y1
            ; PositiveSet.equal x2 y2
            ; IntSet.equal x3 y3
            ; IntSet.equal x4 y4
            ; list_beq _ typedef_beq x5 y5 ].
    Definition ident_info_empty : ident_infos
      := Build_ident_infos IntSet.empty PositiveSet.empty PositiveSet.empty IntSet.empty IntSet.empty [].
    Definition ident_info_diff (x y : ident_infos) : ident_infos
      := let (x0, x1, x2, x3, x4, x5) := x in
         let (y0, y1, y2, y3, y4, y5) := y in
         Build_ident_infos
           (IntSet.diff x0 y0)
           (PositiveSet.diff x1 y1)
           (PositiveSet.diff x2 y2)
           (IntSet.diff x3 y3)
           (IntSet.diff x4 y4)
           (typedefs_diff x5 y5).
    Definition ident_info_diff_except_bitwidths (x y : ident_infos) : ident_infos
      := let (x0, x1, x2, x3, x4, x5) := x in
         let (y0, y1, y2, y3, y4, y5) := y in
         Build_ident_infos
           x0
           (PositiveSet.diff x1 y1)
           (PositiveSet.diff x2 y2)
           (IntSet.diff x3 y3)
           (IntSet.diff x4 y4)
           (typedefs_diff x5 y5).
    Definition ident_info_union (x y : ident_infos) : ident_infos
      := let (x0, x1, x2, x3, x4, x5) := x in
         let (y0, y1, y2, y3, y4, y5) := y in
         Build_ident_infos
           (IntSet.union x0 y0)
           (PositiveSet.union x1 y1)
           (PositiveSet.union x2 y2)
           (IntSet.union x3 y3)
           (IntSet.union x4 y4)
           (x5 ++ typedefs_diff y5 x5).
    Definition ident_info_of_bitwidths_used (v : IntSet.t) : ident_infos
      := {| bitwidths_used := v;
            addcarryx_lg_splits := PositiveSet.empty;
            mulx_lg_splits := PositiveSet.empty;
            cmovznz_bitwidths := IntSet.empty;
            value_barrier_bitwidths := IntSet.empty;
            typedefs_used := [] |}.
    Definition ident_info_of_addcarryx (v : PositiveSet.t) : ident_infos
      := {| bitwidths_used := IntSet.empty;
            addcarryx_lg_splits := v;
            mulx_lg_splits := PositiveSet.empty;
            cmovznz_bitwidths := IntSet.empty;
            value_barrier_bitwidths := IntSet.empty;
            typedefs_used := [] |}.
    Definition ident_info_of_mulx (v : PositiveSet.t) : ident_infos
      := {| bitwidths_used := IntSet.empty;
            addcarryx_lg_splits := PositiveSet.empty;
            mulx_lg_splits := v;
            cmovznz_bitwidths := IntSet.empty;
            value_barrier_bitwidths := IntSet.empty;
            typedefs_used := [] |}.
    Definition ident_info_of_cmovznz (v : IntSet.t) : ident_infos
      := {| bitwidths_used := IntSet.empty;
            addcarryx_lg_splits := PositiveSet.empty;
            mulx_lg_splits := PositiveSet.empty;
            cmovznz_bitwidths := v;
            value_barrier_bitwidths := IntSet.empty;
            typedefs_used := [] |}.
    Definition ident_info_of_value_barrier (v : IntSet.t) : ident_infos
      := {| bitwidths_used := IntSet.empty;
            addcarryx_lg_splits := PositiveSet.empty;
            mulx_lg_splits := PositiveSet.empty;
            cmovznz_bitwidths := IntSet.empty;
            value_barrier_bitwidths := v;
            typedefs_used := [] |}.
    Definition ident_info_of_typedefs (v : list _) : ident_infos
      := {| bitwidths_used := IntSet.empty;
            addcarryx_lg_splits := PositiveSet.empty;
            mulx_lg_splits := PositiveSet.empty;
            cmovznz_bitwidths := IntSet.empty;
            value_barrier_bitwidths := IntSet.empty;
            typedefs_used := v |}.
    Definition ident_info_with_bitwidths_used (i : ident_infos) (v : IntSet.t) : ident_infos
      := {| bitwidths_used := v;
            addcarryx_lg_splits := addcarryx_lg_splits i;
            mulx_lg_splits := mulx_lg_splits i;
            cmovznz_bitwidths := cmovznz_bitwidths i;
            value_barrier_bitwidths := value_barrier_bitwidths i;
            typedefs_used := typedefs_used i |}.
    Definition ident_info_with_addcarryx (i : ident_infos) (v : PositiveSet.t) : ident_infos
      := {| bitwidths_used := bitwidths_used i;
            addcarryx_lg_splits := v;
            mulx_lg_splits := mulx_lg_splits i;
            cmovznz_bitwidths := cmovznz_bitwidths i;
            value_barrier_bitwidths := value_barrier_bitwidths i;
            typedefs_used := typedefs_used i |}.
    Definition ident_info_with_mulx (i : ident_infos) (v : PositiveSet.t) : ident_infos
      := {| bitwidths_used := bitwidths_used i;
            addcarryx_lg_splits := addcarryx_lg_splits i;
            mulx_lg_splits := v;
            cmovznz_bitwidths := cmovznz_bitwidths i;
            value_barrier_bitwidths := value_barrier_bitwidths i;
            typedefs_used := typedefs_used i |}.
    Definition ident_info_with_cmovznz (i : ident_infos) (v : IntSet.t) : ident_infos
      := {| bitwidths_used := bitwidths_used i;
            addcarryx_lg_splits := addcarryx_lg_splits i;
            mulx_lg_splits := mulx_lg_splits i;
            cmovznz_bitwidths := v;
            value_barrier_bitwidths := value_barrier_bitwidths i;
            typedefs_used := typedefs_used i |}.
    Definition ident_info_with_value_barrier (i : ident_infos) (v : IntSet.t) : ident_infos
      := {| bitwidths_used := bitwidths_used i;
            addcarryx_lg_splits := addcarryx_lg_splits i;
            mulx_lg_splits := mulx_lg_splits i;
            cmovznz_bitwidths := cmovznz_bitwidths i;
            value_barrier_bitwidths := v;
            typedefs_used := typedefs_used i |}.
    Definition ident_info_with_typedefs (i : ident_infos) (v : list _) : ident_infos
      := {| bitwidths_used := bitwidths_used i;
            addcarryx_lg_splits := addcarryx_lg_splits i;
            mulx_lg_splits := mulx_lg_splits i;
            cmovznz_bitwidths := cmovznz_bitwidths i;
            value_barrier_bitwidths := value_barrier_bitwidths i;
            typedefs_used := v |}.

    Module Import OfPHOAS.
      Fixpoint base_var_data (t : base.type) : Set
        := match t with
           | base.type.unit
             => unit
           | base.type.type_base base.type.Z => string * bool (* is pointer *) * option int.type * option string (* typedef alias *)
           | base.type.prod A B => base_var_data A * base_var_data B
           | base.type.list A => string * option int.type * nat * option string (* typedef alias *)
           | base.type.type_base _
           | base.type.option _
             => Empty_set
           end.
      Definition var_data (t : API.type) : Set
        := match t with
           | type.base t => base_var_data t
           | type.arrow s d => Empty_set
           end.

      Fixpoint base_var_typedef_data (t : base.type) : Set
        := match t with
           | base.type.unit
             => unit
           | base.type.type_base base.type.Z => option string
           | base.type.prod A B => base_var_typedef_data A * base_var_typedef_data B
           | base.type.list A => option string
           | base.type.type_base _
           | base.type.option _
             => unit
           end.
      Fixpoint base_var_typedef_data_None {t : base.type} : base_var_typedef_data t
        := match t with
           | base.type.unit
             => tt
           | base.type.type_base base.type.Z => None
           | base.type.prod A B => (base_var_typedef_data_None, base_var_typedef_data_None)
           | base.type.list A => None
           | base.type.type_base _
           | base.type.option _
             => tt
           end.

      Definition var_typedef_data (t : API.type) : Set
        := match t with
           | type.base t => base_var_typedef_data t
           | type.arrow s d => unit
           end.

      Definition var_typedef_data_None {t : API.type} : var_typedef_data t
        := match t with
           | type.base t => base_var_typedef_data_None
           | type.arrow _ _ => tt
           end.

      Fixpoint base_var_names (t : base.type) : Set
        := match t with
           | base.type.unit
             => unit
           | base.type.type_base base.type.Z => string
           | base.type.prod A B => base_var_names A * base_var_names B
           | base.type.list A => string
           | base.type.type_base _
           | base.type.option _
             => Empty_set
           end.
      Definition var_names (t : API.type) : Set
        := match t with
           | type.base t => base_var_names t
           | type.arrow s d => Empty_set
           end.

      Fixpoint names_list_of_base_var_names {t} : base_var_names t -> list string
        := match t return base_var_names t -> list string with
           | base.type.unit
             => fun _ => []
           | base.type.type_base base.type.Z
           | base.type.list _
             => fun n => [n]
           | base.type.prod A B
             => fun x : base_var_names A * base_var_names B
                => @names_list_of_base_var_names A (fst x) ++ @names_list_of_base_var_names B (snd x)
           | base.type.type_base _
           | base.type.option _
             => fun absurd : Empty_set => match absurd with end
           end%list.

      Definition names_list_of_var_names {t} : var_names t -> list string
        := match t with
           | type.base t => @names_list_of_base_var_names t
           | type.arrow _ _ => fun absurd : Empty_set => match absurd with end
           end.

      Fixpoint names_of_base_var_data {t} : base_var_data t -> base_var_names t
        := match t return base_var_data t -> base_var_names t with
           | base.type.type_base base.type.Z => fun '(n, is_ptr, _, _) => n
           | base.type.prod A B
             => fun xy => (@names_of_base_var_data A (fst xy), @names_of_base_var_data B (snd xy))
           | base.type.list A => fun x => fst (fst (fst x))
           | base.type.unit
           | base.type.type_base _
           | base.type.option _
             => fun x => x
           end.
      Definition names_of_var_data {t} : var_data t -> var_names t
        := match t with
           | type.base t => names_of_base_var_data
           | type.arrow _ _ => fun x => x
           end.

      Definition names_list_of_base_var_data {t} (v : base_var_data t) : list string
        := names_list_of_base_var_names (names_of_base_var_data v).

      Definition names_list_of_var_data {t} (v : var_data t) : list string
        := names_list_of_var_names (names_of_var_data v).

      Fixpoint flatten_names_list_of_input_data {t : type} : type.for_each_lhs_of_arrow (fun _ => list string) t -> list string
        := match t return type.for_each_lhs_of_arrow _ t -> _ with
           | type.base _ => fun 'tt => nil
           | type.arrow s d
             => fun '(sl, v) => sl ++ @flatten_names_list_of_input_data d v
           end%list.

      Definition names_list_of_input_var_names {t} (v : type.for_each_lhs_of_arrow var_names t) : list string
        := flatten_names_list_of_input_data (type.map_for_each_lhs_of_arrow (@names_list_of_var_names) v).

      Definition names_list_of_input_var_data {t} (v : type.for_each_lhs_of_arrow var_data t) : list string
        := names_list_of_input_var_names (type.map_for_each_lhs_of_arrow (@names_of_var_data) v).

      Fixpoint base_var_data_of_names {t} : base_var_names t -> base_var_data t
        := match t return base_var_names t -> base_var_data t with
           | base.type.type_base base.type.Z => fun n => (n, false, None, None)
           | base.type.prod A B
             => fun xy => (@base_var_data_of_names A (fst xy), @base_var_data_of_names B (snd xy))
           | base.type.list A => fun n => (n, None, 0%nat, None)
           | base.type.unit
           | base.type.type_base _
           | base.type.option _
             => fun x => x
           end.
      Definition var_data_of_names {t} : var_names t -> var_data t
        := match t with
           | type.base t => base_var_data_of_names
           | type.arrow _ _ => fun x => x
           end.

      Fixpoint bound_to_string {skip_typedefs : skip_typedefs_opt} {t : base.type}
        : var_data (type.base t) -> ZRange.type.base.option.interp t -> list string
        := match t return var_data (type.base t) -> ZRange.type.base.option.interp t -> list string with
           | base.type.list _
           | tZ
             => fun '(name, _, _, td) arg
                => if skip_typedefs || Option.is_None td
                   then [(name ++ ": ")
                           ++ match ZRange.type.base.option.lift_Some arg with
                              | Some arg => show arg
                              | None => show arg
                              end]%string
                   else []
           | base.type.prod A B
             => fun '(va, vb) '(a, b)
                => @bound_to_string skip_typedefs A va a ++ @bound_to_string skip_typedefs B vb b
           | base.type.unit
             => fun 'tt _ => nil
           | base.type.option _
           | base.type.type_base _
             => fun absurd : Empty_set => match absurd with end
           end%list.

      Fixpoint input_bounds_to_string {skip_typedefs : skip_typedefs_opt} {t} : type.for_each_lhs_of_arrow var_data t -> type.for_each_lhs_of_arrow ZRange.type.option.interp t -> list string
        := match t return type.for_each_lhs_of_arrow var_data t -> type.for_each_lhs_of_arrow ZRange.type.option.interp t -> list string with
           | type.base t => fun _ _ => nil
           | type.arrow (type.base s) d
             => fun '(v, vs) '(arg, args)
                => (bound_to_string v arg)
                     ++ @input_bounds_to_string skip_typedefs d vs args
           | type.arrow s d
             => fun '(absurd, _) => match absurd : Empty_set with end
           end%list.
    End OfPHOAS.

    Definition format_special_function_name
               {language_naming_conventions : language_naming_conventions_opt}
               (internal_private : bool)
               (prefix : string)
               (name : string)
               (is_signed : bool)
               (bw : Z)
      : string
      := convert_to_naming_convention
           (if internal_private then private_function_naming_convention else public_function_naming_convention)
           (prefix ++ name ++ "_" ++ (if negb is_signed then "u" else "") ++ Decimal.Z.to_string bw).

    Definition name_of_typedef
               {language_naming_conventions : language_naming_conventions_opt}
               (prefix : string)
               (private : bool)
      : typedef_info -> string
      := fun '(name, description, ty, existT t bounds)
         => format_typedef_name prefix private name.

    Definition describe_typedef
               {language_naming_conventions : language_naming_conventions_opt}
               {documentation_options : documentation_options_opt}
               (prefix : string)
               (private : bool)
               (typedef : typedef_info)
      : list string
      := let name := name_of_typedef prefix private typedef in
         let '(_, description, ty, existT t bounds) := typedef in
         (([description name]%string)
            ++ (if ZRange.type.base.option.is_informative bounds
                then let bounds := match ZRange.type.base.option.lift_Some bounds with
                                   | Some bounds => show bounds
                                   | None => show bounds
                                   end in
                     if newline_in_typedef_bounds
                     then ["Bounds:"; "  " ++ bounds]%string
                     else ["Bounds: " ++ bounds]%string
                else []))%list.


    (** None means not array; Some None means array of unknown length; Some Some means array of known length *)
    Definition array_length_of_typedef
      : typedef_info -> option (option nat)
      := fun '(_, _, _, existT t bounds)
         => match t return ZRange.type.base.option.interp t -> option (option nat) with
            | base.type.list _ => fun bounds => Some (option_map (@List.length _) bounds)
            | _ => fun _ => None
            end bounds.

    (** For the second part of the returned type, None means not
        array; Some None means array of unknown length; Some Some
        means array of known length *)
    Definition name_and_type_and_describe_typedef
               {language_naming_conventions : language_naming_conventions_opt}
               {documentation_options : documentation_options_opt}
               (prefix : string)
               (private : bool)
               (typedef : typedef_info)
      : string * (option int.type * option (option nat)) * list string
      := let name := name_of_typedef prefix private typedef in
         let description := describe_typedef prefix private typedef in
         let len := array_length_of_typedef typedef in
         let '(_, _, ty, _) := typedef in
         (name, (ty, len), description).

    Definition format_special_function_name_ty
               {language_naming_conventions : language_naming_conventions_opt}
               (internal_private : bool)
               (prefix : string)
               (name : string)
               (t : int.type)
      : string
      := format_special_function_name internal_private prefix name (int.is_signed t) (int.bitwidth_of t).

    Definition normalize_newlines (lines : list string)
      := String.split String.NewLine (String.concat String.NewLine lines).

    Definition preprocess_comment_block (lines : list string) := normalize_newlines lines.

    (** prepends [prefix] to the first line of [lines] (after
        processing it to adjust for newlines), and indents the rest of
        the lines appropriately *)
    Definition prefix_and_indent (prefix : string) (lines : list string)
      := let lines := normalize_newlines lines in
         match lines with
         | [] => [prefix]
         | val :: vals
           => let indent := String.repeat " " (String.length prefix) in
              (prefix ++ val)
                :: List.map (fun v => indent ++ v) vals
         end.

    Class OutputLanguageAPI :=
      {
        (** [String.concat NewLine (comment_block lines)] should the
            the block-commented form of [String.concat NewLine lines].
            NewLines internal to elements in the list are allowed to
            be ignored / can be assumed to not be present.  Callers
            who want to ensure correct commenting on unknown blocks of
            text should instead run [comment_block
            (preprocess_comment_block lines)]. *)
        comment_block : list string -> list string;

        (** [String.concat NewLine (comment_file_header_block lines)]
            should the the block-commented form of [String.concat
            NewLine lines] which can be used for the header at the top
            of the file.  NewLines internal to elements in the list
            are allowed to be ignored / can be assumed to not be
            present.  Callers who want to ensure correct commenting on
            unknown blocks of text should instead run
            [comment_file_header_block (preprocess_comment_block
            lines)]. *)
        comment_file_header_block : list string -> list string;

        (** Converts a PHOAS AST to lines of code * info on which
            primitive functions are called, or else an error string *)
        ToFunctionLines
        : forall {absint_opts : AbstractInterpretation.Options}
                 {relax_zrange : relax_zrange_opt}
                 {language_naming_conventions : language_naming_conventions_opt}
                 {documentation_options : documentation_options_opt}
                 {output_options : output_options_opt}
                 (machine_wordsize : Z)
                 (do_bounds_check : bool) (internal_private : bool) (private : bool) (all_private : bool) (inline : bool) (prefix : string) (name : string)
                 {t}
                 (e : @API.Expr t)
                 (comment : type.for_each_lhs_of_arrow var_data t -> var_data (type.final_codomain t) -> list string)
                 (name_list : option (list string))
                 (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                 (outbounds : ZRange.type.base.option.interp (type.final_codomain t))
                 (intypedefs : type.for_each_lhs_of_arrow var_typedef_data t)
                 (outtypedefs : base_var_typedef_data (type.final_codomain t)),
            (list string * ident_infos) + string;

        (** Generates a header of any needed typedefs, etc based on the idents used and the curve-specific prefix *)
        header
        : forall {language_naming_conventions : language_naming_conventions_opt}
                 {documentation_options : documentation_options_opt}
                 {package_name : package_name_opt}
                 {class_name : class_name_opt}
                 {output_options : output_options_opt}
                 (machine_wordsize : Z) (internal_private : bool) (private : bool) (prefix : string) (ident_info : ident_infos)
                 (typedef_map : list typedef_info),
            list string;

        (** The footer on the file, if any *)
        footer
        : forall {language_naming_conventions : language_naming_conventions_opt}
                 {documentation_options : documentation_options_opt}
                 {package_name : package_name_opt}
                 {class_name : class_name_opt}
                 (machine_wordsize : Z) (internal_private : bool) (private : bool) (prefix : string) (ident_info : ident_infos),
            list string;

        (** Filters [ident_infos] to strip out primitive functions
            that we don't want to request (because they have special
            language handling) *)
        strip_special_infos
        : forall (machine_wordsize : Z),
            ident_infos -> ident_infos;
      }.
  End ToString.
End Compilers.
