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
Require Crypto.Util.Strings.String.
Require Import Crypto.Util.Structures.Equalities.Sum.
Require Import Crypto.Util.Structures.Equalities.Iso.
Require Import Crypto.Util.Structures.Orders.Sum.
Require Import Crypto.Util.Structures.Orders.Iso.
Require Import Crypto.Util.MSets.Iso.
Require Import Crypto.Util.MSets.Sum.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.Show.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.MSetPositive.Show.
Require Import Crypto.Util.MSets.Show.
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
    (** How to relax zranges *)
    Class relax_zrange_opt := relax_zrange : zrange -> zrange.
    Typeclasses Opaque relax_zrange_opt.
  End Options.

  Module ToString.
    Local Open Scope string_scope.
    Local Open Scope Z_scope.

    Module Import ZRange.
      Module Export type.
        Module Export base.
          Fixpoint show_interp {t} : Show (ZRange.type.base.interp t)
            := match t return bool -> ZRange.type.base.interp t -> string with
               | base.type.unit => @show unit _
               | base.type.type_base base.type.Z => @show zrange _
               | base.type.type_base base.type.bool => @show bool _
               | base.type.type_base base.type.nat => @show nat _
               | base.type.type_base base.type.zrange => @show zrange _
               | base.type.type_base base.type.string => @show string _
               | base.type.prod A B
                 => fun _ '(a, b)
                    => "(" ++ @show_interp A false a ++ ", " ++ @show_interp B true b ++ ")"
               | base.type.list A
                 => let SA := @show_interp A in
                    @show (list (ZRange.type.base.interp A)) _
               | base.type.option A
                 => let SA := @show_interp A in
                    @show (option (ZRange.type.base.interp A)) _
               end%string.
          Global Existing Instance show_interp.
          Module Export option.
            Fixpoint show_interp {t} : Show (ZRange.type.base.option.interp t)
              := match t return bool -> ZRange.type.base.option.interp t -> string with
                 | base.type.unit => @show unit _
                 | base.type.type_base base.type.Z => @show (option zrange) _
                 | base.type.type_base base.type.bool => @show (option bool) _
                 | base.type.type_base base.type.nat => @show (option nat) _
                 | base.type.type_base base.type.zrange => @show (option zrange) _
                 | base.type.type_base base.type.string => @show (option string) _
                 | base.type.prod A B
                   => let SA := @show_interp A in
                      let SB := @show_interp B in
                      @show (ZRange.type.base.option.interp A * ZRange.type.base.option.interp B) _
                 | base.type.list A
                   => let SA := @show_interp A in
                      @show (option (list (ZRange.type.base.option.interp A))) _
                 | base.type.option A
                   => let SA := @show_interp A in
                      @show (option (option (ZRange.type.base.option.interp A))) _
                 end.
            Global Existing Instance show_interp.
          End option.
        End base.

        Module option.
          Global Instance show_interp {t} : Show (ZRange.type.option.interp t)
            := fun parens
               => match t return ZRange.type.option.interp t -> string with
                  | type.base t
                    => fun v : ZRange.type.base.option.interp t
                       => show parens v
                  | type.arrow s d => fun _ => "λ"
                  end.
        End option.
      End type.
    End ZRange.

    Module PHOAS.
      Module type.
        Module base.
          Global Instance show_base : Show base.type.base
            := fun _ t => match t with
                       | base.type.Z => "ℤ"
                       | base.type.bool => "𝔹"
                       | base.type.nat => "ℕ"
                       | base.type.zrange => "zrange"
                       | base.type.string => "string"
                       end.
          Fixpoint show_type (with_parens : bool) (t : base.type) : string
            := match t with
               | base.type.unit => "()"
               | base.type.type_base t => show with_parens t
               | base.type.prod A B => maybe_wrap_parens
                                        with_parens
                                        (@show_type false A ++ " * " ++ @show_type true B)
               | base.type.list A => "[" ++ @show_type false A ++ "]"
               | base.type.option A
                 => maybe_wrap_parens
                      with_parens
                      ("option " ++ @show_type true A)
               end.
          Definition show_base_interp {t} : Show (base.base_interp t)
            := match t with
               | base.type.Z => @show Z _
               | base.type.bool => @show bool _
               | base.type.nat => @show nat _
               | base.type.zrange => @show zrange _
               | base.type.string => @show string _
               end.
          Global Existing Instance show_base_interp.
          Fixpoint show_interp {t} : Show (base.interp t)
            := match t with
               | base.type.unit => @show unit _
               | base.type.type_base t => @show (base.base_interp t) _
               | base.type.prod A B => @show (base.interp A * base.interp B) _
               | base.type.list A => @show (list (base.interp A)) _
               | base.type.option A => @show (option (base.interp A)) _
               end.
          Global Existing Instance show_interp.
          Global Instance show : Show base.type := show_type.
        End base.
        Fixpoint show_for_each_lhs_of_arrow {base_type} {f : type.type base_type -> Type} {show_f : forall t, Show (f t)} {t : type.type base_type} : Show (type.for_each_lhs_of_arrow f t)
          := match t return bool -> type.for_each_lhs_of_arrow f t -> string with
             | type.base t => @show unit _
             | type.arrow s d
               => fun with_parens '((x, xs) : f s * type.for_each_lhs_of_arrow f d)
                  => let _ : Show (f s) := show_f s in
                     let _ : Show (type.for_each_lhs_of_arrow f d) := @show_for_each_lhs_of_arrow base_type f show_f d in
                     match d with
                     | type.base _ => show with_parens x
                     | type.arrow _ _ => maybe_wrap_parens with_parens (show true x ++ ", " ++ show false xs)
                     end
             end.
        Global Existing Instance show_for_each_lhs_of_arrow.

        Fixpoint show_type {base_type} {S : Show base_type} (with_parens : bool) (t : type.type base_type) : string
          := match t with
             | type.base t => S with_parens t
             | type.arrow s d
               => maybe_wrap_parens
                   with_parens
                   (@show_type base_type S true s ++ " → " ++ @show_type base_type S false d)
             end.
        Global Instance show {base_type} {S : Show base_type} : Show (type.type base_type) := show_type.
      End type.

      Definition bitwidth_to_string (v : Z) : string
        := (if v =? 2^Z.log2 v then "2^" ++ Decimal.Z.to_string (Z.log2 v) else HexString.of_Z v).
      Definition show_range_or_ctype (v : zrange) : string
        := if (v.(lower) =? 0) && (v.(upper) =? 2^(Z.log2 (v.(upper) + 1)) - 1)
           then ("uint" ++ Decimal.Z.to_string (Z.log2 (v.(upper) + 1)) ++ "_t")%string
           else let lg2 := 1 + Z.log2 (-v.(lower)) in
                if (v.(lower) =? -2^(lg2-1)) && (v.(upper) =? 2^(lg2-1)-1)
                then ("int" ++ Decimal.Z.to_string lg2 ++ "_t")%string
                else show false v.
      Definition show_compact_Z (with_parens : bool) (v : Z) : string
        := let is_neg := v <? 0 in
           (if is_neg then "-" else "")
             ++ (let v := Z.abs v in
                 (if v <=? 2^8
                  then Decimal.Z.to_string v
                  else if v =? 2^(Z.log2 v)
                       then "2^" ++ (Decimal.Z.to_string (Z.log2 v))
                       else if v =? 2^(Z.log2_up v) - 1
                            then maybe_wrap_parens is_neg ("2^" ++ (Decimal.Z.to_string (Z.log2_up v)) ++ "-1")
                            else Hex.show_Z with_parens v)).

      Fixpoint make_castb {t} : ZRange.type.base.option.interp t -> option string
        := match t with
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
                     => let n := show false (List.length ls) in
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

      Definition maybe_wrap_cast (with_cast : bool) {t} (xr : (nat -> string) * ZRange.type.option.interp t) (lvl : nat) : string
        := match with_cast, make_cast (snd xr) with
           | true, Some c => "(" ++ c ++ ")" ++ fst xr 10%nat
           | _, _ => fst xr lvl
           end.

      Definition show_application (with_casts : bool) {t : type} (f : nat -> string) (args : type.for_each_lhs_of_arrow (fun t => (nat -> string) * ZRange.type.option.interp t)%type t)
        : nat -> string
        := match t return type.for_each_lhs_of_arrow (fun t => (nat -> string) * ZRange.type.option.interp t)%type t -> nat -> string with
           | type.base _ => fun 'tt lvl => f lvl
           | type.arrow s d
             => fun xs lvl
                => let _ : forall t, Show ((nat -> string) * ZRange.type.option.interp t)%type
                       := (fun t with_parens x => maybe_wrap_cast with_casts x 10%nat) in
                   maybe_wrap_parens (Nat.ltb lvl 11) (f 11%nat ++ show true xs)
           end args.

      Module ident.
        Global Instance show_ident {t} : Show (ident.ident t)
          := fun with_parens idc
             => match idc with
                | ident.Literal base.type.Z v => show_compact_Z with_parens v
                | ident.Literal t v => show with_parens v
                | ident.value_barrier => "value_barrier"
                | ident.comment _ => "comment"
                | ident.comment_no_keep _ => "comment_no_keep"
                | ident.tt => "()"
                | ident.Nat_succ => "Nat.succ"
                | ident.Nat_pred => "Nat.pred"
                | ident.Nat_max => "Nat.max"
                | ident.Nat_mul => "Nat.mul"
                | ident.Nat_add => "Nat.add"
                | ident.Nat_sub => "Nat.sub"
                | ident.Nat_eqb => "Nat.eqb"
                | ident.nil t => "[]"
                | ident.cons t => "(::)"
                | ident.pair A B => "(,)"
                | ident.fst A B => "fst"
                | ident.snd A B => "snd"
                | ident.prod_rect A B T => "prod_rect"
                | ident.bool_rect T => "bool_rect"
                | ident.nat_rect P => "nat_rect"
                | ident.eager_nat_rect P => "eager_nat_rect"
                | ident.nat_rect_arrow P Q => "nat_rect(→)"
                | ident.eager_nat_rect_arrow P Q => "eager_nat_rect(→)"
                | ident.list_rect A P => "list_rect"
                | ident.eager_list_rect A P => "eager_list_rect"
                | ident.list_rect_arrow A P Q => "list_rect(→)"
                | ident.eager_list_rect_arrow A P Q => "eager_list_rect(→)"
                | ident.list_case A P => "list_case"
                | ident.List_length T => "length"
                | ident.List_seq => "seq"
                | ident.List_repeat A => "repeat"
                | ident.List_firstn A => "firstn"
                | ident.List_skipn A => "skipn"
                | ident.List_combine A B => "combine"
                | ident.List_map A B => "map"
                | ident.List_app A => "(++)"
                | ident.List_rev A => "rev"
                | ident.List_flat_map A B => "flat_map"
                | ident.List_partition A => "partition"
                | ident.List_fold_right A B => "fold_right"
                | ident.List_update_nth T => "update_nth"
                | ident.List_nth_default T => "nth"
                | ident.eager_List_nth_default T => "eager_nth"
                | ident.Some _ => "Some"
                | ident.None _ => "None"
                | ident.option_rect _ _ => "option_rect"
                | ident.Z_add => "(+)"
                | ident.Z_mul => "( * )"
                | ident.Z_pow => "(^)"
                | ident.Z_sub => "(-)"
                | ident.Z_opp => "-"
                | ident.Z_div => "(/)"
                | ident.Z_modulo => "(mod)"
                | ident.Z_eqb => "(=)"
                | ident.Z_leb => "(≤)"
                | ident.Z_ltb => "(<)"
                | ident.Z_geb => "(≥)"
                | ident.Z_gtb => "(>)"
                | ident.Z_min => "min"
                | ident.Z_max => "max"
                | ident.Z_log2 => "log₂"
                | ident.Z_log2_up => "⌈log₂⌉"
                | ident.Z_of_nat => "(ℕ→ℤ)"
                | ident.Z_to_nat => "(ℤ→ℕ)"
                | ident.Z_shiftr => "(>>)"
                | ident.Z_shiftl => "(<<)"
                | ident.Z_land => "(&)"
                | ident.Z_lor => "(|)"
                | ident.Z_lnot_modulo => "~"
                | ident.Z_lxor => "⊕"
                | ident.Z_bneg => "!"
                | ident.Z_mul_split => "Z.mul_split"
                | ident.Z_mul_high => "Z.mul_high"
                | ident.Z_add_get_carry => "Z.add_get_carry"
                | ident.Z_add_with_carry => "Z.add_with_carry"
                | ident.Z_add_with_get_carry => "Z.add_with_get_carry"
                | ident.Z_sub_get_borrow => "Z.sub_get_borrow"
                | ident.Z_sub_with_get_borrow => "Z.sub_with_get_borrow"
                | ident.Z_ltz => "Z.ltz"
                | ident.Z_zselect => "Z.zselect"
                | ident.Z_add_modulo => "Z.add_modulo"
                | ident.Z_truncating_shiftl => "Z.truncating_shiftl"
                | ident.Z_rshi => "Z.rshi"
                | ident.Z_cc_m => "Z.cc_m"
                | ident.Z_combine_at_bitwidth => "Z.combine_at_bitwidth"
                | ident.Z_cast => "Z.cast"
                | ident.Z_cast2 => "Z.cast2"
                | ident.Build_zrange => "Build_zrange"
                | ident.zrange_rect _ => "zrange_rect"
                | ident.fancy_add => "fancy.add"
                | ident.fancy_addc => "fancy.addc"
                | ident.fancy_sub => "fancy.sub"
                | ident.fancy_subb => "fancy.subb"
                | ident.fancy_mulll => "fancy.mulll"
                | ident.fancy_mullh => "fancy.mullh"
                | ident.fancy_mulhl => "fancy.mulhl"
                | ident.fancy_mulhh => "fancy.mulhh"
                | ident.fancy_rshi => "fancy.rshi"
                | ident.fancy_selc => "fancy.selc"
                | ident.fancy_selm => "fancy.selm"
                | ident.fancy_sell => "fancy.sell"
                | ident.fancy_addm => "fancy.addm"
                end.

        (** N.B. Even though we are nominally printing Gallina
             identifiers here, we parenthesize bitwise operators much
             more frequently.  See, e.g.,
             https://github.com/mit-plv/fiat-crypto/pull/792#issuecomment-627647069,
             where Andres makes the point that in C, [+] binds more
             tightly than [<<]. *)
        Definition show_ident_lvl (with_casts : bool) {t} (idc : ident.ident t)
          : type.for_each_lhs_of_arrow (fun t => (nat -> string) * ZRange.type.option.interp t)%type t -> (nat -> string) * ZRange.type.base.option.interp (type.final_codomain t)
          := match idc in ident.ident t return type.for_each_lhs_of_arrow (fun t => (nat -> string) * ZRange.type.option.interp t)%type t -> (nat -> string) * ZRange.type.base.option.interp (type.final_codomain t) with
             | ident.Literal base.type.Z v => fun 'tt => (fun lvl => show_compact_Z (Nat.eqb lvl 0) v, ZRange.type.base.option.None)
             | ident.Literal t v => fun 'tt => (fun lvl => show (Nat.eqb lvl 0) v, ZRange.type.base.option.Some (t:=t) v)
             | ident.tt => fun _ => (fun _ => "()", tt)
             | ident.Nat_succ => fun '((x, xr), tt) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 10) ((x 10%nat) ++ ".+1"), ZRange.type.base.option.None)
             | ident.Nat_pred => fun '((x, xr), tt) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 10) ((x 10%nat) ++ ".-1"), ZRange.type.base.option.None)
             | ident.Nat_max => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 10) ("Nat.max " ++ x 9%nat ++ " " ++ y 9%nat), ZRange.type.base.option.None)
             | ident.Nat_mul => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 40) (x 40%nat ++ " *ℕ " ++ y 39%nat), ZRange.type.base.option.None)
             | ident.Nat_add => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 50) (x 50%nat ++ " +ℕ " ++ y 49%nat), ZRange.type.base.option.None)
             | ident.Nat_sub => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 50) (x 50%nat ++ " -ℕ " ++ y 49%nat), ZRange.type.base.option.None)
             | ident.Nat_eqb => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 70) (x 69%nat ++ " =ℕ " ++ y 69%nat), ZRange.type.base.option.None)
             | ident.None _ => fun 'tt => (fun _ => "None", ZRange.type.base.option.None)
             | ident.nil t => fun 'tt => (fun _ => "[]", ZRange.type.base.option.None)
             | ident.cons t => fun '(x, ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 60) (maybe_wrap_cast with_casts x 59%nat ++ " :: " ++ y 60%nat), ZRange.type.base.option.None)
             | ident.pair A B => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 201) (maybe_wrap_cast with_casts (x, xr) 201%nat ++ ", " ++ maybe_wrap_cast with_casts (y, yr) 200%nat), (xr, yr))
             | ident.fst A B => fun '((x, xr), tt) => (fun _ => x 0%nat ++ "₁", fst xr)
             | ident.snd A B => fun '((x, xr), tt) => (fun _ => x 0%nat ++ "₂", snd xr)
             | ident.prod_rect A B T => fun '((f, fr), ((p, pr), tt)) => (fun _ => "match " ++ p 200%nat ++ " with " ++ f 200%nat ++ " end", ZRange.type.base.option.None)
             | ident.bool_rect T => fun '(t, (f, ((b, br), tt))) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 200) ("if " ++ b 200%nat ++ " then " ++ maybe_wrap_cast with_casts t 200%nat ++ " else " ++ maybe_wrap_cast with_casts f 200%nat), ZRange.type.base.option.None)
             | ident.List_app _
               => fun '((xs, xsr), ((ys, ysr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 60) (xs 59%nat ++ " ++ " ++ ys 60%nat), ZRange.type.base.option.None)
             | ident.eager_List_nth_default T
               => fun '((d, dr), ((ls, lsr), ((i, ir), tt))) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 10) (ls 10%nat ++ "[[" ++ i 200%nat ++ "]]"), ZRange.type.base.option.None)
             | ident.List_nth_default T
               => fun '((d, dr), ((ls, lsr), ((i, ir), tt))) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 10) (ls 10%nat ++ "[" ++ i 200%nat ++ "]"), ZRange.type.base.option.None)
             | ident.Z_mul => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 40) (x 40%nat ++ " * " ++ y 39%nat), ZRange.type.base.option.None)
             | ident.Z_add => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 50) (x 50%nat ++ " + " ++ y 49%nat), ZRange.type.base.option.None)
             | ident.Z_sub => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 50) (x 50%nat ++ " - " ++ y 49%nat), ZRange.type.base.option.None)
             | ident.Z_pow => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 30) (x 30%nat ++ " ^ " ++ y 29%nat), ZRange.type.base.option.None)
             | ident.Z_opp => fun '((x, xr), tt) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 35) ("-" ++ x 35%nat), ZRange.type.base.option.None)
             | ident.Z_bneg => fun '((x, xr), tt) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 75) ("!" ++ x 75%nat), ZRange.type.base.option.None)
             | ident.Z_lnot_modulo => fun '((x, xr), ((m, mr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 75) ("~" ++ x 75%nat ++ (if with_casts then " (mod " ++ m 200%nat ++ ")" else "")), ZRange.type.base.option.None)
             | ident.Z_lxor => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 50) (x 50%nat ++ " ⊕ " ++ y 49%nat), ZRange.type.base.option.None)
             | ident.Z_div => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 40) (x 40%nat ++ " / " ++ y 39%nat), ZRange.type.base.option.None)
             | ident.Z_modulo => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 40) (x 40%nat ++ " mod " ++ y 39%nat), ZRange.type.base.option.None)
             | ident.Z_eqb => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 70) (x 69%nat ++ " = " ++ y 69%nat), ZRange.type.base.option.None)
             | ident.Z_ltb => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 70) (x 69%nat ++ " < " ++ y 69%nat), ZRange.type.base.option.None)
             | ident.Z_leb => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 70) (x 69%nat ++ " ≤ " ++ y 69%nat), ZRange.type.base.option.None)
             | ident.Z_gtb => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 70) (x 69%nat ++ " > " ++ y 69%nat), ZRange.type.base.option.None)
             | ident.Z_geb => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 70) (x 69%nat ++ " ≥ " ++ y 69%nat), ZRange.type.base.option.None)
             | ident.Z_shiftr => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 55) (x 30%nat ++ " >> " ++ y 29%nat), ZRange.type.base.option.None)
             | ident.Z_shiftl => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 55) (x 30%nat ++ " << " ++ y 29%nat), ZRange.type.base.option.None)
             | ident.Z_land => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 55) (x 30%nat ++ " & " ++ y 29%nat), ZRange.type.base.option.None)
             | ident.Z_lor => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 55) (x 30%nat ++ " | " ++ y 29%nat), ZRange.type.base.option.None)
             | ident.Z_cast
             | ident.Z_cast2
               => fun '((_, range), ((x, xr), tt)) => (x, range)
             | ident.Build_zrange => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 0) ("r[" ++ x 60%nat ++ " ~> " ++ y 200%nat), ZRange.type.base.option.None)
             | ident.comment _ as idc
             | ident.comment_no_keep _ as idc
             | ident.value_barrier as idc
             | ident.Some _ as idc
             | ident.nat_rect _ as idc
             | ident.eager_nat_rect _ as idc
             | ident.eager_nat_rect_arrow _ _ as idc
             | ident.nat_rect_arrow _ _ as idc
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
             | ident.List_fold_right _ _ as idc
             | ident.List_update_nth _ as idc
             | ident.Z_log2 as idc
             | ident.Z_log2_up as idc
             | ident.Z_of_nat as idc
             | ident.Z_to_nat as idc
             | ident.Z_min as idc
             | ident.Z_max as idc
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
               => fun args => (show_application with_casts (fun _ => show false idc) args, ZRange.type.base.option.None)
             end.
      End ident.

      Module expr.
        Local Notation show_ident := ident.show_ident.
        Local Notation show_ident_lvl := ident.show_ident_lvl.
        Fixpoint get_eta_cps_args {A} (t : type) (idx : positive) {struct t}
          : (type.for_each_lhs_of_arrow (fun y => (nat -> string) * ZRange.type.option.interp y)%type t -> positive -> A) -> list string * A
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
                  (k : forall t, @expr.expr base.type ident var t -> type.for_each_lhs_of_arrow (fun t => (nat -> string) * ZRange.type.option.interp t)%type t -> positive -> (positive * (nat -> list string)) * ZRange.type.base.option.interp (type.final_codomain t)).
          Fixpoint show_eta_abs_cps' {t} (idx : positive) (e : @expr.expr base.type ident var t)
            : (positive * (list string * (nat -> list string))) * ZRange.type.base.option.interp (type.final_codomain t)
            := match e in expr.expr t return (unit -> _ * ZRange.type.base.option.interp (type.final_codomain t)) -> _ * ZRange.type.base.option.interp (type.final_codomain t) with
               | expr.Abs s d f
                 => fun _
                    => let n := "x" ++ Decimal.Pos.to_string idx in
                       match of_string s n with
                       | Some n'
                         => let '(_, (args, show_f), r) := @show_eta_abs_cps' d (Pos.succ idx) (f n') in
                            (idx,
                             (n :: args, show_f),
                             r)
                       | None
                         => (idx,
                             ([n], (fun _ => ["λ_(" ++ show false t ++ ")"])),
                             ZRange.type.base.option.None)
                       end
               | _
                 => fun default
                    => default tt
               end (fun _
                    => let '(args, (idx, show_f, r)) := get_eta_cps_args _ idx (@k _ e) in
                       ((idx, (args, show_f)), r)).
          Definition show_eta_abs_cps (with_casts : bool) {t} (idx : positive) (e : @expr.expr base.type ident var t) (extraargs : type.for_each_lhs_of_arrow (fun t => (nat -> string) * ZRange.type.option.interp t)%type t)
            : (positive * (nat -> list string)) * ZRange.type.base.option.interp (type.final_codomain t)
            := let '(idx, (args, show_f), r) := @show_eta_abs_cps' t idx e in
               let argstr := String.concat " " args in
               (idx,
                fun lvl
                => match show_f lvl with
                   | nil => [show_application with_casts (fun _ => "(λ " ++ argstr ++ ", (* NOTHING‽ *))") extraargs 11%nat]%string
                   | show_f::nil
                     => [show_application with_casts (fun _ => "(λ " ++ argstr ++ ", " ++ show_f ++ ")") extraargs 11%nat]%string
                   | show_f
                     => ["(λ " ++ argstr ++ ","]%string ++ (List.map (fun v => String " " (String " " v)) show_f) ++ [")" ++ show_application with_casts (fun _ => "") extraargs 11%nat]%string
                   end%list,
                   r).
          Definition show_eta_cps {t} (idx : positive) (e : @expr.expr base.type ident var t)
            : (positive * (nat -> list string)) * ZRange.type.option.interp t
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

        Fixpoint show_expr_lines_gen (with_casts : bool) {var} (to_string : forall t, var t -> string) (of_string : forall t, string -> option (var t)) {t} (e : @expr.expr base.type ident var t) (args : type.for_each_lhs_of_arrow (fun t => (nat -> string) * ZRange.type.option.interp t)%type t) (idx : positive) {struct e} : (positive * (nat -> list string)) * ZRange.type.base.option.interp (type.final_codomain t)
          := match e in expr.expr t return type.for_each_lhs_of_arrow (fun t => (nat -> string) * ZRange.type.option.interp t)%type t -> (positive * (nat -> list string)) * ZRange.type.base.option.interp (type.final_codomain t) with
             | expr.Ident t idc
               => fun args => let '(v, r) := @show_ident_lvl with_casts t idc args in
                              (idx, fun lvl => [v lvl], r)
             | expr.Var t v
               => fun args => (idx, fun lvl => [show_application with_casts (fun _ => to_string _ v) args lvl], ZRange.type.base.option.None)
             | expr.Abs s d f as e
               => fun args
                  => show_eta_abs_cps of_string (fun t e args idx => let '(idx, v, r) := @show_expr_lines_gen with_casts var to_string of_string t e args idx in (idx, fun _ => v 200%nat, r)) with_casts idx e args
             | expr.App s d f x
               => fun args
                  => let '(idx', x', xr) := show_eta_cps of_string (fun t e args idx => @show_expr_lines_gen with_casts var to_string of_string t e args idx) idx x in
                     @show_expr_lines_gen
                       with_casts var to_string of_string _ f
                       (((fun lvl => String.concat String.NewLine (x' lvl)), xr),
                        args)
                       idx
             | expr.LetIn A (type.base B) x f
               => fun 'tt
                  => let n := "x" ++ Decimal.Pos.to_string idx in
                     let '(_, show_x, xr) := show_eta_cps of_string (fun t e args idx => @show_expr_lines_gen with_casts var to_string of_string t e args idx) idx x in
                     let '(idx, show_f, fr)
                         := match of_string A n with
                            | Some n' => show_eta_cps of_string (fun t e args idx => @show_expr_lines_gen with_casts var to_string of_string t e args idx) (Pos.succ idx) (f n')
                            | None => (idx, (fun _ => ["_"]), ZRange.type.option.None)
                            end in
                     let ty_str := match make_cast xr with
                                   | Some c => " : " ++ c
                                   | None => ""
                                   end in
                     let expr_let_line := "expr_let " ++ n ++ " := " in
                     (idx,
                      (fun lvl
                       => match show_x 200%nat with
                          | nil => [expr_let_line ++ "(* NOTHING‽ *) (*" ++ ty_str ++ " *) in"]%string ++ show_f 200%nat
                          | show_x::nil => [expr_let_line ++ show_x ++ " (*" ++ ty_str ++ " *) in"]%string ++ show_f 200%nat
                          | show_x::rest
                            => ([expr_let_line ++ show_x]%string)
                                 ++ (List.map (fun l => String.string_of_list_ascii (List.repeat " "%char (String.length expr_let_line)) ++ l)%string
                                              rest)
                                 ++ ["(*" ++ ty_str ++ " *)"]%string
                                 ++ ["in"]
                                 ++ show_f 200%nat
                          end%list),
                      fr)
             | expr.LetIn A B x f
               => fun args
                  => let n := "x" ++ Decimal.Pos.to_string idx in
                     let '(_, show_x, xr) := show_eta_cps of_string (fun t e args idx => @show_expr_lines_gen with_casts var to_string of_string t e args idx) idx x in
                     let '(idx, show_f, fr)
                         := match of_string A n with
                            | Some n' => show_eta_cps of_string (fun t e args idx => @show_expr_lines_gen with_casts var to_string of_string t e args idx) (Pos.succ idx) (f n')
                            | None => (idx, (fun _ => ["_"]), ZRange.type.option.None)
                            end in
                     let ty_str := match make_cast xr with
                                   | Some c => " : " ++ c
                                   | None => ""
                                   end in
                     let expr_let_line := "expr_let " ++ n ++ " := " in
                     (idx,
                      (fun lvl
                       => (["("]
                             ++ (map
                                   (String " ")
                                   match show_x 200%nat with
                                   | nil => [expr_let_line ++ "(* NOTHING‽ *) (*" ++ ty_str ++ " *) in"]%string ++ show_f 200%nat
                                   | show_x::nil => [expr_let_line ++ show_x ++ " (*" ++ ty_str ++ " *) in"]%string ++ show_f 200%nat
                                   | show_x::rest
                                     => ([expr_let_line ++ show_x]%string)
                                          ++ (List.map (fun l => String.string_of_list_ascii (List.repeat " "%char (String.length expr_let_line)) ++ l)%string
                                                       rest)
                                          ++ ["(*" ++ ty_str ++ " *)"]%string
                                          ++ ["in"]
                                          ++ show_f 200%nat
                                   end%list)
                             ++ [")"; show_application with_casts (fun _ => "") args 11%nat])%list),
                      ZRange.type.base.option.None)
             end args.
        Definition show_expr_lines (with_casts : bool) {t} (e : @expr.expr base.type ident (fun _ => string) t) (args : type.for_each_lhs_of_arrow (fun t => (nat -> string) * ZRange.type.option.interp t)%type t) (idx : positive) : (positive * (nat -> list string)) * ZRange.type.base.option.interp (type.final_codomain t)
          := @show_expr_lines_gen with_casts (fun _ => string) (fun _ x => x) (fun _ x => Some x) t e args idx.
        Fixpoint show_var_expr {var t} (with_parens : bool) (e : @expr.expr base.type ident var t) : string
          := match e with
             | expr.Ident t idc => show with_parens idc
             | expr.Var t v => maybe_wrap_parens with_parens ("VAR_(" ++ show false t ++ ")")
             | expr.Abs s d f => "λ_(" ++ show false t ++ ")"
             | expr.App s d f x
               => let show_f := @show_var_expr _ _ false f in
                  let show_x := @show_var_expr _ _ true x in
                  maybe_wrap_parens with_parens (show_f ++ " @ " ++ show_x)
             | expr.LetIn A B x f
               => let show_x := @show_var_expr _ _ false x in
                  maybe_wrap_parens with_parens ("expr_let _ := " ++ show_x ++ " in _")
             end%string.
        Definition partially_show_expr {var t} : Show (@expr.expr base.type ident var t) := show_var_expr.
        Local Notation default_with_casts := true.
        Section Show_gen.
          Context {var : type.type base.type -> Type}
                  (to_string : forall t, var t -> string)
                  (of_string : forall t, string -> option (var t)).

          Definition show_lines_expr_gen {t} : ShowLines (@expr.expr base.type ident var t)
            := fun with_parens e => let '(_, v, _) := show_eta_cps of_string (fun t e args idx => @show_expr_lines_gen default_with_casts var to_string of_string t e args idx) 1%positive e in v (if with_parens then 0%nat else 201%nat).
          Definition show_expr_gen {t} : Show (@expr.expr base.type ident var t)
            := fun with_parens e => String.concat String.NewLine (show_lines_expr_gen with_parens e).
        End Show_gen.
        Global Instance show_lines_expr {t} : ShowLines (@expr.expr base.type ident (fun _ => string) t)
          := @show_lines_expr_gen (fun _ => string) (fun _ x => x) (fun _ x => Some x) t.
        Global Instance show_lines_Expr {t} : ShowLines (@expr.Expr base.type ident t)
          := fun with_parens e => show_lines with_parens (e _).
        Global Instance show_expr {t} : Show (@expr.expr base.type ident (fun _ => string) t)
          := fun with_parens e => String.concat String.NewLine (show_lines with_parens e).
        Global Instance show_Expr {t} : Show (@expr.Expr base.type ident t)
          := fun with_parens e => show with_parens (e _).
      End expr.
    End PHOAS.

    Definition LinesToString (lines : list string)
      : string
      := String.concat String.NewLine lines.

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

      Lemma is_signed_of_bitwidth b v : is_signed (of_bitwidth b v) = b.
      Proof. apply is_signed_of_lgbitwidth. Qed.

      Global Instance show_type : Show type
        := fun with_parens t
           => maybe_wrap_parens
                with_parens
                ((if is_unsigned t then "u" else "") ++ "int" ++ Decimal.Z.to_string (bitwidth_of t)).

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

    Module IntSet <: WSets := WIsoSets SumPositiveSet IntAsDecidableType.
    Module Import IntSetShow := ShowWSets IntSet.
    Global Instance show_IntSet : Show IntSet.t := _.
    Global Instance show_lines_IntSet : ShowLines IntSet.t := _.

    (* Work around COQBUG(https://github.com/coq/coq/issues/11942) *)
    Local Unset Decidable Equality Schemes.
    Record ident_infos :=
      { bitwidths_used : IntSet.t;
        addcarryx_lg_splits : PositiveSet.t;
        mulx_lg_splits : PositiveSet.t;
        cmovznz_bitwidths : IntSet.t;
        value_barrier_bitwidths : IntSet.t;
      }.
    Local Set Decidable Equality Schemes.
    Global Instance show_lines_ident_infos : ShowLines ident_infos
      := fun _ v
         => ["{| bitwidths_used := " ++ show false (bitwidths_used v)
             ; " ; addcarryx_lg_splits := " ++ show false (addcarryx_lg_splits v)
             ; " ; mulx_lg_splits := " ++ show false (mulx_lg_splits v)
             ; " ; cmovznz_bitwidths := " ++ show false (cmovznz_bitwidths v)
             ; " ; value_barrier_bitwidths := " ++ show false (value_barrier_bitwidths v) ++ " |}"].
    Global Instance show_ident_infos : Show ident_infos
      := fun _ v => String.concat "" (show_lines false v).
    Definition ident_infos_equal (x y : ident_infos) : bool
      := let (x0, x1, x2, x3, x4) := x in
         let (y0, y1, y2, y3, y4) := y in
         List.fold_right
           andb true
           [IntSet.equal x0 y0
            ; PositiveSet.equal x1 y1
            ; PositiveSet.equal x2 y2
            ; IntSet.equal x3 y3
            ; IntSet.equal x4 y4].
    Definition ident_info_empty : ident_infos
      := Build_ident_infos IntSet.empty PositiveSet.empty PositiveSet.empty IntSet.empty IntSet.empty.
    Definition ident_info_diff (x y : ident_infos) : ident_infos
      := let (x0, x1, x2, x3, x4) := x in
         let (y0, y1, y2, y3, y4) := y in
         Build_ident_infos
           (IntSet.diff x0 y0)
           (PositiveSet.diff x1 y1)
           (PositiveSet.diff x2 y2)
           (IntSet.diff x3 y3)
           (IntSet.diff x4 y4).
    Definition ident_info_diff_except_bitwidths (x y : ident_infos) : ident_infos
      := let (x0, x1, x2, x3, x4) := x in
         let (y0, y1, y2, y3, y4) := y in
         Build_ident_infos
           x0
           (PositiveSet.diff x1 y1)
           (PositiveSet.diff x2 y2)
           (IntSet.diff x3 y3)
           (IntSet.diff x4 y4).
    Definition ident_info_union (x y : ident_infos) : ident_infos
      := let (x0, x1, x2, x3, x4) := x in
         let (y0, y1, y2, y3, y4) := y in
         Build_ident_infos
           (IntSet.union x0 y0)
           (PositiveSet.union x1 y1)
           (PositiveSet.union x2 y2)
           (IntSet.union x3 y3)
           (IntSet.union x4 y4).
    Definition ident_info_of_bitwidths_used (v : IntSet.t) : ident_infos
      := {| bitwidths_used := v;
            addcarryx_lg_splits := PositiveSet.empty;
            mulx_lg_splits := PositiveSet.empty;
            cmovznz_bitwidths := IntSet.empty;
            value_barrier_bitwidths := IntSet.empty |}.
    Definition ident_info_of_addcarryx (v : PositiveSet.t) : ident_infos
      := {| bitwidths_used := IntSet.empty;
            addcarryx_lg_splits := v;
            mulx_lg_splits := PositiveSet.empty;
            cmovznz_bitwidths := IntSet.empty;
            value_barrier_bitwidths := IntSet.empty |}.
    Definition ident_info_of_mulx (v : PositiveSet.t) : ident_infos
      := {| bitwidths_used := IntSet.empty;
            addcarryx_lg_splits := PositiveSet.empty;
            mulx_lg_splits := v;
            cmovznz_bitwidths := IntSet.empty;
            value_barrier_bitwidths := IntSet.empty |}.
    Definition ident_info_of_cmovznz (v : IntSet.t) : ident_infos
      := {| bitwidths_used := IntSet.empty;
            addcarryx_lg_splits := PositiveSet.empty;
            mulx_lg_splits := PositiveSet.empty;
            cmovznz_bitwidths := v;
            value_barrier_bitwidths := IntSet.empty |}.
    Definition ident_info_of_value_barrier (v : IntSet.t) : ident_infos
      := {| bitwidths_used := IntSet.empty;
            addcarryx_lg_splits := PositiveSet.empty;
            mulx_lg_splits := PositiveSet.empty;
            cmovznz_bitwidths := IntSet.empty;
            value_barrier_bitwidths := v |}.
    Definition ident_info_with_bitwidths_used (i : ident_infos) (v : IntSet.t) : ident_infos
      := {| bitwidths_used := v;
            addcarryx_lg_splits := addcarryx_lg_splits i;
            mulx_lg_splits := mulx_lg_splits i;
            cmovznz_bitwidths := cmovznz_bitwidths i;
            value_barrier_bitwidths := value_barrier_bitwidths i |}.
    Definition ident_info_with_addcarryx (i : ident_infos) (v : PositiveSet.t) : ident_infos
      := {| bitwidths_used := bitwidths_used i;
            addcarryx_lg_splits := v;
            mulx_lg_splits := mulx_lg_splits i;
            cmovznz_bitwidths := cmovznz_bitwidths i;
            value_barrier_bitwidths := value_barrier_bitwidths i |}.
    Definition ident_info_with_mulx (i : ident_infos) (v : PositiveSet.t) : ident_infos
      := {| bitwidths_used := bitwidths_used i;
            addcarryx_lg_splits := addcarryx_lg_splits i;
            mulx_lg_splits := v;
            cmovznz_bitwidths := cmovznz_bitwidths i;
            value_barrier_bitwidths := value_barrier_bitwidths i |}.
    Definition ident_info_with_cmovznz (i : ident_infos) (v : IntSet.t) : ident_infos
      := {| bitwidths_used := bitwidths_used i;
            addcarryx_lg_splits := addcarryx_lg_splits i;
            mulx_lg_splits := mulx_lg_splits i;
            cmovznz_bitwidths := v;
            value_barrier_bitwidths := value_barrier_bitwidths i |}.
    Definition ident_info_with_value_barrier (i : ident_infos) (v : IntSet.t) : ident_infos
      := {| bitwidths_used := bitwidths_used i;
            addcarryx_lg_splits := addcarryx_lg_splits i;
            mulx_lg_splits := mulx_lg_splits i;
            cmovznz_bitwidths := cmovznz_bitwidths i;
            value_barrier_bitwidths := v |}.

    Module Import OfPHOAS.
      Fixpoint base_var_data (t : base.type) : Set
        := match t with
           | base.type.unit
             => unit
           | base.type.type_base base.type.Z => string * bool (* is pointer *) * option int.type
           | base.type.prod A B => base_var_data A * base_var_data B
           | base.type.list A => string * option int.type * nat
           | base.type.type_base _
           | base.type.option _
             => Empty_set
           end.
      Definition var_data (t : Compilers.type.type base.type) : Set
        := match t with
           | type.base t => base_var_data t
           | type.arrow s d => Empty_set
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
      Definition var_names (t : Compilers.type.type base.type) : Set
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
           | base.type.type_base base.type.Z => fun '(n, is_ptr, _) => n
           | base.type.prod A B
             => fun xy => (@names_of_base_var_data A (fst xy), @names_of_base_var_data B (snd xy))
           | base.type.list A => fun x => fst (fst x)
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
           | base.type.type_base base.type.Z => fun n => (n, false, None)
           | base.type.prod A B
             => fun xy => (@base_var_data_of_names A (fst xy), @base_var_data_of_names B (snd xy))
           | base.type.list A => fun n => (n, None, 0%nat)
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

      Fixpoint bound_to_string {t : base.type} : var_data (type.base t) -> ZRange.type.base.option.interp t -> list string
        := match t return var_data (type.base t) -> ZRange.type.base.option.interp t -> list string with
           | tZ
             => fun '(name, _, _) arg
                => [(name ++ ": ")
                      ++ match arg with
                         | Some arg => show false arg
                         | None => show false arg
                         end]%string
           | base.type.prod A B
             => fun '(va, vb) '(a, b)
                => @bound_to_string A va a ++ @bound_to_string B vb b
           | base.type.list A
             => fun '(name, _, _) arg
                => [(name ++ ": ")
                      ++ match ZRange.type.base.option.lift_Some arg with
                         | Some arg => show false arg
                         | None => show false arg
                         end]%string
           | base.type.option _
           | base.type.unit
           | base.type.type_base _
             => fun _ _ => nil
           end%list.

      Fixpoint input_bounds_to_string {t} : type.for_each_lhs_of_arrow var_data t -> type.for_each_lhs_of_arrow ZRange.type.option.interp t -> list string
        := match t return type.for_each_lhs_of_arrow var_data t -> type.for_each_lhs_of_arrow ZRange.type.option.interp t -> list string with
           | type.base t => fun _ _ => nil
           | type.arrow (type.base s) d
             => fun '(v, vs) '(arg, args)
                => (bound_to_string v arg)
                     ++ @input_bounds_to_string d vs args
           | type.arrow s d
             => fun '(absurd, _) => match absurd : Empty_set with end
           end%list.
    End OfPHOAS.

    Definition preprocess_comment_block (lines : list string)
      := String.split String.NewLine (String.concat String.NewLine lines).

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
        : forall {relax_zrange : relax_zrange_opt}
                 (machine_wordsize : Z)
                 (do_bounds_check : bool) (static : bool) (prefix : string) (name : string)
                 {t}
                 (e : @Compilers.expr.Expr base.type ident.ident t)
                 (comment : type.for_each_lhs_of_arrow var_data t -> var_data (type.final_codomain t) -> list string)
                 (name_list : option (list string))
                 (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                 (outbounds : ZRange.type.base.option.interp (type.final_codomain t)),
            (list string * ident_infos) + string;

        (** Generates a header of any needed typedefs, etc based on the idents used and the curve-specific prefix *)
        header
        : forall (machine_wordsize : Z) (static : bool) (prefix : string) (ident_info : ident_infos),
            list string;

        (** The footer on the file, if any *)
        footer
        : forall (machine_wordsize : Z) (static : bool) (prefix : string) (ident_info : ident_infos),
            list string;

        (** Filters [ident_infos] to strip out primitive functions
            that we don't want to request (because they have special
            language handling *)
        strip_special_infos
        : forall (machine_wordsize : Z),
            ident_infos -> ident_infos;

      }.
  End ToString.
End Compilers.
