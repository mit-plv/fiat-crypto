Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.HexString.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.Show.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.AbstractInterpretation.
Require Import Crypto.Util.Bool.Equality.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope zrange_scope. Local Open Scope Z_scope.

Module Compilers.
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  Export Language.Compilers.
  Export AbstractInterpretation.Compilers.
  Import invert_expr.
  Import defaults.

  Module ToString.
    Local Open Scope string_scope.

    Module Import ZRange.
      Module Export type.
        Module Export base.
          Fixpoint show_interp {t} : Show (ZRange.type.base.interp t)
            := match t return bool -> ZRange.type.base.interp t -> string with
               | base.type.unit => @show unit _
               | base.type.Z => @show zrange _
               | base.type.bool => @show bool _
               | base.type.nat => @show nat _
               | base.type.prod A B
                 => fun _ '(a, b)
                    => "(" ++ @show_interp A false a ++ ", " ++ @show_interp B true b ++ ")"
               | base.type.list A
                 => let SA := @show_interp A in
                    @show (list (ZRange.type.base.interp A)) _
               end%string.
          Global Existing Instance show_interp.
          Module Export option.
            Fixpoint show_interp {t} : Show (ZRange.type.base.option.interp t)
              := match t return bool -> ZRange.type.base.option.interp t -> string with
                 | base.type.unit => @show unit _
                 | base.type.Z => @show (option zrange) _
                 | base.type.bool => @show (option bool) _
                 | base.type.nat => @show (option nat) _
                 | base.type.prod A B
                   => let SA := @show_interp A in
                      let SB := @show_interp B in
                      @show (ZRange.type.base.option.interp A * ZRange.type.base.option.interp B) _
                 | base.type.list A
                   => let SA := @show_interp A in
                      @show (option (list (ZRange.type.base.option.interp A))) _
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
                       | base.type.unit => "()"
                       | base.type.Z => "ℤ"
                       | base.type.bool => "𝔹"
                       | base.type.nat => "ℕ"
                       end.
          Fixpoint show_type (with_parens : bool) (t : base.type) : string
            := match t with
               | base.type.type_base t => show with_parens t
               | base.type.prod A B => maybe_wrap_parens
                                        with_parens
                                        (@show_type false A ++ " * " ++ @show_type true B)
               | base.type.list A => "[" ++ @show_type false A ++ "]"
               end.
          Fixpoint show_base_interp {t} : Show (base.base_interp t)
            := match t with
               | base.type.unit => @show unit _
               | base.type.Z => @show Z _
               | base.type.bool => @show bool _
               | base.type.nat => @show nat _
               end.
          Global Existing Instance show_base_interp.
          Fixpoint show_interp {t} : Show (base.interp t)
            := match t with
               | base.type.type_base t => @show (base.base_interp t) _
               | base.type.prod A B => @show (base.interp A * base.interp B) _
               | base.type.list A => @show (list (base.interp A)) _
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
        := (if v =? 2^Z.log2 v then "2^" ++ decimal_string_of_Z (Z.log2 v) else HexString.of_Z v).
      Definition show_range_or_ctype (v : zrange) : string
        := if (v.(lower) =? 0) && (v.(upper) =? 2^(Z.log2 (v.(upper) + 1)) - 1)
           then ("uint" ++ decimal_string_of_Z (Z.log2 (v.(upper) + 1)) ++ "_t")%string
           else let lg2 := 1 + Z.log2 (-v.(lower)) in
                if (v.(lower) =? -2^(lg2-1)) && (v.(upper) =? 2^(lg2-1)-1)
                then ("int" ++ decimal_string_of_Z lg2 ++ "_t")%string
                else show false v.
      Definition show_compact_Z (with_parens : bool) (v : Z) : string
        := let is_neg := v <? 0 in
           (if is_neg then "-" else "")
             ++ (let v := Z.abs v in
                 (if v <=? 2^8
                  then decimal_string_of_Z v
                  else if v =? 2^(Z.log2 v)
                       then "2^" ++ (decimal_string_of_Z (Z.log2 v))
                       else if v =? 2^(Z.log2_up v) - 1
                            then maybe_wrap_parens is_neg ("2^" ++ (decimal_string_of_Z (Z.log2_up v)) ++ "-1")
                            else Hex.show_Z with_parens v)).

      Fixpoint make_castb {t} : ZRange.type.base.option.interp t -> option string
        := match t with
           | base.type.Z => option_map show_range_or_ctype
           | base.type.type_base t => fun _ => None
           | base.type.prod A B
             => fun '(r1, r2)
                => match @make_castb A r1, @make_castb B r2 with
                   | Some c1, Some c2 => Some (c1 ++ ", " ++ c2)
                   | None, Some c => Some ("??, " ++ c)
                   | Some c, None => Some (c ++ ", ??")
                   | None, None => None
                   end
           | base.type.list A => fun _ => None
           end.
      Fixpoint make_cast {t} : ZRange.type.option.interp t -> option string
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
        Definition show_ident_lvl (with_casts : bool) {t} (idc : ident.ident t)
          : type.for_each_lhs_of_arrow (fun t => (nat -> string) * ZRange.type.option.interp t)%type t -> (nat -> string) * ZRange.type.base.option.interp (type.final_codomain t)
          := match idc in ident.ident t return type.for_each_lhs_of_arrow (fun t => (nat -> string) * ZRange.type.option.interp t)%type t -> (nat -> string) * ZRange.type.base.option.interp (type.final_codomain t) with
             | ident.Literal base.type.Z v => fun 'tt => (fun lvl => show_compact_Z (Nat.eqb lvl 0) v, ZRange.type.base.option.None)
             | ident.Literal t v => fun 'tt => (fun lvl => show (Nat.eqb lvl 0) v, ZRange.type.base.option.None)
             | ident.Nat_succ => fun '((x, xr), tt) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 10) ((x 10%nat) ++ ".+1"), ZRange.type.base.option.None)
             | ident.Nat_pred => fun '((x, xr), tt) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 10) ((x 10%nat) ++ ".-1"), ZRange.type.base.option.None)
             | ident.Nat_max => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 10) ("Nat.max " ++ x 9%nat ++ " " ++ y 9%nat), ZRange.type.base.option.None)
             | ident.Nat_mul => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 40) (x 40%nat ++ " *ℕ " ++ y 39%nat), ZRange.type.base.option.None)
             | ident.Nat_add => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 50) (x 50%nat ++ " +ℕ " ++ y 49%nat), ZRange.type.base.option.None)
             | ident.Nat_sub => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 50) (x 50%nat ++ " -ℕ " ++ y 49%nat), ZRange.type.base.option.None)
             | ident.nil t => fun 'tt => (fun _ => "[]", ZRange.type.base.option.None)
             | ident.cons t => fun '(x, ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 60) (maybe_wrap_cast with_casts x 59%nat ++ " :: " ++ y 60%nat), ZRange.type.base.option.None)
             | ident.pair A B => fun '(x, (y, tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 201) (maybe_wrap_cast with_casts x 201%nat ++ ", " ++ maybe_wrap_cast with_casts y 200%nat), ZRange.type.base.option.None)
             | ident.fst A B => fun '((x, xr), tt) => (fun _ => x 0%nat ++ "₁", fst xr)
             | ident.snd A B => fun '((x, xr), tt) => (fun _ => x 0%nat ++ "₂", snd xr)
             | ident.prod_rect A B T => fun '((f, fr), ((p, pr), tt)) => (fun _ => "match " ++ p 200%nat ++ " with " ++ f 200%nat ++ " end", ZRange.type.base.option.None)
             | ident.bool_rect T => fun '(t, (f, ((b, br), tt))) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 200) ("if " ++ b 200%nat ++ " then " ++ maybe_wrap_cast with_casts t 200%nat ++ " else " ++ maybe_wrap_cast with_casts f 200%nat), ZRange.type.base.option.None)
             | ident.nat_rect P
               => fun args => (show_application with_casts (fun _ => "nat_rect") args, ZRange.type.base.option.None)
             | ident.list_rect A P
               => fun args => (show_application with_casts (fun _ => "list_rect") args, ZRange.type.base.option.None)
             | ident.list_case A P
               => fun args => (show_application with_casts (fun _ => "list_case") args, ZRange.type.base.option.None)
             | ident.List_length T
               => fun args => (show_application with_casts (fun _ => "len") args, ZRange.type.base.option.None)
             | ident.List_seq
               => fun args => (show_application with_casts (fun _ => "seq") args, ZRange.type.base.option.None)
             | ident.List_repeat A
               => fun args => (show_application with_casts (fun _ => "repeat") args, ZRange.type.base.option.None)
             | ident.List_combine A B
               => fun args => (show_application with_casts (fun _ => "combine") args, ZRange.type.base.option.None)
             | ident.List_map A B
               => fun args => (show_application with_casts (fun _ => "map") args, ZRange.type.base.option.None)
             | ident.List_app A
               => fun '((xs, xsr), ((ys, ysr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 60) (xs 59%nat ++ " ++ " ++ ys 60%nat), ZRange.type.base.option.None)
             | ident.List_rev A
               => fun args => (show_application with_casts (fun _ => "rev") args, ZRange.type.base.option.None)
             | ident.List_flat_map A B
               => fun args => (show_application with_casts (fun _ => "flat_map") args, ZRange.type.base.option.None)
             | ident.List_partition A
               => fun args => (show_application with_casts (fun _ => "partition") args, ZRange.type.base.option.None)
             | ident.List_fold_right A B
               => fun args => (show_application with_casts (fun _ => "fold_right") args, ZRange.type.base.option.None)
             | ident.List_update_nth T
               => fun args => (show_application with_casts (fun _ => "update_nth") args, ZRange.type.base.option.None)
             | ident.List_nth_default T
               => fun '((d, dr), ((ls, lsr), ((i, ir), tt))) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 10) (ls 10%nat ++ "[" ++ i 200%nat ++ "]"), ZRange.type.base.option.None)
             | ident.Z_mul => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 40) (x 40%nat ++ " * " ++ y 39%nat), ZRange.type.base.option.None)
             | ident.Z_add => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 50) (x 50%nat ++ " + " ++ y 49%nat), ZRange.type.base.option.None)
             | ident.Z_sub => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 50) (x 50%nat ++ " - " ++ y 49%nat), ZRange.type.base.option.None)
             | ident.Z_pow => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 30) (x 30%nat ++ " ^ " ++ y 29%nat), ZRange.type.base.option.None)
             | ident.Z_opp => fun '((x, xr), tt) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 35) ("-" ++ x 35%nat), ZRange.type.base.option.None)
             | ident.Z_bneg => fun '((x, xr), tt) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 75) ("!" ++ x 75%nat), ZRange.type.base.option.None)
             | ident.Z_lnot_modulo => fun '((x, xr), ((m, mr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 75) ("~" ++ x 75%nat ++ (if with_casts then " (mod " ++ m 200%nat ++ ")" else "")), ZRange.type.base.option.None)
             | ident.Z_div => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 40) (x 40%nat ++ " / " ++ y 39%nat), ZRange.type.base.option.None)
             | ident.Z_modulo => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 40) (x 40%nat ++ " mod " ++ y 39%nat), ZRange.type.base.option.None)
             | ident.Z_eqb => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 70) (x 69%nat ++ " = " ++ y 69%nat), ZRange.type.base.option.None)
             | ident.Z_leb => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 70) (x 69%nat ++ " ≤ " ++ y 69%nat), ZRange.type.base.option.None)
             | ident.Z_geb => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 70) (x 69%nat ++ " ≥ " ++ y 69%nat), ZRange.type.base.option.None)
             | ident.Z_log2
               => fun args => (show_application with_casts (fun _ => "Z.log2") args, ZRange.type.base.option.None)
             | ident.Z_log2_up
               => fun args => (show_application with_casts (fun _ => "Z.log2_up") args, ZRange.type.base.option.None)
             | ident.Z_of_nat
               => fun args => (show_application with_casts (fun _ => "(ℕ→ℤ)") args, ZRange.type.base.option.None)
             | ident.Z_to_nat
               => fun args => (show_application with_casts (fun _ => "(ℤ→ℕ)") args, ZRange.type.base.option.None)
             | ident.Z_shiftr => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 30) (x 30%nat ++ " >> " ++ y 29%nat), ZRange.type.base.option.None)
             | ident.Z_shiftl => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 30) (x 30%nat ++ " << " ++ y 29%nat), ZRange.type.base.option.None)
             | ident.Z_land => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 50) (x 50%nat ++ " & " ++ y 49%nat), ZRange.type.base.option.None)
             | ident.Z_lor => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 50) (x 50%nat ++ " | " ++ y 49%nat), ZRange.type.base.option.None)
             | ident.Z_mul_split
               => fun args => (show_application with_casts (fun _ => "Z.mul_split") args, ZRange.type.base.option.None)
             | ident.Z_add_get_carry
               => fun args => (show_application with_casts (fun _ => "Z.add_get_carry") args, ZRange.type.base.option.None)
             | ident.Z_add_with_carry
               => fun args => (show_application with_casts (fun _ => "Z.add_with_carry") args, ZRange.type.base.option.None)
             | ident.Z_add_with_get_carry
               => fun args => (show_application with_casts (fun _ => "Z.add_with_get_carry") args, ZRange.type.base.option.None)
             | ident.Z_sub_get_borrow
               => fun args => (show_application with_casts (fun _ => "Z.sub_get_borrow") args, ZRange.type.base.option.None)
             | ident.Z_sub_with_get_borrow
               => fun args => (show_application with_casts (fun _ => "Z.sub_with_get_borrow") args, ZRange.type.base.option.None)
             | ident.Z_zselect
               => fun args => (show_application with_casts (fun _ => "Z.zselect") args, ZRange.type.base.option.None)
             | ident.Z_add_modulo
               => fun args => (show_application with_casts (fun _ => "Z.add_modulo") args, ZRange.type.base.option.None)
             | ident.Z_rshi
               => fun args => (show_application with_casts (fun _ => "Z.rshi") args, ZRange.type.base.option.None)
             | ident.Z_cc_m
               => fun args => (show_application with_casts (fun _ => "Z.cc_m") args, ZRange.type.base.option.None)
             | ident.Z_cast range
               => fun '((x, xr), tt) => (x, Some range)
             | ident.Z_cast2 (r1, r2)
               => fun '((x, xr), tt) => (x, (Some r1, Some r2))
             | ident.fancy_add log2wordmax imm
               => fun args => (show_application with_casts (fun lvl' => maybe_wrap_parens (Nat.ltb lvl' 11) ("fancy.add 2^" ++ decimal_string_of_Z log2wordmax ++ " " ++ HexString.of_Z imm)) args, ZRange.type.base.option.None)
             | ident.fancy_addc log2wordmax imm
               => fun args => (show_application with_casts (fun lvl' => maybe_wrap_parens (Nat.ltb lvl' 11) ("fancy.addc 2^" ++ decimal_string_of_Z log2wordmax ++ " " ++ HexString.of_Z imm)) args, ZRange.type.base.option.None)
             | ident.fancy_sub log2wordmax imm
               => fun args => (show_application with_casts (fun lvl' => maybe_wrap_parens (Nat.ltb lvl' 11) ("fancy.sub 2^" ++ decimal_string_of_Z log2wordmax ++ " " ++ HexString.of_Z imm)) args, ZRange.type.base.option.None)
             | ident.fancy_subb log2wordmax imm
               => fun args => (show_application with_casts (fun lvl' => maybe_wrap_parens (Nat.ltb lvl' 11) ("fancy.subb 2^" ++ decimal_string_of_Z log2wordmax ++ " " ++ HexString.of_Z imm)) args, ZRange.type.base.option.None)
             | ident.fancy_mulll log2wordmax
               => fun args => (show_application with_casts (fun lvl' => maybe_wrap_parens (Nat.ltb lvl' 11) ("fancy.mulll 2^" ++ decimal_string_of_Z log2wordmax)) args, ZRange.type.base.option.None)
             | ident.fancy_mullh log2wordmax
               => fun args => (show_application with_casts (fun lvl' => maybe_wrap_parens (Nat.ltb lvl' 11) ("fancy.mullh 2^" ++ decimal_string_of_Z log2wordmax)) args, ZRange.type.base.option.None)
             | ident.fancy_mulhl log2wordmax
               => fun args => (show_application with_casts (fun lvl' => maybe_wrap_parens (Nat.ltb lvl' 11) ("fancy.mulhl 2^" ++ decimal_string_of_Z log2wordmax)) args, ZRange.type.base.option.None)
             | ident.fancy_mulhh log2wordmax
               => fun args => (show_application with_casts (fun lvl' => maybe_wrap_parens (Nat.ltb lvl' 11) ("fancy.mulhh 2^" ++ decimal_string_of_Z log2wordmax)) args, ZRange.type.base.option.None)
             | ident.fancy_rshi log2wordmax x
               => fun args => (show_application with_casts (fun lvl' => maybe_wrap_parens (Nat.ltb lvl' 11) ("fancy.rshi 2^" ++ decimal_string_of_Z log2wordmax ++ " " ++ decimal_string_of_Z x)) args, ZRange.type.base.option.None)
             | ident.fancy_selc
               => fun args => (show_application with_casts (fun _ => "fancy.selc") args, ZRange.type.base.option.None)
             | ident.fancy_selm log2wordmax
               => fun args => (show_application with_casts (fun lvl' => maybe_wrap_parens (Nat.ltb lvl' 11) ("fancy.selm 2^" ++ decimal_string_of_Z log2wordmax)) args, ZRange.type.base.option.None)
             | ident.fancy_sell
               => fun args => (show_application with_casts (fun _ => "fancy.sell") args, ZRange.type.base.option.None)
             | ident.fancy_addm
               => fun args => (show_application with_casts (fun _ => "fancy.addm") args, ZRange.type.base.option.None)
             end.
        Global Instance show_ident {t} : Show (ident.ident t)
          := fun with_parens idc
             => match idc with
                | ident.Literal base.type.Z v => show_compact_Z with_parens v
                | ident.Literal t v => show with_parens v
                | ident.Nat_succ => "Nat.succ"
                | ident.Nat_pred => "Nat.pred"
                | ident.Nat_max => "Nat.max"
                | ident.Nat_mul => "Nat.mul"
                | ident.Nat_add => "Nat.add"
                | ident.Nat_sub => "Nat.sub"
                | ident.nil t => "[]"
                | ident.cons t => "(::)"
                | ident.pair A B => "(,)"
                | ident.fst A B => "fst"
                | ident.snd A B => "snd"
                | ident.prod_rect A B T => "prod_rect"
                | ident.bool_rect T => "bool_rect"
                | ident.nat_rect P => "nat_rect"
                | ident.list_rect A P => "list_rect"
                | ident.list_case A P => "list_case"
                | ident.List_length T => "length"
                | ident.List_seq => "seq"
                | ident.List_repeat A => "repeat"
                | ident.List_combine A B => "combine"
                | ident.List_map A B => "map"
                | ident.List_app A => "(++)"
                | ident.List_rev A => "rev"
                | ident.List_flat_map A B => "flat_map"
                | ident.List_partition A => "partition"
                | ident.List_fold_right A B => "fold_right"
                | ident.List_update_nth T => "update_nth"
                | ident.List_nth_default T => "nth"
                | ident.Z_add => "(+)"
                | ident.Z_mul => "( * )"
                | ident.Z_pow => "(^)"
                | ident.Z_sub => "(-)"
                | ident.Z_opp => "-"
                | ident.Z_div => "(/)"
                | ident.Z_modulo => "(mod)"
                | ident.Z_eqb => "(=)"
                | ident.Z_leb => "(≤)"
                | ident.Z_geb => "(≥)"
                | ident.Z_log2 => "log₂"
                | ident.Z_log2_up => "⌈log₂⌉"
                | ident.Z_of_nat => "(ℕ→ℤ)"
                | ident.Z_to_nat => "(ℤ→ℕ)"
                | ident.Z_shiftr => "(>>)"
                | ident.Z_shiftl => "(<<)"
                | ident.Z_land => "(&)"
                | ident.Z_lor => "(|)"
                | ident.Z_lnot_modulo => "~"
                | ident.Z_bneg => "!"
                | ident.Z_mul_split => "Z.mul_split"
                | ident.Z_add_get_carry => "Z.add_get_carry"
                | ident.Z_add_with_carry => "Z.add_with_carry"
                | ident.Z_add_with_get_carry => "Z.add_with_get_carry"
                | ident.Z_sub_get_borrow => "Z.sub_get_borrow"
                | ident.Z_sub_with_get_borrow => "Z.sub_with_get_borrow"
                | ident.Z_zselect => "Z.zselect"
                | ident.Z_add_modulo => "Z.add_modulo"
                | ident.Z_rshi => "Z.rshi"
                | ident.Z_cc_m => "Z.cc_m"
                | ident.Z_cast range => "(" ++ show_range_or_ctype range ++ ")"
                | ident.Z_cast2 (r1, r2) => "(" ++ show_range_or_ctype r1 ++ ", " ++ show_range_or_ctype r2 ++ ")"
                | ident.fancy_add log2wordmax imm
                  => maybe_wrap_parens with_parens ("fancy.add 2^" ++ decimal_string_of_Z log2wordmax ++ " " ++ HexString.of_Z imm)
                | ident.fancy_addc log2wordmax imm
                  => maybe_wrap_parens with_parens ("fancy.addc 2^" ++ decimal_string_of_Z log2wordmax ++ " " ++ HexString.of_Z imm)
                | ident.fancy_sub log2wordmax imm
                  => maybe_wrap_parens with_parens ("fancy.sub 2^" ++ decimal_string_of_Z log2wordmax ++ " " ++ HexString.of_Z imm)
                | ident.fancy_subb log2wordmax imm
                  => maybe_wrap_parens with_parens ("fancy.subb 2^" ++ decimal_string_of_Z log2wordmax ++ " " ++ HexString.of_Z imm)
                | ident.fancy_mulll log2wordmax
                  => maybe_wrap_parens with_parens ("fancy.mulll 2^" ++ decimal_string_of_Z log2wordmax)
                | ident.fancy_mullh log2wordmax
                  => maybe_wrap_parens with_parens ("fancy.mullh 2^" ++ decimal_string_of_Z log2wordmax)
                | ident.fancy_mulhl log2wordmax
                  => maybe_wrap_parens with_parens ("fancy.mulhl 2^" ++ decimal_string_of_Z log2wordmax)
                | ident.fancy_mulhh log2wordmax
                  => maybe_wrap_parens with_parens ("fancy.mulhh 2^" ++ decimal_string_of_Z log2wordmax)
                | ident.fancy_rshi log2wordmax x
                  => maybe_wrap_parens with_parens ("fancy.rshi 2^" ++ decimal_string_of_Z log2wordmax ++ " " ++ decimal_string_of_Z x)
                | ident.fancy_selc => "fancy.selc"
                | ident.fancy_selm log2wordmax
                  => maybe_wrap_parens with_parens ("fancy.selm 2^" ++ decimal_string_of_Z log2wordmax)
                | ident.fancy_sell => "fancy.sell"
                | ident.fancy_addm => "fancy.addm"
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
                  => let n := "x" ++ decimal_string_of_pos idx in
                     let '(args, show_f) := @get_eta_cps_args A d (Pos.succ idx) (fun arglist => k (((fun _ => n), ZRange.type.option.None), arglist)) in
                     (n :: args, show_f)
             | type.base _
               => fun k => (nil, k tt idx)
             end.
        Section helper.
          Context (k : forall t, @expr.expr base.type ident (fun _ => string) t -> type.for_each_lhs_of_arrow (fun t => (nat -> string) * ZRange.type.option.interp t)%type t -> positive -> (positive * (nat -> list string)) * ZRange.type.base.option.interp (type.final_codomain t)).
          Fixpoint show_eta_abs_cps' {t} (idx : positive) (e : @expr.expr base.type ident (fun _ => string) t)
            : (positive * (list string * (nat -> list string))) * ZRange.type.base.option.interp (type.final_codomain t)
            := match e in expr.expr t return (unit -> _ * ZRange.type.base.option.interp (type.final_codomain t)) -> _ * ZRange.type.base.option.interp (type.final_codomain t) with
               | expr.Abs s d f
                 => fun _
                    => let n := "x" ++ decimal_string_of_pos idx in
                       let '(_, (args, show_f), r) := @show_eta_abs_cps' d (Pos.succ idx) (f n) in
                       (idx,
                        (n :: args, show_f),
                        r)
               | _
                 => fun default
                    => default tt
               end (fun _
                    => let '(args, (idx, show_f, r)) := get_eta_cps_args _ idx (@k _ e) in
                       ((idx, (args, show_f)), r)).
          Definition show_eta_abs_cps (with_casts : bool) {t} (idx : positive) (e : @expr.expr base.type ident (fun _ => string) t) (extraargs : type.for_each_lhs_of_arrow (fun t => (nat -> string) * ZRange.type.option.interp t)%type t)
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
          Definition show_eta_cps {t} (idx : positive) (e : @expr.expr base.type ident (fun _ => string) t)
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

        Fixpoint show_expr_lines (with_casts : bool) {t} (e : @expr.expr base.type ident (fun _ => string) t) (args : type.for_each_lhs_of_arrow (fun t => (nat -> string) * ZRange.type.option.interp t)%type t) (idx : positive) {struct e} : (positive * (nat -> list string)) * ZRange.type.base.option.interp (type.final_codomain t)
          := match e in expr.expr t return type.for_each_lhs_of_arrow (fun t => (nat -> string) * ZRange.type.option.interp t)%type t -> (positive * (nat -> list string)) * ZRange.type.base.option.interp (type.final_codomain t) with
             | expr.Ident t idc
               => fun args => let '(v, r) := @show_ident_lvl with_casts t idc args in
                              (idx, fun lvl => [v lvl], r)
             | expr.Var t v
               => fun args => (idx, fun lvl => [show_application with_casts (fun _ => v) args lvl], ZRange.type.base.option.None)
             | expr.Abs s d f as e
               => fun args
                  => show_eta_abs_cps (fun t e args idx => let '(idx, v, r) := @show_expr_lines with_casts t e args idx in (idx, fun _ => v 200%nat, r)) with_casts idx e args
             | expr.App s d f x
               => fun args
                  => let '(idx', x', xr) := show_eta_cps (fun t e args idx => @show_expr_lines with_casts t e args idx) idx x in
                     @show_expr_lines
                       with_casts _ f
                       (((fun lvl => String.concat String.NewLine (x' lvl)), xr),
                        args)
                       idx
             | expr.LetIn A (type.base B) x f
               => fun 'tt
                  => let n := "x" ++ decimal_string_of_pos idx in
                     let '(_, show_x, xr) := show_eta_cps (fun t e args idx => @show_expr_lines with_casts t e args idx) idx x in
                     let '(idx, show_f, fr) := show_eta_cps (fun t e args idx => @show_expr_lines with_casts t e args idx) (Pos.succ idx) (f n) in
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
                                 ++ (List.map (fun l => String.of_list (List.repeat " "%char (String.length expr_let_line)) ++ l)%string
                                              rest)
                                 ++ ["(*" ++ ty_str ++ " *)"]%string
                                 ++ ["in"]
                                 ++ show_f 200%nat
                          end%list),
                      fr)
             | expr.LetIn A B x f
               => fun args
                  => let n := "x" ++ decimal_string_of_pos idx in
                     let '(_, show_x, xr) := show_eta_cps (fun t e args idx => @show_expr_lines with_casts t e args idx) idx x in
                     let '(idx, show_f, fr) := show_eta_cps (fun t e args idx => @show_expr_lines with_casts t e args idx) (Pos.succ idx) (f n) in
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
                                          ++ (List.map (fun l => String.of_list (List.repeat " "%char (String.length expr_let_line)) ++ l)%string
                                                       rest)
                                          ++ ["(*" ++ ty_str ++ " *)"]%string
                                          ++ ["in"]
                                          ++ show_f 200%nat
                                   end%list)
                             ++ [")"; show_application with_casts (fun _ => "") args 11%nat])%list),
                      ZRange.type.base.option.None)
             end args.
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
        Local Notation default_with_casts := false.
        Global Instance show_lines_expr {t} : ShowLines (@expr.expr base.type ident (fun _ => string) t)
          := fun with_parens e => let '(_, v, _) := show_eta_cps (fun t e args idx => @show_expr_lines default_with_casts t e args idx) 1%positive e in v (if with_parens then 0%nat else 201%nat).
        Global Instance show_lines_Expr {t} : ShowLines (@expr.Expr base.type ident t)
          := fun with_parens e => show_lines with_parens (e _).
        Global Instance show_expr {t} : Show (@expr.expr base.type ident (fun _ => string) t)
          := fun with_parens e => String.concat String.NewLine (show_lines with_parens e).
        Global Instance show_Expr {t} : Show (@expr.Expr base.type ident t)
          := fun with_parens e => show with_parens (e _).
      End expr.
    End PHOAS.

    Module C.
      Module type.
        Inductive primitive := Z | Zptr.
        Inductive type := type_primitive (t : primitive) | prod (A B : type) | unit.
        Module Export Notations.
          Global Coercion type_primitive : primitive >-> type.
          Delimit Scope Ctype_scope with Ctype.

          Bind Scope Ctype_scope with type.
          Notation "()" := unit : Ctype_scope.
          Notation "A * B" := (prod A B) : Ctype_scope.
          Notation type := type.
        End Notations.
      End type.
      Import type.Notations.

      Module int.
        Inductive type := signed (lgbitwidth : nat) | unsigned (lgbitwidth : nat).

        Definition lgbitwidth_of (t : type) : nat
          := match t with
             | signed lgbitwidth => lgbitwidth
             | unsigned lgbitwidth => lgbitwidth
             end.
        Definition bitwidth_of (t : type) : Z := 2^Z.of_nat (lgbitwidth_of t).
        Definition is_signed (t : type) : bool := match t with signed _ => true | unsigned _ => false end.
        Definition is_unsigned (t : type) : bool := negb (is_signed t).
        Definition to_zrange (t : type) : zrange
          := let bw := bitwidth_of t in
             if is_signed t
             then r[-2^bw ~> 2^(bw-1) - 1]
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

        Global Instance show_type : Show type
          := fun with_parens t
             => maybe_wrap_parens
                 with_parens
                 ((if is_unsigned t then "u" else "") ++ "int" ++ decimal_string_of_Z (bitwidth_of t)).

        Definition union (t1 t2 : type) : type := of_zrange_relaxed (ZRange.union (to_zrange t1) (to_zrange t2)).

        Fixpoint base_interp (t : base.type) : Set
          := match t with
             | base.type.Z => type
             | base.type.type_base _ => unit
             | base.type.prod A B => base_interp A * base_interp B
             | base.type.list A => list (base_interp A)
             end%type.

        Module option.
          Fixpoint interp (t : base.type) : Set
            := match t with
               | base.type.Z => option type
               | base.type.type_base _ => unit
               | base.type.prod A B => interp A * interp B
               | base.type.list A => option (list (interp A))
               end%type.
          Fixpoint None {t} : interp t
            := match t with
               | base.type.Z => Datatypes.None
               | base.type.type_base _ => tt
               | base.type.prod A B => (@None A, @None B)
               | base.type.list A => Datatypes.None
               end.
          Fixpoint Some {t} : base_interp t -> interp t
            := match t with
               | base.type.Z => Datatypes.Some
               | base.type.type_base _ => fun tt => tt
               | base.type.prod A B => fun '(a, b) => (@Some A a, @Some B b)
               | base.type.list A => fun ls => Datatypes.Some (List.map (@Some A) ls)
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

      Section ident.
        Import type.
        Inductive ident : type -> type -> Set :=
        | literal (v : BinInt.Z) : ident unit Z
        | List_nth (n : Datatypes.nat) : ident Zptr Z
        | Addr : ident Z Zptr
        | Dereference : ident Zptr Z
        | Z_shiftr (offset : BinInt.Z) : ident Z Z
        | Z_shiftl (offset : BinInt.Z) : ident Z Z
        | Z_land : ident (Z * Z) Z
        | Z_lor : ident (Z * Z) Z
        | Z_add : ident (Z * Z) Z
        | Z_mul : ident (Z * Z) Z
        | Z_sub : ident (Z * Z) Z
        | Z_opp : ident Z Z
        | Z_lnot (ty:int.type) : ident Z Z
        | Z_bneg : ident Z Z
        | Z_mul_split (lgs:BinInt.Z) : ident ((Zptr * Zptr) * (Z * Z)) unit
        | Z_add_with_get_carry (lgs:BinInt.Z) : ident ((Zptr * Zptr) * (Z * Z * Z)) unit
        | Z_sub_with_get_borrow (lgs:BinInt.Z) : ident ((Zptr * Zptr) * (Z * Z * Z)) unit
        | Z_zselect (ty:int.type) : ident (Zptr * (Z * Z * Z)) unit
        | Z_add_modulo : ident (Z * Z * Z) Z
        | Z_static_cast (ty : int.type) : ident Z Z
        .
      End ident.

      Inductive arith_expr : type -> Set :=
      | AppIdent {s d} (idc : ident s d) (arg : arith_expr s) : arith_expr d
      | Var (t : type.primitive) (v : string) : arith_expr t
      | Pair {A B} (a : arith_expr A) (b : arith_expr B) : arith_expr (A * B)
      | TT : arith_expr type.unit.

      Inductive stmt :=
      | Call (val : arith_expr type.unit)
      | Assign (declare : bool) (t : type.primitive) (sz : option int.type) (name : string) (val : arith_expr t)
      | AssignZPtr (name : string) (sz : option int.type) (val : arith_expr type.Z)
      | DeclareVar (t : type.primitive) (sz : option int.type) (name : string)
      | AssignNth (name : string) (n : nat) (val : arith_expr type.Z).
      Definition expr := list stmt.

      Module Export Notations.
        Export int.Notations.
        Export type.Notations.
        Delimit Scope Cexpr_scope with Cexpr.
        Bind Scope Cexpr_scope with expr.
        Bind Scope Cexpr_scope with stmt.
        Bind Scope Cexpr_scope with arith_expr.
        Infix "@@" := AppIdent : Cexpr_scope.
        Notation "( x , y , .. , z )" := (Pair .. (Pair x%Cexpr y%Cexpr) .. z%Cexpr) : Cexpr_scope.
        Notation "( )" := TT : Cexpr_scope.

        Notation "()" := TT : Cexpr_scope.
        Notation "x ;; y" := (@cons stmt x%Cexpr y%Cexpr) (at level 70, right associativity, format "'[v' x ;; '/' y ']'") : Cexpr_scope.
      End Notations.

      Definition invert_literal {t} (e : arith_expr t) : option (BinInt.Z)
        := match e with
           | AppIdent s d (literal v) arg => Some v
           | _ => None
           end.

      Module OfPHOAS.
        Fixpoint base_var_data (t : base.type) : Set
          := match t with
             | base.type.unit
               => unit
             | base.type.nat
             | base.type.bool
               => Empty_set
             | base.type.Z => string * option int.type
             | base.type.prod A B => base_var_data A * base_var_data B
             | base.type.list A => string * option int.type * nat
             end.
        Definition var_data (t : Compilers.type.type base.type) : Set
          := match t with
             | type.base t => base_var_data t
             | type.arrow s d => Empty_set
             end.

        Fixpoint arith_expr_for_base (t : base.type) : Set
          := match t with
             | base.type.Z
               => arith_expr type.Z * option int.type
             | base.type.prod A B
               => arith_expr_for_base A * arith_expr_for_base B
             | base.type.list A => list (arith_expr_for_base A)
             | base.type.type_base _ as t
               => base.interp t
             end.
        Definition arith_expr_for (t : Compilers.type.type base.type) : Set
          := match t with
             | type.base t => arith_expr_for_base t
             | type.arrow s d => Empty_set
             end.

        (** Quoting
            http://en.cppreference.com/w/c/language/conversion:

            ** Integer promotions

            Integer promotion is the implicit conversion of a value of
            any integer type with rank less or equal to rank of int or
            of a bit field of type _Bool, int, signed int, unsigned
            int, to the value of type int or unsigned int

            If int can represent the entire range of values of the
            original type (or the range of values of the original bit
            field), the value is converted to type int. Otherwise the
            value is converted to unsigned int. *)
        (** We assume a 32-bit [int] type *)
        Definition integer_promote_type (t : int.type) : int.type
          := if int.is_tighter_than t int32
             then int32
             else t.

        (** Quoting
            http://en.cppreference.com/w/c/language/conversion:

            rank above is a property of every integer type and is
            defined as follows:

            1) the ranks of all signed integer types are different and
               increase with their precision: rank of signed char <
               rank of short < rank of int < rank of long int < rank
               of long long int

            2) the ranks of all signed integer types equal the ranks
               of the corresponding unsigned integer types

            3) the rank of any standard integer type is greater than
               the rank of any extended integer type of the same size
               (that is, rank of __int64 < rank of long long int, but
               rank of long long < rank of __int128 due to the rule
               (1))

            4) rank of char equals rank of signed char and rank of
               unsigned char

            5) the rank of _Bool is less than the rank of any other
               standard integer type

            6) the rank of any enumerated type equals the rank of its
               compatible integer type

            7) ranking is transitive: if rank of T1 < rank of T2 and
               rank of T2 < rank of T3 then rank of T1 < rank of T3

            8) any aspects of relative ranking of extended integer
               types not covered above are implementation defined *)
        (** We define the rank to be the bitwidth, which satisfies
            (1), (2), (4), (5), and (7).  Points (3) and (6) do not
            apply. *)
        Definition rank (r : int.type) : BinInt.Z := int.bitwidth_of r.
        Definition IMPOSSIBLE {T} (v : T) : T. exact v. Qed.
        (** Quoting
            http://en.cppreference.com/w/c/language/conversion: *)
        Definition common_type (t1 t2 : int.type) : int.type
          (** First of all, both operands undergo integer promotions
              (see below). Then *)
          := let t1 := integer_promote_type t1 in
             let t2 := integer_promote_type t2 in
             (** - If the types after promotion are the same, that
                   type is the common type *)
             if int.type_beq t1 t2 then
               t1
             (** - Otherwise, if both operands after promotion have
                   the same signedness (both signed or both unsigned),
                   the operand with the lesser conversion rank (see
                   below) is implicitly converted to the type of the
                   operand with the greater conversion rank *)
             else if bool_beq (int.is_signed t1) (int.is_signed t2) then
               (if rank t1 >=? rank t2 then t1 else t2)
             (** - Otherwise, the signedness is different: If the
                   operand with the unsigned type has conversion rank
                   greater or equal than the rank of the type of the
                   signed operand, then the operand with the signed
                   type is implicitly converted to the unsigned type
                   *)
             else if int.is_unsigned t1 && (rank t1 >=? rank t2) then
               t1
             else if int.is_unsigned t2 && (rank t2 >=? rank t1) then
               t2
             (** - Otherwise, the signedness is different and the
                   signed operand's rank is greater than unsigned
                   operand's rank. In this case, if the signed type
                   can represent all values of the unsigned type, then
                   the operand with the unsigned type is implicitly
                   converted to the type of the signed operand. *)
             else if int.is_signed t1 && int.is_tighter_than t2 t1 then
               t1
             else if int.is_signed t2 && int.is_tighter_than t1 t2 then
               t2
             (** - Otherwise, both operands undergo implicit
                   conversion to the unsigned type counterpart of the
                   signed operand's type. *)
             (** N.B. This case ought to be impossible in our code,
                   where [rank] is the bitwidth. *)
             else if int.is_signed t1 then
               int.unsigned_counterpart_of t1
             else
               int.unsigned_counterpart_of t2.

        Definition Zcast_down_if_needed
          : option int.type -> arith_expr_for_base base.type.Z -> arith_expr_for_base base.type.Z
          := fun desired_type '(e, known_type)
             => match desired_type, known_type with
               | None, _ => (e, known_type)
               | Some desired_type, Some known_type
                 => if int.is_tighter_than known_type desired_type
                   then (e, Some known_type)
                   else (Z_static_cast desired_type @@ e, Some desired_type)
               | Some desired_type, None
                 => (Z_static_cast desired_type @@ e, Some desired_type)
               end%core%Cexpr.

        Fixpoint cast_down_if_needed {t}
          : int.option.interp t -> arith_expr_for_base t -> arith_expr_for_base t
          := match t with
             | base.type.Z => Zcast_down_if_needed
             | base.type.type_base _ => fun _ x => x
             | base.type.prod A B
               => fun '(r1, r2) '(e1, e2) => (@cast_down_if_needed A r1 e1,
                                          @cast_down_if_needed B r2 e2)
             | base.type.list A
               => fun r1 ls
                 => match r1 with
                   | Some r1 => List.map (fun '(r, e) => @cast_down_if_needed A r e)
                                        (List.combine r1 ls)
                   | None => ls
                   end
             end.

        Definition Zcast_up_if_needed
          : option int.type -> arith_expr_for_base base.type.Z -> arith_expr_for_base base.type.Z
          := fun desired_type '(e, known_type)
             => match desired_type, known_type with
               | None, _ | _, None => (e, known_type)
               | Some desired_type, Some known_type
                 => if int.is_tighter_than desired_type known_type
                   then (e, Some known_type)
                   else (Z_static_cast desired_type @@ e, Some desired_type)%core%Cexpr
               end.

        Fixpoint cast_up_if_needed {t}
          : int.option.interp t -> arith_expr_for_base t -> arith_expr_for_base t
          := match t with
             | base.type.Z => Zcast_up_if_needed
             | base.type.type_base _ => fun _ x => x
             | base.type.prod A B
               => fun '(r1, r2) '(e1, e2) => (@cast_up_if_needed A r1 e1,
                                          @cast_up_if_needed B r2 e2)
             | base.type.list A
               => fun r1 ls
                 => match r1 with
                   | Some r1 => List.map (fun '(r, e) => @cast_up_if_needed A r e)
                                        (List.combine r1 ls)
                   | None => ls
                   end
             end.

        Definition cast_bigger_up_if_needed
                   (desired_type : option int.type)
                   (args : arith_expr_for (base.type.Z * base.type.Z))
          : arith_expr_for (base.type.Z * base.type.Z)
          := match desired_type with
             | None => args
             | Some _
               => let '((e1, t1), (e2, t2)) := args in
                 match t1, t2 with
                 | None, _ | _, None => args
                 | Some t1', Some t2'
                   => if int.is_tighter_than t2' t1'
                     then (Zcast_up_if_needed desired_type (e1, t1), (e2, t2))
                     else ((e1, t1), Zcast_up_if_needed desired_type (e2, t2))
                 end
             end.

        Definition arith_bin_arith_expr_of_PHOAS_ident
                   (s:=(base.type.Z * base.type.Z)%etype)
                   (d:=base.type.Z)
                   (idc : ident (type.Z * type.Z) type.Z)
          : option int.type -> arith_expr_for s -> arith_expr_for d
          := fun desired_type '((e1, t1), (e2, t2))
             => let t1 := option_map integer_promote_type t1 in
               let t2 := option_map integer_promote_type t2 in
               let '((e1, t1), (e2, t2))
                   := cast_bigger_up_if_needed desired_type ((e1, t1), (e2, t2)) in
               let ct := (t1 <- t1; t2 <- t2; Some (common_type t1 t2))%option in
               Zcast_down_if_needed desired_type ((idc @@ (e1, e2))%Cexpr, ct).

        Local Definition fakeprod (A B : Compilers.type.type base.type) : Compilers.type.type base.type
          := match A, B with
             | type.base A, type.base B => type.base (base.type.prod A B)
             | type.arrow _ _, _
             | _, type.arrow _ _
               => type.base (base.type.type_base base.type.unit)
             end.
        Definition arith_expr_for_uncurried_domain (t : Compilers.type.type base.type)
          := match t with
             | type.base t => unit
             | type.arrow s d => arith_expr_for (type.uncurried_domain fakeprod s d)
             end.

        Section with_bind.
          (* N.B. If we make the [bind*_err] notations, then Coq can't
             infer types correctly; if we make them [Local
             Definition]s or [Let]s, then [ocamlopt] fails with
             "Error: The type of this module, [...], contains type
             variables that cannot be generalized".  We need to run
             [cbv] below to actually unfold them. >.< *)
          Local Notation ErrT T := (T + list string)%type.
          Local Notation ret v := (@inl _ (list string) v) (only parsing).
          Local Notation "x <- v ; f" := (match v with
                                          | inl x => f
                                          | inr err => inr err
                                          end).
          Reserved Notation "A1 ,, A2 <- X ; B" (at level 70, A2 at next level, right associativity, format "'[v' A1 ,,  A2  <-  X ; '/' B ']'").
          Reserved Notation "A1 ,, A2 <- X1 , X2 ; B" (at level 70, A2 at next level, right associativity, format "'[v' A1 ,,  A2  <-  X1 ,  X2 ; '/' B ']'").
          Reserved Notation "A1 ,, A2 ,, A3 <- X ; B" (at level 70, A2 at next level, A3 at next level, right associativity, format "'[v' A1 ,,  A2 ,,  A3  <-  X ; '/' B ']'").
          Reserved Notation "A1 ,, A2 ,, A3 <- X1 , X2 , X3 ; B" (at level 70, A2 at next level, A3 at next level, right associativity, format "'[v' A1 ,,  A2 ,,  A3  <-  X1 ,  X2 ,  X3 ; '/' B ']'").
          Reserved Notation "A1 ,, A2 ,, A3 ,, A4 <- X ; B" (at level 70, A2 at next level, A3 at next level, A4 at next level, right associativity, format "'[v' A1 ,,  A2 ,,  A3 ,,  A4  <-  X ; '/' B ']'").
          Reserved Notation "A1 ,, A2 ,, A3 ,, A4 <- X1 , X2 , X3 , X4 ; B" (at level 70, A2 at next level, A3 at next level, A4 at next level, right associativity, format "'[v' A1 ,,  A2 ,,  A3 ,,  A4  <-  X1 ,  X2 ,  X3 ,  X4 ; '/' B ']'").
          Reserved Notation "A1 ,, A2 ,, A3 ,, A4 ,, A5 <- X ; B" (at level 70, A2 at next level, A3 at next level, A4 at next level, A5 at next level, right associativity, format "'[v' A1 ,,  A2 ,,  A3 ,,  A4 ,,  A5  <-  X ; '/' B ']'").
          Reserved Notation "A1 ,, A2 ,, A3 ,, A4 ,, A5 <- X1 , X2 , X3 , X4 , X5 ; B" (at level 70, A2 at next level, A3 at next level, A4 at next level, A5 at next level, right associativity, format "'[v' A1 ,,  A2 ,,  A3 ,,  A4 ,,  A5  <-  X1 ,  X2 ,  X3 ,  X4 ,  X5 ; '/' B ']'").
          Let bind2_err {A B C} (v1 : ErrT A) (v2 : ErrT B) (f : A -> B -> ErrT C) : ErrT C
            := match v1, v2 with
               | inl x1, inl x2 => f x1 x2
               | inr err, inl _ | inl _, inr err => inr err
               | inr err1, inr err2 => inr (List.app err1 err2)
               end.
          Local Notation "x1 ,, x2 <- v1 , v2 ; f"
            := (bind2_err v1 v2 (fun x1 x2 => f)).
          Local Notation "x1 ,, x2 <- v ; f"
            := (x1 ,, x2 <- fst v , snd v; f).
          Let bind3_err {A B C R} (v1 : ErrT A) (v2 : ErrT B) (v3 : ErrT C) (f : A -> B -> C -> ErrT R) : ErrT R
            := (x12 ,, x3 <- (x1 ,, x2 <- v1, v2; inl (x1, x2)), v3;
                  let '(x1, x2) := x12 in
                  f x1 x2 x3).
          Local Notation "x1 ,, x2 ,, x3 <- v1 , v2 , v3 ; f"
            := (bind3_err v1 v2 v3 (fun x1 x2 x3 => f)).
          Local Notation "x1 ,, x2 ,, x3 <- v ; f"
            := (let '(v1, v2, v3) := v in x1 ,, x2 ,, x3 <- v1 , v2 , v3; f).
          Let bind4_err {A B C D R} (v1 : ErrT A) (v2 : ErrT B) (v3 : ErrT C) (v4 : ErrT D) (f : A -> B -> C -> D -> ErrT R) : ErrT R
            := (x12 ,, x34 <- (x1 ,, x2 <- v1, v2; inl (x1, x2)), (x3 ,, x4 <- v3, v4; inl (x3, x4));
                  let '((x1, x2), (x3, x4)) := (x12, x34) in
                  f x1 x2 x3 x4).
          Local Notation "x1 ,, x2 ,, x3 ,, x4 <- v1 , v2 , v3 , v4 ; f"
            := (bind4_err v1 v2 v3 v4 (fun x1 x2 x3 x4 => f)).
          Local Notation "x1 ,, x2 ,, x3 ,, x4 <- v ; f"
            := (let '(v1, v2, v3, v4) := v in x1 ,, x2 ,, x3 ,, x4 <- v1 , v2 , v3 , v4; f).
          Let bind5_err {A B C D E R} (v1 : ErrT A) (v2 : ErrT B) (v3 : ErrT C) (v4 : ErrT D) (v5 : ErrT E) (f : A -> B -> C -> D -> E -> ErrT R) : ErrT R
            := (x12 ,, x345 <- (x1 ,, x2 <- v1, v2; inl (x1, x2)), (x3 ,, x4 ,, x5 <- v3, v4, v5; inl (x3, x4, x5));
                  let '((x1, x2), (x3, x4, x5)) := (x12, x345) in
                  f x1 x2 x3 x4 x5).
          Local Notation "x1 ,, x2 ,, x3 ,, x4 ,, x5 <- v1 , v2 , v3 , v4 , v5 ; f"
            := (bind5_err v1 v2 v3 v4 v5 (fun x1 x2 x3 x4 x5 => f)).
          Local Notation "x1 ,, x2 ,, x3 ,, x4 ,, x5 <- v ; f"
            := (let '(v1, v2, v3, v4, v5) := v in x1 ,, x2 ,, x3 ,, x4 ,, x5 <- v1 , v2 , v3 , v4 , v5; f).

          Definition maybe_log2 (s : Z) : option Z
            := if 2^Z.log2 s =? s then Some (Z.log2 s) else None.
          Definition maybe_loglog2 (s : Z) : option nat
            := (v <- maybe_log2 s;
                  v <- maybe_log2 v;
                  if Z.leb 0 v
                  then Some (Z.to_nat v)
                  else None).


          Definition arith_expr_of_PHOAS_ident
                     {t}
                     (idc : ident.ident t)
            : int.option.interp (type.final_codomain t) -> type.interpM_final (fun T => ErrT T) arith_expr_for_base t
            := match idc in ident.ident t return int.option.interp (type.final_codomain t) -> type.interpM_final (fun T => ErrT T) arith_expr_for_base t with
               | ident.Literal base.type.Z v
                 => fun r => ret (cast_down_if_needed
                                r
                                (literal v @@ TT, Some (int.of_zrange_relaxed r[v~>v])))
               | ident.nil t
                 => fun _ => ret nil
               | ident.cons t
                 => fun r x xs => ret (cast_down_if_needed r (cons x xs))
               | ident.fst A B => fun r xy => ret (cast_down_if_needed r (@fst _ _ xy))
               | ident.snd A B => fun r xy => ret (cast_down_if_needed r (@snd _ _ xy))
               | ident.List_nth_default base.type.Z
                 => fun r d ls n
                   => List.nth_default (inr ["Invalid list index " ++ show false n]%string)
                                      (List.map (fun x => ret (cast_down_if_needed r x)) ls) n
               | ident.Z_shiftr
                 => fun rout '(e, r) '(offset, roffset)
                   => let rin := option_map integer_promote_type r in
                     match invert_literal offset with
                     | Some offset => ret (cast_down_if_needed rout (Z_shiftr offset @@ e, rin))
                     | None => inr ["Invalid right-shift by a non-literal"]%string
                     end
               | ident.Z_shiftl
                 => fun rout '(e, r) '(offset, roffset)
                   => let rin := option_map integer_promote_type r in
                     match invert_literal offset with
                     | Some offset
                       => let '(e', rin') := cast_up_if_needed rout (e, rin) in
                         ret (cast_down_if_needed rout (Z_shiftl offset @@ e', rin'))
                     | None => inr ["Invalid left-shift by a non-literal"]%string
                     end
               | ident.Z_bneg
                 => fun rout '(e, r)
                   => (** N.B. We assume that C will implicitly cast the output of [!e] to whatever integer type it wants it in *)
                     ret (Z_bneg @@ e, rout)
               | ident.Z_land => fun r x y => ret (arith_bin_arith_expr_of_PHOAS_ident Z_land r (x, y))
               | ident.Z_lor => fun r x y => ret (arith_bin_arith_expr_of_PHOAS_ident Z_lor r (x, y))
               | ident.Z_add => fun r x y => ret (arith_bin_arith_expr_of_PHOAS_ident Z_add r (x, y))
               | ident.Z_mul => fun r x y => ret (arith_bin_arith_expr_of_PHOAS_ident Z_mul r (x, y))
               | ident.Z_sub => fun r x y => ret (arith_bin_arith_expr_of_PHOAS_ident Z_sub r (x, y))
               | ident.Z_lnot_modulo
                 => fun rout '(e, r) '(modulus, _)
                   => let rin := option_map integer_promote_type r in
                     match invert_literal modulus with
                     | Some modulus
                       => match maybe_loglog2 modulus with
                         | Some lgbitwidth
                           => let ty := int.unsigned lgbitwidth in
                             let rin' := Some ty in
                             let '(e, _) := Zcast_up_if_needed rin' (e, r) in
                             ret (cast_down_if_needed rout (cast_up_if_needed rout (Z_lnot ty @@ e, rin')))
                         | None => inr ["Invalid modulus for Z.lnot (not 2^(2^_)): " ++ show false modulus]%string
                         end
                     | None => inr ["Invalid non-literal modulus for Z.lnot"]%string
                     end
               | ident.pair A B
                 => fun _ _ _ => inr ["Invalid identifier in arithmetic expression " ++ show true idc]%string
               | ident.Z_opp (* we pretend this is [0 - _] *)
                 => fun r y => let zero := (literal 0 @@ TT, Some (int.of_zrange_relaxed r[0~>0])) in
                           ret (arith_bin_arith_expr_of_PHOAS_ident Z_sub r (zero, y))
               | ident.Literal _ v
                 => fun _ => ret v
               | ident.Nat_succ
               | ident.Nat_pred
               | ident.Nat_max
               | ident.Nat_mul
               | ident.Nat_add
               | ident.Nat_sub
               | ident.prod_rect _ _ _
               | ident.bool_rect _
               | ident.nat_rect _
               | ident.list_rect _ _
               | ident.list_case _ _
               | ident.List_length _
               | ident.List_seq
               | ident.List_repeat _
               | ident.List_combine _ _
               | ident.List_map _ _
               | ident.List_app _
               | ident.List_rev _
               | ident.List_flat_map _ _
               | ident.List_partition _
               | ident.List_fold_right _ _
               | ident.List_update_nth _
               | ident.List_nth_default _
               | ident.Z_pow
               | ident.Z_div
               | ident.Z_modulo
               | ident.Z_eqb
               | ident.Z_leb
               | ident.Z_geb
               | ident.Z_log2
               | ident.Z_log2_up
               | ident.Z_of_nat
               | ident.Z_to_nat
               | ident.Z_zselect
               | ident.Z_mul_split
               | ident.Z_add_get_carry
               | ident.Z_add_with_carry
               | ident.Z_add_with_get_carry
               | ident.Z_sub_get_borrow
               | ident.Z_sub_with_get_borrow
               | ident.Z_add_modulo
               | ident.Z_rshi
               | ident.Z_cc_m
               | ident.Z_cast _
               | ident.Z_cast2 _
               | ident.fancy_add _ _
               | ident.fancy_addc _ _
               | ident.fancy_sub _ _
               | ident.fancy_subb _ _
               | ident.fancy_mulll _
               | ident.fancy_mullh _
               | ident.fancy_mulhl _
               | ident.fancy_mulhh _
               | ident.fancy_rshi _ _
               | ident.fancy_selc
               | ident.fancy_selm _
               | ident.fancy_sell
               | ident.fancy_addm
                 => fun _ => type.interpM_return _ _ _ (inr ["Invalid identifier in arithmetic expression " ++ show true idc]%string)
               end%core%Cexpr%option%zrange.

          Fixpoint collect_args_and_apply_unknown_casts {t}
            : (int.option.interp (type.final_codomain t) -> type.interpM_final (fun T => ErrT T) arith_expr_for_base t)
              -> type.interpM_final
                  (fun T => ErrT T)
                  (fun t => int.option.interp t -> ErrT (arith_expr_for_base t))
                  t
            := match t
                     return ((int.option.interp (type.final_codomain t) -> type.interpM_final (fun T => ErrT T) arith_expr_for_base t)
                             -> type.interpM_final
                                 (fun T => ErrT T)
                                 (fun t => int.option.interp t -> ErrT (arith_expr_for_base t))
                                 t)
               with
               | type.base t => fun v => ret v
               | type.arrow (type.base s) d
                 => fun f
                     (x : (int.option.interp s -> ErrT (arith_expr_for_base s)))
                   => match x int.option.None with
                     | inl x'
                       => @collect_args_and_apply_unknown_casts
                           d
                           (fun rout => f rout x')
                     | inr errs => type.interpM_return _ _ _ (inr errs)
                     end
               | type.arrow (type.arrow _ _) _
                 => fun _ => type.interpM_return _ _ _ (inr ["Invalid higher-order function"])
               end.

          Definition collect_args_and_apply_known_casts {t}
                     (idc : ident.ident t)
            : ErrT (type.interpM_final
                      (fun T => ErrT T)
                      (fun t => int.option.interp t -> ErrT (arith_expr_for_base t))
                      t)
            := match idc in ident.ident t
                     return ErrT
                              (type.interpM_final
                                 (fun T => ErrT T)
                                 (fun t => int.option.interp t -> ErrT (arith_expr_for_base t))
                                 t)
               with
               | ident.Z_cast r
                 => inl (fun arg => inl (fun r' => arg <- arg (Some (int.of_zrange_relaxed r)); ret (Zcast_down_if_needed r' arg)))
               | ident.Z_cast2 (r1, r2)
                 => inl (fun arg => inl (fun r' => arg <- (arg (Some (int.of_zrange_relaxed r1), Some (int.of_zrange_relaxed r2)));
                                              ret (cast_down_if_needed (t:=base.type.Z*base.type.Z) r' arg)))
               | ident.pair A B
                 => inl (fun ea eb
                        => inl
                            (fun '(ra, rb)
                             => ea' ,, eb' <- ea ra, eb rb;
                                 inl (ea', eb')))
               | ident.nil _
                 => inl (inl (fun _ => inl nil))
               | ident.cons t
                 => inl
                     (fun x xs
                      => inl
                          (fun rls
                           => let mkcons (r : int.option.interp t)
                                        (rs : int.option.interp (base.type.list t))
                                 := x ,, xs <- x r, xs rs;
                                      inl (cons x xs) in
                             match rls with
                             | Some (cons r rs) => mkcons r (Some rs)
                             | Some nil
                             | None
                               => mkcons int.option.None int.option.None
                             end))
               | _ => inr ["Invalid identifier where cast or constructor was expected: " ++ show false idc]%string
               end.

          Definition collect_args_and_apply_casts {t} (idc : ident.ident t)
                     (convert_no_cast : int.option.interp (type.final_codomain t) -> type.interpM_final (fun T => ErrT T) arith_expr_for_base t)
            : type.interpM_final
                (fun T => ErrT T)
                (fun t => int.option.interp t -> ErrT (arith_expr_for_base t))
                t
            := match collect_args_and_apply_known_casts idc with
               | inl res => res
               | inr errs => collect_args_and_apply_unknown_casts convert_no_cast
               end.

          Fixpoint arith_expr_of_base_PHOAS_Var
                   {t}
            : base_var_data t -> int.option.interp t -> ErrT (arith_expr_for_base t)
            := match t with
               | base.type.Z
                 => fun '(n, r) r' => ret (cast_down_if_needed r' (Var type.Z n, r))
               | base.type.prod A B
                 => fun '(da, db) '(ra, rb)
                   => (ea,, eb <- @arith_expr_of_base_PHOAS_Var A da ra, @arith_expr_of_base_PHOAS_Var B db rb;
                        inl (ea, eb))
               | base.type.list base.type.Z
                 => fun '(n, r, len) r'
                   => ret (List.map
                            (fun i => (List_nth i @@ Var type.Zptr n, r))%core%Cexpr
                            (List.seq 0 len))
               | base.type.list _
               | base.type.type_base _
                 => fun _ _ => inr ["Invalid type " ++ show false t]%string
               end.

          Fixpoint arith_expr_of_PHOAS
                   {t}
                   (e : @Compilers.expr.expr base.type ident.ident var_data t)
            : type.interpM_final
                (fun T => ErrT T)
                (fun t => int.option.interp t -> ErrT (arith_expr_for_base t))
                t
            := match e in expr.expr t
                     return type.interpM_final
                              (fun T => ErrT T)
                              (fun t => int.option.interp t -> ErrT (arith_expr_for_base t))
                              t
               with
               | expr.Var (type.base _) v
                 => ret (arith_expr_of_base_PHOAS_Var v)
               | expr.Ident t idc
                 => collect_args_and_apply_casts idc (arith_expr_of_PHOAS_ident idc)
               | expr.App (type.base s) d f x
                 => let x' := @arith_expr_of_PHOAS s x in
                   match x' with
                   | inl x' => @arith_expr_of_PHOAS _ f x'
                   | inr errs => type.interpM_return _ _ _ (inr errs)
                   end
               | expr.Var (type.arrow _ _) _
                 => type.interpM_return _ _ _ (inr ["Invalid non-arithmetic let-bound Var of type " ++ show false t]%string)
               | expr.App (type.arrow _ _) _ _ _
                 => type.interpM_return _ _ _ (inr ["Invalid non-arithmetic let-bound App of type " ++ show false t]%string)
               | expr.LetIn _ _ _ _
                 => type.interpM_return _ _ _ (inr ["Invalid non-arithmetic let-bound LetIn of type " ++ show false t]%string)
               | expr.Abs _ _ _
                 => type.interpM_return _ _ _ (inr ["Invalid non-arithmetic let-bound Abs of type: " ++ show false t]%string)
               end.

          Definition arith_expr_of_base_PHOAS
                     {t:base.type}
                     (e : @Compilers.expr.expr base.type ident.ident var_data t)
                     (rout : int.option.interp t)
            : ErrT (arith_expr_for_base t)
            := (e' <- arith_expr_of_PHOAS e; e' rout).

          Fixpoint make_return_assignment_of_base_arith {t}
            : base_var_data t
              -> @Compilers.expr.expr base.type ident.ident var_data t
              -> ErrT expr
            := match t return base_var_data t -> expr.expr t -> ErrT expr with
               | base.type.Z
                 => fun '(n, r) e
                   => (rhs <- arith_expr_of_base_PHOAS e r;
                        let '(e, r) := rhs in
                        ret [AssignZPtr n r e])
               | base.type.type_base _ => fun _ _ => inr ["Invalid type " ++ show false t]%string
               | base.type.prod A B
                 => fun '(rva, rvb) e
                   => match invert_pair e with
                     | Some (ea, eb)
                       => ea',, eb' <- @make_return_assignment_of_base_arith A rva ea, @make_return_assignment_of_base_arith B rvb eb;
                           ret (ea' ++ eb')
                     | None => inr ["Invalid non-pair expr of type " ++ show false t]%string
                     end
               | base.type.list base.type.Z
                 => fun '(n, r, len) e
                   => (ls <- arith_expr_of_base_PHOAS e (Some (repeat r len));
                        ret (List.map
                               (fun '(i, (e, _)) => AssignNth n i e)
                               (List.combine (List.seq 0 len) ls)))
               | base.type.list _ => fun _ _ => inr ["Invalid type of expr: " ++ show false t]%string
               end%list.
          Definition make_return_assignment_of_arith {t}
            : var_data t
              -> @Compilers.expr.expr base.type ident.ident var_data t
              -> ErrT expr
            := match t with
               | type.base t => make_return_assignment_of_base_arith
               | type.arrow s d => fun _ _ => inr ["Invalid type of expr: " ++ show false t]%string
               end.

          Definition report_type_mismatch (expected : defaults.type) (given : defaults.type) : string
            := ("Type mismatch; expected " ++ show false expected ++ " but given " ++ show false given ++ ".")%string.

          Fixpoint arith_expr_of_PHOAS_args
                   {t}
            : type.for_each_lhs_of_arrow (@Compilers.expr.expr base.type ident.ident var_data) t
              -> ErrT (type.for_each_lhs_of_arrow (fun t => @Compilers.expr.expr base.type ident.ident var_data t * (arith_expr type.Z * option int.type)) t)
            := match t with
               | type.base t => fun 'tt => inl tt
               | type.arrow (type.base base.type.Z) d
                 => fun '(arg, args)
                   => arg' ,, args' <- arith_expr_of_base_PHOAS arg int.option.None , @arith_expr_of_PHOAS_args d args;
                       inl ((arg, arg'), args')
               | type.arrow s d
                 => fun '(arg, args)
                   => arg' ,, args' <- @inr unit _ ["Invalid argument of non-ℤ type " ++ show false s]%string , @arith_expr_of_PHOAS_args d args;
                       inr ["Impossible! (type error got lost somewhere)"]
               end.

          Let recognize_1ref_ident
                     {t}
                     (idc : ident.ident t)
                     (rout : option int.type)
            : type.for_each_lhs_of_arrow (fun t => @Compilers.expr.expr base.type ident.ident var_data t * (arith_expr type.Z * option int.type))%type t
              -> ErrT (arith_expr type.Zptr -> expr)
            := let _ := @PHOAS.expr.partially_show_expr in
               match idc with
               | ident.Z_zselect
                 => fun '((econdv, (econd, rcond)), ((e1v, (e1, r1)), ((e2v, (e2, r2)), tt)))
                   => match rcond with
                     | Some (int.unsigned 0)
                       => let r1 := option_map integer_promote_type r1 in
                         let r2 := option_map integer_promote_type r2 in
                         let '((e1, r1), (e2, r2))
                             := cast_bigger_up_if_needed rout ((e1, r1), (e2, r2)) in
                         let ct := (r1 <- r1; r2 <- r2; Some (common_type r1 r2))%option in
                         ty <- match ct, rout with
                              | Some ct, Some rout
                                => if int.type_beq ct rout
                                  then inl ct
                                  else inr ["Casting the result of Z.zselect to a type other than the common type is not currently supported.  (Cannot cast a pointer to " ++ show false rout ++ " to a pointer to " ++ show false ct ++ ".)"]%string
                              | None, _ => inr ["Unexpected None result of common-type calculation for Z.zselect"]
                              | _, None => inr ["Missing cast annotation on return of Z.zselect"]
                              end;
                           ret (fun retptr => [Call (Z_zselect ty @@ (retptr, (econd, e1, e2)))]%Cexpr)
                     | _ => inr ["Invalid argument to Z.zselect not known to be 0 or 1: " ++ show false econdv]%string
                     end
               | _ => fun _ => inr ["Unrecognized identifier (expecting a 1-pointer-returning function): " ++ show false idc]%string
               end.

          Definition bounds_check (do_bounds_check : bool) (descr : string) {t} (idc : ident.ident t) (s : BinInt.Z) {t'} (ev : @Compilers.expr.expr base.type ident.ident var_data t') (found : option int.type)
            : ErrT unit
            := if negb do_bounds_check
               then ret tt
               else
                 let _ := @PHOAS.expr.partially_show_expr in
                 match found with
                 | None => inr ["Missing range on " ++ descr ++ " " ++ show true idc ++ ": " ++ show true ev]%string
                 | Some ty
                   => if int.is_tighter_than ty (int.of_zrange_relaxed r[0~>2^s-1])
                      then ret tt
                      else inr ["Final bounds check failed on " ++ descr ++ " " ++ show false idc ++ "; expected an unsigned " ++ decimal_string_of_Z s ++ "-bit number (" ++ show false (int.of_zrange_relaxed r[0~>2^s-1]) ++ "), but found a " ++ show false ty ++ "."]%string
                 end.

          Let recognize_3arg_2ref_ident
                     (do_bounds_check : bool)
                     (t:=(base.type.Z -> base.type.Z -> base.type.Z -> base.type.Z * base.type.Z)%etype)
                     (idc : ident.ident t)
                     (rout : option int.type * option int.type)
                     (args : type.for_each_lhs_of_arrow (fun t => @Compilers.expr.expr base.type ident.ident var_data t * (arith_expr type.Z * option int.type))%type t)
            : ErrT (arith_expr (type.Zptr * type.Zptr) -> expr)
            := let _ := @PHOAS.expr.partially_show_expr in
               let '((s, _), ((e1v, (e1, r1)), ((e2v, (e2, r2)), tt))) := args in
               match (s <- invert_Literal s; maybe_log2 s)%option, idc return ErrT (arith_expr (type.Zptr * type.Zptr) -> expr)
               with
               | Some s, ident.Z_mul_split
                 => (_ ,, _ ,, _ ,, _
                      <- bounds_check do_bounds_check "first argument to" idc s e1v r1,
                    bounds_check do_bounds_check "second argument to" idc s e2v r2,
                    bounds_check do_bounds_check "first return value of" idc s e2v (fst rout),
                    bounds_check do_bounds_check "second return value of" idc s e2v (snd rout);
                      inl (fun retptr => [Call (Z_mul_split s @@ (retptr, (e1, e2)))%Cexpr]))
               | Some s, ident.Z_add_get_carry as idc
               | Some s, ident.Z_sub_get_borrow as idc
                 => let idc' : ident _ _ := invert_Some match idc with
                                                       | ident.Z_add_get_carry => Some (Z_add_with_get_carry s)
                                                       | ident.Z_sub_get_borrow => Some (Z_sub_with_get_borrow s)
                                                       | _ => None
                                                       end in
                   (_ ,, _ ,, _ ,, _
                      <- bounds_check do_bounds_check "first argument to" idc s e1v r1,
                    bounds_check do_bounds_check "second argument to" idc s e2v r2,
                    bounds_check do_bounds_check "first return value of" idc s e2v (fst rout),
                    bounds_check do_bounds_check "second return value of" idc 1 (* boolean carry/borrow *) e2v (snd rout);
                      inl (fun retptr => [Call (idc' @@ (retptr, (literal 0 @@ TT, e1, e2)))%Cexpr]))
               | Some _, _ => inr ["Unrecognized identifier when attempting to construct an assignment with 2 arguments: " ++ show true idc]%string
               | None, _ => inr ["Expression is not a literal power of two of type ℤ: " ++ show true s ++ " (when trying to parse the first argument of " ++ show true idc ++ ")"]%string
               end.

          Let recognize_4arg_2ref_ident
                     (do_bounds_check : bool)
                     (t:=(base.type.Z -> base.type.Z -> base.type.Z -> base.type.Z -> base.type.Z * base.type.Z)%etype)
                     (idc : ident.ident t)
                     (rout : option int.type * option int.type)
                     (args : type.for_each_lhs_of_arrow (fun t => @Compilers.expr.expr base.type ident.ident var_data t * (arith_expr type.Z * option int.type))%type t)
            : ErrT (arith_expr (type.Zptr * type.Zptr) -> expr)
            := let _ := @PHOAS.expr.partially_show_expr in
               let '((s, _), ((e1v, (e1, r1)), ((e2v, (e2, r2)), ((e3v, (e3, r3)), tt)))) := args in
               match (s <- invert_Literal s; maybe_log2 s)%option, idc return ErrT (arith_expr (type.Zptr * type.Zptr) -> expr)
               with
               | Some s, ident.Z_add_with_get_carry as idc
               | Some s, ident.Z_sub_with_get_borrow as idc
                 => let idc' : ident _ _ := invert_Some match idc with
                                                       | ident.Z_add_with_get_carry => Some (Z_add_with_get_carry s)
                                                       | ident.Z_sub_with_get_borrow => Some (Z_sub_with_get_borrow s)
                                                       | _ => None
                                                       end in
                   (_ ,, _ ,, _ ,, _ ,, _
                      <- (bounds_check do_bounds_check "first (carry) argument to" idc 1 e1v r1,
                         bounds_check do_bounds_check "second argument to" idc s e2v r2,
                         bounds_check do_bounds_check "third argument to" idc s e2v r2,
                         bounds_check do_bounds_check "first return value of" idc s e2v (fst rout),
                         bounds_check do_bounds_check "second (carry) return value of" idc 1 (* boolean carry/borrow *) e2v (snd rout));
                      inl (fun retptr => [Call (idc' @@ (retptr, (e1, e2, e3)))%Cexpr]))
               | Some _, _ => inr ["Unrecognized identifier when attempting to construct an assignment with 2 arguments: " ++ show true idc]%string
               | None, _ => inr ["Expression is not a literal power of two of type ℤ: " ++ show true s ++ " (when trying to parse the first argument of " ++ show true idc ++ ")"]%string
               end.

          Let recognize_2ref_ident
                     {t}
            : forall (do_bounds_check : bool)
                (idc : ident.ident t)
                (rout : option int.type * option int.type)
                (args : type.for_each_lhs_of_arrow (fun t => @Compilers.expr.expr base.type ident.ident var_data t * (arith_expr type.Z * option int.type))%type t),
              ErrT (arith_expr (type.Zptr * type.Zptr) -> expr)
            := match t with
               | (type.base base.type.Z -> type.base base.type.Z -> type.base base.type.Z -> type.base (base.type.Z * base.type.Z))%etype
                 => recognize_3arg_2ref_ident
               | (type.base base.type.Z -> type.base base.type.Z -> type.base base.type.Z -> type.base base.type.Z -> type.base (base.type.Z * base.type.Z))%etype
                 => recognize_4arg_2ref_ident
               | _ => fun do_bounds_check idc rout args => inr ["Unrecognized type for function call: " ++ show false t ++ " (when trying to handle the identifer " ++ show false idc ++ ")"]%string
               end.

          Definition declare_name
                     (descr : string)
                     (count : positive)
                     (make_name : positive -> option string)
                     (r : option int.type)
            : ErrT (expr * string * arith_expr type.Zptr)
            := (n ,, r <- (match make_name count with
                          | Some n => ret n
                          | None => inr ["Variable naming-function does not support the index " ++ show false count]%string
                          end,
                          match r with
                          | Some r => ret r
                          | None => inr ["Missing return type annotation for " ++ descr]%string
                          end);
                  ret ([DeclareVar type.Z (Some r) n], n, (Addr @@ Var type.Z n)%Cexpr)).

          Let make_assign_arg_1ref_opt
                     (e : @Compilers.expr.expr base.type ident.ident var_data base.type.Z)
                     (count : positive)
                     (make_name : positive -> option string)
            : ErrT (expr * var_data base.type.Z)
            := let _ := @PHOAS.expr.partially_show_expr in
               let e1 := e in
               let '(rout, e) := match invert_Z_cast e with
                                 | Some (r, e) => (Some (int.of_zrange_relaxed r), e)
                                 | None => (None, e)
                                 end%core in
               let res_ref
                   := match invert_AppIdent_curried e with
                      | Some (existT _ (idc, args))
                        => args <- arith_expr_of_PHOAS_args args;
                            idce <- recognize_1ref_ident idc rout args;
                            v <- declare_name (show false idc) count make_name rout;
                            let '(decls, n, retv) := v in
                            ret ((decls ++ (idce retv))%list, (n, rout))
                      | None => inr ["Invalid assignment of non-identifier-application: " ++ show false e]%string
                      end in
               match res_ref with
               | inl res => ret res
               | inr _
                 => e1 <- arith_expr_of_base_PHOAS e1 None;
                     let '(e1, r1) := e1 in
                     match make_name count with
                     | Some n1
                       => ret ([Assign true type.Z r1 n1 e1], (n1, r1))
                     | None => inr ["Variable naming-function does not support the index " ++ show false count]%string
                     end
               end.

          Let make_assign_arg_2ref
                     (do_bounds_check : bool)
                     (e : @Compilers.expr.expr base.type ident.ident var_data (base.type.Z * base.type.Z))
                     (count : positive)
                     (make_name : positive -> option string)
            : ErrT (expr * var_data (base.type.Z * base.type.Z))
            := let _ := @PHOAS.expr.partially_show_expr in
               let '((rout1, rout2), e)
                   := match invert_Z_cast2 e with
                      | Some ((r1, r2), e) => ((Some (int.of_zrange_relaxed r1), Some (int.of_zrange_relaxed r2)), e)
                      | None => ((None, None), e)
                      end%core in
               match invert_AppIdent_curried e with
               | Some (existT t (idc, args))
                 => args <- arith_expr_of_PHOAS_args args;
                     idce <- recognize_2ref_ident do_bounds_check idc (rout1, rout2) args;
                     v1,, v2 <- (declare_name (show false idc) count make_name rout1,
                                declare_name (show false idc) (Pos.succ count) make_name rout2);
                     let '(decls1, n1, retv1) := v1 in
                     let '(decls2, n2, retv2) := v2 in
                     ret (decls1 ++ decls2 ++ (idce (retv1, retv2)%Cexpr), ((n1, rout1), (n2, rout2)))%list
               | None => inr ["Invalid assignment of non-identifier-application: " ++ show false e]%string
               end.

          Let make_assign_arg_ref
                     (do_bounds_check : bool)
                     {t}
            : forall (e : @Compilers.expr.expr base.type ident.ident var_data t)
                (count : positive)
                (make_name : positive -> option string),
              ErrT (expr * var_data t)
            := let _ := @PHOAS.expr.partially_show_expr in
               match t with
               | type.base base.type.Z => make_assign_arg_1ref_opt
               | type.base (base.type.Z * base.type.Z)%etype => make_assign_arg_2ref do_bounds_check
               | _ => fun e _ _ => inr ["Invalid type of assignment expression: " ++ show false t ++ " (with expression " ++ show true e ++ ")"]
               end.

          Fixpoint size_of_type (t : base.type) : positive
            := match t with
               | base.type.type_base t => 1
               | base.type.prod A B => size_of_type A + size_of_type B
               | base.type.list A => 1
               end%positive.

          Let make_uniform_assign_expr_of_PHOAS
                     (do_bounds_check : bool)
                     {s} (e1 : @Compilers.expr.expr base.type ident.ident var_data s)
                     {d} (e2 : var_data s -> var_data d -> ErrT expr)
                     (count : positive)
                     (make_name : positive -> option string)
                     (vd : var_data d)
            : ErrT expr
            := let _ := @PHOAS.expr.partially_show_expr in (* for TC resolution *)
               e1_vs <- make_assign_arg_ref do_bounds_check e1 count make_name;
                 let '(e1, vs) := e1_vs in
                 e2 <- e2 vs vd;
                   ret (e1 ++ e2)%list.

          (* See above comment about extraction issues *)
          Definition make_assign_expr_of_PHOAS
                     (do_bounds_check : bool)
                     {s} (e1 : @Compilers.expr.expr base.type ident.ident var_data s)
                     {s' d} (e2 : var_data s' -> var_data d -> ErrT expr)
                     (count : positive)
                     (make_name : positive -> option string)
                     (v : var_data d)
            : ErrT expr
            := Eval cbv beta iota delta [bind2_err bind3_err bind4_err bind5_err recognize_1ref_ident recognize_3arg_2ref_ident recognize_4arg_2ref_ident recognize_2ref_ident make_assign_arg_1ref_opt make_assign_arg_2ref make_assign_arg_ref make_uniform_assign_expr_of_PHOAS make_uniform_assign_expr_of_PHOAS] in
                match type.try_transport base.try_make_transport_cps _ _ s' e1 with
                | Some e1 => make_uniform_assign_expr_of_PHOAS do_bounds_check e1 e2 count make_name v
                | None => inr [report_type_mismatch s' s]
                end.

          Fixpoint expr_of_base_PHOAS
                   (do_bounds_check : bool)
                   {t}
                   (e : @Compilers.expr.expr base.type ident.ident var_data t)
                   (count : positive)
                   (make_name : positive -> option string)
                   {struct e}
            : forall (ret_val : var_data t), ErrT expr
            := match e in expr.expr t return var_data t -> ErrT expr with
               | expr.LetIn (type.base s) d e1 e2
                 => make_assign_expr_of_PHOAS
                      do_bounds_check
                     e1
                     (fun vs vd => @expr_of_base_PHOAS do_bounds_check d (e2 vs) (size_of_type s + count)%positive make_name vd)
                     count make_name
               | expr.LetIn (type.arrow _ _) _ _ _ as e
               | expr.Var _ _ as e
               | expr.Ident _ _ as e
               | expr.App _ _ _ _ as e
               | expr.Abs _ _ _ as e
                 => fun v => make_return_assignment_of_arith v e
               end%expr_pat%option.

          Fixpoint base_var_data_of_bounds {t}
                   (count : positive)
                   (make_name : positive -> option string)
                   {struct t}
            : ZRange.type.base.option.interp t -> option (positive * var_data t)
            := match t return ZRange.type.base.option.interp t -> option (positive * var_data t) with
               | base.type.Z
                 => fun r => (n <- make_name count;
                            Some (Pos.succ count, (n, option_map int.of_zrange_relaxed r)))
               | base.type.prod A B
                 => fun '(ra, rb)
                   => (va <- @base_var_data_of_bounds A count make_name ra;
                        let '(count, va) := va in
                        vb <- @base_var_data_of_bounds B count make_name rb;
                          let '(count, vb) := vb in
                          Some (count, (va, vb)))
               | base.type.list base.type.Z
                 => fun r
                   => (ls <- r;
                        n <- make_name count;
                        Some (Pos.succ count,
                              (n,
                               match List.map (option_map int.of_zrange_relaxed) ls with
                               | nil => None
                               | cons x xs
                                 => List.fold_right
                                     (fun r1 r2 => r1 <- r1; r2 <- r2; Some (int.union r1 r2))
                                     x
                                     xs
                               end,
                               length ls)))
               | base.type.unit
                 => fun _ => Some (count, tt)
               | base.type.list _
               | base.type.type_base _
                 => fun _ => None
               end%option.

          Definition var_data_of_bounds {t}
                     (count : positive)
                     (make_name : positive -> option string)
            : ZRange.type.option.interp t -> option (positive * var_data t)
            := match t with
               | type.base t => base_var_data_of_bounds count make_name
               | type.arrow s d => fun _ => None
               end.

          Fixpoint expr_of_PHOAS'
                   (do_bounds_check : bool)
                   {t}
                   (e : @Compilers.expr.expr base.type ident.ident var_data t)
                   (make_in_name : positive -> option string)
                   (make_name : positive -> option string)
                   (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                   (out_data : var_data (type.final_codomain t))
                   (count : positive)
                   (in_to_body_count : positive -> positive)
                   {struct t}
            : ErrT (type.for_each_lhs_of_arrow var_data t * var_data (type.final_codomain t) * expr)
            := let _ := @PHOAS.expr.partially_show_expr in (* for TC resolution *)
               match t return @Compilers.expr.expr base.type ident.ident var_data t -> type.for_each_lhs_of_arrow ZRange.type.option.interp t -> var_data (type.final_codomain t) -> ErrT (type.for_each_lhs_of_arrow var_data t * var_data (type.final_codomain t) * expr) with
               | type.base t
                 => fun e tt vd
                   => rv <- expr_of_base_PHOAS do_bounds_check e (in_to_body_count count) make_name vd;
                       ret (tt, vd, rv)
               | type.arrow s d
                 => fun e '(inbound, inbounds) vd
                   => match var_data_of_bounds count make_in_name inbound, invert_Abs e with
                     | Some (count, vs), Some f
                       => retv <- @expr_of_PHOAS' do_bounds_check d (f vs) make_in_name make_name inbounds vd count in_to_body_count;
                           let '(vss, vd, rv) := retv in
                           ret (vs, vss, vd, rv)
                     | None, _ => inr ["Unable to bind names for all arguments and bounds at type " ++ show false s]%string%list
                     | _, None => inr ["Invalid non-λ expression of arrow type (" ++ show false t ++ "): " ++ show true e]%string%list
                     end
               end%core%expr e inbounds out_data.

          Definition expr_of_PHOAS
                     (do_bounds_check : bool)
                     {t}
                     (e : @Compilers.expr.expr base.type ident.ident var_data t)
                     (make_in_name : positive -> option string)
                     (make_out_name : positive -> option string)
                     (make_name : positive -> option string)
                     (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                     (outbounds : ZRange.type.option.interp (type.final_codomain t))
                     (count : positive)
                     (in_to_body_count out_to_in_count : positive -> positive)
            : ErrT (type.for_each_lhs_of_arrow var_data t * var_data (type.final_codomain t) * expr)
            := match var_data_of_bounds count make_out_name outbounds with
               | Some vd
                 => let '(count, vd) := vd in
                   let count := out_to_in_count count in
                   @expr_of_PHOAS' do_bounds_check t e make_in_name make_name inbounds vd count in_to_body_count
               | None => inr ["Unable to bind names for all return arguments and bounds at type " ++ show false (type.final_codomain t)]%string
               end.

          Definition ExprOfPHOAS
                     (do_bounds_check : bool)
                     {t}
                     (e : @Compilers.expr.Expr base.type ident.ident t)
                     (name_list : option (list string))
                     (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
            : ErrT (type.for_each_lhs_of_arrow var_data t * var_data (type.final_codomain t) * expr)
            := (let outbounds := partial.Extract e inbounds in
                let make_name_gen prefix := match name_list with
                                            | None => fun p => Some (prefix ++ decimal_string_of_Z (Zpos p))
                                            | Some ls => fun p => List.nth_error ls (pred (Pos.to_nat p))
                                            end in
                let make_in_name := make_name_gen "arg" in
                let make_out_name := make_name_gen "out" in
                let make_name := make_name_gen "x" in
                let reset_if_names_given := match name_list with
                                            | Some _ => fun p : positive => p
                                            | None => fun _ : positive => 1%positive
                                            end in
                expr_of_PHOAS do_bounds_check (e _) make_in_name make_out_name make_name inbounds outbounds 1 reset_if_names_given reset_if_names_given).
        End with_bind.
      End OfPHOAS.

      Module String.
        Definition typedef_header (prefix : string) (bitwidths_used : PositiveSet.t)
        : list string
          := (["#include <stdint.h>"]
                ++ (if PositiveSet.mem 1 bitwidths_used
                    then ["typedef unsigned char " ++ prefix ++ "uint1;";
                            "typedef signed char " ++ prefix ++ "int1;"]%string
                    else [])
                ++ (if PositiveSet.mem 128 bitwidths_used
                    then ["typedef signed __int128 " ++ prefix ++ "int128;";
                            "typedef unsigned __int128 " ++ prefix ++ "uint128;"]%string
                    else []))%list.

        Definition stdint_bitwidths : list Z := [8; 16; 32; 64].
        Definition is_special_bitwidth (bw : Z) := negb (existsb (Z.eqb bw) stdint_bitwidths).

        Module int.
          Module type.
            Definition to_string (prefix : string) (t : int.type) : string
              := ((if is_special_bitwidth (int.bitwidth_of t) then prefix else "")
                    ++ (if int.is_unsigned t then "u" else "")
                    ++ "int"
                    ++ decimal_string_of_Z (int.bitwidth_of t)
                    ++ (if is_special_bitwidth (int.bitwidth_of t) then "" else "_t"))%string.
            Definition to_literal_macro_string (t : int.type) : option string
              := if Z.ltb (int.bitwidth_of t) 8
                 then None
                 else Some ((if int.is_unsigned t then "U" else "")
                              ++ "INT"
                              ++ decimal_string_of_Z (int.bitwidth_of t)
                              ++ "_C")%string.
          End type.
        End int.

        Module type.
          Module primitive.
            Definition to_string (prefix : string) (t : type.primitive) (r : option int.type) : string
              := match r with
                 | Some int_t => int.type.to_string prefix int_t
                 | None => "ℤ"
                 end ++ match t with
                        | type.Zptr => "*"
                        | type.Z => ""
                        end.
          End primitive.
        End type.
      End String.

      Module primitive.
        Definition to_string (prefix : string) (t : type.primitive) (v : BinInt.Z) : string
          := match t, String.int.type.to_literal_macro_string (int.of_zrange_relaxed r[v ~> v]) with
             | type.Z, Some macro
               => macro ++ "(" ++ HexString.of_Z v ++ ")"
             | type.Z, None => HexString.of_Z v
             | type.Zptr, _ => "#error ""literal address " ++ HexString.of_Z v ++ """;"
             end.
      End primitive.

      Fixpoint arith_to_string (prefix : string) {t} (e : arith_expr t) : string
        := match e with
           | (literal v @@ _) => primitive.to_string prefix type.Z v
           | (List_nth n @@ Var _ v)
             => "(" ++ v ++ "[" ++ decimal_string_of_Z (Z.of_nat n) ++ "])"
           | (Addr @@ Var _ v) => "&" ++ v
           | (Dereference @@ e) => "( *" ++ @arith_to_string prefix _ e ++ " )"
           | (Z_shiftr offset @@ e)
             => "(" ++ @arith_to_string prefix _ e ++ " >> " ++ decimal_string_of_Z offset ++ ")"
           | (Z_shiftl offset @@ e)
             => "(" ++ @arith_to_string prefix _ e ++ " << " ++ decimal_string_of_Z offset ++ ")"
           | (Z_land @@ (e1, e2))
             => "(" ++ @arith_to_string prefix _ e1 ++ " & " ++ @arith_to_string prefix _ e2 ++ ")"
           | (Z_lor @@ (e1, e2))
             => "(" ++ @arith_to_string prefix _ e1 ++ " | " ++ @arith_to_string prefix _ e2 ++ ")"
           | (Z_add @@ (x1, x2))
             => "(" ++ @arith_to_string prefix _ x1 ++ " + " ++ @arith_to_string prefix _ x2 ++ ")"
           | (Z_mul @@ (x1, x2))
             => "(" ++ @arith_to_string prefix _ x1 ++ " * " ++ @arith_to_string prefix _ x2 ++ ")"
           | (Z_sub @@ (x1, x2))
             => "(" ++ @arith_to_string prefix _ x1 ++ " - " ++ @arith_to_string prefix _ x2 ++ ")"
           | (Z_opp @@ e)
             => "(-" ++ @arith_to_string prefix _ e ++ ")"
           | (Z_lnot _ @@ e)
             => "(~" ++ @arith_to_string prefix _ e ++ ")"
           | (Z_bneg @@ e)
             => "(!" ++ @arith_to_string prefix _ e ++ ")"
           | (Z_mul_split lg2s @@ args)
             => prefix
                 ++ "mulx_u"
                 ++ decimal_string_of_Z lg2s ++ "(" ++ @arith_to_string prefix _ args ++ ")"
           | (Z_add_with_get_carry lg2s @@ args)
             => prefix
                 ++ "addcarryx_u"
                 ++ decimal_string_of_Z lg2s ++ "(" ++ @arith_to_string prefix _ args ++ ")"
           | (Z_sub_with_get_borrow lg2s @@ args)
             => prefix
                 ++ "subborrowx_u"
                 ++ decimal_string_of_Z lg2s ++ "(" ++ @arith_to_string prefix _ args ++ ")"
           | (Z_zselect ty @@ args)
             => prefix
                 ++ "cmovznz_"
                 ++ (if int.is_unsigned ty then "u" else "")
                 ++ decimal_string_of_Z (int.bitwidth_of ty) ++ "(" ++ @arith_to_string prefix _ args ++ ")"
           | (Z_add_modulo @@ (x1, x2, x3)) => "#error addmodulo;"
           | (Z_static_cast int_t @@ e)
             => "(" ++ String.type.primitive.to_string prefix type.Z (Some int_t) ++ ")"
                    ++ @arith_to_string prefix _ e
           | Var _ v => v
           | Pair A B a b
             => @arith_to_string prefix A a ++ ", " ++ @arith_to_string prefix B b
           | (List_nth _ @@ _)
           | (Addr @@ _)
           | (Z_add @@ _)
           | (Z_mul @@ _)
           | (Z_sub @@ _)
           | (Z_land @@ _)
           | (Z_lor @@ _)
           | (Z_add_modulo @@ _)
             => "#error bad_arg;"
           | TT
             => "#error tt;"
           end%core%Cexpr.

      Fixpoint stmt_to_string (prefix : string) (e : stmt) : string
        := match e with
           | Call val
             => arith_to_string prefix val ++ ";"
           | Assign true t sz name val
             => String.type.primitive.to_string prefix t sz ++ " " ++ name ++ " = " ++ arith_to_string prefix val ++ ";"
           | Assign false _ sz name val
             => name ++ " = " ++ arith_to_string prefix val ++ ";"
           | AssignZPtr name sz val
             => "*" ++ name ++ " = " ++ arith_to_string prefix val ++ ";"
           | DeclareVar t sz name
             => String.type.primitive.to_string prefix t sz ++ " " ++ name ++ ";"
           | AssignNth name n val
             => name ++ "[" ++ decimal_string_of_Z (Z.of_nat n) ++ "] = " ++ arith_to_string prefix val ++ ";"
           end.
      Definition to_strings (prefix : string) (e : expr) : list string
        := List.map (stmt_to_string prefix) e.

      Record ident_infos :=
        { bitwidths_used : PositiveSet.t;
          addcarryx_lg_splits : PositiveSet.t;
          mulx_lg_splits : PositiveSet.t;
          cmovznz_bitwidths : PositiveSet.t }.
      Definition ident_info_empty : ident_infos
        := Build_ident_infos PositiveSet.empty PositiveSet.empty PositiveSet.empty PositiveSet.empty.
      Definition ident_info_union (x y : ident_infos) : ident_infos
        := let (x0, x1, x2, x3) := x in
           let (y0, y1, y2, y3) := y in
           Build_ident_infos
             (PositiveSet.union x0 y0)
             (PositiveSet.union x1 y1)
             (PositiveSet.union x2 y2)
             (PositiveSet.union x3 y3).
      Definition ident_info_of_bitwidths_used (v : PositiveSet.t) : ident_infos
        := {| bitwidths_used := v;
              addcarryx_lg_splits := PositiveSet.empty;
              mulx_lg_splits := PositiveSet.empty;
              cmovznz_bitwidths := PositiveSet.empty |}.
      Definition ident_info_of_addcarryx (v : PositiveSet.t) : ident_infos
        := {| bitwidths_used := PositiveSet.empty;
              addcarryx_lg_splits := v;
              mulx_lg_splits := PositiveSet.empty;
              cmovznz_bitwidths := PositiveSet.empty |}.
      Definition ident_info_of_mulx (v : PositiveSet.t) : ident_infos
        := {| bitwidths_used := PositiveSet.empty;
              addcarryx_lg_splits := PositiveSet.empty;
              mulx_lg_splits := v;
              cmovznz_bitwidths := PositiveSet.empty |}.
      Definition ident_info_of_cmovznz (v : PositiveSet.t) : ident_infos
        := {| bitwidths_used := PositiveSet.empty;
              addcarryx_lg_splits := PositiveSet.empty;
              mulx_lg_splits := PositiveSet.empty;
              cmovznz_bitwidths := v |}.

      Definition collect_bitwidths_of_int_type (t : int.type) : PositiveSet.t
        := PositiveSet.add (Z.to_pos (int.bitwidth_of t)) PositiveSet.empty.
      Definition collect_infos_of_ident {s d} (idc : ident s d) : ident_infos
        := match idc with
           | Z_static_cast ty => ident_info_of_bitwidths_used (collect_bitwidths_of_int_type ty)
           | Z_mul_split lg2s
             => ident_info_of_mulx (PositiveSet.add (Z.to_pos lg2s) PositiveSet.empty)
           | Z_add_with_get_carry lg2s
           | Z_sub_with_get_borrow lg2s
             => ident_info_of_addcarryx (PositiveSet.add (Z.to_pos lg2s) PositiveSet.empty)
           | Z_zselect ty
             => ident_info_of_cmovznz (collect_bitwidths_of_int_type ty)
           | literal _
           | List_nth _
           | Addr
           | Dereference
           | Z_shiftr _
           | Z_shiftl _
           | Z_land
           | Z_lor
           | Z_add
           | Z_mul
           | Z_sub
           | Z_opp
           | Z_bneg
           | Z_lnot _
           | Z_add_modulo
             => ident_info_empty
           end.
      Fixpoint collect_infos_of_arith_expr {t} (e : arith_expr t) : ident_infos
        := match e with
           | AppIdent s d idc arg => ident_info_union (collect_infos_of_ident idc) (@collect_infos_of_arith_expr _ arg)
           | Var t v => ident_info_empty
           | Pair A B a b => ident_info_union (@collect_infos_of_arith_expr _ a) (@collect_infos_of_arith_expr _ b)
           | TT => ident_info_empty
           end.

      Fixpoint collect_infos_of_stmt (e : stmt) : ident_infos
        := match e with
           | Assign _ _ (Some sz) _ val
           | AssignZPtr _ (Some sz) val
             => ident_info_union (ident_info_of_bitwidths_used (collect_bitwidths_of_int_type sz)) (collect_infos_of_arith_expr val)
           | Call val
           | Assign _ _ None _ val
           | AssignZPtr _ None val
           | AssignNth _ _ val
             => collect_infos_of_arith_expr val
           | DeclareVar _ (Some sz) _
             => ident_info_of_bitwidths_used (collect_bitwidths_of_int_type sz)
           | DeclareVar _ None _
             => ident_info_empty
           end.

      Fixpoint collect_infos (e : expr) : ident_infos
        := fold_right
             ident_info_union
             ident_info_empty
             (List.map
                collect_infos_of_stmt
                e).

      Import OfPHOAS.

      Fixpoint to_base_arg_list (prefix : string) {t} : base_var_data t -> list string
        := match t return base_var_data t -> _ with
           | base.type.Z
             => fun '(n, r) => [String.type.primitive.to_string prefix type.Z r ++ " " ++ n]
           | base.type.prod A B
             => fun '(va, vb) => (@to_base_arg_list prefix A va ++ @to_base_arg_list prefix B vb)%list
           | base.type.list base.type.Z
             => fun '(n, r, len) => ["const " ++ String.type.primitive.to_string prefix type.Z r ++ " " ++ n ++ "[" ++ decimal_string_of_Z (Z.of_nat len) ++ "]"]
           | base.type.list _ => fun _ => ["#error ""complex list"";"]
           | base.type.unit => fun _ => ["#error unit;"]
           | base.type.nat => fun _ => ["#error ℕ;"]
           | base.type.bool => fun _ => ["#error bool;"]
           end.

      Definition to_arg_list (prefix : string) {t} : var_data t -> list string
        := match t return var_data t -> _ with
           | type.base t => to_base_arg_list prefix
           | type.arrow _ _ => fun _ => ["#error arrow;"]
           end.

      Fixpoint to_arg_list_for_each_lhs_of_arrow (prefix : string) {t} : type.for_each_lhs_of_arrow var_data t -> list string
        := match t return type.for_each_lhs_of_arrow var_data t -> _ with
           | type.base t => fun _ => nil
           | type.arrow s d
             => fun '(x, xs)
                => to_arg_list prefix x ++ @to_arg_list_for_each_lhs_of_arrow prefix d xs
           end%list.

      Fixpoint to_base_retarg_list prefix {t} : base_var_data t -> list string
        := match t return base_var_data t -> _ with
           | base.type.Z
             => fun '(n, r) => [String.type.primitive.to_string prefix type.Zptr r ++ " " ++ n]
           | base.type.prod A B
             => fun '(va, vb) => (@to_base_retarg_list prefix A va ++ @to_base_retarg_list prefix B vb)%list
           | base.type.list base.type.Z
             => fun '(n, r, len) => [String.type.primitive.to_string prefix type.Z r ++ " " ++ n ++ "[" ++ decimal_string_of_Z (Z.of_nat len) ++ "]"]
           | base.type.list _ => fun _ => ["#error ""complex list"";"]
           | base.type.unit => fun _ => ["#error unit;"]
           | base.type.nat => fun _ => ["#error ℕ;"]
           | base.type.bool => fun _ => ["#error bool;"]
           end.

      Definition to_retarg_list (prefix : string) {t} : var_data t -> list string
        := match t return var_data t -> _ with
           | type.base _ => to_base_retarg_list prefix
           | type.arrow _ _ => fun _ => ["#error arrow;"]
           end.

      Fixpoint bound_to_string {t : base.type} : var_data t -> ZRange.type.base.option.interp t -> list string
        := match t return var_data t -> ZRange.type.base.option.interp t -> list string with
           | base.type.Z
             => fun '(name, _) arg
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
           | base.type.unit
           | base.type.bool
           | base.type.nat
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

      Definition to_function_lines (static : bool) (prefix : string) (name : string)
                 {t}
                 (f : type.for_each_lhs_of_arrow var_data t * var_data (type.final_codomain t) * expr)
        : list string
        := let '(args, rets, body) := f in
           (((((if static then "static " else "")
                 ++ "void "
                 ++ name ++ "("
                 ++ (String.concat ", " (to_retarg_list prefix rets ++ to_arg_list_for_each_lhs_of_arrow prefix args))
                 ++ ") {")%string)
               :: (List.map (fun s => "  " ++ s)%string (to_strings prefix body)))
              ++ ["}"])%list.

      Definition ToFunctionLines (do_bounds_check : bool) (static : bool) (prefix : string) (name : string) (comment : list string)
                 {t}
                 (e : @Compilers.expr.Expr base.type ident.ident t)
                 (name_list : option (list string))
                 (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                 (outbounds : ZRange.type.base.option.interp (type.final_codomain t))
        : (list string * ident_infos) + string
        := match ExprOfPHOAS do_bounds_check e name_list inbounds with
           | inl (indata, outdata, f)
             => inl ((["/*"]
                        ++ (List.map (fun s => " * " ++ s)%string comment)
                        ++ [" * Input Bounds:"]
                        ++ List.map (fun v => " *   " ++ v)%string (input_bounds_to_string indata inbounds)
                        ++ [" * Output Bounds:"]
                        ++ List.map (fun v => " *   " ++ v)%string (bound_to_string outdata outbounds)
                        ++ [" */"]
                        ++ to_function_lines static prefix name (indata, outdata, f))%list,
                     collect_infos f)
           | inr nil
             => inr ("Unknown internal error in converting " ++ name ++ " to C")%string
           | inr [err]
             => inr ("Error in converting " ++ name ++ " to C:" ++ String.NewLine ++ err)%string
           | inr errs
             => inr ("Errors in converting " ++ name ++ " to C:" ++ String.NewLine ++ String.concat String.NewLine errs)%string
           end.

      Definition LinesToString (lines : list string)
        : string
        := String.concat String.NewLine lines.

      Definition ToFunctionString (do_bounds_check : bool) (static : bool) (prefix : string) (name : string) (comment : list string)
                 {t}
                 (e : @Compilers.expr.Expr base.type ident.ident t)
                 (name_list : option (list string))
                 (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                 (outbounds : ZRange.type.option.interp (type.final_codomain t))
        : (string * ident_infos) + string
        := match ToFunctionLines do_bounds_check static prefix name comment e name_list inbounds outbounds with
           | inl (ls, used_types) => inl (LinesToString ls, used_types)
           | inr err => inr err
           end.
    End C.
    Notation ToFunctionLines := C.ToFunctionLines.
    Notation ToFunctionString := C.ToFunctionString.
    Notation LinesToString := C.LinesToString.
  End ToString.
End Compilers.
