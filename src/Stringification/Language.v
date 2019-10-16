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
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.Util.Bool.Equality.
Require Import Crypto.Util.Notations.
Import Coq.Lists.List ListNotations. Local Open Scope zrange_scope. Local Open Scope Z_scope.

Module Compilers.
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  Export Language.Language.Compilers.
  Export Language.API.Compilers.
  Export AbstractInterpretation.Compilers.
  Import invert_expr.
  Import Compilers.API.

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
          Fixpoint show_base_interp {t} : Show (base.base_interp t)
            := match t with
               | base.type.Z => @show Z _
               | base.type.bool => @show bool _
               | base.type.nat => @show nat _
               | base.type.zrange => @show zrange _
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
           | base.type.type_base base.type.Z => option_map show_range_or_ctype
           | base.type.prod A B
             => fun '(r1, r2)
                => match @make_castb A r1, @make_castb B r2 with
                   | Some c1, Some c2 => Some (c1 ++ ", " ++ c2)
                   | None, Some c => Some ("??, " ++ c)
                   | Some c, None => Some (c ++ ", ??")
                   | None, None => None
                   end
           | base.type.unit
           | base.type.type_base _
           | base.type.list _
           | base.type.option _
             => fun _ => None
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
             | ident.tt => fun _ => (fun _ => "()", tt)
             | ident.Nat_succ => fun '((x, xr), tt) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 10) ((x 10%nat) ++ ".+1"), ZRange.type.base.option.None)
             | ident.Nat_pred => fun '((x, xr), tt) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 10) ((x 10%nat) ++ ".-1"), ZRange.type.base.option.None)
             | ident.Nat_max => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 10) ("Nat.max " ++ x 9%nat ++ " " ++ y 9%nat), ZRange.type.base.option.None)
             | ident.Nat_mul => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 40) (x 40%nat ++ " *ℕ " ++ y 39%nat), ZRange.type.base.option.None)
             | ident.Nat_add => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 50) (x 50%nat ++ " +ℕ " ++ y 49%nat), ZRange.type.base.option.None)
             | ident.Nat_sub => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 50) (x 50%nat ++ " -ℕ " ++ y 49%nat), ZRange.type.base.option.None)
             | ident.Nat_eqb => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 70) (x 69%nat ++ " =ℕ " ++ y 69%nat), ZRange.type.base.option.None)
             | ident.Some _
               => fun args => (show_application with_casts (fun _ => "Some") args, ZRange.type.base.option.None)
             | ident.None _ => fun 'tt => (fun _ => "None", ZRange.type.base.option.None)
             | ident.nil t => fun 'tt => (fun _ => "[]", ZRange.type.base.option.None)
             | ident.cons t => fun '(x, ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 60) (maybe_wrap_cast with_casts x 59%nat ++ " :: " ++ y 60%nat), ZRange.type.base.option.None)
             | ident.pair A B => fun '(x, (y, tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 201) (maybe_wrap_cast with_casts x 201%nat ++ ", " ++ maybe_wrap_cast with_casts y 200%nat), ZRange.type.base.option.None)
             | ident.fst A B => fun '((x, xr), tt) => (fun _ => x 0%nat ++ "₁", fst xr)
             | ident.snd A B => fun '((x, xr), tt) => (fun _ => x 0%nat ++ "₂", snd xr)
             | ident.prod_rect A B T => fun '((f, fr), ((p, pr), tt)) => (fun _ => "match " ++ p 200%nat ++ " with " ++ f 200%nat ++ " end", ZRange.type.base.option.None)
             | ident.bool_rect T => fun '(t, (f, ((b, br), tt))) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 200) ("if " ++ b 200%nat ++ " then " ++ maybe_wrap_cast with_casts t 200%nat ++ " else " ++ maybe_wrap_cast with_casts f 200%nat), ZRange.type.base.option.None)
             | ident.nat_rect P
               => fun args => (show_application with_casts (fun _ => "nat_rect") args, ZRange.type.base.option.None)
             | ident.eager_nat_rect P
               => fun args => (show_application with_casts (fun _ => "eager_nat_rect") args, ZRange.type.base.option.None)
             | ident.eager_nat_rect_arrow P Q
               => fun args => (show_application with_casts (fun _ => "eager_nat_rect(→)") args, ZRange.type.base.option.None)
             | ident.nat_rect_arrow P Q
               => fun args => (show_application with_casts (fun _ => "nat_rect(→)") args, ZRange.type.base.option.None)
             | ident.option_rect A P
               => fun args => (show_application with_casts (fun _ => "option_rect") args, ZRange.type.base.option.None)
             | ident.list_rect A P
               => fun args => (show_application with_casts (fun _ => "list_rect") args, ZRange.type.base.option.None)
             | ident.eager_list_rect A P
               => fun args => (show_application with_casts (fun _ => "eager_list_rect") args, ZRange.type.base.option.None)
             | ident.list_rect_arrow A P Q
               => fun args => (show_application with_casts (fun _ => "list_rect(→)") args, ZRange.type.base.option.None)
             | ident.eager_list_rect_arrow A P Q
               => fun args => (show_application with_casts (fun _ => "eager_list_rect(→)") args, ZRange.type.base.option.None)
             | ident.list_case A P
               => fun args => (show_application with_casts (fun _ => "list_case") args, ZRange.type.base.option.None)
             | ident.List_length T
               => fun args => (show_application with_casts (fun _ => "len") args, ZRange.type.base.option.None)
             | ident.List_seq
               => fun args => (show_application with_casts (fun _ => "seq") args, ZRange.type.base.option.None)
             | ident.List_repeat A
               => fun args => (show_application with_casts (fun _ => "repeat") args, ZRange.type.base.option.None)
             | ident.List_firstn A
               => fun args => (show_application with_casts (fun _ => "firstn") args, ZRange.type.base.option.None)
             | ident.List_skipn A
               => fun args => (show_application with_casts (fun _ => "skipn") args, ZRange.type.base.option.None)
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
             | ident.Z_div => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 40) (x 40%nat ++ " / " ++ y 39%nat), ZRange.type.base.option.None)
             | ident.Z_modulo => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 40) (x 40%nat ++ " mod " ++ y 39%nat), ZRange.type.base.option.None)
             | ident.Z_eqb => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 70) (x 69%nat ++ " = " ++ y 69%nat), ZRange.type.base.option.None)
             | ident.Z_ltb => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 70) (x 69%nat ++ " < " ++ y 69%nat), ZRange.type.base.option.None)
             | ident.Z_leb => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 70) (x 69%nat ++ " ≤ " ++ y 69%nat), ZRange.type.base.option.None)
             | ident.Z_gtb => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 70) (x 69%nat ++ " > " ++ y 69%nat), ZRange.type.base.option.None)
             | ident.Z_geb => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 70) (x 69%nat ++ " ≥ " ++ y 69%nat), ZRange.type.base.option.None)
             | ident.Z_log2
               => fun args => (show_application with_casts (fun _ => "Z.log2") args, ZRange.type.base.option.None)
             | ident.Z_log2_up
               => fun args => (show_application with_casts (fun _ => "Z.log2_up") args, ZRange.type.base.option.None)
             | ident.Z_of_nat
               => fun args => (show_application with_casts (fun _ => "(ℕ→ℤ)") args, ZRange.type.base.option.None)
             | ident.Z_to_nat
               => fun args => (show_application with_casts (fun _ => "(ℤ→ℕ)") args, ZRange.type.base.option.None)
             | ident.Z_min
               => fun args => (show_application with_casts (fun _ => "Z.min") args, ZRange.type.base.option.None)
             | ident.Z_max
               => fun args => (show_application with_casts (fun _ => "Z.max") args, ZRange.type.base.option.None)
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
             | ident.Z_truncating_shiftl
               => fun args => (show_application with_casts (fun _ => "Z.truncating_shiftl") args, ZRange.type.base.option.None)
             | ident.Z_rshi
               => fun args => (show_application with_casts (fun _ => "Z.rshi") args, ZRange.type.base.option.None)
             | ident.Z_cc_m
               => fun args => (show_application with_casts (fun _ => "Z.cc_m") args, ZRange.type.base.option.None)
             | ident.Z_combine_at_bitwidth
               => fun args => (show_application with_casts (fun _ => "Z.combine_at_bitwidth") args, ZRange.type.base.option.None)
             | ident.Z_cast
             | ident.Z_cast2
               => fun '((_, range), ((x, xr), tt)) => (x, range)
             | ident.Build_zrange => fun '((x, xr), ((y, yr), tt)) => (fun lvl => maybe_wrap_parens (Nat.ltb lvl 0) ("r[" ++ x 60%nat ++ " ~> " ++ y 200%nat), ZRange.type.base.option.None)
             | ident.zrange_rect A
               => fun args => (show_application with_casts (fun _ => "zrange_rect") args, ZRange.type.base.option.None)
             | ident.fancy_add
               => fun args => (show_application with_casts (fun _ => "fancy.add") args, ZRange.type.base.option.None)
             | ident.fancy_addc
               => fun args => (show_application with_casts (fun _ => "fancy.addc") args, ZRange.type.base.option.None)
             | ident.fancy_sub
               => fun args => (show_application with_casts (fun _ => "fancy.sub") args, ZRange.type.base.option.None)
             | ident.fancy_subb
               => fun args => (show_application with_casts (fun _ => "fancy.subb") args, ZRange.type.base.option.None)
             | ident.fancy_mulll
               => fun args => (show_application with_casts (fun _ => "fancy.mulll") args, ZRange.type.base.option.None)
             | ident.fancy_mullh
               => fun args => (show_application with_casts (fun _ => "fancy.mullh") args, ZRange.type.base.option.None)
             | ident.fancy_mulhl
               => fun args => (show_application with_casts (fun _ => "fancy.mulhl") args, ZRange.type.base.option.None)
             | ident.fancy_mulhh
               => fun args => (show_application with_casts (fun _ => "fancy.mulhh") args, ZRange.type.base.option.None)
             | ident.fancy_rshi
               => fun args => (show_application with_casts (fun _ => "fancy.rshi") args, ZRange.type.base.option.None)
             | ident.fancy_selc
               => fun args => (show_application with_casts (fun _ => "fancy.selc") args, ZRange.type.base.option.None)
             | ident.fancy_selm
               => fun args => (show_application with_casts (fun _ => "fancy.selm") args, ZRange.type.base.option.None)
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
                | ident.Z_bneg => "!"
                | ident.Z_mul_split => "Z.mul_split"
                | ident.Z_add_get_carry => "Z.add_get_carry"
                | ident.Z_add_with_carry => "Z.add_with_carry"
                | ident.Z_add_with_get_carry => "Z.add_with_get_carry"
                | ident.Z_sub_get_borrow => "Z.sub_get_borrow"
                | ident.Z_sub_with_get_borrow => "Z.sub_with_get_borrow"
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
      Definition bitwidth_of (t : type) : Z := 2^Z.of_nat (lgbitwidth_of t).
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

      Global Instance show_type : Show type
        := fun with_parens t
           => maybe_wrap_parens
                with_parens
                ((if is_unsigned t then "u" else "") ++ "int" ++ decimal_string_of_Z (bitwidth_of t)).

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

    Module Import OfPHOAS.
      Fixpoint base_var_data (t : base.type) : Set
        := match t with
           | base.type.unit
             => unit
           | base.type.type_base base.type.Z => string * option int.type
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

      Fixpoint names_of_base_var_data {t} : base_var_data t -> base_var_names t
        := match t return base_var_data t -> base_var_names t with
           | base.type.type_base base.type.Z => @fst _ _
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
    End OfPHOAS.

    Class OutputLanguageAPI :=
      {
        (** [String.concat NewLine (comment_block lines)] should the
            the block-commented form of [String.concat NewLine lines].
            NewLines internal to elements in the list are allowed to
            be ignored / can be assumed to not be present.  Callers
            who want to ensure correct commenting on unknown blocks of
            text should instead run [comment_block (String.split
            NewLine (String.concat NewLine lines))]. *)
        comment_block : list string -> list string;

        (** Converts a PHOAS AST to lines of code * info on which
            primitive functions are called, or else an error string *)
        ToFunctionLines
        : forall (do_bounds_check : bool) (static : bool) (prefix : string) (name : string)
                 {t}
                 (e : @Compilers.expr.Expr base.type ident.ident t)
                 (comment : type.for_each_lhs_of_arrow var_data t -> var_data (type.final_codomain t) -> list string)
                 (name_list : option (list string))
                 (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                 (outbounds : ZRange.type.base.option.interp (type.final_codomain t)),
            (list string * ident_infos) + string;

        (** Generates a header of any needed typedefs based on the bitwidths used and the curve-specific prefix *)
        (** TODO: should we pick a more generic name than "typedef_header"? *)
        typedef_header
        : forall (static : bool) (prefix : string) (bitwidths_used : PositiveSet.t),
            list string
      }.
  End ToString.
End Compilers.
