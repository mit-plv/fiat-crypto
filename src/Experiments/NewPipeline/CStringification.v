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

      Module ident.
        Definition bitwidth_to_string (v : Z) : string
          := (if v =? 2^Z.log2 v then "2^" ++ decimal_string_of_Z (Z.log2 v) else HexString.of_Z v).
        Global Instance show_ident {t} : Show (ident.ident t)
          := fun with_parens idc
             => match idc with
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
               | ident.pair_rect A B T => "pair_rect"
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
               | ident.List_nth_default T => "nth_default"
               | ident.Z_add => "(+)"
               | ident.Z_mul => "( * )"
               | ident.Z_pow => "(^)"
               | ident.Z_sub => "(-)"
               | ident.Z_opp => "-"
               | ident.Z_div => "(/)"
               | ident.Z_modulo => "(mod)"
               | ident.Z_eqb => "(=)"
               | ident.Z_leb => "(≤)"
               | ident.Z_of_nat => "(ℕ→ℤ)"
               | ident.Z_shiftr offset => "(>> " ++ decimal_string_of_Z offset ++ ")"
               | ident.Z_shiftl offset => "(<< " ++ decimal_string_of_Z offset ++ ")"
               | ident.Z_land mask => "(& " ++ HexString.of_Z mask ++ ")"
               | ident.Z_mul_split => "Z.mul_split"
               | ident.Z_mul_split_concrete s => maybe_wrap_parens with_parens ("Z.mul_split " ++ bitwidth_to_string s)
               | ident.Z_add_get_carry => "Z.add_get_carry"
               | ident.Z_add_get_carry_concrete s => maybe_wrap_parens with_parens ("Z.add_get_carry " ++ bitwidth_to_string s)
               | ident.Z_add_with_carry => "Z.add_with_carry"
               | ident.Z_add_with_get_carry => "Z.add_with_get_carry"
               | ident.Z_add_with_get_carry_concrete s => maybe_wrap_parens with_parens ("Z.add_with_get_carry " ++ bitwidth_to_string s)
               | ident.Z_sub_get_borrow => "Z.sub_get_borrow"
               | ident.Z_sub_get_borrow_concrete s => maybe_wrap_parens with_parens ("Z.sub_get_borrow " ++ bitwidth_to_string s)
               | ident.Z_sub_with_get_borrow => "Z.sub_with_get_borrow"
               | ident.Z_sub_with_get_borrow_concrete s => maybe_wrap_parens with_parens ("Z.sub_with_get_borrow " ++ bitwidth_to_string s)
               | ident.Z_zselect => "Z.zselect"
               | ident.Z_add_modulo => "Z.add_modulo"
               | ident.Z_rshi => "Z.rshi"
               | ident.Z_rshi_concrete s offset => maybe_wrap_parens with_parens ("Z.rshi " ++ bitwidth_to_string s ++ " " ++ decimal_string_of_Z offset)
               | ident.Z_cc_m => "Z.cc_m"
               | ident.Z_cc_m_concrete s => maybe_wrap_parens with_parens ("Z.cc_m " ++ bitwidth_to_string s)
               | ident.Z_neg_snd => "Z.neg_snd"
               | ident.Z_cast range => "(" ++ show false range ++ ")"
               | ident.Z_cast2 range => "(" ++ show false range ++ ")"
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

      Local Notation NewLine := (String "010" "") (only parsing).

      Module expr.
        Section with_base_type.
          Context {base_type} {ident : type.type base_type -> Type}
                  {show_base_type : Show base_type}
                  {show_ident : forall t, Show (ident t)}.
          Fixpoint show_expr_lines {t} (e : @expr.expr base_type ident (fun _ => string) t) (idx : positive) (with_parens : bool) : positive * list string
            := match e with
               | expr.Ident t idc
                 => (idx, [show with_parens idc])
               | expr.Var t v
                 => (idx, [v])
               | expr.Abs s d f
                 => (idx,
                    let n := "x" ++ decimal_string_of_pos idx in
                    let '(_, show_f) := @show_expr_lines _ (f n) (Pos.succ idx) false in
                    match show_f with
                    | nil => ["(λ " ++ n ++ ", (* NOTHING‽ *))"]%string
                    | show_f::nil
                      => ["(λ " ++ n ++ ", " ++ show_f ++ ")"]%string
                    | show_f
                      => ["(λ " ++ n ++ ","]%string ++ (List.map (String " ") show_f) ++ [")"]
                    end%list)
               | expr.App s d f x
                 => let '(idx, show_f) := @show_expr_lines _ f idx false in
                   let '(idx, show_x) := @show_expr_lines _ x idx true in
                   (idx, match show_f, show_x with
                         | [show_f], [show_x] => [maybe_wrap_parens with_parens (show_f ++ " @ " ++ show_x)]
                         | _, _ => ["("] ++ show_f ++ [") @ ("] ++ show_x ++ [")"]
                         end%list)
               | expr.LetIn A B x f
                 => let n := "x" ++ decimal_string_of_pos idx in
                   let '(_, show_x) := @show_expr_lines _ x idx false in
                   let '(idx, show_f) := @show_expr_lines _ (f n) (Pos.succ idx) false in
                   let expr_let_line := "expr_let " ++ n ++ " := " in
                   (idx,
                    match show_x with
                    | nil => [expr_let_line ++ "(* NOTHING‽ *) in"]%string ++ show_f
                    | show_x::nil => [expr_let_line ++ show_x ++ " in"]%string ++ show_f
                    | show_x::rest
                      => ([expr_let_line ++ show_x]%string)
                          ++ (List.map (fun l => String.of_list (List.repeat " "%char (String.length expr_let_line)) ++ l)%string
                                       rest)
                          ++ ["in"]
                          ++ show_f
                    end%list)
               end.
          Global Instance show_lines_expr {t} : ShowLines (@expr.expr base_type ident (fun _ => string) t)
            := fun with_parens e => snd (@show_expr_lines t e 1%positive with_parens).
          Global Instance show_lines_Expr {t} : ShowLines (@expr.Expr base_type ident t)
            := fun with_parens e => show_lines with_parens (e _).
          Global Instance show_expr {t} : Show (@expr.expr base_type ident (fun _ => string) t)
            := fun with_parens e => String.concat NewLine (snd (@show_expr_lines t e 1%positive with_parens)).
          Global Instance show_Expr {t} : Show (@expr.Expr base_type ident t)
            := fun with_parens e => show with_parens (e _).
        End with_base_type.
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
        | Z_land (mask : BinInt.Z) : ident Z Z
        | Z_add : ident (Z * Z) Z
        | Z_mul : ident (Z * Z) Z
        | Z_sub : ident (Z * Z) Z
        | Z_opp : ident Z Z
        | Z_mul_split (lgs:BinInt.Z) : ident (Z * Z * Zptr) Z
        | Z_add_get_carry (lgs:BinInt.Z) : ident (Z * Z * Zptr) Z
        | Z_add_with_get_carry (lgs:BinInt.Z) : ident (Z * Z * Z * Zptr) Z
        | Z_sub_get_borrow (lgs:BinInt.Z) : ident (Z * Z * Zptr) Z
        | Z_sub_with_get_borrow (lgs:BinInt.Z) : ident (Z * Z * Z * Zptr) Z
        | Z_zselect : ident (Z * Z * Z) Z
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
          : option int.type -> arith_expr_for s -> option (arith_expr_for d)
          := fun desired_type '((e1, t1), (e2, t2))
             => let t1 := option_map integer_promote_type t1 in
               let t2 := option_map integer_promote_type t2 in
               let '((e1, t1), (e2, t2))
                   := cast_bigger_up_if_needed desired_type ((e1, t1), (e2, t2)) in
               let ct := (t1 <- t1; t2 <- t2; Some (common_type t1 t2))%option in
               Some (Zcast_down_if_needed desired_type ((idc @@ (e1, e2))%Cexpr, ct)).

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

        Fixpoint arith_expr_of_PHOAS_ident
                 {t}
                 (idc : ident.ident t)
          : int.option.interp (type.final_codomain t) -> type.interpM_final (fun T => option T) arith_expr_for_base t
          := match idc in ident.ident t return int.option.interp (type.final_codomain t) -> type.interpM_final (fun T => option T) arith_expr_for_base t with
             | ident.Literal base.type.Z v
               => fun r => Some (cast_down_if_needed
                               r
                               (literal v @@ TT, Some (int.of_zrange_relaxed r[v~>v])))
             | ident.nil t
               => fun _ => Some nil
             | ident.cons t
               => fun r x xs => Some (cast_down_if_needed r (cons x xs))
             | ident.fst A B => fun r xy => Some (cast_down_if_needed r (@fst _ _ xy))
             | ident.snd A B => fun r xy => Some (cast_down_if_needed r (@snd _ _ xy))
             | ident.List_nth_default base.type.Z
               => fun r d ls n
                 => List.nth_default None (List.map (fun x => Some (cast_down_if_needed r x)) ls) n
             | ident.Z_shiftr offset
               => fun rout '(e, r)
                 => let rin := option_map integer_promote_type r in
                   Some (cast_down_if_needed rout (Z_shiftr offset @@ e, rin))
             | ident.Z_shiftl offset
               => fun rout '(e, r)
                 => let rin := option_map integer_promote_type r in
                   let '(e', rin') := cast_up_if_needed rout (e, rin) in
                   Some (cast_down_if_needed rout (Z_shiftl offset @@ e', rin'))
             | ident.Z_land mask
               => fun rout '(e, r)
                 => Some (cast_down_if_needed
                           rout
                           (Z_land mask @@ e,
                            option_map integer_promote_type r))
             | ident.Z_add => fun r x y => arith_bin_arith_expr_of_PHOAS_ident Z_add r (x, y)
             | ident.Z_mul => fun r x y => arith_bin_arith_expr_of_PHOAS_ident Z_mul r (x, y)
             | ident.Z_sub => fun r x y => arith_bin_arith_expr_of_PHOAS_ident Z_sub r (x, y)
             | ident.Z_zselect
               => fun rout '(econd, _) '(e1, r1) '(e2, r2)
                 => let r1 := option_map integer_promote_type r1 in
                   let r2 := option_map integer_promote_type r2 in
                   let '((e1, r1), (e2, r2))
                       := cast_bigger_up_if_needed rout ((e1, r1), (e2, r2)) in
                   let ct := (r1 <- r1; r2 <- r2; Some (common_type r1 r2))%option in
                   Some (cast_down_if_needed rout ((Z_zselect @@ (econd, e1, e2))%Cexpr, ct))
             | ident.pair A B
               => fun _ _ _ => None
             | ident.Z_opp
               => fun _ _ => None
             | ident.Literal _ v
               => fun _ => Some v
             | ident.Nat_succ
             | ident.Nat_pred
             | ident.Nat_max
             | ident.Nat_mul
             | ident.Nat_add
             | ident.Nat_sub
             | ident.pair_rect _ _ _
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
             | ident.Z_of_nat
             | ident.Z_mul_split
             | ident.Z_mul_split_concrete _
             | ident.Z_add_get_carry
             | ident.Z_add_get_carry_concrete _
             | ident.Z_add_with_carry
             | ident.Z_add_with_get_carry
             | ident.Z_add_with_get_carry_concrete _
             | ident.Z_sub_get_borrow
             | ident.Z_sub_get_borrow_concrete _
             | ident.Z_sub_with_get_borrow
             | ident.Z_sub_with_get_borrow_concrete _
             | ident.Z_add_modulo
             | ident.Z_rshi
             | ident.Z_rshi_concrete _ _
             | ident.Z_cc_m
             | ident.Z_cc_m_concrete _
             | ident.Z_neg_snd
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
               => fun _ => type.interpM_return _ _ _ None
             end%core%Cexpr%option%zrange.

        Fixpoint collect_args_and_apply_unknown_casts {t}
          : (int.option.interp (type.final_codomain t) -> type.interpM_final (fun T => option T) arith_expr_for_base t)
            -> type.interpM_final
                (fun T => option T)
                (fun t => int.option.interp t -> option (arith_expr_for_base t))
                t
          := match t
                   return ((int.option.interp (type.final_codomain t) -> type.interpM_final (fun T => option T) arith_expr_for_base t)
                           -> type.interpM_final
                               (fun T => option T)
                               (fun t => int.option.interp t -> option (arith_expr_for_base t))
                               t)
             with
             | type.base t => fun v => Some v
             | type.arrow (type.base s) d
               => fun f
                   (x : (int.option.interp s -> option (arith_expr_for_base s)))
                 => match x int.option.None with
                   | Some x'
                     => @collect_args_and_apply_unknown_casts
                         d
                         (fun rout => f rout x')
                   | None => type.interpM_return _ _ _ None
                   end
             | type.arrow (type.arrow _ _) _
               => fun _ => type.interpM_return _ _ _ None
             end.

        Definition collect_args_and_apply_known_casts {t}
                   (idc : ident.ident t)
          : option (type.interpM_final
                      (fun T => option T)
                      (fun t => int.option.interp t -> option (arith_expr_for_base t))
                      t)
          := match idc in ident.ident t
                   return option
                            (type.interpM_final
                               (fun T => option T)
                               (fun t => int.option.interp t -> option (arith_expr_for_base t))
                               t)
             with
             | ident.Z_cast r
               => Some (fun arg => Some (fun r' => option_map (Zcast_down_if_needed r') (arg (Some (int.of_zrange_relaxed r)))))
             | ident.Z_cast2 (r1, r2)
               => Some (fun arg => Some (fun r' => option_map (cast_down_if_needed (t:=base.type.Z*base.type.Z) r')
                                                       (arg (Some (int.of_zrange_relaxed r1), Some (int.of_zrange_relaxed r2)))))
             | ident.pair A B
               => Some (fun ea eb
                       => Some
                           (fun '(ra, rb)
                            => (ea' <- ea ra;
                                 eb' <- eb rb;
                                 Some (ea', eb'))))
             | ident.nil _
               => Some (Some (fun _ => Some nil))
             | ident.cons t
               => Some
                   (fun x xs
                    => Some
                        (fun rls
                         => let mkcons (r : int.option.interp t)
                                      (rs : int.option.interp (base.type.list t))
                               := (x <- x r;
                                     xs <- xs rs;
                                     Some (cons x xs)) in
                           match rls with
                           | Some (cons r rs) => mkcons r (Some rs)
                           | Some nil
                           | None
                             => mkcons int.option.None int.option.None
                           end))
             | _ => None
             end%option.

        Definition collect_args_and_apply_casts {t} (idc : ident.ident t)
                   (convert_no_cast : int.option.interp (type.final_codomain t) -> type.interpM_final (fun T => option T) arith_expr_for_base t)
          : type.interpM_final
              (fun T => option T)
              (fun t => int.option.interp t -> option (arith_expr_for_base t))
              t
          := match collect_args_and_apply_known_casts idc with
             | Some res => res
             | None => collect_args_and_apply_unknown_casts convert_no_cast
             end.

        Fixpoint arith_expr_of_base_PHOAS_Var
                 {t}
          : base_var_data t -> int.option.interp t -> option (arith_expr_for_base t)
          := match t with
             | base.type.Z
               => fun '(n, r) r' => Some (cast_down_if_needed r' (Var type.Z n, r))
             | base.type.prod A B
               => fun '(da, db) '(ra, rb)
                 => (ea <- @arith_expr_of_base_PHOAS_Var A da ra;
                      eb <- @arith_expr_of_base_PHOAS_Var B db rb;
                      Some (ea, eb))%option
             | base.type.list base.type.Z
               => fun '(n, r, len) r'
                 => Some (List.map
                           (fun i => (List_nth i @@ Var type.Zptr n, r))%core%Cexpr
                           (List.seq 0 len))
             | base.type.list _
             | base.type.type_base _
               => fun _ _ => None
             end.

        Fixpoint arith_expr_of_PHOAS
                 {t}
                 (e : @Compilers.expr.expr base.type ident.ident var_data t)
          : type.interpM_final
              (fun T => option T)
              (fun t => int.option.interp t -> option (arith_expr_for_base t))
              t
          := match e in expr.expr t
                   return type.interpM_final
                            (fun T => option T)
                            (fun t => int.option.interp t -> option (arith_expr_for_base t))
                            t
             with
             | expr.Var (type.base _) v
               => Some (arith_expr_of_base_PHOAS_Var v)
             | expr.Ident t idc
               => collect_args_and_apply_casts idc (arith_expr_of_PHOAS_ident idc)
             | expr.App (type.base s) d f x
               => let x' := @arith_expr_of_PHOAS s x in
                 match x' with
                 | Some x' => @arith_expr_of_PHOAS _ f x'
                 | None => type.interpM_return _ _ _ None
                 end
             | expr.Var (type.arrow _ _) _
             | expr.App (type.arrow _ _) _ _ _
             | expr.LetIn _ _ _ _
             | expr.Abs _ _ _
               => type.interpM_return _ _ _ None
             end.

        Definition arith_expr_of_base_PHOAS
                   {t:base.type}
                   (e : @Compilers.expr.expr base.type ident.ident var_data t)
                   (rout : int.option.interp t)
          : option (arith_expr_for_base t)
          := (e' <- arith_expr_of_PHOAS e; e' rout)%option.

        Fixpoint make_return_assignment_of_base_arith {t}
          : base_var_data t
            -> @Compilers.expr.expr base.type ident.ident var_data t
            -> option expr
          := match t return base_var_data t -> expr.expr t -> option expr with
             | base.type.Z
               => fun '(n, r) e
                 => (rhs <- arith_expr_of_base_PHOAS e r;
                      let '(e, r) := rhs in
                      Some [AssignZPtr n r e])
             | base.type.type_base _ => fun _ _ => None
             | base.type.prod A B
               => fun '(rva, rvb) e
                 => match invert_pair e with
                   | Some (ea, eb)
                     => (ea' <- @make_return_assignment_of_base_arith A rva ea;
                          eb' <- @make_return_assignment_of_base_arith B rvb eb;
                          Some (ea' ++ eb'))
                   | None => None
                   end
             | base.type.list base.type.Z
               => fun '(n, r, len) e
                 => (ls <- arith_expr_of_base_PHOAS e (Some (repeat r len));
                      List.fold_right
                        (fun a b
                         => match b with
                           | Some b => Some (a ++ b)
                           | None => Some a
                           end)
                        None
                        (List.map
                           (fun '(i, (e, _)) => [AssignNth n i e])
                           (List.combine (List.seq 0 len) ls)))
             | base.type.list _ => fun _ _ => None
             end%option%list.
        Definition make_return_assignment_of_arith {t}
          : var_data t
            -> @Compilers.expr.expr base.type ident.ident var_data t
            -> option expr
          := match t with
             | type.base t => make_return_assignment_of_base_arith
             | type.arrow s d => fun _ _ => None
             end.

        Definition make_assign_2arg_1ref
                   {t1 t2 d t3}
                   (r1 r2 : option int.type)
                   (x1 : @Compilers.expr.expr base.type ident.ident var_data t1)
                   (x2 : @Compilers.expr.expr base.type ident.ident var_data t2)
                   (idc : ident (type.Z * type.Z * type.Zptr) type.Z)
                   (count : positive)
                   (make_name : positive -> option string)
                   (v : var_data t3)
                   (e2 : var_data d -> var_data (base.type.Z * base.type.Z)%etype -> option expr)
          : option expr
          := (v <- type.try_transport base.try_make_transport_cps var_data _ d v;
                x1 <- type.try_transport base.try_make_transport_cps expr.expr _ base.type.Z x1;
                x2 <- type.try_transport base.try_make_transport_cps expr.expr _ base.type.Z x2;
                let e2 := e2 v in
                x1 <- arith_expr_of_base_PHOAS x1 None;
                  x2 <- arith_expr_of_base_PHOAS x2 None;
                  let '(x1, x1r) := x1 in
                  let '(x2, x2r) := x2 in
                  n1 <- make_name count;
                    n2 <- make_name (Pos.succ count);
                    e2 <- e2 ((n1, r1), (n2, r2));
                    Some ([DeclareVar type.Z r2 n2;
                             Assign true type.Z r1 n1 (idc @@ (x1, x2, Addr @@ Var type.Z n2))]
                            ++ e2))%option%list.

        Definition make_assign_3arg_1ref
                   {t1 t2 t3 d t4}
                   (r1 r2 : option int.type)
                   (x1 : @Compilers.expr.expr base.type ident.ident var_data t1)
                   (x2 : @Compilers.expr.expr base.type ident.ident var_data t2)
                   (x3 : @Compilers.expr.expr base.type ident.ident var_data t3)
                   (idc : ident (type.Z * type.Z * type.Z * type.Zptr) type.Z)
                   (count : positive)
                   (make_name : positive -> option string)
                   (v : var_data t4)
                   (e2 : var_data d -> var_data (base.type.Z * base.type.Z)%etype -> option expr)
          : option expr
          := (v <- type.try_transport base.try_make_transport_cps var_data _ d v;
                x1 <- type.try_transport base.try_make_transport_cps expr.expr _ base.type.Z x1;
                x2 <- type.try_transport base.try_make_transport_cps expr.expr _ base.type.Z x2;
                x3 <- type.try_transport base.try_make_transport_cps expr.expr _ base.type.Z x3;
                let e2 := e2 v in
                x1 <- arith_expr_of_base_PHOAS x1 None;
                  x2 <- arith_expr_of_base_PHOAS x2 None;
                  x3 <- arith_expr_of_base_PHOAS x3 None;
                  let '(x1, x1r) := x1 in
                  let '(x2, x2r) := x2 in
                  let '(x3, x3r) := x3 in
                  n1 <- make_name count;
                    n2 <- make_name (Pos.succ count);
                    e2 <- e2 ((n1, r1), (n2, r2));
                    Some ([DeclareVar type.Z r2 n2;
                             Assign true type.Z r1 n1 (idc @@ (x1, x2, x3, Addr @@ Var type.Z n2))]
                            ++ e2))%option%list.

        Fixpoint size_of_type (t : base.type) : positive
          := match t with
             | base.type.type_base t => 1
             | base.type.prod A B => size_of_type A + size_of_type B
             | base.type.list A => 1
             end%positive.

        Definition maybe_log2 (s : Z) : option Z
          := if 2^Z.log2 s =? s then Some (Z.log2 s) else None.

        Definition recognize_ident_2arg {t} (idc : ident.ident t)
          : option (ident (type.type_primitive type.Z * type.type_primitive type.Z * type.type_primitive type.Zptr) (type.type_primitive type.Z))
          := match idc with
             | ident.Z_mul_split_concrete s
               => option_map Z_mul_split (maybe_log2 s)
             | ident.Z_add_get_carry_concrete s
               => option_map Z_add_get_carry (maybe_log2 s)
             | ident.Z_sub_get_borrow_concrete s
               => option_map Z_sub_get_borrow (maybe_log2 s)
             | _ => None
             end.
        Definition recognize_ident_3arg {t} (idc : ident.ident t)
          : option (ident (type.type_primitive type.Z * type.type_primitive type.Z * type.type_primitive type.Z * type.type_primitive type.Zptr) (type.type_primitive type.Z))
          := match idc with
             | ident.Z_add_with_get_carry_concrete s
               => option_map Z_add_with_get_carry (maybe_log2 s)
             | ident.Z_sub_with_get_borrow_concrete s
               => option_map Z_sub_with_get_borrow (maybe_log2 s)
             | _ => None
             end.

        Definition make_uniform_assign_expr_of_PHOAS
                   {s} (e1 : @Compilers.expr.expr base.type ident.ident var_data s)
                   {d} (e2 : var_data s -> var_data d -> option expr)
                   (count : positive)
                   (make_name : positive -> option string)
                   (v : var_data d)
          : option expr
          := match s return (@Compilers.expr.expr base.type ident.ident var_data s)
                            -> (var_data s -> var_data d -> option expr)
                            -> option expr
             with
             | type.base (base.type.type_base base.type.Z)
               => fun e1 e2
                 => (e1 <- arith_expr_of_base_PHOAS e1 None;
                      let '(e1, r1) := e1 in
                      n1 <- make_name count;
                        e2 <- e2 (n1, r1) v;
                        Some ((Assign true type.Z r1 n1 e1)
                                :: e2))
             | type.base (base.type.Z * base.type.Z)%etype
               => fun e1 e2
                 => let '((r1, r2), e1)%core
                       := match invert_Z_cast2 e1 with
                          | Some ((r1, r2), e) => ((Some (int.of_zrange_relaxed r1), Some (int.of_zrange_relaxed r2)), e)
                          | None => ((None, None), e1)
                          end%core in
                   match e1 with
                   | (#idc @ x1 @ x2)
                     => idc <- recognize_ident_2arg idc;
                         make_assign_2arg_1ref
                           r1 r2
                           x1 x2 idc count make_name v
                           (fun v rv => e2 rv v)
                   | (#idc @ x1 @ x2 @ x3)
                     => idc <- recognize_ident_3arg idc;
                         make_assign_3arg_1ref
                           r1 r2
                           x1 x2 x3 idc count make_name v
                           (fun v rv => e2 rv v)
                   | _ => None
                   end%expr_pat
             | _ => fun _ _ => None
             end%option e1 e2.
        Definition make_assign_expr_of_PHOAS
                   {s} (e1 : @Compilers.expr.expr base.type ident.ident var_data s)
                   {s' d} (e2 : var_data s' -> var_data d -> option expr)
                   (count : positive)
                   (make_name : positive -> option string)
                   (v : var_data d)
          : option expr
          := (e1 <- type.try_transport base.try_make_transport_cps _ _ _ e1;
                make_uniform_assign_expr_of_PHOAS e1 e2 count make_name v).

        Fixpoint expr_of_base_PHOAS
                 {t}
                 (e : @Compilers.expr.expr base.type ident.ident var_data t)
                 (count : positive)
                 (make_name : positive -> option string)
                 {struct e}
          : forall (ret_val : var_data t), option expr
          := match e in expr.expr t return var_data t -> option expr with
             | expr.LetIn (type.base s) d e1 e2
               => make_assign_expr_of_PHOAS
                   e1
                   (fun vs vd => @expr_of_base_PHOAS d (e2 vs) (size_of_type s + count)%positive make_name vd)
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

        Fixpoint expr_of_PHOAS
                 {t}
                 (e : @Compilers.expr.expr base.type ident.ident var_data t)
                 (make_name : positive -> option string)
                 (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                 (outbounds : ZRange.type.option.interp (type.final_codomain t))
                 (count : positive)
                 {struct t}
          : option (type.for_each_lhs_of_arrow var_data t * var_data (type.final_codomain t) * expr)
          := match t return @Compilers.expr.expr base.type ident.ident var_data t -> type.for_each_lhs_of_arrow ZRange.type.option.interp t -> ZRange.type.option.interp (type.final_codomain t) -> option (type.for_each_lhs_of_arrow var_data t * var_data (type.final_codomain t) * expr) with
             | type.base t
               => fun e tt outbounds
                 => vd <- var_data_of_bounds count make_name outbounds;
                     let '(count, vd) := vd in
                     rv <- expr_of_base_PHOAS e count make_name vd;
                       Some (tt, vd, rv)
             | type.arrow s d
               => fun e '(inbound, inbounds) outbounds
                 => vs <- var_data_of_bounds count make_name inbound;
                     let '(count, vs) := vs in
                     f <- invert_Abs e;
                       ret <- @expr_of_PHOAS d (f vs) make_name inbounds outbounds count;
                       let '(vss, vd, rv) := ret in
                       Some (vs, vss, vd, rv)
             end%option%core%expr e inbounds outbounds.

        Definition ExprOfPHOAS
                   {t}
                   (e : @Compilers.expr.Expr base.type ident.ident t)
                   (name_list : option (list string))
                   (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
          : option (type.for_each_lhs_of_arrow var_data t * var_data (type.final_codomain t) * expr)
          := (let outbounds := partial.Extract e inbounds in
              let make_name := match name_list with
                               | None => fun p => Some ("x" ++ decimal_string_of_Z (Zpos p))
                               | Some ls => fun p => List.nth_error ls (pred (Pos.to_nat p))
                               end in
              expr_of_PHOAS (e _) make_name inbounds outbounds 1).
      End OfPHOAS.

      Module primitive.
        Definition small_enough (v : Z) : bool
          := Z.log2_up (Z.abs v + 1) <=? 128.
        Definition to_UL_postfix (r : zrange) : string
          := let lower := lower r in
             let upper := upper r in
             let u := (if lower >=? 0 then "U" else "") in
             let sz := Z.log2_up (Z.max (Z.abs upper + 1) (Z.abs lower)) in
             if sz <=? 32
             then ""
             else if sz <=? 64
                  then u ++ "L"
                  else if sz <=? 128
                       then u ++ "LL"
                       else " /* " ++ HexString.of_Z lower ++ " <= val <= " ++ HexString.of_Z upper ++ " */".

        Definition to_string {t : type.primitive} (v : BinInt.Z) : string
          := match t with
             | type.Z => HexString.of_Z v ++ (if small_enough v
                                             then to_UL_postfix r[v~>v]
                                             else "ℤ")
             | type.Zptr => "#error ""literal address " ++ HexString.of_Z v ++ """;"
             end.
      End primitive.

      Module String.
        Definition typedef_header : list string
          := ["typedef unsigned char uint1_t;"]%string.
        Module int.
          Module type.
            Definition to_string (t : int.type) : string
              := ((if int.is_unsigned t then "u" else "")
                    ++ "int"
                    ++ decimal_string_of_Z (int.bitwidth_of t)
                    ++ "_t")%string.
          End type.
        End int.

        Module type.
          Module primitive.
            Definition to_string (t : type.primitive) (r : option int.type) : string
              := match r with
                 | Some int_t => int.type.to_string int_t
                 | None => "ℤ"
                 end ++ match t with
                        | type.Zptr => "*"
                        | type.Z => ""
                        end.
          End primitive.
        End type.
      End String.

      Fixpoint arith_to_string {t} (e : arith_expr t) : string
        := match e with
           | (literal v @@ _) => primitive.to_string (t:=type.Z) v
           | (List_nth n @@ Var _ v)
             => "(" ++ v ++ "[" ++ decimal_string_of_Z (Z.of_nat n) ++ "])"
           | (Addr @@ Var _ v) => "&" ++ v
           | (Dereference @@ e) => "( *" ++ @arith_to_string _ e ++ " )"
           | (Z_shiftr offset @@ e)
             => "(" ++ @arith_to_string _ e ++ " >> " ++ decimal_string_of_Z offset ++ ")"
           | (Z_shiftl offset @@ e)
             => "(" ++ @arith_to_string _ e ++ " << " ++ decimal_string_of_Z offset ++ ")"
           | (Z_land mask @@ e)
             => "(" ++ @arith_to_string _ e ++ " & " ++ primitive.to_string (t:=type.Z) mask ++ ")"
           | (Z_add @@ (x1, x2))
             => "(" ++ @arith_to_string _ x1 ++ " + " ++ @arith_to_string _ x2 ++ ")"
           | (Z_mul @@ (x1, x2))
             => "(" ++ @arith_to_string _ x1 ++ " * " ++ @arith_to_string _ x2 ++ ")"
           | (Z_sub @@ (x1, x2))
             => "(" ++ @arith_to_string _ x1 ++ " - " ++ @arith_to_string _ x2 ++ ")"
           | (Z_opp @@ e)
             => "(-" ++ @arith_to_string _ e ++ ")"
           | (Z_mul_split lg2s @@ (x1, x2, x3))
             => "_mulx_u"
                  ++ decimal_string_of_Z lg2s ++ "("
                  ++ @arith_to_string _ x1 ++ ", "
                  ++ @arith_to_string _ x2 ++ ", "
                  ++ @arith_to_string _ x3 ++ ")"
           | (Z_add_get_carry lg2s @@ (x1, x2, x3))
             => "_add_carryx_u"
                  ++ decimal_string_of_Z lg2s ++ "(0, "
                  ++ @arith_to_string _ x1 ++ ", "
                  ++ @arith_to_string _ x2 ++ ", "
                  ++ @arith_to_string _ x3 ++ ")"
           | (Z_add_with_get_carry lg2s @@ (x1, x2, x3, x4))
             => "_add_carryx_u"
                  ++ decimal_string_of_Z lg2s ++ "("
                  ++ @arith_to_string _ x1 ++ ", "
                  ++ @arith_to_string _ x2 ++ ", "
                  ++ @arith_to_string _ x3 ++ ", "
                  ++ @arith_to_string _ x4 ++ ")"
           | (Z_sub_get_borrow lg2s @@ (x1, x2, x3))
             => "_subborrow_u"
                  ++ decimal_string_of_Z lg2s ++ "(0, "
                  ++ @arith_to_string _ x1 ++ ", "
                  ++ @arith_to_string _ x2 ++ ", "
                  ++ @arith_to_string _ x3 ++ ")"
           | (Z_sub_with_get_borrow lg2s @@ (x1, x2, x3, x4))
             => "_subborrow_u"
                  ++ decimal_string_of_Z lg2s ++ "("
                  ++ @arith_to_string _ x1 ++ ", "
                  ++ @arith_to_string _ x2 ++ ", "
                  ++ @arith_to_string _ x3 ++ ", "
                  ++ @arith_to_string _ x4 ++ ")"
           | (Z_zselect @@ (cond, et, ef)) => "#error zselect;"
           | (Z_add_modulo @@ (x1, x2, x3)) => "#error addmodulo;"
           | (Z_static_cast int_t @@ e)
             => "(" ++ String.type.primitive.to_string type.Z (Some int_t) ++ ")"
                    ++ @arith_to_string _ e
           | Var _ v => v
           | (List_nth _ @@ _)
           | (Addr @@ _)
           | (Z_add @@ _)
           | (Z_mul @@ _)
           | (Z_sub @@ _)
           | (Z_mul_split _ @@ _)
           | (Z_add_get_carry _ @@ _)
           | (Z_add_with_get_carry _ @@ _)
           | (Z_sub_get_borrow _ @@ _)
           | (Z_sub_with_get_borrow _ @@ _)
           | (Z_zselect @@ _)
           | (Z_add_modulo @@ _)
             => "#error bad_arg;"
           | Pair A B a b
             => "#error pair;"
           | TT
             => "#error tt;"
           end%core%Cexpr.

      Fixpoint stmt_to_string (e : stmt) : string
        := match e with
           | Assign true t sz name val
             => String.type.primitive.to_string t sz ++ " " ++ name ++ " = " ++ arith_to_string val ++ ";"
           | Assign false _ sz name val
             => name ++ " = " ++ arith_to_string val ++ ";"
           | AssignZPtr name sz val
             => "*" ++ name ++ " = " ++ arith_to_string val ++ ";"
           | DeclareVar t sz name
             => String.type.primitive.to_string t sz ++ " " ++ name ++ ";"
           | AssignNth name n val
             => name ++ "[" ++ decimal_string_of_Z (Z.of_nat n) ++ "] = " ++ arith_to_string val ++ ";"
           end.
      Definition to_strings (e : expr) : list string
        := List.map stmt_to_string e.

      Import OfPHOAS.

      Fixpoint to_base_arg_list {t} : base_var_data t -> list string
        := match t return base_var_data t -> _ with
           | base.type.Z
             => fun '(n, r) => [String.type.primitive.to_string type.Z r ++ " " ++ n]
           | base.type.prod A B
             => fun '(va, vb) => (@to_base_arg_list A va ++ @to_base_arg_list B vb)%list
           | base.type.list base.type.Z
             => fun '(n, r, len) => [String.type.primitive.to_string type.Z r ++ " " ++ n ++ "[" ++ decimal_string_of_Z (Z.of_nat len) ++ "]"]
           | base.type.list _ => fun _ => ["#error ""complex list"";"]
           | base.type.unit => fun _ => ["#error unit;"]
           | base.type.nat => fun _ => ["#error ℕ;"]
           | base.type.bool => fun _ => ["#error bool;"]
           end.

      Definition to_arg_list {t} : var_data t -> list string
        := match t return var_data t -> _ with
           | type.base t => to_base_arg_list
           | type.arrow _ _ => fun _ => ["#error arrow;"]
           end.

      Fixpoint to_arg_list_for_each_lhs_of_arrow {t} : type.for_each_lhs_of_arrow var_data t -> list string
        := match t return type.for_each_lhs_of_arrow var_data t -> _ with
           | type.base t => fun _ => nil
           | type.arrow s d
             => fun '(x, xs)
                => to_arg_list x ++ @to_arg_list_for_each_lhs_of_arrow d xs
           end%list.

      Fixpoint to_base_retarg_list {t} : base_var_data t -> list string
        := match t return base_var_data t -> _ with
           | base.type.Z
             => fun '(n, r) => [String.type.primitive.to_string type.Zptr r ++ " " ++ n]
           | base.type.prod A B
             => fun '(va, vb) => (@to_base_retarg_list A va ++ @to_base_retarg_list B vb)%list
           | base.type.list base.type.Z
             => fun '(n, r, len) => [String.type.primitive.to_string type.Z r ++ " " ++ n ++ "[" ++ decimal_string_of_Z (Z.of_nat len) ++ "]"]
           | base.type.list _ => fun _ => ["#error ""complex list"";"]
           | base.type.unit => fun _ => ["#error unit;"]
           | base.type.nat => fun _ => ["#error ℕ;"]
           | base.type.bool => fun _ => ["#error bool;"]
           end.

      Definition to_retarg_list {t} : var_data t -> list string
        := match t return var_data t -> _ with
           | type.base _ => to_base_arg_list
           | type.arrow _ _ => fun _ => ["#error arrow;"]
           end.

      Definition to_function_lines (name : string)
                 {t}
                 (f : type.for_each_lhs_of_arrow var_data t * var_data (type.final_codomain t) * expr)
        : list string
        := let '(args, rets, body) := f in
           (((("void "
                 ++ name ++ "("
                 ++ (String.concat ", " (to_arg_list_for_each_lhs_of_arrow args ++ to_retarg_list rets))
                 ++ ") {")%string)
               :: (List.map (fun s => "  " ++ s)%string (to_strings body)))
              ++ ["}"])%list.

      Local Notation NewLine := (String "010" "") (only parsing).

      Definition ToFunctionLines (name : string)
                 {t}
                 (e : @Compilers.expr.Expr base.type ident.ident t)
                 (name_list : option (list string))
                 (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        : option (list string)
        := (f <- ExprOfPHOAS e name_list inbounds;
              Some (to_function_lines name f)).

      Definition LinesToString (lines : list string)
        : string
        := String.concat NewLine lines.

      Definition ToFunctionString (name : string)
                 {t}
                 (e : @Compilers.expr.Expr base.type ident.ident t)
                 (name_list : option (list string))
                 (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        : option string
        := (ls <- ToFunctionLines name e name_list inbounds;
              Some (LinesToString ls)).
    End C.
    Notation ToFunctionLines := C.ToFunctionLines.
    Notation ToFunctionString := C.ToFunctionString.
    Notation LinesToString := C.LinesToString.
  End ToString.
End Compilers.
