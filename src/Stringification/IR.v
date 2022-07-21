Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.HexString.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.Show.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.Stringification.Language.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.Util.Bool.Equality.
Require Import Crypto.Util.Notations.
Import Coq.Lists.List ListNotations. Local Open Scope zrange_scope. Local Open Scope Z_scope.

Module Compilers.
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  Export Language.Compilers.
  Export Language.API.Compilers.
  Export AbstractInterpretation.Compilers.
  Export AbstractInterpretation.ZRange.Compilers.
  Export Stringification.Language.Compilers.
  Import invert_expr.
  Import Compilers.API.

  Local Notation tZ := (base.type.type_base base.type.Z).

  Module ToString.
    Import Stringification.Language.Compilers.ToString.
    Import Stringification.Language.Compilers.ToString.ZRange.
    Local Open Scope string_scope.
    Local Open Scope Z_scope.

    Module IR.
      Module type.
        Inductive primitive := Z | Zptr.
        Inductive type := type_primitive (t : primitive) | prod (A B : type) | unit.
        Module Export Notations.
          Global Coercion type_primitive : primitive >-> type.
          Declare Scope Ctype_scope.
          Delimit Scope Ctype_scope with Ctype.

          Bind Scope Ctype_scope with type.
          Notation "()" := unit : Ctype_scope.
          Notation "A * B" := (prod A B) : Ctype_scope.
          Notation type := type.
        End Notations.
      End type.
      Import type.Notations.
      Import int.Notations.

      Section ident.
        Import type.
        Inductive Z_binop : Set :=
        | Z_land
        | Z_lor
        | Z_lxor
        | Z_add
        | Z_mul
        | Z_sub
        .
        Inductive Z_unop : Set :=
        | Z_shiftr (offset : BinInt.Z)
        | Z_shiftl (offset : BinInt.Z)
        (*| Z_opp*)
        | Z_lnot (ty:int.type)
        | Z_bneg
        | Z_value_barrier (ty:int.type)
        .
        Inductive ident : type -> type -> Set :=
        | literal (v : BinInt.Z) : ident unit Z
        | List_nth (n : Datatypes.nat) : ident Zptr Z
        | Addr : ident Z Zptr
        | Dereference : ident Zptr Z
        | iunop (op : Z_unop) : ident Z Z
        | ibinop (op : Z_binop) : ident (Z * Z) Z
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
      | Comment (lines : list string) (mentioned_variables : list { t : _ & OfPHOAS.var_data t})
      | Assign (declare : bool) (t : type.primitive) (sz : option int.type) (name : string) (val : arith_expr t)
      | AssignZPtr (name : string) (sz : option int.type) (val : arith_expr type.Z)
      | DeclareVar (t : type.primitive) (sz : option int.type) (name : string)
      | AssignNth (name : string) (n : nat) (val : arith_expr type.Z).
      Definition expr := list stmt.

      Module Export Notations.
        Export int.Notations.
        Export type.Notations.
        Declare Scope Cexpr_scope.
        Delimit Scope Cexpr_scope with Cexpr.
        Bind Scope Cexpr_scope with expr.
        Bind Scope Cexpr_scope with stmt.
        Bind Scope Cexpr_scope with arith_expr.
        Infix "@@@" := AppIdent : Cexpr_scope.
        Notation "( x , y , .. , z )" := (Pair .. (Pair x%Cexpr y%Cexpr) .. z%Cexpr) : Cexpr_scope.
        Notation "( )" := TT : Cexpr_scope.

        Notation "()" := TT : Cexpr_scope.
        Notation "x ;; y" := (@cons stmt x%Cexpr y%Cexpr) (at level 70, right associativity, format "'[v' x ;; '/' y ']'") : Cexpr_scope.
        Global Coercion iunop : Z_unop >-> ident.
        Global Coercion ibinop : Z_binop >-> ident.
      End Notations.

      Definition invert_literal {t} (e : arith_expr t) : option (BinInt.Z)
        := match e with
           | AppIdent s d (literal v) arg => Some v
           | _ => None
           end.

      Module ident_infos.
        Definition collect_infos_of_ident {s d} (idc : ident s d) : ident_infos
          := match idc with
             | Z_static_cast ty => ident_info_of_bitwidths_used (IntSet.singleton ty)
             | Z_mul_split lg2s
               => ident_info_of_mulx (PositiveSet.add (Z.to_pos lg2s) PositiveSet.empty)
             | Z_add_with_get_carry lg2s
             | Z_sub_with_get_borrow lg2s
               => ident_info_of_addcarryx (PositiveSet.add (Z.to_pos lg2s) PositiveSet.empty)
             | Z_zselect ty
               => ident_info_of_cmovznz (IntSet.singleton ty)
             | iunop (Z_value_barrier ty)
               =>ident_info_of_value_barrier (IntSet.singleton ty)
             | literal _
             | List_nth _
             | Addr
             | Dereference
             | ibinop _
             | iunop _
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

        Definition collect_infos_of_stmt (e : stmt) : ident_infos
          := match e with
             | Assign _ _ (Some sz) _ val
             | AssignZPtr _ (Some sz) val
               => ident_info_union (ident_info_of_bitwidths_used (IntSet.singleton sz)) (collect_infos_of_arith_expr val)
             | Call val
             | Assign _ _ None _ val
             | AssignZPtr _ None val
             | AssignNth _ _ val
               => collect_infos_of_arith_expr val
             | DeclareVar _ (Some sz) _
               => ident_info_of_bitwidths_used (IntSet.singleton sz)
             | DeclareVar _ None _
             | Comment _ _
               => ident_info_empty
             end.

        Fixpoint collect_infos_of_base_typedef_data {t} : OfPHOAS.base_var_typedef_data t -> ident_infos
          := match t return OfPHOAS.base_var_typedef_data t -> ident_infos with
             | tZ
               => fun n => match n with
                           | Some n => ident_info_of_typedefs [n]
                           | None => ident_info_empty
                           end
             | base.type.prod A B
               => fun '(tda, tdb)
                  => ident_info_union (@collect_infos_of_base_typedef_data A tda)
                                      (@collect_infos_of_base_typedef_data B tdb)
             | base.type.list tZ
               => fun n => match n with
                           | Some n => ident_info_of_typedefs [n]
                           | None => ident_info_empty
                           end
             | base.type.list _
             | base.type.option _
             | base.type.type_base _
             | base.type.unit
               => fun _ => ident_info_empty
             end.

        Definition collect_infos_of_typedef_data {t} : OfPHOAS.var_typedef_data t -> ident_infos
          := match t return OfPHOAS.var_typedef_data t -> ident_infos with
             | type.base t => collect_infos_of_base_typedef_data
             | type.arrow _ _ => fun 'tt => ident_info_empty
             end.

        Fixpoint collect_infos_of_arg_typedef_data {t} : type.for_each_lhs_of_arrow OfPHOAS.var_typedef_data t -> ident_infos
          := match t with
             | type.base _ => fun 'tt => ident_info_empty
             | type.arrow s d
               => fun '(td, tds)
                  => ident_info_union (collect_infos_of_typedef_data td)
                                      (@collect_infos_of_arg_typedef_data d tds)
             end.

        Definition collect_infos (e : expr) : ident_infos
          := fold_right
               ident_info_union
               ident_info_empty
               (List.map
                  collect_infos_of_stmt
                  e).

        Definition collect_all_infos {skip_typedefs : skip_typedefs_opt}
                   (e : expr)
                   {t}
                   (intypedefs : type.for_each_lhs_of_arrow OfPHOAS.var_typedef_data t)
                   (outtypedefs : OfPHOAS.base_var_typedef_data (type.final_codomain t))
          := ident_info_union
               (collect_infos e)
               (if skip_typedefs
                then ident_info_empty
                else ident_info_union
                       (ident_infos.collect_infos_of_arg_typedef_data intypedefs)
                       (ident_infos.collect_infos_of_typedef_data (t:=type.base _) outtypedefs)).
      End ident_infos.

      Module name_infos.
        Notation t := (list string) (only parsing).
        Definition mem (v : string) (m : t) : bool := existsb (fun s => v =? s)%string m.
        Definition add (v : string) (m : t) : t
          := if mem v m then m else v :: m.
        Definition union (m1 m2 : t) : t
          := let '(l1, l2) := (List.length m1, List.length m2) in
             let '(m1, m2) := if (l1 <=? l2)%nat then (m1, m2) else (m2, m1) in
             (* now m1 is shorter, so we recurse over m1 *)
             List.fold_right add m2 m1.
        Definition empty : t := nil.
        Definition singleton (v : string) : t := add v empty.
        Definition of_list (v : list string) : t := v.

        Section __.
          Context (consider_retargs_live : forall s d, ident s d -> bool).

          Let consider_addr_dead s d (idc : ident s d) : bool
            := match idc with
               | Addr => false
               | _ => true
               end.

          Fixpoint collect_live_of_arith_expr
                   (consider_args_live : forall s d, ident s d -> bool)
                   {t'} (e : arith_expr t') : t
            := match e with
               | AppIdent s d idc arg
                 => if consider_args_live s d idc
                    then @collect_live_of_arith_expr
                           (if consider_retargs_live s d idc
                            then consider_args_live
                            else consider_addr_dead)
                           _ arg
                    else empty
               | Var t v => singleton v
               | Pair A B a b => union (@collect_live_of_arith_expr consider_args_live _ a) (@collect_live_of_arith_expr consider_args_live _ b)
               | TT => empty
               end.

          Definition collect_live_of_stmt (e : stmt) : t
            := match e with
               | Assign _ _ _ _ val
               | AssignZPtr _ _ val
               | Call val
               | AssignNth _ _ val
                 => collect_live_of_arith_expr (fun _ _ _ => true) val
               | Comment _ live_vars
                 => of_list (List.flat_map (fun v => OfPHOAS.names_list_of_var_data (projT2 v)) live_vars)
               | DeclareVar _ _ _ => empty
               end.

          Definition collect_live (e : expr) : t
            := fold_right
                 union
                 empty
                 (List.map
                    collect_live_of_stmt
                    e).

          Section adjust_dead.
            Context (rename_dead : string -> string)
                    (live : t).

            Definition rename_if_dead (v : string) : string
              := if mem v live then v else rename_dead v.

            Fixpoint adjust_dead_of_arith_expr {t'} (e : arith_expr t') : arith_expr t'
              := match e with
                 | AppIdent s d idc arg => AppIdent idc (@adjust_dead_of_arith_expr _ arg)
                 | Var t v => Var t (rename_if_dead v)
                 | Pair A B a b => Pair (@adjust_dead_of_arith_expr _ a) (@adjust_dead_of_arith_expr _ b)
                 | TT => TT
                 end.

            Definition adjust_dead_of_stmt (e : stmt) : list stmt
              := match e with
                 | Call val
                   => [Call (adjust_dead_of_arith_expr val)]
                 | Assign declare t sz name val
                   => [Assign declare t sz name (adjust_dead_of_arith_expr val)]
                 | AssignZPtr name sz val
                   => [AssignZPtr name sz (adjust_dead_of_arith_expr val)]
                 | AssignNth name n val
                   => [AssignNth name n (adjust_dead_of_arith_expr val)]
                 | DeclareVar t sz name
                   => if mem name live
                      then [DeclareVar t sz name]
                      else []
                 | Comment _ _ as e
                   => [e]
                 end.

            Definition adjust_dead_of_expr (e : expr) : expr
              := flat_map adjust_dead_of_stmt e.
          End adjust_dead.

          Definition adjust_dead (rename_dead : string -> string) (e : expr) : expr
            := adjust_dead_of_expr rename_dead (collect_live e) e.
        End __.
      End name_infos.

      Module LiftDeclare.
        Local Open Scope list_scope.

        Definition split_declare (e : stmt) : list stmt (* decls *) * list stmt (* non-decls *)
          := match e with
             | Assign true t sz name val
               => ([DeclareVar t sz name], [Assign false t sz name val])
             | DeclareVar _ _ _ as e
               => ([e], [])
             | e => ([], [e])
             end.

        Definition split_declarations (e : expr) : expr (* decls *) * expr (* non-decls *)
          := let ls := List.map split_declare e in
             (List.flat_map (@fst _ _) ls,
              List.flat_map (@snd _ _) ls).

        Definition lift_declarations (e : expr) : expr
          := let '(decls, rest) := split_declarations e in
             decls ++ rest.
      End LiftDeclare.

      Module OfPHOAS.
        Export Stringification.Language.Compilers.ToString.OfPHOAS.

        Fixpoint arith_expr_for_base (t : base.type) : Type
          := match t with
             | tZ
               => arith_expr type.Z * option int.type
             | base.type.prod A B
               => arith_expr_for_base A * arith_expr_for_base B
             | base.type.list A => list (arith_expr_for_base A)
             | base.type.option A => option (arith_expr_for_base A)
             | base.type.unit as t
             | base.type.type_base _ as t
               => base.interp t
             end.
        Definition arith_expr_for (t : Compilers.type.type base.type) : Type
          := match t with
             | type.base t => arith_expr_for_base t
             | type.arrow s d => Empty_set
             end.

        (* Parametrizes the PHOAS -> IR translation over language specific
           numeric conversions *)
        Class LanguageCasts :=
          {
            (* [bin_op_natural_output] takes in a binary operation and
               the known types that the input fits into, and returns
               the type that the output will land in if no casts are
               present. *)
            bin_op_natural_output
            : Z_binop -> int.type * int.type -> int.type;
            (* [bin_op_casts] takes in a binary operation, the known
               type that the output fits in, and the pair of known
               types that the inputs fit in.  It returns the triple of
               (output, (input1, intput2)) of casts that are necessary
               for running the operation.  No-op casts on the inputs
               will later be discarded; the cast on the output, if
               given, will always be used. *)
            bin_op_casts
            : Z_binop -> option int.type -> int.type * int.type -> option int.type * (option int.type * option int.type);
            (* [un_op_casts] takes in a unary operation, the known
               type that the output fits in, and the known types that
               the input fits in.  It returns the tuple of (output,
               input) of casts that are necessary for running the
               operation.  No-op casts on the inputs will later be
               discarded; the cast on the output, if given, will
               always be used. *)
            un_op_casts
            : Z_unop -> option int.type -> int.type -> option int.type * option int.type;
            (* Are upcasts necessary on assignments? *)
            upcast_on_assignment : bool;
            (* Are upcasts necessary for arguments to function calls? *)
            upcast_on_funcall : bool;

            (* Should we declare pointer variables explicitly (rather than declaring non-pointer variables and taking references to them *)
            explicit_pointer_variables : bool;
          }.

        Class consider_retargs_live_opt := consider_retargs_live : forall {s d}, ident s d -> bool.
        Class rename_dead_opt := rename_dead : string -> string.
        Class lift_declarations_opt := lift_declarations : bool.

        Section __.
          Context {lang_casts : LanguageCasts}
                  {relax_zrange : relax_zrange_opt}
                  {consider_retargs_live : consider_retargs_live_opt}
                  {rename_dead : rename_dead_opt}
                  {lift_declarations : lift_declarations_opt}
                  {language_specific_cast_adjustment : language_specific_cast_adjustment_opt}.

          (* None means unconstrained *)
          Definition bin_op_natural_output_opt
            : Z_binop -> option int.type * option int.type -> option int.type
            := fun idc '(t1, t2)
               => match t1, t2 with
                  | Some t1, Some t2 => Some (bin_op_natural_output idc (t1, t2))
                  | _, _ => None
                  end.
          Definition bin_op_casts_opt
            : Z_binop -> option int.type -> option int.type * option int.type -> option int.type * (option int.type * option int.type)
            := fun idc tout '(t1, t2)
               => match t1, t2 with
                  | Some t1, Some t2
                    => bin_op_casts idc tout (t1, t2)
                  | _, _ => (tout, (None, None))
                  end.
          Definition un_op_casts_opt
            : Z_unop -> option int.type -> option int.type -> option int.type * option int.type
            := fun idc tout t1
               => match t1 with
                  | Some t1
                    => un_op_casts idc tout t1
                  | None => (tout, None)
                  end.

          Definition Zcast {always : bool}
            : option int.type -> arith_expr_for_base tZ -> arith_expr_for_base tZ
            := fun desired_type '(e, known_type)
               => let eq_known_type_desired_type
                    := (known_type <- known_type;
                        desired_type <- desired_type;
                        Some (int.type_beq known_type desired_type))%option in
                 match always, language_specific_cast_adjustment, desired_type, eq_known_type_desired_type with
                 | true, _, Some desired_type, _ (* if we always insert the cast, and there's a cast, then insert it *)
                 | _, true, Some desired_type, Some false (* if we are doing language-specific casts and we know the desired type and it's not the same as the known type, insert it *)
                 | _, true, Some desired_type, None (* if we are doing language-specific casts and we know the desired type and there was no known type, insert it *)
                   => (Z_static_cast desired_type @@@ e, Some desired_type)
                 | false, false, _, _ (* if we're not doing cast insertion (neither by forcing nor by language-specific casts), don't insert a cast *)
                 | _, true, Some _, Some true (* if we're doing language-specific casts but the new type is the same as the known type, we don't need to insert a cast *)
                 | _, _, None, _ (* if we don't know the type to insert, we can't insert a cast *)
                   => (e, known_type)
                 end%core%Cexpr%bool.

          Definition get_Zcast_down_if_needed
            : option int.type -> option int.type -> option int.type
            := fun desired_type known_type
               => match desired_type, known_type with
                  | None, _ => None
                  | Some desired_type, Some known_type
                    => if int.is_tighter_than known_type desired_type
                       then None
                       else Some desired_type
                  | Some desired_type, None
                    => Some desired_type
                  end%core%Cexpr.

          Definition Zcast_down_if_needed
            : option int.type -> arith_expr_for_base tZ -> arith_expr_for_base tZ
            := fun desired_type '(e, known_type)
               => Zcast (always:=false) (get_Zcast_down_if_needed desired_type known_type) (e, known_type).

          Fixpoint cast_down_if_needed {t}
            : int.option.interp t -> arith_expr_for_base t -> arith_expr_for_base t
            := match t with
               | tZ => Zcast_down_if_needed
               | base.type.type_base _
               | base.type.unit
                 => fun _ x => x
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
               | base.type.option A
                 => fun r1 ls
                    => match r1 with
                       | Some r1 => Option.map (fun '(r, e) => @cast_down_if_needed A r e)
                                               (Option.combine r1 ls)
                       | None => ls
                       end
               end.

          Definition get_Zcast_up_if_needed
            : option int.type -> option int.type -> option int.type
            := fun desired_type known_type
               => match desired_type, known_type with
                  | None, _ | _, None => None
                  | Some desired_type, Some known_type
                    => if int.is_tighter_than desired_type known_type
                       then None
                       else Some desired_type
                  end.

          Definition Zcast_up_if_needed
            : option int.type -> arith_expr_for_base tZ -> arith_expr_for_base tZ
            := fun desired_type '(e, known_type)
               => Zcast (always:=false) (get_Zcast_up_if_needed desired_type known_type) (e, known_type).

          Fixpoint cast_up_if_needed {t}
            : int.option.interp t -> arith_expr_for_base t -> arith_expr_for_base t
            := match t with
               | tZ => Zcast_up_if_needed
               | base.type.type_base _
               | base.type.unit
                 => fun _ x => x
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
               | base.type.option A
                 => fun r1 ls
                    => match r1 with
                       | Some r1 => Option.map (fun '(r, e) => @cast_up_if_needed A r e)
                                               (Option.combine r1 ls)
                       | None => ls
                       end
               end.

          Fixpoint cast {always:bool} {t}
            : int.option.interp t -> arith_expr_for_base t -> arith_expr_for_base t
            := match t with
               | tZ => Zcast (always:=always)
               | base.type.type_base _
               | base.type.unit
                 => fun _ x => x
               | base.type.prod A B
                 => fun '(r1, r2) '(e1, e2) => (@cast always A r1 e1,
                                                @cast always B r2 e2)
               | base.type.list A
                 => fun r1 ls
                    => match r1 with
                       | Some r1 => List.map (fun '(r, e) => @cast always A r e)
                                             (List.combine r1 ls)
                       | None => ls
                       end
               | base.type.option A
                 => fun r1 ls
                    => match r1 with
                       | Some r1 => Option.map (fun '(r, e) => @cast always A r e)
                                               (Option.combine r1 ls)
                       | None => ls
                       end
               end.

          Definition arith_bin_arith_expr_of_PHOAS_ident
                     (s:=(tZ * tZ)%etype)
                     (d:=tZ)
                     (idc : Z_binop)
            : option int.type -> arith_expr_for (type.base s) -> arith_expr_for (type.base d)
            := fun desired_type '((e1, t1), (e2, t2)) =>
                 let '(cstout, (cst1, cst2)) := bin_op_casts_opt idc desired_type (t1, t2) in
                 let typ := bin_op_natural_output_opt idc (Option.or_else cst1 t1, Option.or_else cst2 t2) in
                 let '((e1, t1), (e2, t2)) := (Zcast (always:=false) cst1 (e1, t1), Zcast (always:=false) cst2 (e2, t2)) in
                 Zcast (always:=false) cstout ((idc @@@ (e1, e2))%Cexpr, typ).

          Definition arith_un_arith_expr_of_PHOAS_ident
                     (s:=tZ)
                     (d:=tZ)
                     (idc : Z_unop)
            : option int.type -> arith_expr_for (type.base s) -> arith_expr_for (type.base d)
            := fun desired_type '(e, t) =>
                 let '(cstout, cst) := un_op_casts_opt idc desired_type t in
                 let typ := (*un_op_natural_output_opt idc*) Option.or_else cst t in
                 let '(e, t) := Zcast (always:=false) cst (e, t) in
                 Zcast (always:=false) cstout ((idc @@@ e)%Cexpr, typ).

          Local Definition fakeprod (A B : Compilers.type.type base.type) : Compilers.type.type base.type
            := match A, B with
               | type.base A, type.base B => type.base (base.type.prod A B)
               | type.arrow _ _, _
               | _, type.arrow _ _
                 => type.base base.type.unit
               end.
          Definition arith_expr_for_uncurried_domain (t : Compilers.type.type base.type)
            := match t return Type with
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
            Declare Scope err_scope.
            (*Local*) Delimit Scope err_scope with err.
            Local Notation "x <- v ; f" := (match v with
                                            | inl x => f
                                            | inr err => inr err
                                            end) : err_scope.
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


            Definition arith_expr_of_PHOAS_literal_Z
                       (t:=tZ)
                       v
              : int.option.interp (type.final_codomain t) -> arith_expr_for_base t
              := fun r
                 => cast_down_if_needed
                      r
                      (literal v @@@ TT, Some (int.of_zrange_relaxed (relax_zrange r[v~>v])))%core%Cexpr%option%zrange.

            Definition arith_expr_of_PHOAS_ident
                       {t}
                       (idc : ident.ident t)
              : int.option.interp (type.final_codomain t) -> type.interpM_final (fun T => ErrT T) arith_expr_for_base t
              := match idc in ident.ident t return int.option.interp (type.final_codomain t) -> type.interpM_final (fun T => ErrT T) arith_expr_for_base t with
                 | ident.Literal base.type.Z v
                   => fun r => ret (arith_expr_of_PHOAS_literal_Z v r)
                 | ident.tt => fun _ => ret tt
                 | ident.nil t
                   => fun _ => ret nil
                 | ident.cons t
                   => fun r x xs => ret (cast_down_if_needed r (cons x xs))
                 | ident.fst A B => fun r xy => ret (cast_down_if_needed r (@fst _ _ xy))
                 | ident.snd A B => fun r xy => ret (cast_down_if_needed r (@snd _ _ xy))
                 | ident.List_nth_default tZ
                   => fun r d ls n
                      => List.nth_default (inr ["Invalid list index " ++ show n]%string)
                                          (List.map (fun x => ret (cast_down_if_needed r x)) ls) n
                 | ident.Z_shiftr
                   => fun r e '(offset, roffset)
                      => match invert_literal offset with
                         | Some offset
                           => ret (arith_un_arith_expr_of_PHOAS_ident (Z_shiftr offset) r e)
                         | None => inr ["Invalid right-shift by a non-literal"]%string
                         end
                 | ident.Z_shiftl
                   => fun r e '(offset, roffset)
                      => match invert_literal offset with
                         | Some offset
                           => ret (arith_un_arith_expr_of_PHOAS_ident (Z_shiftl offset) r e)
                         | None => inr ["Invalid left-shift by a non-literal"]%string
                         end
                 | ident.Z_truncating_shiftl
                   => fun r '(bitwidth, rbitwidth) e '(offset, roffset)
                      => match invert_literal bitwidth, invert_literal offset with
                         | Some bitwidth, Some offset
                           => let rpre_out := Some (int.of_zrange_relaxed r[0 ~> Z.max (2^offset) (2^bitwidth-1)]%zrange) in
                              let shifted := arith_un_arith_expr_of_PHOAS_ident (Z_shiftl offset) rpre_out e in
                              let truncated := arith_bin_arith_expr_of_PHOAS_ident Z_land r (shifted, arith_expr_of_PHOAS_literal_Z (2^bitwidth-1) (Some (int.of_zrange_relaxed r[0~>2^bitwidth - 1]))) in
                              ret truncated
                         | _, None => inr ["Invalid (truncating) left-shift by a non-literal"]%string
                         | None, _ => inr ["Invalid left-shift truncated to a non-literal bitwidth"]%string
                         end
                 | ident.value_barrier
                   => fun r '(x, rx)
                      => match rx with
                         | Some ty
                           => ret (cast_down_if_needed r (Z_value_barrier ty @@@ x, Some ty))
                         | None => inr ["Invalid unknown integer size for value_barrier"]%string
                         end
                 | ident.Z_bneg => fun r x => ret (arith_un_arith_expr_of_PHOAS_ident Z_bneg r x)
                 | ident.Z_land => fun r x y => ret (arith_bin_arith_expr_of_PHOAS_ident Z_land r (x, y))
                 | ident.Z_lor => fun r x y => ret (arith_bin_arith_expr_of_PHOAS_ident Z_lor r (x, y))
                 | ident.Z_lxor => fun r x y => ret (arith_bin_arith_expr_of_PHOAS_ident Z_lxor r (x, y))
                 | ident.Z_add => fun r x y => ret (arith_bin_arith_expr_of_PHOAS_ident Z_add r (x, y))
                 | ident.Z_mul => fun r x y => ret (arith_bin_arith_expr_of_PHOAS_ident Z_mul r (x, y))
                 | ident.Z_sub => fun r x y => ret (arith_bin_arith_expr_of_PHOAS_ident Z_sub r (x, y))
                 | ident.Z_lnot_modulo
                   => fun rout '(e, r) '(modulus, _)
                      => match invert_literal modulus with
                         | Some modulus
                           => match maybe_loglog2 modulus with
                              | Some lgbitwidth
                                => let ty := int.unsigned lgbitwidth in
                                   let rin' := Some ty in
                                   let '(e, _) := Zcast (always:=false) rin' (e, r) in
                                   ret (cast_down_if_needed rout (cast_up_if_needed rout (Z_lnot ty @@@ e, rin')))
                              | None => inr ["Invalid modulus for Z.lnot (not 2^(2^_)): " ++ show modulus]%string
                              end
                         | None => inr ["Invalid non-literal modulus for Z.lnot"]%string
                         end
                 | ident.pair A B
                   => fun _ _ _ => inr ["Invalid identifier in arithmetic expression " ++ show idc]%string
                 | ident.Z_opp (* we pretend this is [0 - _] *)
                   => fun r x =>
                        let zero := (literal 0 @@@ TT, Some (int.of_zrange_relaxed (relax_zrange r[0~>0]))) in
                        ret (arith_bin_arith_expr_of_PHOAS_ident Z_sub r (zero, x))
                 | ident.Literal _ v
                   => fun _ => ret v
                 | ident.comment _
                 | ident.comment_no_keep _
                 | ident.Nat_succ
                 | ident.Nat_pred
                 | ident.Nat_max
                 | ident.Nat_mul
                 | ident.Nat_add
                 | ident.Nat_sub
                 | ident.Nat_eqb
                 | ident.prod_rect _ _ _
                 | ident.bool_rect _
                 | ident.bool_rect_nodep _
                 | ident.nat_rect _
                 | ident.eager_nat_rect _
                 | ident.nat_rect_arrow _ _
                 | ident.eager_nat_rect_arrow _ _
                 | ident.Some _
                 | ident.None _
                 | ident.option_rect _ _
                 | ident.list_rect _ _
                 | ident.eager_list_rect _ _
                 | ident.list_rect_arrow _ _ _
                 | ident.eager_list_rect_arrow _ _ _
                 | ident.list_case _ _
                 | ident.List_length _
                 | ident.List_seq
                 | ident.List_repeat _
                 | ident.List_firstn _
                 | ident.List_skipn _
                 | ident.List_combine _ _
                 | ident.List_map _ _
                 | ident.List_app _
                 | ident.List_rev _
                 | ident.List_flat_map _ _
                 | ident.List_partition _
                 | ident.List_fold_right _ _
                 | ident.List_update_nth _
                 | ident.List_nth_default _
                 | ident.eager_List_nth_default _
                 | ident.Z_pow
                 | ident.Z_div
                 | ident.Z_modulo
                 | ident.Z_eqb
                 | ident.Z_leb
                 | ident.Z_ltb
                 | ident.Z_geb
                 | ident.Z_gtb
                 | ident.Z_min
                 | ident.Z_max
                 | ident.Z_log2
                 | ident.Z_log2_up
                 | ident.Z_of_nat
                 | ident.Z_to_nat
                 | ident.Z_ltz
                 | ident.Z_zselect
                 | ident.Z_mul_split
                 | ident.Z_mul_high
                 | ident.Z_add_get_carry
                 | ident.Z_add_with_carry
                 | ident.Z_add_with_get_carry
                 | ident.Z_sub_get_borrow
                 | ident.Z_sub_with_get_borrow
                 | ident.Z_add_modulo
                 | ident.Z_rshi
                 | ident.Z_cc_m
                 | ident.Z_combine_at_bitwidth
                 | ident.Z_cast
                 | ident.Z_cast2
                 | ident.Build_zrange
                 | ident.zrange_rect _
                 | ident.fancy_add
                 | ident.fancy_addc
                 | ident.fancy_sub
                 | ident.fancy_subb
                 | ident.fancy_mulll
                 | ident.fancy_mullh
                 | ident.fancy_mulhl
                 | ident.fancy_mulhh
                 | ident.fancy_rshi
                 | ident.fancy_selc
                 | ident.fancy_selm
                 | ident.fancy_sell
                 | ident.fancy_addm
                   => fun _ => type.interpM_return _ _ _ (inr ["Invalid identifier in arithmetic expression " ++ show idc]%string)
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
                      => match x int.option.None return _ with
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
                 | ident.Z_cast
                   => inl
                        (fun r arg
                         => r <- r tt;
                         let r := Some (int.of_zrange_relaxed r) in
                         inl (fun r'
                              => if language_specific_cast_adjustment
                                 then
                                   arg <- arg r; ret (Zcast_down_if_needed r' arg)
                                 else
                                   arg <- arg None; ret (Zcast (always:=true) r arg)))
                 | ident.Z_cast2
                   => inl
                        (fun r arg
                         => r <- r (tt, tt);
                         let r := (Some (int.of_zrange_relaxed (fst r)), Some (int.of_zrange_relaxed (snd r))) in
                         inl (fun r'
                              => if language_specific_cast_adjustment
                                 then
                                   (arg <- arg r; ret (cast_down_if_needed (t:=tZ*tZ) r' arg))
                                 else
                                   (arg <- arg (None, None); ret (cast (always:=true) (t:=tZ*tZ) r arg))))
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
                 | _ => inr ["Invalid identifier where cast or constructor was expected: " ++ show idc]%string
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
                 | tZ
                   => fun '(n, is_ptr, r, td) r'
                      => let v := if is_ptr
                                  then (Dereference @@@ Var type.Zptr n)%Cexpr
                                  else Var type.Z n in
                         ret (cast_down_if_needed r' (v, r))
                 | base.type.prod A B
                   => fun '(da, db) '(ra, rb)
                      => (ea,, eb <- @arith_expr_of_base_PHOAS_Var A da ra, @arith_expr_of_base_PHOAS_Var B db rb;
                            inl (ea, eb))
                 | base.type.list tZ
                   => fun '(n, r, len, td) r'
                      => ret (List.map
                                (fun i => (List_nth i @@@ Var type.Zptr n, r))%core%Cexpr
                                (List.seq 0 len))
                 | base.type.list _
                 | base.type.option _
                 | base.type.type_base _
                 | base.type.unit
                   => fun _ _ => inr ["Invalid type " ++ show t]%string
                 end.

            Fixpoint arith_expr_of_PHOAS
                     {t}
                     (e : @API.expr var_data t)
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
                   => let x' := @arith_expr_of_PHOAS (type.base s) x in
                      match x' with
                      | inl x' => @arith_expr_of_PHOAS _ f x'
                      | inr errs => type.interpM_return _ _ _ (inr errs)
                      end
                 | expr.Var (type.arrow _ _) _
                   => type.interpM_return _ _ _ (inr ["Invalid non-arithmetic let-bound Var of type " ++ show t]%string)
                 | expr.App (type.arrow _ _) _ _ _
                   => type.interpM_return _ _ _ (inr ["Invalid non-arithmetic let-bound App of type " ++ show t]%string)
                 | expr.LetIn _ _ _ _
                   => type.interpM_return _ _ _ (inr ["Invalid non-arithmetic let-bound LetIn of type " ++ show t]%string)
                 | expr.Abs _ _ _
                   => type.interpM_return _ _ _ (inr ["Invalid non-arithmetic let-bound Abs of type: " ++ show t]%string)
                 end.

            Definition arith_expr_of_base_PHOAS
                       {t:base.type}
                       (e : @API.expr var_data (type.base t))
                       (rout : int.option.interp t)
              : ErrT (arith_expr_for_base t)
              := (e' <- arith_expr_of_PHOAS e; e' rout).

            Definition result_upcast {t}
              : int.option.interp t -> arith_expr_for_base t -> arith_expr_for_base t
              := if upcast_on_assignment
                 then cast (always:=false)
                 else fun _ e => e.

            Definition funcall_upcast {t}
              : int.option.interp t -> arith_expr_for_base t -> arith_expr_for_base t
              := if upcast_on_funcall
                 then cast (always:=false)
                 else fun _ e => e.

            Fixpoint make_return_assignment_of_base_arith {t}
              : base_var_data t
                -> @API.expr var_data (type.base t)
                -> ErrT expr
              := match t return base_var_data t -> expr.expr (type.base t) -> ErrT expr with
                 | tZ
                   => fun '(n, is_ptr, r, td) e
                      => (rhs <- arith_expr_of_base_PHOAS e r;
                            let '(e, r) := result_upcast (t:=tZ) r rhs in
                            ret (if is_ptr
                                 then [AssignZPtr n r e]
                                 else [Assign false type.Z r n e]))
                 | base.type.type_base _
                 | base.type.unit
                   => fun _ _ => inr ["Invalid type " ++ show t]%string
                 | base.type.prod A B
                   => fun '(rva, rvb) e
                      => match invert_pair e with
                         | Some (ea, eb)
                           => ea',, eb' <- @make_return_assignment_of_base_arith A rva ea, @make_return_assignment_of_base_arith B rvb eb;
                                ret (ea' ++ eb')
                         | None => inr ["Invalid non-pair expr of type " ++ show t]%string
                         end
                 | base.type.list tZ
                   => fun '(n, r, len, td) e
                      => (ls <- arith_expr_of_base_PHOAS e (Some (repeat r len));
                            ret (List.map
                                   (fun '(i, rhs) =>
                                      let '(e, _) := result_upcast (t:=tZ) r rhs in
                                      AssignNth n i e)
                                   (List.combine (List.seq 0 len) ls)))
                 | base.type.list _
                 | base.type.option _
                   => fun _ _ => inr ["Invalid type of expr: " ++ show t]%string
                 end%list.
            Definition make_return_assignment_of_arith {t}
              : var_data t
                -> @API.expr var_data t
                -> ErrT expr
              := match t with
                 | type.base t => make_return_assignment_of_base_arith
                 | type.arrow s d => fun _ _ => inr ["Invalid type of expr: " ++ show t]%string
                 end.

            Definition report_type_mismatch (expected : API.type) (given : API.type) : string
              := ("Type mismatch; expected " ++ show expected ++ " but given " ++ show given ++ ".")%string.

            Fixpoint arith_expr_of_PHOAS_args
                     {t}
              : type.for_each_lhs_of_arrow (@API.expr var_data) t
                -> ErrT (type.for_each_lhs_of_arrow (fun t => @API.expr var_data t * (arith_expr type.Z * option int.type)) t)
              := match t with
                 | type.base t => fun 'tt => inl tt
                 | type.arrow (type.base tZ) d
                   => fun '(arg, args)
                      => arg' ,, args' <- arith_expr_of_base_PHOAS arg int.option.None , @arith_expr_of_PHOAS_args d args;
                           inl ((arg, arg'), args')
                 | type.arrow s d
                   => fun '(arg, args)
                      => arg' ,, args' <- @inr unit _ ["Invalid argument of non-ℤ type " ++ show s]%string , @arith_expr_of_PHOAS_args d args;
                           inr ["Impossible! (type error got lost somewhere)"]
                 end.

            Fixpoint base_var_names_of_string_opt {t} (n : string) : option (base_var_names t)
              := match t return option (base_var_names t) with
                 | tZ
                 | base.type.list _
                   => Some n
                 | base.type.prod A B
                   => (a <- @base_var_names_of_string_opt A (n ++ "₁");
                      b <- @base_var_names_of_string_opt B (n ++ "₂");
                      Some (a, b))%option
                 | base.type.unit => Some tt
                 | base.type.option _
                 | base.type.type_base _
                   => None
                 end.

            Fixpoint string_of_base_var_names {t} : base_var_names t -> string
              := match t return base_var_names t -> string with
                 | tZ
                 | base.type.list _
                   => fun n => n
                 | base.type.prod A B
                   => fun x : base_var_names A * base_var_names B
                      => let a := @string_of_base_var_names A (fst x) in
                         let b := @string_of_base_var_names B (snd x) in
                         let len_a := String.length a in
                         let len_b := String.length b in
                         let '(a, a_tl) := (String.substring 0 (len_a - 1) a, String.substring (len_a - 1) 1 a) in
                         let '(b, b_tl) := (String.substring 0 (len_b - 1) b, String.substring (len_b - 1) 1 b) in
                         if ((len_a =? len_b)%nat && (a =? b) && (a_tl =? "₁") && (b_tl =? "₂"))
                         then a
                         else "(" ++ a ++ "," ++ b ++ ")"
                 | base.type.unit => fun 'tt => "()"
                 | base.type.option _
                 | base.type.type_base _
                   => fun absurd : Empty_set => match absurd with end
                 end%string%bool.

            Definition var_names_of_string_opt {t} (n : string) : option (var_names t)
              := match t with
                 | type.base _ => @base_var_names_of_string_opt _ n
                 | type.arrow _ _ => None
                 end.

            Definition string_of_var_names {t} : var_names t -> string
              := match t with
                 | type.base _ => @string_of_base_var_names _
                 | type.arrow _ _ => fun absurd : Empty_set => match absurd with end
                 end.

            Definition base_var_data_of_string_opt {t} (n : string) : option (base_var_data t)
              := option_map base_var_data_of_names (base_var_names_of_string_opt n).
            Definition var_data_of_string_opt {t} (n : string) : option (var_data t)
              := option_map var_data_of_names (var_names_of_string_opt n).

            Definition string_of_base_var_data {t} (v : base_var_data t) : string
              := string_of_base_var_names (names_of_base_var_data v).
            Definition string_of_var_data {t} (v : var_data t) : string
              := string_of_var_names (names_of_var_data v).

            Fixpoint extract_var_data_list {t} (e : @API.expr var_data t) : list { t : _ & var_data t }
              := match e with
                 | expr.Ident t idc => []
                 | expr.Var t v => [existT _ _ v]
                 | expr.Abs s d f
                   => match var_data_of_string_opt "(FAKE_extract_var_data_list)" with
                      | Some d => extract_var_data_list (f d)
                      | None => []
                      end
                 | expr.App s d f x
                   => extract_var_data_list f ++ extract_var_data_list x
                 | expr.LetIn A B x f
                   => (extract_var_data_list x)
                        ++ match var_data_of_string_opt "(FAKE_extract_var_data_list)" with
                           | Some d => extract_var_data_list (f d)
                           | None => []
                           end
                 end.

            Let make_comment
                {t}
                (e : @API.expr var_data t)
              : ErrT (expr * var_data t)
              := let _ := @PHOAS.expr.partially_show_expr in
                 let ret_err := inr ["Not a comment " ++ show e]%string in
                 match invert_AppIdent e, var_data_of_string_opt "()" with
                 | Some (existT t (idc, arg)), Some retdata
                   => let should_keep_live := match idc return option bool with
                                              | ident.comment _ => Some true
                                              | ident.comment_no_keep _ => Some false
                                              | _ => None
                                              end in
                      match should_keep_live with
                      | Some should_keep_live
                        => inl ([Comment
                                   (PHOAS.expr.show_lines_expr_gen (@string_of_var_data) (@var_data_of_string_opt) arg) (* comment lines *)
                                   (if should_keep_live then extract_var_data_list arg else []) (* live variables *)],
                                retdata)
                      | None => ret_err
                      end
                 | None, _ | _, None => ret_err
                 end.

            Definition bounds_check (do_bounds_check : bool) (descr : string) {t} (idc : ident.ident t) (s : BinInt.Z) {t'} (ev : @API.expr var_data t') (found : option int.type)
              : ErrT unit
              := if negb do_bounds_check
                 then ret tt
                 else
                   let _ := @PHOAS.expr.partially_show_expr in
                   match found with
                   | None => inr ["Missing range on " ++ descr ++ " " ++ show idc ++ ": " ++ show ev]%string
                   | Some ty
                     => if int.is_tighter_than ty (int.of_zrange_relaxed (relax_zrange r[0~>2^s-1]))
                        then ret tt
                        else inr ["Final bounds check failed on " ++ descr ++ " " ++ show idc ++ "; expected an unsigned " ++ Decimal.Z.to_string s ++ "-bit number (relaxed to " ++ show (int.of_zrange_relaxed (relax_zrange r[0~>2^s-1])) ++ "), but found a " ++ show ty ++ "."]%string
                   end.

            Let recognize_1ref_ident
                (do_bounds_check : bool)
                {t}
                (idc : ident.ident t)
              : option (forall (rout : option int.type),
                           type.for_each_lhs_of_arrow (fun t => @API.expr var_data t * (arith_expr type.Z * option int.type))%type t
                           -> ErrT (arith_expr type.Zptr -> expr))
              := let _ := @PHOAS.expr.partially_show_expr in
                 match idc in ident.ident t
                       return option (forall (rout : option int.type),
                                                        type.for_each_lhs_of_arrow (fun t => @API.expr var_data t * (arith_expr type.Z * option int.type))%type t
                                                        -> ErrT (arith_expr type.Zptr -> expr))
                 with
                 | ident.Z_zselect
                   => Some
                        (fun rout '((econdv, (econd, rcond)), ((e1v, (e1, r1)), ((e2v, (e2, r2)), tt)))
                         => (*let err := inr ["Invalid argument to Z.zselect not known to be 0 or 1: " ++ show econdv]%string in*)
                           _ <- bounds_check do_bounds_check "first argument to" idc 1 econdv rcond;
                             let '((e1, r1), (e2, r2)) :=
                                 funcall_upcast (t:=tZ*tZ) (rout, rout) ((e1, r1), (e2, r2)) in
                             ty <- match rout with
                                   | Some rout
                                     => inl rout
                                   | None => inr ["Missing cast annotation on return of Z.zselect"]
                                   end;
                               ret (fun retptr => [Call (Z_zselect ty @@@ (retptr, (econd, e1, e2)))]%Cexpr))
                 | _ => None (* fun _ => inr ["Unrecognized identifier (expecting a 1-pointer-returning function): " ++ show idc]%string *)
                 end.

            Let round_up_to_split_type (lgs : Z) (t : option int.type) : option int.type
              := option_map (int.union (int.of_zrange_relaxed (relax_zrange r[0~>2^lgs-1]))) t.

            Let check_literal_rangeZ (r : option zrange) (v : Z) (nth : string) {t'} (idc : ident.ident t') : ErrT unit
              := match r with
                 | None => inl tt
                 | Some r
                   => if ZRange.type.is_bounded_by (t:=tZ) r v
                      then inl tt
                      else inr ["Literal value " ++ show v ++ " is not within the casted range " ++ show r ++ " (when trying to parse the " ++ nth ++ " argument of " ++ show idc ++ ")"]%string
                 end.

            Let recognize_3arg_2ref_ident
                {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
                (do_bounds_check : bool)
                (t:=(tZ -> tZ -> tZ -> tZ * tZ)%etype)
                (idc : ident.ident t)
                (rout : option int.type * option int.type)
                (args : type.for_each_lhs_of_arrow (fun t => @API.expr var_data t *
                                                             (arith_expr type.Z * option int.type))%type t)
              : ErrT ((option int.type * option int.type) * (arith_expr (type.Zptr * type.Zptr) -> expr))
              := let _ := @PHOAS.expr.partially_show_expr in
                 let '((s, _), ((e1v, (e1, r1)), ((e2v, (e2, r2)), tt))) := args in
                  match (rs <- invert_Literal_through_cast s; lg2s <- maybe_log2 (snd rs); Some (fst rs, lg2s))%option, idc return ErrT ((option int.type * option int.type) * (arith_expr (type.Zptr * type.Zptr) -> expr))
                  with
                  | Some (r, s), ident.Z_mul_split
                    => (_ <- check_literal_rangeZ r (2^s) "first" idc;
                       _ ,, _ ,, _ ,, _
                          <- bounds_check do_bounds_check "first argument to" idc s e1v r1,
                        bounds_check do_bounds_check "second argument to" idc s e2v r2,
                        bounds_check do_bounds_check "first return value of" idc s e2v (fst rout),
                        bounds_check do_bounds_check "second return value of" idc s e2v (snd rout);
                          inl ((round_up_to_split_type s (fst rout), round_up_to_split_type s (snd rout)),
                               fun retptr => [Call (Z_mul_split s @@@ (retptr, (e1, e2)))%Cexpr]))
                  | Some (r, s), ident.Z_add_get_carry as idc
                  | Some (r, s), ident.Z_sub_get_borrow as idc
                    => let idc' : ident _ _ := Option.invert_Some
                                                 match idc with
                                                 | ident.Z_add_get_carry => Some (Z_add_with_get_carry s)
                                                 | ident.Z_sub_get_borrow => Some (Z_sub_with_get_borrow s)
                                                 | _ => None
                                                 end in
                       (_ <- check_literal_rangeZ r (2^s) "first" idc;
                       let '(return_carry_borrow_width, round_up_return_carry)
                           := if List.existsb (Z.eqb s) relax_adc_sbb_return_carry_to_bitwidth
                              then (s, round_up_to_split_type s)
                              else (1 (* boolean carry/borrow *), fun x => x) in
                       _ ,, _ ,, _ ,, _
                          <- bounds_check do_bounds_check "first argument to" idc s e1v r1,
                        bounds_check do_bounds_check "second argument to" idc s e2v r2,
                        bounds_check do_bounds_check "first return value of" idc s e2v (fst rout),
                        bounds_check do_bounds_check "second return value of" idc return_carry_borrow_width e2v (snd rout);
                       let '(e1, _) := result_upcast (t:=tZ) (Some (int.of_zrange_relaxed r[0 ~> 2 ^ s - 1])) (e1, r1) in
                       let '(e2, _) := result_upcast (t:=tZ) (Some (int.of_zrange_relaxed r[0 ~> 2 ^ s - 1])) (e2, r2) in
                       inl ((round_up_to_split_type s (fst rout), round_up_return_carry (snd rout)),
                            fun retptr => [Call (idc' @@@ (retptr, (literal 0 @@@ TT, e1, e2)))%Cexpr]))
                  | Some _, _ => inr ["Unrecognized identifier when attempting to construct an assignment with 2 arguments: " ++ show idc]%string
                  | None, _ => inr ["Expression is not a literal power of two of type ℤ: " ++ show s ++ " (when trying to parse the first argument of " ++ show idc ++ ")"]%string
                  end.

            Let recognize_4arg_2ref_ident
                {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
                (do_bounds_check : bool)
                (t:=(tZ -> tZ -> tZ -> tZ -> tZ * tZ)%etype)
                (idc : ident.ident t)
                (rout : option int.type * option int.type)
                (args : type.for_each_lhs_of_arrow (fun t => @API.expr var_data t * (arith_expr type.Z * option int.type))%type t)
              : ErrT ((option int.type * option int.type) * (arith_expr (type.Zptr * type.Zptr) -> expr))
              := let _ := @PHOAS.expr.partially_show_expr in
                 let '((s, _), ((e1v, (e1, r1)), ((e2v, (e2, r2)), ((e3v, (e3, r3)), tt)))) := args in
                 match (rs <- invert_Literal_through_cast s; lg2s <- maybe_log2 (snd rs); Some (fst rs, lg2s))%option, idc return ErrT ((option int.type * option int.type) * (arith_expr (type.Zptr * type.Zptr) -> expr))
                 with
                 | Some (r, s), ident.Z_add_with_get_carry as idc
                 | Some (r, s), ident.Z_sub_with_get_borrow as idc
                   => let idc' : ident _ _ := Option.invert_Some
                                                match idc with
                                                | ident.Z_add_with_get_carry => Some (Z_add_with_get_carry s)
                                                | ident.Z_sub_with_get_borrow => Some (Z_sub_with_get_borrow s)
                                                | _ => None
                                                end in
                      (_ <- check_literal_rangeZ r (2^s) "first" idc;
                      let '(return_carry_borrow_width, round_up_return_carry)
                          := if List.existsb (Z.eqb s) relax_adc_sbb_return_carry_to_bitwidth
                             then (s, round_up_to_split_type s)
                             else (1 (* boolean carry/borrow *), fun x => x) in
                      _ ,, _ ,, _ ,, _ ,, _
                         <- (bounds_check do_bounds_check "first (carry) argument to" idc 1 e1v r1,
                             bounds_check do_bounds_check "second argument to" idc s e2v r2,
                             bounds_check do_bounds_check "third argument to" idc s e2v r2,
                             bounds_check do_bounds_check "first return value of" idc s e2v (fst rout),
                             bounds_check do_bounds_check "second (carry) return value of" idc return_carry_borrow_width e2v (snd rout));
                         let '(e1, _) := result_upcast (t:=tZ) (Some (int.of_zrange_relaxed (relax_zrange r[0 ~> 2 ^ 1 - 1]))) (e1, r1) in
                         let '(e2, _) := result_upcast (t:=tZ) (Some (int.of_zrange_relaxed (relax_zrange r[0 ~> 2 ^ s - 1]))) (e2, r2) in
                         let '(e3, _) := result_upcast (t:=tZ) (Some (int.of_zrange_relaxed (relax_zrange r[0 ~> 2 ^ s - 1]))) (e3, r3) in
                         inl ((round_up_to_split_type s (fst rout), round_up_return_carry (snd rout)),
                              fun retptr => [Call (idc' @@@ (retptr, (e1, e2, e3)))%Cexpr]))
                 | Some _, _ => inr ["Unrecognized identifier when attempting to construct an assignment with 2 arguments: " ++ show idc]%string
                 | None, _ => inr ["Expression is not a literal power of two of type ℤ: " ++ show s ++ " (when trying to parse the first argument of " ++ show idc ++ ")"]%string
                 end.

            Let recognize_2ref_ident
                {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
                {t}
              : forall (do_bounds_check : bool)
                       (idc : ident.ident t)
                       (rout : option int.type * option int.type)
                       (args : type.for_each_lhs_of_arrow (fun t => @API.expr var_data t * (arith_expr type.Z * option int.type))%type t),
                ErrT ((option int.type * option int.type) * (arith_expr (type.Zptr * type.Zptr) -> expr))
              := match t with
                 | (type.base tZ -> type.base tZ -> type.base tZ -> type.base (tZ * tZ))%etype
                   => recognize_3arg_2ref_ident
                 | (type.base tZ -> type.base tZ -> type.base tZ -> type.base tZ -> type.base (tZ * tZ))%etype
                   => recognize_4arg_2ref_ident
                 | _ => fun do_bounds_check idc rout args => inr ["Unrecognized type for function call: " ++ show t ++ " (when trying to handle the identifer " ++ show idc ++ ")"]%string
                 end.

            Definition declare_name
                       (descr : string)
                       (count : positive)
                       (make_name : positive -> option string)
                       (r : option int.type)
              : ErrT (expr * string * bool (* is pointer *) * arith_expr type.Zptr)
              := (n ,, r <- (match make_name count with
                             | Some n => ret n
                             | None => inr ["Variable naming-function does not support the index " ++ show count]%string
                             end,
                             match r with
                             | Some r => ret r
                             | None => inr ["Missing return type annotation for " ++ descr]%string
                             end);
                 ret (if explicit_pointer_variables
                      then ([DeclareVar type.Zptr (Some r) n], n, true, (Var type.Zptr n)%Cexpr)
                      else ([DeclareVar type.Z (Some r) n], n, false, (Addr @@@ Var type.Z n)%Cexpr))).

            Let make_assign_arg_1ref_opt
                (do_bounds_check : bool)
                (e : @API.expr var_data tZ)
                (count : positive)
                (make_name : positive -> option string)
              : ErrT (expr * var_data tZ)
              := let _ := @PHOAS.expr.partially_show_expr in
                 let e1 := e in
                 let '(rout, e) := match invert_App_Z_cast e with
                                   | Some (r, e) => (Some (int.of_zrange_relaxed r), e)
                                   | None => (None, e)
                                   end%core in
                 let res_ref
                     := (idc_args <- invert_AppIdent_curried e;
                           let '(existT _ (idc, args)) := idc_args in
                           recognize <- recognize_1ref_ident do_bounds_check idc;
                             Some
                               (args <- arith_expr_of_PHOAS_args args;
                                  idce <- recognize rout args;
                                  v <- declare_name (show idc) count make_name rout;
                                  let '(decls, n, is_ptr, retv) := v in
                                  ret ((decls ++ (idce retv))%list, (n, is_ptr, rout, None)))%err)%option in
                 match res_ref with
                 | Some (inl res) => ret res
                 | Some (inr err) => inr err
                 | None
                   => e1 <- arith_expr_of_base_PHOAS e1 None;
                        let '(e1, r1) := e1 in
                        match make_name count with
                        | Some n1
                          => ret ([Assign true type.Z r1 n1 e1], (n1, false, r1, None))
                        | None => inr ["Variable naming-function does not support the index " ++ show count]%string
                        end
                 end.

            Let make_assign_arg_2ref
                {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
                (do_bounds_check : bool)
                (e : @API.expr var_data (tZ * tZ))
                (count : positive)
                (make_name : positive -> option string)
              : ErrT (expr * var_data (tZ * tZ))
              := let _ := @PHOAS.expr.partially_show_expr in
                 let '((rout1, rout2), e)
                     := match invert_App_Z_cast2 e with
                        | Some ((r1, r2), e) => ((Some (int.of_zrange_relaxed r1), Some (int.of_zrange_relaxed r2)), e)
                        | None => ((None, None), e)
                        end%core in
                 match invert_AppIdent_curried e with
                 | Some (existT t (idc, args))
                   => args <- arith_expr_of_PHOAS_args args;
                        idce <- recognize_2ref_ident do_bounds_check idc (rout1, rout2) args;
                        let '((rout1, rout2), idce) := idce in
                        v1,, v2 <- (declare_name (show idc) count make_name rout1,
                                    declare_name (show idc) (Pos.succ count) make_name rout2);
                          let '(decls1, n1, is_ptr1, retv1) := v1 in
                          let '(decls2, n2, is_ptr2, retv2) := v2 in
                          ret (decls1 ++ decls2 ++ (idce (retv1, retv2)%Cexpr), ((n1, is_ptr1, rout1, None), (n2, is_ptr2, rout2, None)))%list
                 | None => inr ["Invalid assignment of non-identifier-application: " ++ show e]%string
                 end.

            Let make_assign_arg_ref
                {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
                (do_bounds_check : bool)
                {t}
              : forall (e : @API.expr var_data t)
                       (count : positive)
                       (make_name : positive -> option string),
                ErrT (expr * var_data t)
              := let _ := @PHOAS.expr.partially_show_expr in
                 match t with
                 | type.base tZ => make_assign_arg_1ref_opt do_bounds_check
                 | type.base (tZ * tZ)%etype => make_assign_arg_2ref do_bounds_check
                 | type.base base.type.unit => fun e _ _ => make_comment e
                 | _ => fun e _ _ => inr ["Invalid type of assignment expression: " ++ show t ++ " (with expression " ++ show e ++ ")"]
                 end.

            Fixpoint size_of_type (t : base.type) : positive
              := match t with
                 | base.type.type_base _
                 | base.type.unit
                   => 1
                 | base.type.prod A B => size_of_type A + size_of_type B
                 | base.type.list A => 1
                 | base.type.option A => 1
                 end%positive.

            Let make_uniform_assign_expr_of_PHOAS
                {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
                (do_bounds_check : bool)
                {s} (e1 : @API.expr var_data s)
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
                       {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
                       (do_bounds_check : bool)
                       {s} (e1 : @API.expr var_data s)
                       {s' d} (e2 : var_data s' -> var_data d -> ErrT expr)
                       (count : positive)
                       (make_name : positive -> option string)
                       (v : var_data d)
              : ErrT expr
              := Eval cbv beta iota delta [bind2_err bind3_err bind4_err bind5_err recognize_1ref_ident recognize_3arg_2ref_ident recognize_4arg_2ref_ident recognize_2ref_ident make_assign_arg_1ref_opt make_assign_arg_2ref make_assign_arg_ref make_uniform_assign_expr_of_PHOAS make_uniform_assign_expr_of_PHOAS round_up_to_split_type make_comment check_literal_rangeZ] in
                  match type.try_transport _ _ s' e1 with
                  | Some e1 => make_uniform_assign_expr_of_PHOAS do_bounds_check e1 e2 count make_name v
                  | None => inr [report_type_mismatch s' s]
                  end.

            Fixpoint expr_of_base_PHOAS
                     {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
                     (do_bounds_check : bool)
                     {t}
                     (e : @API.expr var_data t)
                     (count : positive)
                     (make_name : positive -> option string)
                     {struct e}
              : forall (ret_val : var_data t), ErrT expr
              := match e in expr.expr t return var_data t -> ErrT expr with
                 | expr.LetIn (type.base s) d e1 e2
                   => make_assign_expr_of_PHOAS
                        do_bounds_check
                        e1
                        (fun vs vd => expr_of_base_PHOAS do_bounds_check (t:=d) (e2 vs) (size_of_type s + count)%positive make_name vd)
                        count make_name
                 | expr.LetIn (type.arrow _ _) _ _ _ as e
                 | expr.Var _ _ as e
                 | expr.Ident _ _ as e
                 | expr.App _ _ _ _ as e
                 | expr.Abs _ _ _ as e
                   => fun v => make_return_assignment_of_arith v e
                 end%expr_pat%option.

            Fixpoint base_var_data_of_bounds_and_typedefs {t}
                     (is_ptr : bool)
                     (count : positive)
                     (make_name : positive -> option string)
                     {struct t}
              : ZRange.type.base.option.interp t -> base_var_typedef_data t -> option (positive * var_data (type.base t))
              := match t return ZRange.type.base.option.interp t -> base_var_typedef_data t -> option (positive * var_data (type.base t)) with
                 | tZ as t
                   => fun r typedefs
                      => (n <- make_name count;
                         Some (Pos.succ count, (n, is_ptr, int.option.interp.of_zrange_relaxed (t:=t) (option_map relax_zrange r), typedefs)))
                 | base.type.prod A B
                   => fun '(ra, rb) '(typedefsa, typedefsb)
                      => (va <- @base_var_data_of_bounds_and_typedefs A is_ptr count make_name ra typedefsa;
                            let '(count, va) := va in
                            vb <- @base_var_data_of_bounds_and_typedefs B is_ptr count make_name rb typedefsb;
                              let '(count, vb) := vb in
                              Some (count, (va, vb)))
                 | base.type.list tZ as t
                   => fun r typedefs
                      => (ls <- r;
                         n <- make_name count;
                         Some (Pos.succ count,
                               (n,
                                int.option.interp.to_union
                                  (int.option.interp.of_zrange_relaxed
                                     (t:=t) (Some (List.map (option_map relax_zrange) ls))),
                                length ls,
                                typedefs)))
                 | base.type.unit
                   => fun _ _ => Some (count, tt)
                 | base.type.list _
                 | base.type.option _
                 | base.type.type_base _
                   => fun _ _ => None
                 end%option.

            Definition var_data_of_bounds_and_typedefs {t}
                       (is_ptr : bool)
                       (count : positive)
                       (make_name : positive -> option string)
              : ZRange.type.option.interp t -> var_typedef_data t -> option (positive * var_data t)
              := match t with
                 | type.base t => base_var_data_of_bounds_and_typedefs is_ptr count make_name
                 | type.arrow s d => fun _ _ => None
                 end.

            Fixpoint expr_of_PHOAS'_cps
                     {t}
                     (e : @API.expr var_data t)
                     (make_in_name : positive -> option string)
                     (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                     (intypedefs : type.for_each_lhs_of_arrow var_typedef_data t)
                     (count : positive)
                     {T}
                     {struct t}
              : (positive * (type.for_each_lhs_of_arrow var_data t * @API.expr var_data (type.final_codomain t)) -> ErrT T) -> ErrT T
              := let _ := @PHOAS.expr.partially_show_expr in (* for TC resolution *)
                 match t return @API.expr var_data t -> type.for_each_lhs_of_arrow ZRange.type.option.interp t -> type.for_each_lhs_of_arrow var_typedef_data t -> (positive * (type.for_each_lhs_of_arrow var_data t * @API.expr var_data (type.final_codomain t)) -> ErrT T) -> ErrT T with
                 | type.base t
                   => fun e 'tt 'tt k => k (count, (tt, e))
                 | type.arrow s d
                   => fun e '(inbound, inbounds) '(intypedef, intypedefs) k
                      => match var_data_of_bounds_and_typedefs false count make_in_name inbound intypedef, invert_Abs e with
                         | Some (count, vs), Some f
                           => @expr_of_PHOAS'_cps
                                d (f vs) make_in_name inbounds intypedefs count _
                                (fun '(count, (vss, rv))
                                 => k (count, ((vs, vss), rv)))
                         | None, _ => inr ["Unable to bind names for all arguments and bounds at type " ++ show s]%string%list
                         | _, None => inr ["Invalid non-λ expression of arrow type (" ++ show t ++ "): " ++ show e]%string%list
                         end
                 end%core%expr e inbounds intypedefs.

            Definition expr_of_PHOAS'_cont
                       {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
                       (do_bounds_check : bool)
                       {t}
                       (make_name : positive -> option string)
                       (out_data : var_data (type.base (type.final_codomain t)))
                       (in_to_body_count : positive -> positive)
              : positive * (type.for_each_lhs_of_arrow var_data t * @API.expr var_data (type.final_codomain t))
                -> ErrT (type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)) * expr)
              := let _ := @PHOAS.expr.partially_show_expr in (* for TC resolution *)
                 fun '(count, (d, e))
                 => (rv <- expr_of_base_PHOAS do_bounds_check e (in_to_body_count count) make_name out_data;
                    let rv := name_infos.adjust_dead consider_retargs_live rename_dead rv in
                    let rv := if lift_declarations then LiftDeclare.lift_declarations rv else rv in
                    ret (d, out_data, rv)).

            Definition expr_of_PHOAS'
                       {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
                       (do_bounds_check : bool)
                       {t}
                       (e : @API.expr var_data t)
                       (make_in_name : positive -> option string)
                       (make_name : positive -> option string)
                       (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                       (intypedefs : type.for_each_lhs_of_arrow var_typedef_data t)
                       (out_data : var_data (type.base (type.final_codomain t)))
                       (count : positive)
                       (in_to_body_count : positive -> positive)
              : ErrT (type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)) * expr)
              := @expr_of_PHOAS'_cps
                   _ e make_in_name inbounds intypedefs count _
                   (expr_of_PHOAS'_cont do_bounds_check (t:=t) make_name out_data in_to_body_count).

            Definition expr_of_PHOAS_cont
                       {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
                       (do_bounds_check : bool)
                       {t}
                       (make_name : positive -> option string)
                       (in_to_body_count : positive -> positive)
              : positive * (type.for_each_lhs_of_arrow var_data t * var_data (type.final_codomain t) * @API.expr var_data (type.final_codomain t))
                -> ErrT (type.for_each_lhs_of_arrow var_data t * var_data (type.final_codomain t) * expr)
              := fun '(count, (din, dout, e))
                 => expr_of_PHOAS'_cont do_bounds_check (t:=t) make_name dout in_to_body_count (count, (din, e)).

            Definition expr_of_PHOAS_cps
                       {t}
                       (e : @API.expr var_data t)
                       (make_in_name : positive -> option string)
                       (make_out_name : positive -> option string)
                       (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                       (outbounds : ZRange.type.option.interp (type.base (type.final_codomain t)))
                       (intypedefs : type.for_each_lhs_of_arrow var_typedef_data t)
                       (outtypedefs : var_typedef_data (type.base (type.final_codomain t)))
                       (count : positive)
                       (out_to_in_count : positive -> positive)
                       {T}
                       (k : positive * (type.for_each_lhs_of_arrow var_data t * var_data (type.final_codomain t) * @API.expr var_data (type.final_codomain t)) -> ErrT T)
              : ErrT T
              := match var_data_of_bounds_and_typedefs true count make_out_name outbounds outtypedefs with
                 | Some vd
                   => let '(count, dout) := vd in
                      let count := out_to_in_count count in
                      @expr_of_PHOAS'_cps
                        t e make_in_name inbounds intypedefs count _
                        (fun '(count, (din, e)) => k (count, (din, dout, e)))
                 | None => inr ["Unable to bind names for all return arguments and bounds at type " ++ show (type.final_codomain t)]%string
                 end.

            Definition expr_of_PHOAS
                       {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
                       (do_bounds_check : bool)
                       {t}
                       (e : @API.expr var_data t)
                       (make_in_name : positive -> option string)
                       (make_out_name : positive -> option string)
                       (make_name : positive -> option string)
                       (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                       (outbounds : ZRange.type.option.interp (type.base (type.final_codomain t)))
                       (intypedefs : type.for_each_lhs_of_arrow var_typedef_data t)
                       (outtypedefs : var_typedef_data (type.base (type.final_codomain t)))
                       (count : positive)
                       (in_to_body_count out_to_in_count : positive -> positive)
              : ErrT (type.for_each_lhs_of_arrow var_data t * var_data (type.final_codomain t) * expr)
              := @expr_of_PHOAS_cps
                   _ e make_in_name make_out_name inbounds outbounds intypedefs outtypedefs count out_to_in_count _
                   (expr_of_PHOAS_cont do_bounds_check (t:=t) make_name in_to_body_count).

            Let make_name_gen (name_list : option (list string))
              := fun prefix
                 => match name_list with
                    | None => fun p => Some (prefix ++ Decimal.Z.to_string (Zpos p))
                    | Some ls => fun p => List.nth_error ls (pred (Pos.to_nat p))
                    end.

            Let make_in_name name_list := make_name_gen name_list "arg".
            Let make_out_name name_list := make_name_gen name_list "out".
            Let make_name name_list := make_name_gen name_list "x".
            Let reset_if_names_given (name_list : option (list string))
              := match name_list with
                 | Some _ => fun p : positive => p
                 | None => fun _ : positive => 1%positive
                 end.

            Definition ExprOfPHOAS_cont
                       {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
                       (do_bounds_check : bool)
                       {t}
                       (name_list : option (list string))
              : positive * (type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)) * @API.expr var_data (type.final_codomain t))
                -> ErrT (type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)) * expr)
              := expr_of_PHOAS_cont
                   do_bounds_check (t:=t)
                   (make_name name_list) (reset_if_names_given name_list).

            Definition ExprOfPHOAS_with_opt_outbounds_cps
                       {absint_opts : AbstractInterpretation.Options}
                       {t}
                       (e : @API.Expr t)
                       (name_list : option (list string))
                       (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                       (outbounds : option (ZRange.type.base.option.interp (type.final_codomain t)))
                       (intypedefs : type.for_each_lhs_of_arrow var_typedef_data t)
                       (outtypedefs : base_var_typedef_data (type.final_codomain t))
                       {T}
                       (k : positive * (type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)) * @API.expr var_data (type.final_codomain t)) -> ErrT T)
              : ErrT T
              := let outbounds := Option.value outbounds (partial.Extract true (* assume the output has casts around it *) e inbounds) in
                 expr_of_PHOAS_cps
                   (e _) (make_in_name name_list) (make_out_name name_list) inbounds outbounds intypedefs outtypedefs 1 (reset_if_names_given name_list) k.

            Definition ExprOfPHOAS_cps
                       {absint_opts : AbstractInterpretation.Options}
                       {t}
                       (e : @API.Expr t)
                       (name_list : option (list string))
                       (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                       (intypedefs : type.for_each_lhs_of_arrow var_typedef_data t)
                       (outtypedefs : base_var_typedef_data (type.final_codomain t))
                       {T}
                       (k : positive * (type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)) * @API.expr var_data (type.final_codomain t)) -> ErrT T)
              : ErrT T
              := ExprOfPHOAS_with_opt_outbounds_cps e name_list inbounds None intypedefs outtypedefs k.

            Definition var_data_of_PHOAS
                       {absint_opts : AbstractInterpretation.Options}
                       {t}
                       (e : @API.Expr t)
                       (name_list : option (list string))
                       (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                       (intypedefs : type.for_each_lhs_of_arrow var_typedef_data t)
                       (outtypedefs : base_var_typedef_data (type.final_codomain t))
              : ErrT (type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)))
              := ExprOfPHOAS_with_opt_outbounds_cps
                   e name_list inbounds None intypedefs outtypedefs
                   (fun '(count, (din, dout, e)) => ret (din, dout)).

            Definition var_data_of_PHOAS_bounds
                       {absint_opts : AbstractInterpretation.Options}
                       {t}
                       (e : @API.Expr t)
                       (name_list : option (list string))
                       (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                       (outbounds : ZRange.type.base.option.interp (type.final_codomain t))
                       (intypedefs : type.for_each_lhs_of_arrow var_typedef_data t)
                       (outtypedefs : base_var_typedef_data (type.final_codomain t))
              : ErrT (type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)))
              := ExprOfPHOAS_with_opt_outbounds_cps
                   e name_list inbounds (Some outbounds) intypedefs outtypedefs
                   (fun '(count, (din, dout, e)) => ret (din, dout)).

            Definition ExprOfPHOAS
                       {absint_opts : AbstractInterpretation.Options}
                       {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
                       (do_bounds_check : bool)
                       {t}
                       (e : @API.Expr t)
                       (name_list : option (list string))
                       (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                       (intypedefs : type.for_each_lhs_of_arrow var_typedef_data t)
                       (outtypedefs : base_var_typedef_data (type.final_codomain t))
              : ErrT (type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)) * expr)
              := ExprOfPHOAS_cps
                   e name_list inbounds intypedefs outtypedefs
                   (ExprOfPHOAS_cont do_bounds_check name_list).
          End with_bind.
        End __.
      End OfPHOAS.
    End IR.
  End ToString.
End Compilers.
