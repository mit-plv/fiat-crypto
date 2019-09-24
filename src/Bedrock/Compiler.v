Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require bedrock2.Syntax.
Require bedrock2.Semantics.
Require bedrock2.BasicC64Semantics. (* for debugging *)
Require Import Crypto.Util.ZRange.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Import Language.Compilers.

Module Compiler.
  Section __.
    Context {p : Semantics.parameters}
            (next_varname : Syntax.varname -> Syntax.varname)
            (error : Syntax.expr.expr)
            (ident_to_funname : forall t, ident.ident t -> Syntax.funname).
    Local Notation cexpr := (@Language.Compilers.expr.expr base.type ident.ident).

    (* cexpr typing cheat sheet:
         Language.Compilers.type === type.type := base (of base.type) or arrow (recursive type.type)
         base.type === base.type.type := type_base (of base.type.base) or prod/list/option
         base.type.base := unit/Z/bool/nat/zrange *)

    (* interpretation of base.type *)
    Fixpoint base_var (t : base.type) : Type :=
      match t with
      | base.type.prod a b => base_var a * base_var b
      | base.type.list base.type.Z => Syntax.expr.expr (* N.B. for lists, represents the list's *location in memory* *)
      | _ => Syntax.varname
      end.
    (* interpretation of type.type base.type *)
    Fixpoint var (t : type.type base.type) : Type :=
      match t with
      | type.base t => base_var t
      | type.arrow s d => var s -> var d
      end.

    (* the type of *values* of variables in terms of Syntax.expr.expr *)
    Fixpoint base_value (t : base.type) : Type :=
      match t with
      | base.type.prod a b => base_value a * base_value b
      | _ => Syntax.expr.expr
      end.
    Fixpoint value (t : type.type base.type) : Type :=
      match t with
      | type.base a => base_value a
      | type.arrow a b => value a -> value b
      end.

    (* convert vars to values (used for renaming the variables) *)
    Fixpoint value_of_var {t} : base_var t -> base_value t :=
      match t with
      | base.type.prod a b => fun x => (value_of_var (fst x), value_of_var (snd x))
      | base.type.list base.type.Z => fun loc => loc
      | base.type.list _ | base.type.option _ | base.type.Z | base.type.nat
      | base.type.unit | base.type.bool | base.type.zrange => Syntax.expr.var
      end.

    (* error creation *)
    Fixpoint base_make_error t : base_value t :=
      match t with
      | base.type.prod a b => (base_make_error a, base_make_error b)
      | base.type.list _ | base.type.option _ | base.type.Z | base.type.nat
      | base.type.unit | base.type.bool | base.type.zrange => error
      end.
    Fixpoint make_error t : value t :=
      match t with
      | type.base a => base_make_error a
      | type.arrow a b => fun _ => make_error b
      end.

    (* given the next variable name to use and the type of a let
       binder, generate a correctly-typed structure of variable names to
       assign *)
    Fixpoint get_retnames (t : base.type) (startname : Syntax.varname)
      : Syntax.varname * base_var t :=
      match t with
      (* prod is a special case -- assign to multiple variables *)
      | base.type.prod a b =>
        let step1 := get_retnames a startname in
        let step2 := get_retnames b (fst step1) in
        (fst step2, (snd step1, snd step2))
      (* this should not get called on lists of Zs -- return garbage *)
      | base.type.list base.type.Z => (startname, Syntax.expr.literal 0)
      (* everything else is single-variable assignment *)
      | base.type.list _ | base.type.option _ | base.type.Z | base.type.nat
      | base.type.unit | base.type.bool | base.type.zrange =>
                                          (next_varname startname, startname)
      end.

    Fixpoint set_return_values {t : base.type}
      : base_var t -> base_value t -> Syntax.cmd.cmd :=
      match t with
      | base.type.prod a b =>
        fun retnames values =>
          Syntax.cmd.seq (set_return_values (fst retnames) (fst values))
                         (set_return_values (snd retnames) (snd values))
      (* this should not be called on lists of Zs -- return garbage *)
      | base.type.list base.type.Z => fun _ _ => Syntax.cmd.skip
      | base.type.list _ | base.type.option _ | base.type.Z | base.type.nat
      | base.type.unit | base.type.bool | base.type.zrange => Syntax.cmd.set
      end.

    Definition max_range : zrange := {| lower := 0; upper := 2 ^ Semantics.width |}.
    Definition range_good (r : zrange) : bool := is_tighter_than_bool r max_range.

    Local Notation type_nat := (type.base (base.type.type_base base.type.nat)).
    Local Notation type_Z := (type.base (base.type.type_base base.type.Z)).
    Local Notation type_ZZ :=
      (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))).

    (* checks that the expression is either a) a literal nat or Z that
    falls within the allowed range or b) an expression surrounded by
    casts that fall within the allowed range *)
    Definition has_casts {t} (e : @cexpr var t) : bool :=
      match e with
      | (expr.App
           type_Z type_Z
           (expr.Ident _ (ident.Z_cast r)) _) => range_good r
      | (expr.App
           type_ZZ type_ZZ
           (expr.Ident _ (ident.Z_cast2 (r1, r2))) _) =>
        (range_good r1 && range_good r2)%bool
      | (expr.Ident _ (ident.Literal base.type.Z z)) =>
        is_bounded_by_bool z max_range
      | (expr.Ident _ (ident.Literal base.type.nat n)) =>
        is_bounded_by_bool (Z.of_nat n) max_range
      | (expr.App _ (type.base (base.type.list _)) _ _) =>
        (* lists get a pass *)
        true
      | _ => false
      end.

    (* TODO: of_inner_expr needs to handle:
       - all binary operations (mul_split, add_get_carry, add_with_get_carry, add, lor, shiftl, truncating_shiftl)
       - nth_default of lists
       - fst/snd
       - list formation (cons, nil)
     *)
    (* TODO : better comments in this function *)
    (* Used to interpret expressions that are not allowed to contain let statements *)
    Fixpoint of_inner_expr
             (require_cast : bool)
             {t} (e : @cexpr var t) : value t :=
      if (require_cast && negb (has_casts e))%bool
      then make_error _
      else
        match e with
        | (expr.App
             type_Z type_Z
             (expr.Ident _ (ident.Z_cast r)) x) =>
          (* strip casts -- we already checked for them in has_casts *)
          of_inner_expr false x
        | (expr.App
             type_ZZ type_ZZ
             (expr.Ident _ (ident.Z_cast2 (r1, r2))) x) =>
          (* strip casts -- we already checked for them in has_casts *)
          of_inner_expr false x
        | (expr.App
             type_Z type_ZZ
             (expr.App type_Z (type.arrow type_Z type_ZZ)
                       (expr.App type_Z (type.arrow type_Z (type.arrow type_Z type_ZZ))
                                 (expr.Ident _ ident.Z_add_get_carry)
                                 (expr.Ident _ (ident.Literal base.type.Z 18446744073709551616)))
                       x) y) =>
          let sum := Syntax.expr.op Syntax.bopname.add (of_inner_expr true x) (of_inner_expr true y) in
          let carry := Syntax.expr.op Syntax.bopname.ltu sum (of_inner_expr true x) in
          (sum, carry)
        | (expr.App
             type_Z type_Z
             (expr.App type_Z (type.arrow type_Z type_Z)
                       (expr.Ident _ ident.Z_add) x) y) =>
          Syntax.expr.op Syntax.bopname.add (of_inner_expr true x) (of_inner_expr true y)
        | (expr.App
             type_Z type_Z
             (expr.App type_Z (type.arrow type_Z type_Z)
                       (expr.Ident _ ident.Z_land) x) y) =>
          Syntax.expr.op Syntax.bopname.and (of_inner_expr true x) (of_inner_expr true y)
        | (expr.App
             type_Z type_Z
             (expr.App type_Z (type.arrow type_Z type_Z)
                       (expr.Ident _ ident.Z_shiftr) x) y) =>
          Syntax.expr.op Syntax.bopname.sru (of_inner_expr true x) (of_inner_expr true y)
        | (expr.App
             type_Z type_Z
             (expr.App type_Z (type.arrow type_Z type_Z)
                       (expr.Ident _ ident.Z_shiftl) x) y) =>
          Syntax.expr.op Syntax.bopname.slu (of_inner_expr true x) (of_inner_expr true y)
        | (expr.App
             (type.base (base.type.prod (base.type.type_base base.type.Z) _)) type_Z
             (expr.Ident _ (ident.fst base.type.Z _))
             x) =>
          fst (of_inner_expr false x)
        | (expr.App
             (type.base (base.type.prod _ (base.type.type_base base.type.Z))) type_Z
             (expr.Ident _ (ident.snd _ base.type.Z))
             x) =>
          snd (of_inner_expr false x)
        | (expr.App
             type_nat type_Z
             (expr.App
                (type.base (base.type.list _)) _
                (expr.App _ _
                          (expr.Ident _ (ident.List_nth_default _))
                          d) l) i) =>
          let addr := Syntax.expr.op Syntax.bopname.add
                                     (of_inner_expr false l)
                                     (of_inner_expr true i) in
          Syntax.expr.load Syntax.access_size.word addr
        | expr.Ident type_Z (ident.Literal base.type.Z x) =>
          Syntax.expr.literal x
        | expr.Ident type_nat (ident.Literal base.type.nat x) =>
          Syntax.expr.literal (Z.of_nat x)
        | expr.Var (type.base _) x => value_of_var x
        | _ => make_error _
        end.

    Fixpoint of_expr {t} (e : @cexpr var t)
             (nextname : Syntax.varname)
      : var t -> Syntax.varname * Syntax.cmd.cmd :=
      match e with
      | expr.LetIn (type.base t1) (type.base t2) x f =>
        fun retnames : var (type.base t2) =>
          let gr := get_retnames t1 nextname in
          let cmdx := set_return_values (snd gr) (of_inner_expr true x) in
          let recf := of_expr (f (snd gr)) (fst gr) retnames in
          (fst recf, Syntax.cmd.seq cmdx (snd recf))
      | expr.App
          (type.base (base.type.list base.type.Z)) (type.base (base.type.list base.type.Z))
          (expr.App type_Z _ (expr.Ident _ (ident.cons _)) x) l =>
        fun retloc : Syntax.expr.expr =>
          (* retloc is the address at which to store the head of the list *)
          let cmdx := (Syntax.cmd.store Syntax.access_size.word retloc (of_inner_expr true x)) in
          let recl :=
              of_expr l nextname (Syntax.expr.op Syntax.bopname.add retloc (Syntax.expr.literal 1)) in
          (fst recl, Syntax.cmd.seq cmdx (snd recl))
      | (expr.Ident _ (ident.nil base.type.Z)) =>
        fun _ => (nextname, Syntax.cmd.skip)
      | expr.App _ (type.base _) f x =>
        fun retnames =>
          let v := of_inner_expr true (expr.App f x) in
          (nextname, set_return_values retnames v)
      | expr.Ident (type.base _) x =>
        fun retnames =>
          let v := of_inner_expr true (expr.Ident x) in
          (nextname, set_return_values retnames v)
      | expr.Var (type.base _) x =>
        fun retnames =>
          let v := of_inner_expr true (expr.Var x) in
          (nextname, set_return_values retnames v)
      | _ => fun _ => (nextname, Syntax.cmd.skip)
      end.
  End __.

  Section debug.
    Import Coq.Strings.String. Local Open Scope string_scope.
    Let ERROR : Syntax.expr.expr := (Syntax.expr.var "ERROR").
    Let nv : String.string -> String.string :=
      fun old_varname =>
        let old_num := List.nth_default ""%string (String.split "x" old_varname) 1 in
        let new_num := Decimal.decimal_string_of_Z (Decimal.Z_of_decimal_string old_num + 1) in
        String.append "x" new_num.
    Local Notation of_expr e := (@of_expr BasicC64Semantics.parameters nv ERROR _ e "x0").
    Local Notation of_inner_expr := (@of_inner_expr BasicC64Semantics.parameters ERROR _).

    (* Test expression for debugging:

       let r0 := cast2 (uint64, uint64) (Z.add_get_carry (2^64) x y) in
       fst r0
     *)
    Definition test_expr x y
      : @Language.Compilers.expr.expr base.type ident.ident var
                                      (type.base (base.type.type_base base.type.Z)) :=
      expr.LetIn
        (A:=type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))
        (expr.App (expr.Ident (ident.Z_cast2 (r[0 ~> 18446744073709551615]%zrange,
                                              r[0 ~> 18446744073709551615]%zrange)))
                  (expr.App
                     (expr.App
                        (expr.App
                           (expr.Ident ident.Z_add_get_carry)
                           (expr.Ident (ident.Literal (t:=base.type.Z) 18446744073709551616)))
                           x) y))
        (fun res =>
           expr.App
             (expr.Ident (ident.Z_cast r[0 ~> 18446744073709551615]%zrange))
             (expr.App
                (expr.Ident ident.fst)
                (expr.Var res))).

    (* Test expression for debugging:

       let r0 := cast2 (uint64, uint64) (Z.add_get_carry (2^64) $x $y) in
       let r1 := cast2 (uint64, uint64) (Z.add_get_carry (2^64) (fst r0) $y) in
       fst r1
     *)
    Definition test_expr2 (x y : Syntax.varname)
      : @Language.Compilers.expr.expr base.type ident.ident var
                                      (type.base (base.type.type_base base.type.Z)) :=
      expr.LetIn
        (A:=type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))
        (expr.App (expr.Ident (ident.Z_cast2 (r[0 ~> 18446744073709551615]%zrange,
                                              r[0 ~> 18446744073709551615]%zrange)))
                  (expr.App
                     (expr.App
                        (expr.App
                           (expr.Ident ident.Z_add_get_carry)
                           (expr.Ident (ident.Literal (t:=base.type.Z) 18446744073709551616)))
                        (expr.App
                           (expr.Ident (ident.Z_cast r[0 ~> 18446744073709551615]%zrange))
                           (expr.Var x)))
                        (expr.App
                           (expr.Ident (ident.Z_cast r[0 ~> 18446744073709551615]%zrange))
                           (expr.Var y))))
        (fun res =>
           expr.LetIn
             (A:=type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))
             (expr.App (expr.Ident (ident.Z_cast2 (r[0 ~> 18446744073709551615]%zrange,
                                                   r[0 ~> 18446744073709551615]%zrange)))
                       (expr.App
                          (expr.App
                             (expr.App
                                (expr.Ident ident.Z_add_get_carry)
                                (expr.Ident (ident.Literal (t:=base.type.Z) 18446744073709551616)))
                             (expr.App
                                (expr.Ident (ident.Z_cast r[0 ~> 18446744073709551615]%zrange))
                                (expr.App
                                   (expr.Ident ident.fst)
                                   (expr.Var res))))
                             (expr.App
                                (expr.Ident (ident.Z_cast r[0 ~> 18446744073709551615]%zrange))
                                (expr.Var y))))
             (fun res2 =>
                (expr.App
                   (expr.Ident (ident.Z_cast r[0 ~> 18446744073709551615]%zrange))
                   (expr.App
                      (expr.Ident ident.fst)
                      (expr.Var res2))))).

    (* Test expression for debugging:

       let r0 := cast2 (uint64, uint64) (Z.add_get_carry (2^64) $x $y) in
       fst r0
     *)
    Definition test_expr3 (x y : Syntax.varname)
      : @Language.Compilers.expr.expr base.type ident.ident var
                                      (type.base (base.type.type_base base.type.Z)) :=
      expr.LetIn
        (A:=type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))
        (expr.App (expr.Ident (ident.Z_cast2 (r[0 ~> 18446744073709551615]%zrange,
                                              r[0 ~> 18446744073709551615]%zrange)))
                  (expr.App
                     (expr.App
                        (expr.App
                           (expr.Ident ident.Z_add_get_carry)
                           (expr.Ident (ident.Literal (t:=base.type.Z) 18446744073709551616)))
                        (expr.App
                           (expr.Ident (ident.Z_cast r[0 ~> 18446744073709551615]%zrange))
                           (expr.Var x)))
                     (expr.App
                        (expr.Ident (ident.Z_cast r[0 ~> 18446744073709551615]%zrange))
                        (expr.Var y))))
        (fun res =>
           (expr.App
              (expr.Ident (ident.Z_cast r[0 ~> 18446744073709551615]%zrange))
              (expr.App
                 (expr.Ident ident.fst)
                 (expr.Var res)))).

    (* Test expression for debugging:

       let r0 := cast2 (uint64, uint64) (Z.add_get_carry (2^64) ((uint64) x[1]) #6) in
       fst r0
     *)
    Definition test_expr4 (x : Syntax.expr.expr)
      : @Language.Compilers.expr.expr base.type ident.ident var
                                      (type.base (base.type.type_base base.type.Z)) :=
      expr.LetIn
        (A:=type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))
        (expr.App (expr.Ident (ident.Z_cast2 (r[0 ~> 18446744073709551615]%zrange,
                                              r[0 ~> 18446744073709551615]%zrange)))
                  (expr.App
                     (expr.App
                        (expr.App
                           (expr.Ident ident.Z_add_get_carry)
                           (expr.Ident (ident.Literal (t:=base.type.Z) 18446744073709551616)))
                        (expr.App
                           (expr.Ident (ident.Z_cast r[0 ~> 18446744073709551615]%zrange))
                           (expr.App
                              (expr.App
                                 (expr.App
                                    (expr.Ident (ident.List_nth_default))
                                    (expr.Ident (ident.Literal (t:=base.type.Z) 0)))
                                 (expr.Var x))
                              (expr.Ident (ident.Literal (t:=base.type.nat) 1%nat)))
                           ))
                     (expr.App
                        (expr.Ident (ident.Z_cast r[0 ~> 18446744073709551615]%zrange))
                        (expr.Ident (ident.Literal (t:=base.type.Z) 6)))))
        (fun res =>
           (expr.App
              (expr.Ident (ident.Z_cast r[0 ~> 18446744073709551615]%zrange))
              (expr.App
                 (expr.Ident ident.fst)
                 (expr.Var res)))).

    (* Test expression for debugging:

       let r0 := (uint64) ((uint64) ((uint64) $x + (uint64) $y) >> 20) in
       [1; 2; (uint64) $r0]
     *)
    Definition test_expr5 (x y : Syntax.varname)
      : @Language.Compilers.expr.expr base.type ident.ident var
                                      (type.base (base.type.list base.type.Z)) :=
      expr.LetIn
        (expr.App (expr.Ident (ident.Z_cast (r[0 ~> 18446744073709551615]%zrange)))
                  (expr.App
                     (expr.App
                        (expr.Ident ident.Z_shiftr)
                        (expr.App
                           (expr.Ident (ident.Z_cast r[0 ~> 18446744073709551615]%zrange))
                           (expr.App
                              (expr.App
                                 (expr.Ident ident.Z_add)
                                 (expr.App
                                    (expr.Ident (ident.Z_cast r[0 ~> 18446744073709551615]%zrange))
                                    (expr.Var x)))
                              (expr.App
                                 (expr.Ident (ident.Z_cast r[0 ~> 18446744073709551615]%zrange))
                                 (expr.Var y)))))
                     (expr.Ident (ident.Literal (t:=base.type.Z) 20))))
        (fun res =>
           expr.App
             (expr.App
                (expr.Ident ident.cons)
                (expr.Ident (ident.Literal (t:=base.type.Z) 1)))
             (expr.App
                (expr.App
                   (expr.Ident ident.cons)
                   (expr.Ident (ident.Literal (t:=base.type.Z) 2)))
                (expr.App
                   (expr.App
                      (expr.Ident ident.cons)
                      (expr.App
                         (expr.Ident (ident.Z_cast r[0 ~> 18446744073709551615]%zrange))
                         (expr.Var res)))
                   (expr.Ident ident.nil)))).

    (*
    Local Notation "'uint64'" := (ident.Z_cast r[0 ~> 18446744073709551615]%zrange) : expr_scope.
    Local Notation "'uint64,uint64'" := (ident.Z_cast2
                                           (r[0 ~> 18446744073709551615]%zrange,
                                            r[0 ~> 18446744073709551615]%zrange)%core) : expr_scope.
    Local Notation "x ; y" := (Syntax.cmd.seq x y)
                                (at level 199, y at next level, format "x ; '//'  y") : syntax_scope.
    Local Notation "% x" := (Syntax.expr.var x) (at level 0, only printing, format "% x") : syntax_scope.
    Local Notation "x <- y" := (Syntax.cmd.set x y) (at level 199, y at next level) : syntax_scope.
    Local Notation "x <-- y" := (Syntax.cmd.store Syntax.access_size.word x y)
                                 (at level 199) : syntax_scope.
    Local Notation "x" := (Syntax.expr.literal x) (at level 199, only printing) : syntax_scope.
    Import Syntax. Import Syntax.bopname.
    Local Open Scope syntax_scope.
    Eval simpl in (fun x y => of_expr (test_expr x y) "ret").
    Eval lazy in (fun x y => of_expr (test_expr2 x y) "ret").
    Eval lazy in (fun x y => of_expr (test_expr3 x y) "ret").
    Eval lazy in (fun x => of_expr (test_expr4 x) "ret").
    Eval lazy in (fun x y => of_expr (test_expr5 x y) (Syntax.expr.var "ret")).
    *)
  End debug.
End Compiler.
