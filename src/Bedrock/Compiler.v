Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require bedrock2.Syntax.
Require bedrock2.Semantics.
Require bedrock2.WeakestPrecondition.
Require Import bedrock2.Map.Separation bedrock2.Array bedrock2.Scalars.
Require Import Crypto.Util.ZRange.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Language.API.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Import API.Compilers.

Module Compiler.
  Section Compiler.
    Context {p : Semantics.parameters}
            (next_varname : Syntax.varname -> Syntax.varname)
            (error : Syntax.expr.expr)
            (word_size_in_bytes : Z)
            (ident_to_funname : forall t, ident.ident t -> Syntax.funname).
    Local Notation maxint := (2 ^ Semantics.width).

    (* Notations for commonly-used types *)
    Local Notation type_range := (type.base (base.type.type_base base.type.zrange)).
    Local Notation type_nat := (type.base (base.type.type_base base.type.nat)).
    Local Notation type_Z := (type.base (base.type.type_base base.type.Z)).
    Local Notation type_range2 :=
      (type.base (base.type.prod (base.type.type_base base.type.zrange)
                                 (base.type.type_base base.type.zrange))).
    Local Notation type_ZZ :=
      (type.base (base.type.prod (base.type.type_base base.type.Z)
                                 (base.type.type_base base.type.Z))).

    (* Types that appear in the bedrock2 expressions on the left-hand-side of
       assignments (or in return values). For example, if we want to assign three
       integers, we need three [Syntax.varname]s.

       Lists use [Syntax.expr.expr] instead of [Syntax.varname] because lists
       are stored in main memory; we use [Syntax.cmd.store] instead of
       [Syntax.cmd.set], which allows expressions for the storage location.

       Functions can't appear on the left-hand-side, so we return garbage output
       (the unit type). *)
    Fixpoint base_ltype (t : base.type) : Type :=
      match t with
      | base.type.prod a b => base_ltype a * base_ltype b
      | base.type.list (base.type.type_base base.type.Z) =>
        Syntax.expr.expr (* N.B. for lists, represents the list's *location in memory* *)
      | _ => Syntax.varname
      end.
    Fixpoint ltype (t : type.type base.type) : Type :=
      match t with
      | type.base t => base_ltype t
      | type.arrow s d => unit (* garbage *)
      end.

    (* Types that appear in the bedrock2 expressions on the right-hand-side of
       assignments. For example, if we want to assign three integers, we need
       three [Syntax.expr.expr]s. *)
    Fixpoint base_rtype (t : base.type) : Type :=
      match t with
      | base.type.prod a b => base_rtype a * base_rtype b
      | _ => Syntax.expr.expr
      end.
    Fixpoint rtype (t : type.type base.type) : Type :=
      match t with
      | type.base a => base_rtype a
      | type.arrow a b => rtype a -> rtype b
      end.

    (* convert ltypes to rtypes (used for renaming variables) - the opposite
       direction is not permitted *)
    Fixpoint rtype_of_ltype {t} : base_ltype t -> base_rtype t :=
      match t with
      | base.type.prod a b => fun x => (rtype_of_ltype (fst x), rtype_of_ltype (snd x))
      | base.type.list (base.type.type_base base.type.Z) => fun loc => loc
      | base.type.list _ | base.type.option _ | base.type.unit
      | base.type.type_base _ => Syntax.expr.var
      end.

    (* error creation *)
    Fixpoint base_make_error t : base_rtype t :=
      match t with
      | base.type.prod a b => (base_make_error a, base_make_error b)
      | base.type.list _ | base.type.option _ | base.type.unit
      | base.type.type_base _ => error
      end.
    Fixpoint make_error t : rtype t :=
      match t with
      | type.base a => base_make_error a
      | type.arrow a b => fun _ => make_error b
      end.

    (* Used to generate left-hand-side of assignments, given the next variable
       name to use. Returns the new next name to use, and the left-hand-side. *)
    Fixpoint translate_lhs (t : base.type) (startname : Syntax.varname)
      : Syntax.varname * base_ltype t :=
      match t with
      (* prod is a special case -- assign to multiple variables *)
      | base.type.prod a b =>
        let step1 := translate_lhs a startname in
        let step2 := translate_lhs b (fst step1) in
        (fst step2, (snd step1, snd step2))
      (* this should not get called on lists of Zs -- return garbage *)
      | base.type.list (base.type.type_base base.type.Z) =>
        (startname, Syntax.expr.literal 0)
      (* everything else is single-variable assignment *)
      | base.type.list _ | base.type.option _ | base.type.unit
      | base.type.type_base _ => (next_varname startname, startname)
      end.

    Fixpoint assign {t : base.type}
      : base_ltype t -> base_rtype t -> Syntax.cmd.cmd :=
      match t with
      | base.type.prod a b =>
        fun (lhs : base_ltype (a * b)) (rhs : base_rtype (a * b)) =>
          Syntax.cmd.seq (assign (fst lhs) (fst rhs))
                         (assign (snd lhs) (snd rhs))
      (* this should not be called on lists of Zs -- return garbage *)
      | base.type.list (base.type.type_base base.type.Z) =>
        fun _ _ => Syntax.cmd.skip
      | base.type.list _ | base.type.option _ | base.type.unit
      | base.type.type_base _ => Syntax.cmd.set
      end.

    Definition max_range : zrange := {| lower := 0; upper := 2 ^ Semantics.width |}.
    Definition range_good (r : zrange) : bool := is_tighter_than_bool r max_range.

    (* checks that the expression is either a) a literal nat or Z that
    falls within the allowed range or b) an expression surrounded by
    casts that fall within the allowed range *)
    Definition has_casts {t} (e : @API.expr ltype t) : bool :=
      match e with
      | (expr.App
           type_Z type_Z
           (expr.App
              type_range (type.arrow type_Z type_Z)
              (expr.Ident _ ident.Z_cast)
              (expr.Ident _ (ident.Literal base.type.zrange r))) _) =>
        range_good r
      | (expr.App
           type_ZZ type_ZZ
           (expr.App
              type_range2 (type.arrow type_ZZ type_ZZ)
              (expr.Ident _ ident.Z_cast2)
              (expr.App
                 type_range type_range2
                 (expr.App
                    type_range (type.arrow type_range type_range2)
                    (expr.Ident _ (ident.pair _ _))
                    (expr.Ident _ (ident.Literal base.type.zrange r1)))
                 (expr.Ident _ (ident.Literal base.type.zrange r2)))) _) =>
        range_good r1 && range_good r2
      | (expr.Ident _ (ident.Literal base.type.Z z)) =>
        is_bounded_by_bool z max_range
      | (expr.Ident _ (ident.Literal base.type.nat n)) =>
        is_bounded_by_bool (Z.of_nat n) max_range
      | (expr.App _ (type.base (base.type.list _)) _ _) =>
        (* lists get a pass *)
        true
      | _ => false
      end.

    (* Used to interpret expressions that are not allowed to contain let statements *)
    Fixpoint translate_inner_expr
             (require_cast : bool)
             {t} (e : @API.expr ltype t) : rtype t :=
      if (require_cast && negb (has_casts e))%bool
      then make_error _
      else
        match e with
        (* Z_cast : clear casts because has_casts already checked for them *)
        | (expr.App
             type_Z type_Z
             (expr.App
                type_range (type.arrow type_Z type_Z)
                (expr.Ident _ ident.Z_cast) _) x) => translate_inner_expr false x
        (* Z_cast2 : clear casts because has_casts already checked for them *)
      | (expr.App
           type_ZZ type_ZZ
           (expr.App
              type_range2 (type.arrow type_ZZ type_ZZ)
              (expr.Ident _ ident.Z_cast2) _) x) => translate_inner_expr false x
        (* Z_mul_split : compute high and low separately and assign to two
           different variables *)
        (* TODO : don't duplicate argument expressions *)
        | (expr.App
             type_Z type_ZZ
             (expr.App type_Z (type.arrow type_Z type_ZZ)
                       (expr.App type_Z (type.arrow type_Z (type.arrow type_Z type_ZZ))
                                 (expr.Ident _ ident.Z_mul_split)
                                 (expr.Ident _ (ident.Literal base.type.Z s)))
                       x) y) =>
          if Z.eqb s maxint
          then
            let low := Syntax.expr.op
                         Syntax.bopname.mul
                         (translate_inner_expr true x) (translate_inner_expr true y) in
            let high := Syntax.expr.op
                          Syntax.bopname.mulhuu
                          (translate_inner_expr true x) (translate_inner_expr true y) in
            (low, high)
          else make_error _
        (* Z_add -> bopname.add *)
        | (expr.App
             type_Z type_Z
             (expr.App type_Z (type.arrow type_Z type_Z)
                       (expr.Ident _ ident.Z_add) x) y) =>
          Syntax.expr.op Syntax.bopname.add (translate_inner_expr true x) (translate_inner_expr true y)
        (* Z_mul -> bopname.mul *)
        | (expr.App
             type_Z type_Z
             (expr.App type_Z (type.arrow type_Z type_Z)
                       (expr.Ident _ ident.Z_mul) x) y) =>
          Syntax.expr.op Syntax.bopname.mul (translate_inner_expr true x) (translate_inner_expr true y)
        (* Z_land -> bopname.and *)
        | (expr.App
             type_Z type_Z
             (expr.App type_Z (type.arrow type_Z type_Z)
                       (expr.Ident _ ident.Z_land) x) y) =>
          Syntax.expr.op Syntax.bopname.and (translate_inner_expr true x) (translate_inner_expr true y)
        (* Z_lor -> bopname.or *)
        | (expr.App
             type_Z type_Z
             (expr.App type_Z (type.arrow type_Z type_Z)
                       (expr.Ident _ ident.Z_lor) x) y) =>
          Syntax.expr.op Syntax.bopname.or (translate_inner_expr true x) (translate_inner_expr true y)
        (* Z_shiftr -> bopname.sru *)
        | (expr.App
             type_Z type_Z
             (expr.App type_Z (type.arrow type_Z type_Z)
                       (expr.Ident _ ident.Z_shiftr) x) y) =>
          Syntax.expr.op Syntax.bopname.sru (translate_inner_expr true x) (translate_inner_expr true y)
        (* Z_truncating_shiftl : convert to bopname.slu if the truncation matches *)
        | (expr.App
             type_Z type_Z
             (expr.App type_Z (type.arrow type_Z type_Z)
                       (expr.App type_Z (type.arrow type_Z (type.arrow type_Z type_Z))
                                 (expr.Ident _ ident.Z_truncating_shiftl)
                                 (expr.Ident _ (ident.Literal base.type.Z s)))
                       x) y) =>
          if Z.eqb s Semantics.width
          then Syntax.expr.op Syntax.bopname.slu (translate_inner_expr true x) (translate_inner_expr true y)
          else make_error _
        (* fst : since the [rtype] of a product type is a tuple, simply use Coq's [fst] *)
        | (expr.App
             (type.base (base.type.prod (base.type.type_base base.type.Z) _)) type_Z
             (expr.Ident _ (ident.fst (base.type.type_base base.type.Z) _))
             x) =>
          fst (translate_inner_expr false x)
        (* snd : since the [rtype] of a product type is a tuple, simply Coq's [snd] *)
        | (expr.App
             (type.base (base.type.prod _ (base.type.type_base base.type.Z))) type_Z
             (expr.Ident _ (ident.snd _ (base.type.type_base base.type.Z)))
             x) =>
          snd (translate_inner_expr false x)
        (* List_nth_default : lists are represented by the location of the head
           of the list in memory; therefore, to get the nth element of the list,
           we add the index and load from the resulting address *)
        | (expr.App
             type_nat type_Z
             (expr.App
                (type.base (base.type.list _)) _
                (expr.App _ _
                          (expr.Ident _ (ident.List_nth_default _))
                          d) l) i) =>
          let offset := Syntax.expr.op Syntax.bopname.mul
                                       (translate_inner_expr true i)
                                       (Syntax.expr.literal word_size_in_bytes) in
          let addr := Syntax.expr.op Syntax.bopname.add
                                     (translate_inner_expr false l)
                                     offset in
          Syntax.expr.load Syntax.access_size.word addr
        (* Literal (Z) -> Syntax.expr.literal *)
        | expr.Ident type_Z (ident.Literal base.type.Z x) =>
          Syntax.expr.literal x
        (* Literal (nat) : convert to Z, then use Syntax.expr.literal *)
        | expr.Ident type_nat (ident.Literal base.type.nat x) =>
          Syntax.expr.literal (Z.of_nat x)
        (* Var : use rtype_of_ltype to convert the expression *)
        | expr.Var (type.base _) x => rtype_of_ltype x
        (* if no clauses matched the expression, return an error *)
        | _ => make_error _
        end.

    Definition translate_add_get_carry (sum carry : Syntax.varname)
               r1 r2 s (x y : API.expr type_Z) : Syntax.cmd.cmd :=
      if (range_good r1 && range_good r2)%bool
      then if Z.eqb s maxint
           then
             let sum_expr := Syntax.expr.op Syntax.bopname.add
                                            (translate_inner_expr true x) (translate_inner_expr true y) in
             (* Given (0 <= x < w) and (0 <= y < w), carry bit = (x + y) mod w
                <? x: if (x + y) mod w < x, then clearly the sum must have
                overflowed (since 0 <= y) if the sum overflowed, then (x + y)
                mod w = x + y - w < x *)
             let carry_expr := Syntax.expr.op Syntax.bopname.ltu
                                              (Syntax.expr.var sum) (translate_inner_expr true x) in
             Syntax.cmd.seq (Syntax.cmd.set sum sum_expr) (Syntax.cmd.set carry carry_expr)
           else Syntax.cmd.skip
      else Syntax.cmd.skip.

    Definition translate_add_with_get_carry (sum carry : Syntax.varname)
               r1 r2 s (c x y : API.expr type_Z) : Syntax.cmd.cmd :=
      if (range_good r1 && range_good r2)%bool
      then if Z.eqb s maxint
           then
             let sum_cx := Syntax.expr.op Syntax.bopname.add
                                          (translate_inner_expr true c) (translate_inner_expr true x) in
             let sum_cxy := Syntax.expr.op Syntax.bopname.add
                                           (Syntax.expr.var sum) (translate_inner_expr true y) in
             (* compute the carry by adding together the carries of both
                additions, using the same strategy as in Z_add_get_carry *)
             let carry_cx := Syntax.expr.op Syntax.bopname.ltu
                                            (Syntax.expr.var sum) (translate_inner_expr true x) in
             let carry_cxy := Syntax.expr.op Syntax.bopname.ltu
                                             (Syntax.expr.var sum) (translate_inner_expr true y) in
             let carry_expr := Syntax.expr.op Syntax.bopname.add (Syntax.expr.var carry) carry_cxy in
             (* sum := c + x
                carry := (sum <? x)
                sum +=y
                carry += (sum <? y) *)
             (Syntax.cmd.seq
                (Syntax.cmd.seq
                   (Syntax.cmd.seq
                      (Syntax.cmd.set sum sum_cx)
                      (Syntax.cmd.set carry carry_cx))
                   (Syntax.cmd.set sum sum_cxy))
                (Syntax.cmd.set carry carry_expr))
           else Syntax.cmd.skip
      else Syntax.cmd.skip.

    Local Notation AddGetCarry r1 r2 s x y :=
      (expr.App
         (s:=type_ZZ) (d:=type_ZZ)
         (* cast *)
         (expr.App
            (s:=type_range2) (d:=type.arrow type_ZZ type_ZZ)
            (expr.Ident ident.Z_cast2)
            (expr.App
               (s:=type_range) (d:=type_range2)
               (expr.App
                  (s:=type_range) (d:=type.arrow type_range type_range2)
                  (expr.Ident ident.pair)
                  (expr.Ident (ident.Literal (t:=base.type.zrange) r1)))
               (expr.Ident (ident.Literal (t:=base.type.zrange) r2))))
         (* add-get-carry expression *)
         (expr.App (s:=type_Z)
                   (expr.App (s:=type_Z)
                             (expr.App
                                (expr.Ident ident.Z_add_get_carry)
                                (expr.Ident (ident.Literal (t:=base.type.Z) s)))
                             x) y)).
    Local Notation AddWithGetCarry r1 r2 s c x y :=
      (expr.App
         (s:=type_ZZ) (d:=type_ZZ)
         (* cast *)
         (expr.App
            (s:=type_range2) (d:=type.arrow type_ZZ type_ZZ)
            (expr.Ident ident.Z_cast2)
            (expr.App
               (s:=type_range) (d:=type_range2)
               (expr.App
                  (s:=type_range) (d:=type.arrow type_range type_range2)
                  (expr.Ident ident.pair)
                  (expr.Ident (ident.Literal (t:=base.type.zrange) r1)))
               (expr.Ident (ident.Literal (t:=base.type.zrange) r2))))
         (* add-with-get-carry expression *)
         (expr.App (s:=type_Z)
                   (expr.App (s:=type_Z)
                             (expr.App (s:=type_Z)
                                       (expr.App
                                          (expr.Ident ident.Z_add_with_get_carry)
                                          (expr.Ident (ident.Literal (t:=base.type.Z) s)))
                                       c) x) y)).

    Definition translate_carries {t} (e : @API.expr ltype t)
      : ltype t -> option Syntax.cmd.cmd :=
      match e with
      | AddGetCarry r1 r2 s x y =>
        fun ret => Some (translate_add_get_carry (fst ret) (snd ret) r1 r2 s x y)
      | AddWithGetCarry r1 r2 s c x y =>
        fun ret =>
          Some (translate_add_with_get_carry (fst ret) (snd ret) r1 r2 s c x y)
      | _ => fun _ => None
      end.

    Fixpoint translate_expr {t} (e : @API.expr ltype t)
             (nextname : Syntax.varname)
      : type.for_each_lhs_of_arrow ltype t (* argument names *)
        -> base_ltype (type.final_codomain t) (* return value names *)
        -> Syntax.varname * Syntax.cmd.cmd :=
      match e with
      | expr.LetIn (type.base t1) (type.base t2) x f =>
        fun argnames retnames  =>
          let gr := translate_lhs t1 nextname in
          let cmdx :=
              match translate_carries x (snd gr) with
              | Some cmdx => cmdx
              | None => assign (snd gr) (translate_inner_expr true x)
              end in
          let recf := translate_expr (f (snd gr)) (fst gr) argnames retnames in
          (fst recf, Syntax.cmd.seq cmdx (snd recf))
      | expr.App
          (type.base (base.type.list (base.type.type_base base.type.Z)))
          (type.base (base.type.list (base.type.type_base base.type.Z)))
          (expr.App type_Z _ (expr.Ident _ (ident.cons _)) x) l =>
        fun argnames (retloc : Syntax.expr.expr) =>
          (* retloc is the address at which to store the head of the list *)
          let cmdx := (Syntax.cmd.store Syntax.access_size.word retloc (translate_inner_expr true x)) in
          let next_retloc := (Syntax.expr.op Syntax.bopname.add retloc (Syntax.expr.literal 1)) in
          let set_next_retloc := (Syntax.cmd.set nextname next_retloc) in
          let recl := translate_expr l (next_varname nextname) argnames (Syntax.expr.var nextname) in
          (fst recl, Syntax.cmd.seq (Syntax.cmd.seq cmdx set_next_retloc) (snd recl))
      | (expr.Ident _ (ident.nil (base.type.type_base base.type.Z))) =>
        fun _ _ => (nextname, Syntax.cmd.skip)
      | expr.App _ (type.base _) f x =>
        fun _ retnames =>
          let v := translate_inner_expr true (expr.App f x) in
          (nextname, assign retnames v)
      | expr.Ident (type.base _) x =>
        fun _ retnames =>
          let v := translate_inner_expr true (expr.Ident x) in
          (nextname, assign retnames v)
      | expr.Var (type.base _) x =>
        fun _ retnames =>
          let v := translate_inner_expr true (expr.Var x) in
          (nextname, assign retnames v)
      | expr.Abs (type.base s) d f =>
        fun (argnames : base_ltype s * type.for_each_lhs_of_arrow _ d)
            (retnames : base_ltype (type.final_codomain d)) =>
          translate_expr (f (fst argnames)) nextname (snd argnames) retnames
      | _ => fun _ _ => (nextname, Syntax.cmd.skip)
      end.
  End Compiler.

  Section Proofs.
    Context {p : Semantics.parameters}
            (next_varname : Syntax.varname -> Syntax.varname)
            (error : Syntax.expr.expr)
            (word_size_in_bytes : Z)
            (word_size_in_bytes_eq : word_size_in_bytes * 8 = Semantics.width)
            (ident_to_funname : forall t, ident.ident t -> Syntax.funname).
    Local Notation maxint := (2 ^ Semantics.width).

    (* Notations for commonly-used types *)
    Local Notation type_nat := (type.base (base.type.type_base base.type.nat)).
    Local Notation type_Z := (type.base (base.type.type_base base.type.Z)).
    Local Notation type_ZZ :=
      (type.base (base.type.prod (base.type.type_base base.type.Z)
                                 (base.type.type_base base.type.Z))).

    (* TODO : fill these in *)
    Axiom valid_carry_expr : forall {t}, @API.expr ltype t -> Prop.
    Axiom valid_inner_expr : forall {t}, @API.expr ltype t -> Prop.

    (* states whether the expression is acceptable input for [of_expr] *)
    Inductive valid_expr : forall {t}, @API.expr ltype t -> Prop :=
    | valid_carry_let :
        forall t x f,
          valid_carry_expr x ->
          (forall names, valid_expr (f names)) ->
          valid_expr (expr.LetIn (A:=type_ZZ) (B:=t) x f)
    | valid_let :
        forall t1 t2 x f,
          valid_inner_expr x ->
          (forall names, valid_expr (f names)) ->
          valid_expr (expr.LetIn (A:=type.base t1) (B:=t2) x f)
    | valid_cons :
        forall x l,
          valid_inner_expr x ->
          valid_expr l ->
          valid_expr
            (expr.App
               (expr.App
                  (expr.Ident
                     (@ident.cons (base.type.type_base base.type.Z)))
                  x) l)
    | valid_nil :
        valid_expr (expr.Ident
                      (@ident.nil (base.type.type_base base.type.Z)))
    | valid_app :
        forall s d f x,
          valid_inner_expr (expr.App (s:=type.base s) (d:=type.base d) f x) ->
          valid_expr (expr.App f x)
    | valid_ident :
        forall t i,
          valid_inner_expr (expr.Ident (t:=type.base t) i) ->
          valid_expr (expr.Ident i)
    | valid_var :
        forall t x,
          valid_inner_expr (expr.Var (t:=type.base t) x) ->
          valid_expr (expr.Var x)
    | valid_abs :
        forall s d f,
          (forall names, valid_expr (f names)) ->
          valid_expr (expr.Abs (s:=type.base s) (d:=d) f)
    .

    (* Convert expressions from ltype to the flat list format expected by
       bedrock2 for function input/output *)
    Fixpoint flatten_names {t} : base_ltype t -> option (list Syntax.varname) :=
      match t with
      | base.type.prod a b =>
        fun x : base_ltype a * base_ltype b =>
          Option.bind (flatten_names (fst x))
                      (fun lx => option_map (app lx) (flatten_names (snd x)))
      | base.type.list (base.type.type_base base.type.Z) =>
        fun x : Syntax.expr.expr =>
          match x with
          | Syntax.expr.var n => Some [n]
          | _ => None (* fail if list location is any expr other than a variable *)
          end
      | _ => fun x : Syntax.varname => Some [x]
      end.

    (* Convert the type of arguments from the nested for_each_lhs_of_arrow
       construction to a flat list; similar to flatten_names, but has to deal
       with the extra structure of for_each_lhs_of_arrow even though we disallow
       functions. *)
    Fixpoint flatten_argnames {t}
      : type.for_each_lhs_of_arrow ltype t -> option (list Syntax.varname) :=
      match t with
      | type.base _ => fun _ : unit => Some nil
      | type.arrow (type.base s) d =>
        fun args : base_ltype s * type.for_each_lhs_of_arrow ltype d =>
          Option.bind
            (flatten_names (fst args))
            (fun x =>
               option_map
                 (app x)
                 (flatten_argnames (snd args)))
      | type.arrow (type.arrow s d1) d2 => fun _ => None (* can't have function arguments *)
      end.

    Local Definition zarray
          (start : Interface.word.rep) (xs : list Z)
          (mem : Interface.map.rep (map:=Semantics.mem))
      : Prop :=
      let size := Interface.word.of_Z word_size_in_bytes in
      array (truncated_scalar Syntax.access_size.word) size start xs mem.

    (* states that a fiat-crypto value is equivalent to a bedrock value *)
    Fixpoint equivalent {t}
      : base.interp t -> list Interface.word.rep ->
        Interface.map.rep (map:=Semantics.mem) -> Prop :=
      match t with
      (* product case *)
      | base.type.prod a b =>
        fun (x : base.interp a * base.interp b)
            (y : list Interface.word.rep)
            (mem : Interface.map.rep) =>
          exists y1 y2,
            y = y1 ++ y2 /\
            sep (equivalent (fst x) y1)
                (equivalent (snd x) y2) mem
      (* list case -- only list Z allowed *)
      | base.type.list (base.type.type_base base.type.Z) =>
        fun (x : list Z)
            (y : list Interface.word.rep)
            (mem : Interface.map.rep) =>
          exists loc,
            y = loc :: nil /\
            zarray loc x mem
      (* base type case -- only Z allowed *)
      | base.type.type_base base.type.Z =>
        fun (x : Z)
            (y : list Interface.word.rep)
            (mem : Interface.map.rep) =>
          exists w,
            y = w :: nil /\
            Interface.word.unsigned w = x
      | _ => fun _ _ _ => False
      end.

    (* wrapper for equivalent that deals with for_each_lhs_of_arrow *)
    Fixpoint args_equivalent {t} :
      type.for_each_lhs_of_arrow (type.interp base.interp) t
      -> list Interface.word.rep
      -> Interface.map.rep (map:=Semantics.mem) -> Prop :=
      match t with
      | type.base a =>
        fun _ _ _ => True (* no more arguments; done *)
      | type.arrow (type.base s) d =>
        (* peel off one argument and enforce separation logic *)
        fun (args : base.interp s * type.for_each_lhs_of_arrow _ d)
            (w : list Interface.word.rep)
            (mem : Interface.map.rep) =>
          exists w1 w2,
            w = w1 ++ w2 /\
            sep (equivalent (fst args) w1)
                (args_equivalent (snd args) w2) mem
      | type.arrow (type.arrow _ _) _ =>
        fun _ _ _ => False (* disallow function arguments *)
      end.

    Lemma translate_expr_correct {t} (e : API.Expr t) :
      (* e is valid input to translate_expr *)
      valid_expr (e ltype) ->
      forall (args : type.for_each_lhs_of_arrow (type.interp base.interp) t)
             (bedrock_args : list Interface.word.rep)
             (argnames : type.for_each_lhs_of_arrow ltype t)
             (flat_argnames : list Syntax.varname)
             (retnames : base_ltype (type.final_codomain t))
             (flat_retnames : list Syntax.varname)
             (nextname : Syntax.varname)
             (mem : Interface.map.rep),
        (* args and bedrock_args are equivalent *)
        args_equivalent args bedrock_args mem ->
        (* argnames and flat_argnames are equivalent *)
        flatten_argnames argnames = Some flat_argnames ->
        (* retnames and flat_retnames are equivalent *)
        flatten_names retnames = Some flat_retnames ->
        (* ret := result of applying e to args *)
        let ret : base.interp (type.final_codomain t) :=
            type.app_curried (API.interp (e _)) args in
        (* bedrock_e := translation of e as bedrock2 function body *)
        let bedrock_e : Syntax.cmd.cmd :=
            snd (translate_expr next_varname error word_size_in_bytes
                                (e ltype) nextname argnames retnames) in
        forall (fname : Syntax.funname)
               (funnames' : list _)
               (* fname's body is bedrock_e *)
               (funnames := (fname, (flat_argnames, flat_retnames, bedrock_e))
                              :: funnames')
               (tr : Semantics.trace)
               (R : Interface.map.rep -> Prop),
          (* calling fname with bedrock_args is equivalent to ret *)
          WeakestPrecondition.call
            funnames fname tr mem bedrock_args
            (fun tr' m' bedrock_ret =>
               tr = tr' /\ sep (equivalent ret bedrock_ret) R m').
    Proof.
      (* TODO : look at Jason's final correctness theorem, make sure this short-circuits correctly. *)
    Admitted.
  End Proofs.
End Compiler.
