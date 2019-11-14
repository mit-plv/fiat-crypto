Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
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

Class parameters :=
  {
    semantics :> Semantics.parameters;
    varname_gen : nat -> Syntax.varname;
    error : Syntax.expr.expr;
    word_size_in_bytes : Z;
    maxint := 2 ^ Semantics.width;
  }.

Class ok {p:parameters} :=
  {
    semantics_ok : Semantics.parameters_ok semantics;
    word_size_in_bytes_ok : 0 < word_size_in_bytes;
    varname_gen_unique :
      forall i j : nat, varname_gen i = varname_gen j <-> i = j;
  }.

(* Notations for commonly-used types *)
Local Notation type_range := (type.base (base.type.type_base base.type.zrange)).
Local Notation type_nat := (type.base (base.type.type_base base.type.nat)).
Local Notation type_Z := (type.base (base.type.type_base base.type.Z)).
Local Notation type_listZ := (type.base (base.type.list (base.type.type_base base.type.Z))).
Local Notation type_range2 :=
  (type.base (base.type.prod (base.type.type_base base.type.zrange)
                             (base.type.type_base base.type.zrange))).
Local Notation type_ZZ :=
  (type.base (base.type.prod (base.type.type_base base.type.Z)
                             (base.type.type_base base.type.Z))).

Module Compiler.
  Section Compiler.
    Context {p : parameters}.

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
      | _ => Syntax.varname (* N.B. for lists, the value of the variable
                               represents the list's *location in memory* *)
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
    Fixpoint translate_lhs (t : base.type) (nextn : nat)
      : nat * base_ltype t :=
      match t with
      (* prod is a special case -- assign to multiple variables *)
      | base.type.prod a b =>
        let step1 := translate_lhs a nextn in
        let step2 := translate_lhs b (fst step1) in
        (fst step2, (snd step1, snd step2))
      (* everything else is single-variable assignment *)
      | base.type.list _ | base.type.option _ | base.type.unit
      | base.type.type_base _ => (S nextn, varname_gen nextn)
      end.

    Fixpoint assign {t : base.type}
      : base_ltype t -> base_rtype t -> Syntax.cmd.cmd :=
      match t with
      | base.type.prod a b =>
        fun (lhs : base_ltype (a * b)) (rhs : base_rtype (a * b)) =>
          Syntax.cmd.seq (assign (fst lhs) (fst rhs))
                         (assign (snd lhs) (snd rhs))
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
             {t} (e : @API.expr ltype (type.base t)) : base_rtype t :=
      if (require_cast && negb (has_casts e))%bool
      then base_make_error _
      else
        match e in expr.expr t0 return rtype t0 with
        (* Z_cast : clear casts because has_casts already checked for them *)
        | (expr.App
             type_Z type_Z
             (expr.App
                type_range (type.arrow type_Z type_Z)
                (expr.Ident _ ident.Z_cast) _) x) =>
          translate_inner_expr false x
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
          else base_make_error _
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
          else base_make_error _ 
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
                type_listZ _
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

    Fixpoint translate_expr {t} (e : @API.expr ltype (type.base t)) (nextn : nat)
      : base_ltype t (* return value names *)
        -> nat * Syntax.cmd.cmd :=
      match e in expr.expr t0 return ltype t0 -> _ with
      | expr.LetIn (type.base t1) (type.base t2) x f =>
        fun retnames  =>
          let gr := translate_lhs t1 nextn in
          let cmdx :=
              match translate_carries x (snd gr) with
              | Some cmdx => cmdx
              | None => assign (snd gr) (translate_inner_expr true x)
              end in
          let recf := translate_expr (f (snd gr)) (fst gr) retnames in
          (fst recf, Syntax.cmd.seq cmdx (snd recf))
      | expr.App
          type_listZ type_listZ
          (expr.App type_Z _ (expr.Ident _ (ident.cons _)) x) l =>
        fun (retloc : Syntax.varname) =>
          (* retloc is the address at which to store the head of the list *)
          let cmdx := (Syntax.cmd.store Syntax.access_size.word
                                        (Syntax.expr.var retloc) (translate_inner_expr true x)) in
          let next_retloc := (Syntax.expr.op Syntax.bopname.add
                                             (Syntax.expr.var retloc) (Syntax.expr.literal 1)) in
          let set_next_retloc := (Syntax.cmd.set (varname_gen nextn) next_retloc) in
          let recl := translate_expr l (S nextn) (varname_gen nextn) in
          (fst recl, Syntax.cmd.seq (Syntax.cmd.seq cmdx set_next_retloc) (snd recl))
      | (expr.Ident _ (ident.nil (base.type.type_base base.type.Z))) =>
        fun _ => (nextn, Syntax.cmd.skip)
      | expr.App _ (type.base _) f x =>
        fun retnames =>
          let v := translate_inner_expr true (expr.App f x) in
          (nextn, assign retnames v)
      | expr.Ident (type.base _) x =>
        fun retnames =>
          let v := translate_inner_expr true (expr.Ident x) in
          (nextn, assign retnames v)
      | expr.Var (type.base _) x =>
        fun retnames =>
          let v := translate_inner_expr true (expr.Var x) in
          (nextn, assign retnames v)
      | _ => fun _ => (nextn, Syntax.cmd.skip)
      end.

    Fixpoint translate_func {t} (e : @API.expr ltype t) (nextn : nat)
      : type.for_each_lhs_of_arrow ltype t -> (* argument names *)
        base_ltype (type.final_codomain t) -> (* return value names *)
        Syntax.cmd.cmd :=
      match e with
      | expr.Abs (type.base s) d f =>
        (* if we have an abs, peel off one argument and recurse *)
        fun (argnames : base_ltype s * type.for_each_lhs_of_arrow _ d)
            (retnames : base_ltype (type.final_codomain d)) =>
          translate_func (f (fst argnames)) nextn (snd argnames) retnames
      (* if any expression that outputs a base type, call translate_expr *)
      | expr.Ident (type.base b) idc =>
        fun (_:unit) retnames =>
          snd (translate_expr (expr.Ident idc) nextn retnames)
      | expr.Var (type.base b) v =>
        fun (_:unit) retnames =>
          snd (translate_expr (expr.Var v) nextn retnames)
      | expr.App _ (type.base b) f x =>
        fun (_:unit) retnames =>
          snd (translate_expr (expr.App f x) nextn retnames)
      | expr.LetIn _ (type.base b) x f =>
        fun (_:unit) retnames =>
          snd (translate_expr (expr.LetIn x f) nextn retnames)
      (* if the expression does not have a base type and is not an Abs, return garbage *)
      | _ => fun _ _ => Syntax.cmd.skip
      end.
  End Compiler.

  Section Proofs.
    Context {p : parameters} {p_ok : @ok p }.

    (* TODO : fill these in *)
    Axiom valid_carry_expr : forall {t}, @API.expr (fun _ => unit) t -> Prop.
    Axiom valid_inner_expr : forall {t}, bool -> @API.expr (fun _ => unit) t -> Prop.

    (* Inductive version: *)
    Inductive valid_expr : forall {t}, @API.expr (fun _ => unit) (type.base t) -> Prop :=
    | valid_LetIn_carry :
        forall {b} x f,
          valid_carry_expr x -> valid_expr (f tt) ->
          valid_expr (expr.LetIn (A:=type_ZZ) (B:=type.base b) x f)
    | valid_LetIn :
        forall {a b} x f,
          valid_inner_expr true x -> valid_expr (f tt) ->
          valid_expr (expr.LetIn (A:=type.base a) (B:=type.base b) x f)
    | valid_cons :
        forall x l,
          valid_inner_expr true x -> valid_expr l ->
          valid_expr
            (expr.App
               (expr.App
                  (expr.Ident
                     (ident.cons (t:=base.type.type_base base.type.Z))) x) l)
    | valid_nil :
        valid_expr (expr.Ident (ident.nil (t:=base.type.type_base base.type.Z)))
    | valid_inner : forall {t} e,
        valid_inner_expr true e -> valid_expr (t:=t) e
    .

    Inductive valid_func : forall {t}, @API.expr (fun _ => unit) t -> Prop :=
    | validf_Abs :
        forall {s d} f, valid_func (f tt) ->
                        valid_func (expr.Abs (s:=type.base s) (d:=d) f)
    | validf_base :
        forall {b} e, valid_func (t:=type.base b) e
    .

    (* Fixpoint version:
    (* states whether the expression is acceptable input for translate_expr *)
    Fixpoint valid_expr {t} (e : @API.expr (fun _ => unit) t) : bool :=
      match e with
      (* let-in with a carry expression *)
      | expr.LetIn type_ZZ (type.base t2) x f =>
        (valid_carry_expr x && valid_expr (f tt))
      (* other let-in *)
      | expr.LetIn (type.base t1) (type.base t2) x f =>
        (valid_inner_expr x && valid_expr (f tt))
      (* list-of-Z cons *)
      | expr.App
          _ _
          (expr.App
             _ _
             (expr.Ident
                _ (ident.cons (base.type.type_base base.type.Z)))
             x) l =>
        valid_inner_expr x && valid_expr l
      (* list-of-Z nil -- always valid *)
      | expr.Ident
          _ (ident.nil (base.type.type_base base.type.Z)) =>
         true
      (* Abs case is special *)
      | expr.Abs s d f =>
        valid_expr (f tt)
      | _ => valid_inner_expr e
      end. *)

    (* Convert expressions from ltype to the flat list format expected by
       bedrock2 for function input/output *)
    Fixpoint flatten_names {t} : base_ltype t -> option (list Syntax.varname) :=
      match t with
      | base.type.prod a b =>
        fun x : base_ltype a * base_ltype b =>
          Option.bind (flatten_names (fst x))
                      (fun lx => option_map (app lx) (flatten_names (snd x)))
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

    Definition zarray
               (start : @Interface.word.rep
                          (@Semantics.width semantics) (@Semantics.word semantics))
               (xs : list Z)
               (mem : Interface.map.rep
                        (map:=Semantics.mem (parameters:=semantics)))
      : Prop :=
      let size := Interface.word.of_Z word_size_in_bytes in
      Array.array (Scalars.truncated_scalar Syntax.access_size.word) size start xs mem.

    Fixpoint equivalent {t}
      : base.interp t -> (* fiat-crypto value *)
        base_rtype t -> (* bedrock2 value *)
        Interface.map.rep (map:=Semantics.locals) -> (* bedrock2 local variables *)
        Interface.map.rep (map:=Semantics.mem) -> (* bedrock2 main memory *)
        Prop :=
      match t with
      (* product case *)
      | base.type.prod a b =>
        fun (x : base.interp a * base.interp b)
            (y : base_rtype a * base_rtype b)
            locals mem =>
          sep (equivalent (fst x) (fst y) locals)
              (equivalent (snd x) (snd y) locals) mem
      (* list case -- only list Z allowed *)
      | base.type.list (base.type.type_base base.type.Z) =>
        fun (x : list Z)
            (y : Syntax.expr.expr)
            locals =>
          Lift1Prop.ex1
            (fun loc =>
               sep
                 (fun mem =>
                    WeakestPrecondition.dexpr mem locals y loc)
                 (zarray loc x))
      (* base type case -- only Z allowed *)
      | base.type.type_base base.type.Z =>
        fun (x : Z) (y : Syntax.expr.expr)
            locals =>
          Lift1Prop.ex1
            (fun w mem =>
                WeakestPrecondition.dexpr mem locals y w)
      | _ => fun _ _ _ _ => False
      end.

    (* TODO : remove if unused
    (* states that a fiat-crypto value is equivalent to the return values of a bedrock function *)
    Fixpoint equivalent {t}
      : base.interp t -> (* fiat-crypto return value *)
        base_ltype t -> (* bedrock2 local variables in which return values are stored *)
        Interface.map.rep (map:=Semantics.locals) -> (* bedrock2 local variables *)
        Interface.map.rep (map:=Semantics.mem) -> (* bedrock2 main memory *)
        Prop :=
      match t with
      (* product case *)
      | base.type.prod a b =>
        fun (x : base.interp a * base.interp b)
            (y : base_ltype a * base_ltype b)
            locals mem =>
          sep (equivalent (fst x) (fst y) locals)
              (equivalent (snd x) (snd y) locals) mem
      (* list case -- only list Z allowed *)
      | base.type.list (base.type.type_base base.type.Z) =>
        fun (x : list Z)
            (y : Syntax.varname)
            locals =>
          Lift1Prop.ex1
            (fun loc mem =>
               Lift1Prop.and1
                 (fun _ =>
                    Interface.map.get locals y = Some loc)
                 (zarray loc x))
      (* base type case -- only Z allowed *)
      | base.type.type_base base.type.Z =>
        fun (x : Z) (y : Syntax.varname)
            locals =>
          emp
            (exists w,
                Interface.map.get locals y = Some w
                /\ Interface.word.unsigned w = x)
      | _ => fun _ _ _ _ => False
      end. *)

    Fixpoint varname_set {t} : base_ltype t -> PropSet.set Syntax.varname :=
      match t with
      | base.type.prod a b =>
        fun x => PropSet.union (varname_set (fst x)) (varname_set (snd x))
      | _ => fun x => PropSet.singleton_set x
      end.

    Fixpoint context_list_equiv {var1}
               (locals : Interface.map.rep (map:=Semantics.locals))
               (mem : Interface.map.rep (map:=Semantics.mem))
               (G : list {t : API.type & (var1 t * API.interp_type t * ltype t)%type})
      : Prop :=
      match G with
      | [] => True
      | existT (type.base b) (w, x, y) :: G' =>
        sep (equivalent x y locals)
            (Lift1Prop.ex1
               (fun prev_locals mem' =>
                  Interface.map.only_differ prev_locals (varname_set y) locals
                  /\ context_list_equiv prev_locals mem' G')) mem
      | existT (type.arrow _ _) _ :: G' => False (* no functions allowed *)
      end.

    (*
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
      end. *)

    (*    (* wrapper for equivalent that deals with for_each_lhs_of_arrow *)
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
      end. *)

    (* TODO : move *)
    Require Import bedrock2.Map.SeparationLogic bedrock2.ProgramLogic.

    (* Cheat sheet on wf:
       Wf.Compilers.expr.wf = inductive stating two exprs match
       Wf.Compilers.expr.Wf = proof that for any Expr, giving it two different
         vars results in exprs that match  *)
    Import Rewriter.Language.Wf.Compilers.expr.

    Require Import Crypto.Util.Tactics.DestructHead.
    Require Import Crypto.Util.Tactics.BreakMatch.

    Ltac cleanup :=
      repeat first [ progress cbn [fst snd eq_rect] in *
                   | progress destruct_head'_and
                   | match goal with H : exists _, _ |- _ => destruct H end
                   | match goal with H : ?x = ?x |- _ => clear H end ].
    Import Rewriter.Language.Inversion.Compilers.
    (* borrowed from Fancy/Compiler.v *)
    Ltac hammer_wf :=
      repeat first [ progress subst
                   | progress cbn [eq_rect fst snd projT1 projT2] in *
                   | progress destruct_head'_False
                   | progress inversion_wf_one_constr
                   | progress expr.invert_subst
                   | progress destruct_head'_and
                   | progress destruct_head'_sig
                   | progress expr.inversion_expr
                   | break_innermost_match_hyps_step 
                   | match goal with
                     | H : existT _ _ _ = existT _ _ _ |- _ =>
                       apply Eqdep_dec.inj_pair2_eq_dec in H;
                       [ | solve [ apply type.type_eq_Decidable] ]
                     end ]; cleanup.

    
    Ltac hammer :=
      repeat first [
                    progress subst
                             (*
                  | progress inversion_sigma
                  | progress inversion_option
                  | progress inversion_prod *)
                  | progress cbv [id]
                  | progress cbn [eq_rect projT1 projT2 expr.interp ident.interp Coercions.base Coercions.type_base interp option_map] in *
                  | progress cbn [invert_expr.invert_Ident] in * (* N.B. Must be above [break_innermost_match] for proofs below to work *)
                  | progress Language.Inversion.Compilers.type_beq_to_eq
                  | progress Language.Inversion.Compilers.rewrite_type_transport_correct
                  | progress HProp.eliminate_hprop_eq
                  | progress break_innermost_match_hyps
                  | progress break_innermost_match
                  | progress inversion_type
                  | progress expr.invert_subst
                  | progress Language.Inversion.Compilers.expr.inversion_expr
                  | solve [auto]
                  | contradiction
             ].

    Lemma translate_carries_Some {t : base.type}
          G x1 x2 x3 nextn :
      wf3 (var2:=API.interp_type) G x1 x2 x3 ->
      valid_carry_expr x1 ->
      exists cmdx,
        translate_carries (t:=type.base t) x3 (snd (translate_lhs t nextn)) = Some cmdx.
    Admitted.

    (* valid inner expressions can't possibly be valid carry expressions *)
    Lemma translate_carries_None {t : base.type}
          G x1 x2 x3 nextn :
      wf3 (var2:=API.interp_type) G x1 x2 x3 ->
      valid_inner_expr true x1 ->
      translate_carries (t:=type.base t) x3 (snd (translate_lhs t nextn)) = None.
    Admitted.

    (* N.B. technically, x2 and f2 are not needed in the following lemmas, it just makes things easier *)

    Lemma translate_expr_carry {t1 t2 : base.type}
          G x1 x2 x3 f1 f2 f3 nextn retnames cmdx:
      wf3 G x1 x2 x3 ->
      (forall v1 v2 v3,
          wf3 (existT (fun t => (unit * API.interp_type t * ltype t)%type) (type.base t1) (v1, v2, v3) :: G)
              (f1 v1) (f2 v2) (f3 v3)) ->
      (* valid_carry_expr x1 -> valid_expr (f1 tt) -> *)
      let gr := translate_lhs t1 nextn in
      let recf := translate_expr (f3 (snd gr)) (fst gr) retnames in 
      translate_carries (t:=type.base t1) x3 (snd gr) = Some cmdx ->
      translate_expr (expr.LetIn (A:=type.base t1) (B:=type.base t2) x3 f3) nextn retnames =
      (fst recf, Syntax.cmd.seq cmdx (snd recf)).
    Proof.
      cbv zeta; intros. cbn [translate_expr].
      break_innermost_match; congruence.
    Qed.

    (* shouldn't need any properties of call, since the compiler does not output
       bedrock2 function calls *)
    Context (call : Syntax.funname ->
                    Semantics.trace ->
                    Interface.map.rep (map:=Semantics.mem) ->
                    list Interface.word.rep ->
                    (Semantics.trace -> Interface.map.rep (map:=Semantics.mem) ->
                     list Interface.word.rep -> Prop) ->
                    Prop).

    Context (Proper_call :
               Morphisms.pointwise_relation
                 Syntax.funname
                 (Morphisms.pointwise_relation
                    Semantics.trace
                    (Morphisms.pointwise_relation
                       Interface.map.rep
                       (Morphisms.pointwise_relation
                          (list Interface.word.rep)
                          (Morphisms.respectful
                             (Morphisms.pointwise_relation
                                Semantics.trace
                                (Morphisms.pointwise_relation
                                   Interface.map.rep
                                   (Morphisms.pointwise_relation
                                      (list Interface.word.rep) Basics.impl)))
                             Basics.impl)))) call call).


    Lemma translate_carries_correct {t}
          (* three exprs, representing the same Expr with different vars *)
          (e1 : @API.expr (fun _ => unit) (type.base t))
          (e2 : @API.expr API.interp_type (type.base t))
          (e3 : @API.expr ltype (type.base t)) :
      (* e1 is a valid input to translate_carries_correct *)
      valid_carry_expr e1 ->
      forall G cmdx nextn,
        wf3 G e1 e2 e3 ->
        let gr := translate_lhs t nextn in
        translate_carries e3 (snd gr) = Some cmdx ->
        forall (tr : Semantics.trace)
               (mem locals : Interface.map.rep)
               (R : Interface.map.rep -> Prop),
          context_list_equiv locals mem G ->
          WeakestPrecondition.cmd
            call cmdx tr mem locals
            (fun tr' mem' locals' =>
               tr = tr'
               (* translate_carries never stores anything -- mem unchanged *)
               /\ mem = mem'
               (* new locals only differ in the values of LHS variables *)
               /\ Interface.map.only_differ locals (varname_set (snd gr)) locals'
               (* no variables disappear *)
               /\ Interface.map.sub_domain locals locals'
               (* information stored in LHS variables is equivalent to interp *)
               /\ sep (equivalent (API.interp e2) (snd gr) locals') R mem').
    Admitted.

    Print WeakestPrecondition.dexpr.
    Lemma translate_inner_expr_correct {t}
          (* three exprs, representing the same Expr with different vars *)
          (e1 : @API.expr (fun _ => unit) (type.base t))
          (e2 : @API.expr API.interp_type (type.base t))
          (e3 : @API.expr ltype (type.base t))
          (require_cast : bool) :
      (* e1 is a valid input to translate_carries_correct *)
      valid_inner_expr require_cast e1 ->
      forall G nextn,
        let gr := translate_lhs t nextn in
        let out := translate_inner_expr require_cast e3 in
        wf3 G e1 e2 e3 ->
        forall (tr : Semantics.trace)
               (mem locals : Interface.map.rep)
               (R : Interface.map.rep -> Prop),
          context_list_equiv locals mem G ->
          WeakestPrecondition.cmd
            call (assign (snd gr) out)
            tr mem locals
            (fun tr' mem' locals' =>
               tr = tr'
               /\ Interface.map.sub_domain locals locals'
               /\ sep (equivalent (API.interp e2) (snd gr) locals') R mem').
    Admitted.
    About translate_inner_expr.
    Search base_rtype.
    Print base_rtype.
    Print assign.
    About equivalent.
    Check base.interp.
    Lemma assign_correct {t}
          (x : base.interp t)
          (lhs : base_ltype t)
          (rhs : base_rtype t) :
      forall G nextn,
        forall (tr : Semantics.trace)
               (mem locals : Interface.map.rep)
               (R : Interface.map.rep -> Prop),
          equivalent x lhs locals mem ->
          WeakestPrecondition.cmd
            call (assign lhs rhs)
            tr mem locals
            (fun tr' mem' locals' =>
               tr = tr'
               (* translate_carries never stores anything -- mem unchanged *)
               /\ mem = mem'
               (* new locals only differ in the values of LHS variables *)
               /\ Interface.map.only_differ locals (varname_set (snd gr)) locals'
               (* no variables disappear *)
               /\ Interface.map.sub_domain locals locals'
               (* information stored in LHS variables is equivalent to interp *)
               /\ sep (equivalent (API.interp e2) (snd gr) locals') R mem').
    Admitted.

    Lemma translate_inner_expr_correct {t}
          (* three exprs, representing the same Expr with different vars *)
          (e1 : @API.expr (fun _ => unit) (type.base t))
          (e2 : @API.expr API.interp_type (type.base t))
          (e3 : @API.expr ltype (type.base t))
          (require_cast : bool) :
      (* e1 is a valid input to translate_carries_correct *)
      valid_inner_expr require_cast e1 ->
      forall G nextn,
        let gr := translate_lhs t nextn in
        let out := translate_inner_expr require_cast e3 in
        wf3 G e1 e2 e3 ->
        forall (tr : Semantics.trace)
               (mem locals : Interface.map.rep)
               (R : Interface.map.rep -> Prop),
          context_list_equiv locals mem G ->
          WeakestPrecondition.cmd
            call (assign (snd gr) out)
            tr mem locals
            (fun tr' mem' locals' =>
               tr = tr'
               /\ Interface.map.sub_domain locals locals'
               /\ sep (equivalent (API.interp e2) (snd gr) locals') R mem').
    Admitted.

    (* TODO: see if there's a bedrock2 lemma that proves this *)
    Lemma sep_indep {k v}
          {map : Interface.map.map k v}
          a b m :
      sep (map:=map) (fun _ => a) b m -> a /\ sep (fun _ => True) b m.
    Proof.
      cbv [sep]; intros.
      repeat match goal with H : exists _, _ |- _ => destruct H end.
      destruct_head'_and; split; [ assumption | ].
      intros; do 2 eexists.
      repeat (split; try eassumption).
    Qed.

    (* states that the variables given as return types are okay; this means that
       if a list is returned, the variable holding the location where the list head
       should go actually exists in the local context. *)
    Fixpoint retnames_ok
             {t} (locals : Interface.map.rep (map:=Semantics.locals))
      : base_ltype t -> Prop :=
      match t with
      | base.type.prod a b =>
        fun x =>
          retnames_ok locals (fst x) /\ retnames_ok locals (snd x)
      | base.type.list (base.type.type_base base.type.Z) =>
        fun x =>
          exists a, WeakestPrecondition.get locals x (eq a)
      | _ => fun _ => True
      end.

    Lemma sub_domain_retnames t retnames locals locals' :
      Interface.map.sub_domain locals locals' ->
      retnames_ok locals retnames ->
      @retnames_ok t locals' retnames.
    Admitted.

    Local Ltac simpl_sep :=
      let t := ltac:(solve [eapply Semantics.mem_ok]) in
      match goal with
      | H : sep (fun mem => sep _ _ mem) _ _ |- _ =>
        apply @sep_assoc in H; [ | t]
      | H : sep (emp _) _ _ |- _ =>
        apply @sep_emp_l in H; [ cleanup | t]
      | |- sep (fun mem => sep _ _ mem) _ _ =>
        apply @sep_assoc; [t | ]
      | |- sep (emp _) _ _ =>
        apply @sep_emp_l; [t | ]
      | |- _ /\ _ => split; [ solve [eauto] | ]
      end.

    Lemma translate_expr_correct' {t'} (t:=type.base t')
          (* three exprs, representing the same Expr with different vars *)
          (e1 : @API.expr (fun _ => unit) t)
          (e2 : @API.expr API.interp_type t)
          (e3 : @API.expr ltype t)
          (* e1 is valid input to translate_expr *)
          (e1_valid : valid_expr e1)
          (* context list *)
          (G : list _) :
      (* exprs are all related *)
      wf3 G e1 e2 e3 ->
      forall (locals : Interface.map.rep)
             (memlocs : list Syntax.expr.expr)
             (retnames : base_ltype t')
             (nextn : nat),
        (* ret := fiat-crypto interpretation of e2 *)
        let ret : base.interp t' := API.interp e2 in
        (* out := translation output for e3 *)
        let out := translate_expr e3 nextn retnames in
        (* retnames are okay *)
        retnames_ok locals retnames ->
        (*
        (* output expression doesn't look up variables that don't exist *)
        snd (accesses_ok locals nextn memlocs (fst out) (snd out)) -> *)
        forall (tr : Semantics.trace)
               (mem : Interface.map.rep)
               (R : Interface.map.rep -> Prop),
          (*
          (* all the variable names between startn and nextn are in locals *)
          Interface.map.sub_domain (dummy_locals startn (nextn - startn)) locals -> *)
          (* contexts are equivalent; for every variable in the context list G,
             the fiat-crypto and bedrock2 results match *)
          context_list_equiv locals mem G ->
          (* executing translation output is equivalent to interpreting e *)
          WeakestPrecondition.cmd call (snd out) tr mem locals
                                  (fun tr' mem' locals' =>
                                     tr = tr'
                                     (* locals' needs to have *some* value for everything that was in locals
                  (output may overwrite input, but input variables cannot disappear) *)
                                     /\ Interface.map.sub_domain locals locals'
                                     /\ sep (equivalent ret retnames locals') R mem').
    Proof.
      revert e2 e3 G.
      subst t.
      induction e1_valid; inversion 1; cbv zeta in *; intros.
      all:hammer_wf. (* get rid of the wf nonsense *)

      { (* carry let-in *)
        (* posit the existence of a return value from translate_carries and use
           it to rewrite translate_expr *)
        match goal with H : valid_carry_expr _ |- _ =>
                        pose proof H;
                        eapply translate_carries_Some in H;
                        [ destruct H | eassumption .. ]
        end.
        erewrite @translate_expr_carry by eassumption.
        cleanup.

        (* simplify fiat-crypto step *)
        intros; cbn [expr.interp type.app_curried].
        cbv [Rewriter.Util.LetIn.Let_In]. cleanup.

        (* simplify bedrock2 step *)
        cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
        eapply WeakestPreconditionProperties.Proper_cmd;
          [ eapply Proper_call | repeat intro | ].
        (* N.B. putting below line in the [ | | ] above makes eassumption fail *)
        2 : eapply translate_carries_correct with (R0:=R); try eassumption.

        (* use inductive hypothesis *)
        cbn [translate_lhs] in *; cleanup.
        eapply WeakestPreconditionProperties.Proper_cmd;
          [ eapply Proper_call | repeat intro | ].
        2: { eapply IHe1_valid with (R:=R); try eassumption;
             try solve [eapply sub_domain_retnames; eauto];
             try match goal with
                 | H : (forall v1 v2 v3,
                           wf3  _ (_ v1) (_ v2) (_ v3)),
                       H' : sep (equivalent ?x _ _) _ _ |- _ =>
                   apply H with (v2:=x)
                 end; [ ].
             clear IHe1_valid.
             cbn [context_list_equiv equivalent] in *.
             (* for some reason, [repeat] or [do x] makes this fail... *)
             simpl_sep. simpl_sep. simpl_sep. simpl_sep. simpl_sep.
             simpl_sep. simpl_sep. simpl_sep.
             subst; eexists; split; solve [eauto]. }
      { intros; cleanup; subst.
        split; try congruence; [ ].
        repeat split; try eassumption;
          eauto using Properties.map.sub_domain_trans. } }
    { (* non-carry let-in *)
      (* simplify one translation step *)
      cbn [translate_expr].
      erewrite translate_carries_None by eassumption.
      cleanup.

      (* simplify fiat-crypto step *)
      intros; cbn [expr.interp type.app_curried].
      cbv [Rewriter.Util.LetIn.Let_In]. cleanup.

      (* simplify bedrock2 step *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      (* N.B. putting below line in the [ | | ] above makes eassumption fail *)
      2 : eapply translate_inner_expr_correct with (R0:=R); eassumption.

      (* use inductive hypothesis *)
      (* use inductive hypothesis *)
        cbn [translate_lhs] in *; cleanup.
        eapply WeakestPreconditionProperties.Proper_cmd;
          [ eapply Proper_call | repeat intro | ].
        2: { eapply IHe1_valid with (R:=R); try eassumption;
             try solve [eapply sub_domain_retnames; eauto];
             try match goal with
                 | H : (forall v1 v2 v3,
                           wf3  _ (_ v1) (_ v2) (_ v3)),
                       H' : sep (equivalent ?x _ _) _ _ |- _ =>
                   apply H with (v2:=x)
                 end; [ ].
             clear IHe1_valid.
             cbn [context_list_equiv equivalent] in *.
             (* for some reason, [repeat] or [do x] makes this fail... *)
             simpl_sep. simpl_sep. simpl_sep. simpl_sep. simpl_sep.
             simpl_sep. simpl_sep. simpl_sep.
             subst; eexists; split; solve [eauto]. }
      { intros; cleanup; subst.
        split; try congruence; [ ].
        repeat split; try eassumption;
          eauto using Properties.map.sub_domain_trans. } }
    { (* cons *)

      (* repeatedly do inversion until the cons is exposed *)
      repeat match goal with
             | H : wf3 _ _ _ _ |- _ =>
               match type of H with context [Compilers.ident.cons] =>
                                    inversion H; hammer_wf
               end
             end.
      
      (* simplify one translation step *)
      cbn [translate_expr]. cleanup.

      cbn [type.for_each_lhs_of_arrow
             type.app_curried type.final_codomain base_ltype] in *.

      cbn [retnames_ok] in *.
      cleanup.

      (* simplify bedrock2 step *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].

      Print Syntax.cmd.cmd.
      Print Syntax.expr.expr.
      Print WeakestPrecondition.dexpr.
      Print WeakestPrecondition.expr_body.

      cbn [WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists; split; [ eassumption | ].

      Print WeakestPrecondition.cmd_body.
      (* 
           here, the goal says that translate_inner_expr is an expression that evaluates to some word a
           ...and that's true only if it doesn't look up variables that don't exist
           ...which is why we needed accessses_ok before

           Try to think of more elegant solutions

           Note: haven't used translate_inner_expr_correct yet, and might well
           want a totally different form for it -- WeakestPrecondition.dexpr instead of cmd
           
       *)

      
      (* here is where, before, we used translate_inner_expr_correct_store *)
      (* need some kind of statement in the validity precondition or some
        extra precondition on the provided return values that the return
        variable holding list locations exists -- probably also need somewhere
        to fold through that next_varname will never overwrite this variable *)
      (* probably will also need to know eventually that next_varname doesn't
           repeat *)
      (* presumably for the inductive hypothesis we need more information
        about locals? Every time we get the value of a var, we need to know it
        was in context *)
      (* Need to think carefully. Don't rush it.
           1) How do we deal with the representation of lists? Variables are
              maybe not the best way -- are literals possible?
           2) More broadly (probably this should be answered first) -- what's up
              with local variables? For induction to work, how much information
              about them does my theorem statement need to have?

           Focusing first on 2) -- when does WeakestPrecondition.cmd need to
           know local information?

           In store, we get two expressions ea and ev and need to say there
           exist a and v, both words, such that evaluating ea in the local
           context gives you a and evaluating ev gives you v -- no misses
           allowed, so all vars and loads have to have information there.

           set also needs to know that there exists v : word such that the
           expression on the RHS (ev) evaluates to v.

           Perhaps we need a predicate on the expression that says "no misses"
           -- that is, no references to variables that don't exist, and maybe no
           loads where there weren't previous stores.

           The loads might be tricky -- if arguments are lists, we'd have to
           load from those places, so any "no misses" predicate would need to
           know where the input data is stored. Should be folded neatly into an
           inductive hypothesis that allows stores, even though I don't think we
           do load-store.

           Or maybe we could be more direct and just have a predicate saying,
           for every place where we call store or load, the preconditions in
           WeakestPrecondition.cmd hold. I'm fuzzy on this one.

           Loads might be possible to make way simpler if we just use literals,
           so instead let's think about set, which we definitely need to use.

           Can we add a definition saying that all inner expressions do evaluate
           to some word, to our postcondition? Would that help? No, probably
           not, since it would be a proof obligation and not a hypothesis, and
           we don't need it for the continuation -- we need it for the inner
           expressions of the exposed step.

           Idea: make predicate on locals and API.expr, and use it to say that
           all vars called in the start expression exist; require this for
           initial locals and also add to postcondition (so it must hold for all
           locals).  During the inductive step, your IH will require the proof
           that the exposed step obeys the rule, and prove to you that it's true
           for the continuation, but this is not very useful -- how do you get
           the information for the current step?

           Can we use nextn? So, say, our predicate states that every
           variable call is <= nextn, using the nextn-takes-nat
           construction, or is equal to something that we know is in the start
           context (arguments or return value variables that require variable
           loads -- list currently).

           We would then need to use the compiler structure to prove that, if
           the predicate holds, the WeakestPrecondition.expr stuff works for all
           inner expressions. The logic would be that all the variables must
           have been set, since we don't waste variable names[0], and we don't
           have any loads.

           How do we state that proof (in particular, "expr stuff works"), and
           could it just be folded into the main proof? So the predicate takes
           care of saying all our variable reads are of stuff that's in the
           arguments or the set range of names, and the precondition takes care
           of saying that those variables are set -- we have to prove the
           precondition each time in the main proof, but that's better than two
           proofs.

           Predicate should be fixpoint on *bedrock2* expression, so in terms of
           output -- fill precondition by compute. Similarly, compute a function
           on arguments that gives you all the memory addresses and variables
           that are filled at the start, which is input to the predicate. So the
           predicate is dumb and just says "all accesses are in this list, all
           variables in this one", starting with the two lists given by
           extracting them from arguments and updating with loads/sets.

           ...actually, do we then need to deal with nextn at all? Since
           we're working with a function of the output, we could just aggregate
           all the variables that have been set. No need to deal with nextn,
           just that list, same as arguments. And our predicate says "forall v :
           varname, In v <list> -> exists a : word, WeakestPrecondition.get
           locals v (eq a)".

           But what gets plugged in for locals? For arguments, it's starting
           locals, and that's why we originally thought of using nextn -- so
           we wouldn't have to keep track of locals. Then we just say in the
           inductive proof that we have a start_nextn and that everything
           between nextn and start_nextn is in locals (in postcondition).
           So in the inductive step, we increase nextn, and need to prove our
           new locals contains the new variables, which it should. Sounds right.

           Next, reread and think through concrete steps. Write them down and
           then start.

           [0] probably looks like an extra precondition in the inductive proof
           saying (forall n, start_nextn <= n <= nextn, exists a,
           WeakestPrecondition.get locals (varname n) (eq a)), and then removing
           the precondition for non-inductive wrapper because at the start,
           start_nextn = nextn
       *)
      (* ideas:

           A: instead of next_varname function, use a list varname_list and have a
           default_varname

           pros: easy to state that the list variables in retnames don't get
           overwritten, flexible
           cons: annoying to state if you don't know how many variables you need

           B: keep as-is, write a statement saying "next_varname will never
           produce the list variables in retname"

           pros: minimal code changes
           cons: difficult to state and work with in proofs

           C: Make the whole system not use varnames for lists, but rather literals

           pros: easy for proofs
           cons: constricting for callers

           D: make next_varname take a nat and have a proof that the nats aren't
           equal; then you just start with the index of the first varname, and
           have a proof that refnames is not equal to any varnames greater than
           that
       *)
      Print Syntax.expr.expr.
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      (* N.B. putting below line in the [ | | ] above makes eassumption fail *)
      2 : eapply translate_inner_expr_correct with (R0:=R); eassumption.




      (* use exec.seq and translate_inner_expr_correct to take a bedrock2 step *)
      eapply Semantics.exec.seq
        with (mid:=fun tr' mem' locals' _ =>
                     tr = tr'
                     /\ Interface.map.get locals retnames = Interface.map.get locals' retnames
                     /\ (exists x y,
                            Interface.map.get locals' nextn = Some x
                            /\ Interface.map.get locals' retnames = Some y
                            /\ x = Interface.word.add y (Interface.word.of_Z 1))
                     /\ sep (equivalent (expr.interp (t:=type_Z) (@Compilers.ident_interp) x4)
                                        retnames locals') R mem');
        [ eapply Semantics.exec.seq;
          [ eapply translate_inner_expr_correct_store with (R:=R); eassumption | ] | ].
      2 : {
        (* simplify fiat-crypto step *)
        intros; cbn [expr.interp type.app_curried Compilers.ident_interp].
        cbn [Compilers.ident_interp]. cleanup.

        (* simplify equivalent and other things depending on the expr type *)
        cbn [type.for_each_lhs_of_arrow
               type.app_curried equivalent type.final_codomain base_ltype] in *.

        destruct_head'_and. subst.

        eapply exec_weaken;
          [ | eapply IHe1_valid with (R:=R); eassumption].
        clear IHe1_valid.

        intros; cleanup.
        destruct_head'_and.
        split; try congruence; [ ].

        apply (sep_ex1_l (ok:=Semantics.mem_ok (parameters_ok:=semantics_ok))).
        repeat match goal with
               | H : _ |- _ =>
                 apply (sep_ex1_l (ok:=Semantics.mem_ok (parameters_ok:=semantics_ok))) in H;
                   destruct H as [? H]
               end.


        match goal with H : Interface.map.get _ retnames = Some ?x |- _ =>
                        exists x end.
        repeat match goal with H : sep _ R _ |- _ =>
                               eapply sep_indep in H end.
        cleanup.
        match goal with H1 : (?x = Some ?y1), H2 : (?x = Some ?y2) |- _ =>
                        replace y1 with y2 in * by congruence end.

        match goal with
          H : forall c, c -> sep (fun _ => c) ?R ?m |- sep (fun _ => ?p) ?R ?m =>
          apply H end.

        cbv [Lift1Prop.and1] in *.
        intros.
        (* here, we've lost information about the locals when we applied IH,
             so l' = locals' = locals is not clear -- need to weaken again before applying IH? *)
        
        Search locals.
        Search locals'.
        rewrite H2.
        

        split; try eassumption.
        
        
        (* x4 == x6 == retnames, nextn == x6+1 *)
        (* TODO : figure out what's going on here with nextn/retname -- which is doing what? *)


        (* 
             we're dealing with an expression whose return type is list, so retnames
               is a variable that holds the head of the list when we're done
             so when we encounter a cons (x :: l), we store l in the location indicated by retnames,
               set nextn := $retnames + 1, and then recursive call with retnames:=nextn
             therefore, us having retnames in the thing that still has the cons and having
               nextn in the one that doesn't have the cons is just fine, although we
               probably need from mid that nextn:=$retnames+1

         *)

        cbv [sep].
        do 2 eexists. repeat split; try eassumption.
        1-2:admit.

        (* here's where we need more about locals *)
        eauto.
        
        cbv [Lift1Prop.and1] in H3.
        Search sep Lift1Prop.and1.
        Print Lift1Prop.
        
        
        Print zarray.
        cbn [zarray array truncated_scalar].
        Search Lift1Prop.ex1.
        rewrite sep_ex1_l.

        (*
    Semantics.exec.exec env (snd (translate_expr x3 (next_varname nextn) argnames nextn)) t' m' l' mc'
        (fun (tr' : Semantics.trace) (mem' locals' : Interface.map.rep) (_ : MetricLogging.MetricLog) =>
        t' = tr' /\
        sep
        (fun mem0 : Interface.map.rep =>
            exists loc : Interface.word.rep,
            Interface.map.get locals' retnames = Some loc /\
            zarray loc (expr.interp (@Compilers.ident_interp) x4 :: expr.interp (@Compilers.ident_interp) x2) mem0)
        R mem')
         *)


        Search Semantics.exec.exec.
        (* mid should say something about x4 being related to x; here, we need
          to somehow pull out the cons and use the IH for l/x2/x3 *)
        (* we should be able to turn the zarray into a conjuction, somehow
          pull the conjunction out of sep, and then out of exec post, to get two
          exec goals, one of which uses IH and the other mid *)
        Set Printing Implicit.
        
        eapply IHe1_valid; eauto.
      }

      { intros.
        cleanup.
        destruct_head'_and.
        cbn [base_ltype type.final_codomain equivalent] in *.

        match goal with
        | H : _ |- _ => apply sep_indep in H
        end.

        repeat match goal with H : exists _, _ |- _ => destruct H end.
        destruct_head'_and.
        
        eapply Semantics.exec.set.
        { cbn [Semantics.eval_expr].
          match goal with H : Interface.map.get _ _ = _ |- _ => rewrite H end.
          reflexivity. }
        split; try congruence; [ ].
      (* ?mid t' m'
               (Interface.map.put l' nextn (bopname.add x0 1))
               (... logging ...) *) }
      
      match goal with
      | H : _ |- _ => apply sep_indep in H
      end.

      repeat match goal with H : exists _, _ |- _ => destruct H end.
      
      [ eapply translate_inner_expr_correct with (R0:=R); eassumption | ].

      (* simplify fiat-crypto step *)
      intros; cbn [expr.interp type.app_curried].
      cbv [Rewriter.Util.LetIn.Let_In]. cleanup.

      (* use inductive hypothesis *)
      destruct_head'_and. subst.
      eapply IHe1_valid; eauto. }

    (* nil *)
    (* Abs *)

    (* all the rest are inner *)
    (* Ident *)
    (* Var *)
    (* Abs *)
    (* App *)
    (* LetIn *)
    
    
    Qed.

    Lemma translate_expr_correct {t} (* (e : API.Expr t) *) :
      (* e is valid input to translate_expr *)
      forall e : API.Expr t, valid_expr (e _) ->
                             forall (args : type.for_each_lhs_of_arrow (type.interp base.interp) t)
                                    (bedrock_args : list Interface.word.rep)
                                    (argnames : type.for_each_lhs_of_arrow ltype t)
                                    (flat_argnames : list Syntax.varname)
                                    (retnames : base_ltype (type.final_codomain t))
                                    (flat_retnames : list Syntax.varname)
                                    (nextn : Syntax.varname)
                                    (mem : Interface.map.rep),
                               (* args and bedrock_args are equivalent *)
                               args_equivalent args bedrock_args mem ->
                               (* argnames and flat_argnames are equivalent *)
                               flatten_argnames argnames = Some flat_argnames ->
                               (* retnames and flat_retnames are equivalent *)
                               flatten_names retnames = Some flat_retnames ->
                               (* ret := result of applying e to args *)
                               let ret : base.interp (type.final_codomain t) :=
                                   type.app_curried (API.Interp e) args in
                               (* bedrock_e := translation of e as bedrock2 function body *)
                               let bedrock_e : Syntax.cmd.cmd :=
                                   snd (translate_expr (e ltype) nextn argnames retnames) in
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
      induction 1; cbv zeta in *; intros.
      { eauto. }
      { repeat (straightline || (straightline_call; [solve[ecancel_assumption]|])).
        eauto. }
      { repeat (straightline || (straightline_call; [solve[ecancel_assumption]|])).
        eauto. }
      ; []; eauto. }.
    Qed.
  End Proofs.
End Compiler.
