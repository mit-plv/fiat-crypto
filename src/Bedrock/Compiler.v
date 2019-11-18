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
      | base.type.list (base.type.type_base base.type.Z) =>
        list Syntax.varname (* N.B. we require lists to have all their values
                               stored in local variables, so we don't have to
                               do memory reads *)
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
      | base.type.list (base.type.type_base base.type.Z) =>
        list Syntax.expr.expr
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
      | base.type.list (base.type.type_base base.type.Z) =>
        map Syntax.expr.var
      | base.type.list _ | base.type.option _ | base.type.unit
      | base.type.type_base _ => Syntax.expr.var
      end.

    (* error creation *)
    Fixpoint base_make_error t : base_rtype t :=
      match t with
      | base.type.prod a b => (base_make_error a, base_make_error b)
      | base.type.list (base.type.type_base base.type.Z) => [error]
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
      (* assignments to lists are not allowed; we only construct lists as
         output, and don't assign them to variables, so return garbage *)
      | base.type.list (base.type.type_base base.type.Z) =>
       (nextn, nil) 
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
      | base.type.list (base.type.type_base base.type.Z) =>
        fun _ _ => Syntax.cmd.skip (* not allowed to assign to a list; return garbage *)
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
        (* List_nth_default : lists are represented by lists of variables, so we
           can perform the nth_default inline. This saves us from having to
           prove that all indexing into lists is in-bounds. *)
        | (expr.App
             type_nat type_Z
             (expr.App
                type_listZ _
                (expr.App type_Z _
                          (expr.Ident _ (ident.List_nth_default _))
                          d) (expr.Var type_listZ l))
             (expr.Ident _ (ident.Literal base.type.nat i))) =>
          let l : list Syntax.varname := l in
          let i : nat := i in
          let d : Syntax.expr.expr := translate_inner_expr true d in
          nth_default d (map Syntax.expr.var l) i
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
        fun (retnames : list Syntax.varname) =>
          match retnames with
          | nil => (nextn, Syntax.cmd.skip) (* shouldn't happen *)
          | n :: retnames' =>
            let x := translate_inner_expr true x in
            let recl := translate_expr l nextn retnames' in
            (fst recl, Syntax.cmd.seq (Syntax.cmd.set n x) (snd recl))
          end
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

  (*
  Section Proofs.
    Context {p : parameters} {p_ok : @ok p }.

    Local Instance sem_ok : Semantics.parameters_ok semantics
      := semantics_ok.
    Local Instance mem_ok : Interface.map.ok Semantics.mem
      := Semantics.mem_ok.
    Local Instance varname_eqb_spec x y : BoolSpec _ _ _
      := Semantics.varname_eqb_spec x y.

    (* TODO : fill these in *)
    Axiom valid_carry_expr : forall {t}, @API.expr (fun _ => unit) t -> Prop.


    Set Printing All.
    (* DESIGN TIME

    Problems:
      - need to not require a context-matching precondition in inductive proofs that change memory
      - need to include in validity precondition that nth_default doesn't overshoot the list

      these problems *together* do suggest some reads-first approach, but I'm not quite sure how it would look
      

      ...could we make rtype for lists a list of Syntax.expr? (wouldn't solve
      problem that we need something to say in validity precondition)


      imagine a new compiler pass that replaces e.g. fun x => f (x[[2]], x[[4]]) with fun x2 x4 => f(x2, x4)


      when we reach Abs, and the value to be taken in is a list, then we want to
      return an Abs that takes in *some number* of Zs. we could do it by making
      a fixpoint type called length that returns a nat for lists and a unit for
      everything else, and checking what the length is supposed to be. Then we
      make an Abs that takes in the Zs, constructs the list, and then passes the
      constructed list into the continuation. When we later encounter
      nth_default, we require that the structure of the list is exposed and
      recurse down until we either go out of bounds (replacing the nth_default
      with d) or get the right element (replacing nth_default with that var).

      then when we go through and convert to bedrock2, we can have a validity
      precondition that excludes memory reads entirely.

      The correctness proof would need to say that the transformation preserves
      return values. And then the bedrock2 translation would have to somehow go
      back to lists...


      In the translation, var=ltype
      can ltype require lists of Syntax.varname for lists? (where the
      varname is the variable holding the *value stored*, not the address)
      that would mean that when we encounter nth_default, we require the list to
      be an expr.Var and we get a list Syntax.varname in context that we can
      perform the nth_default on and output just the varname as the translation,
      bypassing the read entirely

      when we want to say the contexts match (context_list_equiv), for the list
      case, we get an (API.interp type_listZ = list Z) and an (ltype type_listZ
      = list Syntax.varname); the proposition then becomes whether these
      variables pairwise-match the Zs

      But we do still want the bedrock2 arguments to be a list...need to make
      the translation expression start with loading all the list-arguments into
      variables


      THINK. How does this solve problems?

      Well, the nth_default equivalence works because during the translation we
      *perform* nth_default. And this structure makes it so we have *no memory
       reads*, and therefore need no memory state in context_list_equiv; we can
       assume memory changes have no effect on the interpretation of any
       expression.

       How can we now wrap this in reads at the beginning and writes at the end?
       this compiler will take in a normal fiat-crypto expression (i.e. takes in
       lists and outputs lists) and return a bedrock2 cmd that requires starting
       with a context that has all list elts pre-loaded and returns values in
       separate variables. The correctness proofs will need to know both lists,
       and know that the ones in arguments are equivalent to fiat-crypto
       arguments in the given context.


       Then we'll need a new ltype that *does* represent lists as locations in
       memory, and things to convert to and from this type by loading or
       storing.

       Then, we can write something that takes in fiat-crypto arguments
       (API.interp type, so list Z for type_listZ), and loads any lists into
       variables (using varname_gen), returning a bedrock2 cmd, an ltype for the
       arguments, and a new nextn. We can prove that the ltype and the
       fiat-crypto arguments are equivalent in the new context after running the
       cmd, which composes with the previous proof.

       To wrap the end -- given ltype (type_listZ==>list Syntax.varname), store
       the list.

       Plan:

       - for now, focus on the "middle part" -- everything is in locals. Once
         that's done, write the rest.

     *)
    Print base_ltype.

    

    (* special structure for the construction of output lists; they must consist
    only of cons and nil, and are not allowed to contain reads from lists (since
    in the bedrock2 translation, this would mean reading from memory, and the
    proofs want to assume that all memory reads happen before any memory
    writes). *)
    Inductive valid_inner_expr
      : forall {t},
        bool (* require expression to be enclosed by casts? (require_casts = rc) *) ->
        bool (* memory reads allowed? (reads_allowed = ra) *) ->
        @API.expr (fun _ => unit) t -> Prop :=
    | valid_inner_cast1 :
        forall (rc ra : bool) r x,
          valid_inner_expr false ra x ->
          range_good r = true ->
          valid_inner_expr (t:=type_Z) rc ra
                           (expr.App
                              (expr.App (expr.Ident ident.Z_cast)
                                        (expr.Ident (ident.Literal (t:=base.type.zrange) r))) x)
    | valid_inner_cast2 :
        forall (rc ra : bool) r1 r2 x,
          valid_inner_expr false ra x ->
          range_good r1 = true ->
          range_good r2 = true ->
          valid_inner_expr (t:=type_ZZ) rc ra
                           (expr.App
                              (expr.App (expr.Ident ident.Z_cast2)
                                        (expr.App
                                           (expr.App
                                              (expr.Ident ident.pair)
                                              (expr.Ident (ident.Literal (t:=base.type.zrange) r1)))
                                           (expr.Ident (ident.Literal (t:=base.type.zrange) r2)))) x)
    | valid_inner_literalz :
        forall rc ra z,
          (* either bounded or casts not required *)
          (is_bounded_by_bool z max_range || negb rc = true)%bool ->
          valid_inner_expr (t:=type_Z) rc ra (expr.Ident (ident.Literal (t:=base.type.Z) z))
    | valid_inner_literalnat :
        forall rc ra n,
          (* either bounded or casts not required *)
          (is_bounded_by_bool (Z.of_nat n) max_range || negb rc = true)%bool ->
          valid_inner_expr (t:=type_nat) rc ra (expr.Ident (ident.Literal (t:=base.type.nat) n))
    | valid_inner_add :
        forall ra x y,
          valid_inner_expr true ra x ->
          valid_inner_expr true ra y ->
          valid_inner_expr false ra (expr.App (expr.App (expr.Ident ident.Z_add) x) y)
    (* TODO: need many more cases here, one for each in translate_inner_expr  *)
    | valid_inner_nth_default :
        forall rc d l i,
          valid_inner_expr false true l ->
          (* index fits in bounds *)
          is_bounded_by_bool (Z.of_nat i) max_range = true ->
          (* index fits in list *)
          
          valid_inner_expr
            (t:=type_listZ)
            rc (* lists get a pass on casts *)
            true (* lists involve memory reads *)
            (expr.App (expr.App (expr.App (expr.Ident ident.List_nth_default) d) l)
            (expr.Ident (ident.Literal i)))
        
    .
    (*
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
        end. *)
    Inductive valid_list : @API.expr (fun _ => unit) type_listZ -> Prop :=
    | valid_cons :
        forall x l,
          valid_inner_expr true x ->
          valid_list l ->
          valid_list
            (expr.App
               (expr.App
                  (expr.Ident
                     (ident.cons (t:=base.type.type_base base.type.Z))) x) l)
    | valid_nil :
        valid_list (expr.Ident (ident.nil (t:=base.type.type_base base.type.Z)))
    .

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
    | valid_outlist : forall l, valid_list l -> valid_expr l
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
      Array.array scalar size start (map Interface.word.of_Z xs) mem.

    (* relation that states whether a fiat-crypto value and a bedrock2 value are
       equivalent in a given bedrock2 context *)
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

    Fixpoint varname_set {t} : base_ltype t -> PropSet.set Syntax.varname :=
      match t with
      | base.type.prod a b =>
        fun x => PropSet.union (varname_set (fst x)) (varname_set (snd x))
      | _ => fun x => PropSet.singleton_set x
      end.

    Fixpoint context_list_equiv {var1}
             (G : list {t : API.type & (var1 t * API.interp_type t * ltype t)%type})
             (locals : Interface.map.rep (map:=Semantics.locals)) {struct G}
      : Interface.map.rep (map:=Semantics.mem) -> Prop :=
      match G with
      | [] => fun _ => True
      | existT (type.base b) (w, x, y) :: G' =>
        (* This is not a separation-logic condition because the memory cannot
        change (we don't allow writing to memory except as the very last step,
        after all reads) and we want the values of locals to be able to read
        from the same sections of memory. *)
        fun mem =>
          equivalent x (rtype_of_ltype y) locals mem
          /\ (exists prev_locals,
                 Interface.map.only_differ prev_locals (varname_set y) locals
                 /\ context_list_equiv G' prev_locals mem)
      | existT (type.arrow _ _) _ :: G' => fun _ => False (* no functions allowed *)
      end.

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
          context_list_equiv G locals mem ->
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
               /\ sep (equivalent (API.interp e2) (rtype_of_ltype (snd gr)) locals')
                      R mem').
    Admitted.

    About varname_set.

    Lemma assign_correct {t} :
      forall (x : base.interp t)
             (lhs : base_ltype t) (rhs : base_rtype t)
             (tr : Semantics.trace)
             (mem locals : Interface.map.rep)
             (R : Interface.map.rep -> Prop),
        (* rhs == x *)
        equivalent x rhs locals mem ->
        WeakestPrecondition.cmd
          call (assign lhs rhs)
          tr mem locals
          (fun tr' mem' locals' =>
             tr = tr'
             (* assign never stores anything -- mem unchanged *)
             /\ mem = mem'
             (* new locals only differ in the values of LHS variables *)
             /\ Interface.map.only_differ locals (varname_set lhs) locals'
             (* evaluating lhs == x *)
             /\ sep (equivalent x (rtype_of_ltype lhs) locals') R mem').
    Admitted.

    Lemma translate_inner_expr_correct {t}
          (* three exprs, representing the same Expr with different vars *)
          (e1 : @API.expr (fun _ => unit) (type.base t))
          (e2 : @API.expr API.interp_type (type.base t))
          (e3 : @API.expr ltype (type.base t))
          (require_cast : bool) :
      (* e1 is a valid input to translate_carries_correct *)
      valid_inner_expr require_cast e1 ->
      forall G mem locals,
        wf3 G e1 e2 e3 ->
        let out := translate_inner_expr require_cast e3 in
        context_list_equiv G locals mem ->
        equivalent (API.interp e2) out locals mem.
    Admitted.

    (* TODO: see if there's a bedrock2 lemma that proves this *)
    Lemma sep_indep {k v}
          {map : Interface.map.map k v}
          a b m :
      sep (map:=map) (fun _ => a) b m <-> a /\ sep (fun _ => True) b m.
    Proof.
     cbv [sep]; split; intros; cleanup.
     { split; [ assumption | ].
        do 2 eexists. repeat (split; try eassumption). }
      { do 2 eexists. repeat (split; try eassumption). }
    Qed.

    (* if a list appears in the type, the variable holding the location where
       the list head should go actually exists in the local context and maps to
       a location in memory. *)
    Fixpoint lists_ok {t}
             (locals : Interface.map.rep (map:=Semantics.locals))
      : base_ltype t ->
        base.interp t -> (* get lengths of lists from fiat-crypto compiler output *)
        Interface.map.rep (map:=Semantics.mem) ->
        Prop :=
      match t with
      | base.type.prod a b =>
        fun x r =>
          sep (lists_ok locals (fst x) (fst r))
              (lists_ok locals (snd x) (snd r))
      | base.type.list (base.type.type_base base.type.Z) =>
        fun x r =>
          Lift1Prop.ex1
            (fun old_data =>
               Lift1Prop.ex1
                 (fun loc =>
                    sep (emp (length old_data = length r
                              /\ WeakestPrecondition.get locals x (eq loc)))
                        (zarray loc old_data)))
    | _ => fun _ _ _ => True
      end.

    (* TODO : move *)
    Lemma disjoint_union {E} s1 s2 s3 :
      @PropSet.disjoint E (PropSet.union s1 s2) s3 <->
      PropSet.disjoint s1 s3 /\ PropSet.disjoint s2 s3.
    Proof.
      cbv [PropSet.disjoint PropSet.union PropSet.elem_of]; split.
      { intro H; split; intro x; specialize (H x); tauto. }
      { intros [H1 H2] x. specialize (H1 x). specialize (H2 x). tauto. } 
    Qed.

    (* TODO : move *)
    Lemma disjoint_singleton {E} {eqb : E -> E -> bool} {dec : @Decidable.EqDecider eqb} :
          forall e1 e2,
            e1 <> e2 ->
            @PropSet.disjoint E (PropSet.singleton_set e1) (PropSet.singleton_set e2).
    Proof.
      cbv [PropSet.disjoint PropSet.singleton_set PropSet.elem_of].
      intros e1 e2 ? x; destruct (dec e1 x); subst; try tauto.
      right; congruence.
    Qed.

    (* TODO : move *)
    Lemma disjoint_comm {E} s1 s2 :
      @PropSet.disjoint E s1 s2 <-> PropSet.disjoint s2 s1.
    Proof.
      cbv [PropSet.disjoint PropSet.elem_of]; split;
        intros H x; specialize (H x); tauto.
    Qed.

    (* if two maps only differ on some keys, and we get a key that is not in the
    differing set, then any proposition that holds on one result should hold on
    the other. *)
    Lemma get_untouched m1 m2 ks k P :
      Interface.map.only_differ m2 ks m1 ->
      PropSet.disjoint (PropSet.singleton_set k) ks ->
      WeakestPrecondition.get m1 k P <-> WeakestPrecondition.get m2 k P.
    Admitted.

    Lemma get_put m k v :
      WeakestPrecondition.get (Interface.map.put m k v) k (eq v).
    Proof.
      cbv [WeakestPrecondition.get]; exists v; split;
        rewrite ?Interface.map.get_put_same; reflexivity.
    Qed.

    Lemma lists_ok_step {t} locals locals' ks mem retnames ret :
      Interface.map.only_differ locals ks locals' ->
      PropSet.disjoint (varname_set retnames) ks ->
      forall R,
        sep (lists_ok locals retnames ret) R mem ->
        sep (@lists_ok t locals' retnames ret) R mem.
    Proof.
      induction t; cbn [lists_ok varname_set]; intros;
        break_match; try tauto; [ | ].
      { apply sep_assoc.
        match goal with H : _ |- _ =>
                        apply disjoint_union in H; cleanup end.
        apply IHt1; [ solve [eauto] .. | ].
        apply sep_comm, sep_assoc.
        apply IHt2; [ solve [eauto] .. | ].
        apply sep_assoc, sep_comm, sep_assoc.
        assumption. }
      { repeat match goal with
               | H : sep (Lift1Prop.ex1 _) _ _ |- _ =>
                 apply sep_ex1_l in H; destruct H
               | |- sep (Lift1Prop.ex1 _) _ _ =>
                 apply sep_ex1_l; eexists; [ ]
               end.
        eapply Proper_sep_iff1; [ intro | reflexivity | eassumption ].
        cbv beta. rewrite !sep_emp_l.
        apply and_iff_compat_r.
        apply and_iff_compat_l.
        eapply get_untouched; eauto. }
    Qed.

    (* TODO : remove if unused
    Local Ltac simpl_sep :=
      let t := ltac:(solve [eapply Semantics.mem_ok]) in
      match goal with
      | _ => progress cleanup
      | H : Lift1Prop.ex1 _ _ |- _ => destruct H
      | H : sep (fun mem => sep _ _ mem) _ _ |- _ =>
        apply @sep_assoc in H; [ | t]
      | H : sep (sep _ _) _ _ |- _ =>
        apply @sep_assoc in H; [ | t]
      | H : sep (emp _) _ _ |- _ =>
        apply @sep_emp_l in H; [ cleanup | t]
      | H : sep (Lift1Prop.ex1 _) _ _ |- _ =>
        apply @sep_ex1_l in H; [ | t]
      | H : sep (fun _ => True) _ _ |- _ =>
        (* N.B. must go *above* sep_indep to avoid infinite loop *)
        apply @sep_comm in H; [ | t]
      | H : sep (fun _ => ?x) _ _ |- _ =>
        apply @sep_indep in H
      | |- sep (fun mem => sep _ _ mem) _ _ =>
        apply @sep_assoc; [t | ]
      | |- sep (sep _ _) _ _ =>
        apply @sep_assoc; [t | ]
      | |- sep (emp _) _ _ =>
        apply @sep_emp_l; [t | ]
      | |- sep (Lift1Prop.ex1 _) _ _  =>
        apply @sep_ex1_l ; [t | ]
      | |- sep (fun _ => True) _ _ =>
        (* N.B. must go *above* sep_indep to avoid infinite loop *)
        apply @sep_comm; [ t | ]
      | |- sep (fun _ => ?x) _ _ =>
        apply @sep_indep
      | |- _ /\ _ => split; [ solve [eauto] | ]
      | |- Lift1Prop.ex1 _ _ => eexists
      end. *)

    Lemma translate_lhs_mono t :
      forall nextn, (nextn <= fst (translate_lhs t nextn))%nat.
    Proof.
      induction t; cbn [translate_lhs fst]; eauto with lia; [ ].
      intros. etransitivity; [ | apply IHt2]. eauto.
    Qed.

    Lemma disjoint_translate_lhs s t :
      forall nextn,
        (forall n : nat,
            (nextn <= n)%nat ->
            PropSet.disjoint (PropSet.singleton_set (varname_gen n)) s) ->
        PropSet.disjoint (varname_set (snd (translate_lhs t nextn))) s.
    Proof.
      induction t; cbn [translate_lhs varname_set fst snd]; eauto; [ ].
      intros nextn Hdisj. pose proof (translate_lhs_mono t1 nextn).
      apply disjoint_union; split; eauto with lia.
    Qed.

    Lemma translate_list_correct
          (* three exprs, representing the same Expr with different vars *)
          (e1 : @API.expr (fun _ => unit) type_listZ)
          (e2 : @API.expr API.interp_type type_listZ)
          (e3 : @API.expr ltype type_listZ)
          (* e1 is valid input to translate_list *)
          (e1_valid : valid_list e1)
          (* context list *)
          (G : list _) :
      (* exprs are all related *)
      wf3 G e1 e2 e3 ->
      forall (locals : Interface.map.rep)
             (dst : Syntax.varname)
             (nextn : nat),
        (* ret := fiat-crypto interpretation of e2 *)
        let ret : list Z := API.interp e2 in
        (* out := translation output for e3 *)
        let out := translate_list e3 nextn dst in
        (* dst is not a variable we could accidentally overwrite *)
        (forall n,
            (nextn <= n)%nat ->
            varname_gen n <> dst) ->
        forall (tr : Semantics.trace)
               (mem : Interface.map.rep)
               (R : Interface.map.rep -> Prop),
          (* dst contains a valid memory location at which there exists a list
             of the right length *)
          (exists addr old_data,
              length old_data = length ret
              /\ WeakestPrecondition.get locals dst (eq addr)
              /\ sep (zarray addr old_data) R mem) ->
          (* outputs are equivalent *)
          WeakestPrecondition.cmd
            call (snd out) tr mem locals
            (fun tr' mem' locals' =>
               tr = tr'
               /\ sep (equivalent (t:=base.type.list (base.type.type_base base.type.Z))
                                  ret (rtype_of_ltype (t:=base.type.type_base base.type.Z) dst)
                                  locals') R mem').
    Proof.
      revert e2 e3 G.
      induction e1_valid; inversion 1; cbv zeta in *; intros.
      all:hammer_wf.
      { (* cons *) 
        repeat match goal with
               | H : wf3 _ _ _ _ |- _ =>
                 match type of H with context [Compilers.ident.cons] =>
                                      inversion H; hammer_wf
                 end
               end.

        cbn [translate_list].
        cbn [expr.interp Compilers.ident_interp] in *.
        cbv [zarray] in *. cbn [array map] in *.
        cleanup.

        (* simplify bedrock2 step *)
        cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].

        (* read from variable holding memory location *)
        cbn [WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body].
        eexists; split; [ eassumption | ].

        (* PROBLEM : inner_expr wants context_list_equiv, and we might even need
        it for reading return variables. Find a way to make this irrespective of
        memory! *)

        (* ideas:

        A) separate compiler into three phases: one reads all the memory from
        input, compiling to an rtype that needs lists of exprs for lists, and
        another does the construction of the output list at the end. Cons:
        restricts how to read from input, kind of complex.

        B) make just the output part special; read from all the input first 

        C) make a special valid_inner_expr for the construction of output lists
        that doesn't allow reads from lists


        C proof structure:
        translate_func_correct
          -> translate_expr_correct (has context_list_equiv precondition)
             -> translate_inner_expr_correct (has context_list_equiv precondition IFF memory reads are allowed)
             -> translate_list_correct (no context_list_equiv precondition)
                -> translate_inner_expr_correct (memory reads not allowed)

        *)
        
        (* inner_expr creates a valid expression *)
        match goal with
        | H : wf3 ?G ?x1 ?x2 ?x3 |- context [translate_inner_expr ?rc ?x3] =>
          pose proof
               (translate_inner_expr_correct
                  x1 x2 x3 rc
                  ltac:(assumption) G) end.
        cbv [equivalent Lift1Prop.ex1] in H4.
        cbv [context_list_equiv] in H4.
        apply H4.
        

        ltac:(eassumption)) as X;
            cbv [equivalent Lift1Prop.ex1] in X
        end.
        cleanup.
        eexists; split; [ eassumption | ].

        (* store expression at head of list *)
        eapply store_word_of_sep; [ | ].
        1: solve [match goal with H : _ |- _ => apply H end].

        intros.
        (* now we need to set the new destination to retnames+1 *)
        eexists. split.
        { eapply WeakestPreconditionProperties.Proper_get;
            [ repeat intro | eassumption ].
          subst; reflexivity. }
        { cbv [coqutil.dlet.dlet].
          cbn [rtype_of_ltype equivalent varname_set] in *.
          cbv [zarray] in *. cbn [array map] in *.

          eapply WeakestPreconditionProperties.Proper_cmd;
            [ eapply Proper_call | repeat intro | ].
          
          2: { eapply IHe1_valid; try eassumption;
               clear IHe1_valid.
               { intros. apply disjoint_singleton.
                 rewrite varname_gen_unique. lia. }
               {
                 Search m.
                 (* we know that context_list_equiv holds on locals/mem/G, now need
                it for (locals ++ (vg n, x0+1))/m/G

                we know almost nothing about m, just have a sep-logic condition
                ideally should have m == mem...
                for mem we have a sep-logic condition that looks similar to the one for m. does that prove mem = m?
                m is introduced with store_word_of_sep
                maybe need to add context_list_equiv to the seplogic condition?
                  *)
                 admit. }
               { apply sep_ex1_l.
                 eexists.
                 apply sep_assoc.
                 apply sep_emp_l. split; [ solve [apply get_put] | ].
                 match goal with
                 | H : sep _ (sep ?p _) ?m |- sep ?p _ ?m =>
                   apply sep_comm, sep_assoc in H; apply H
                 end. } }
          { intros; cleanup; subst; tauto. } }
        apply Wea
        eapply IHe1_valid.
    Admitted.
    
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
             (retnames : base_ltype t')
             (nextn : nat),
        (* ret := fiat-crypto interpretation of e2 *)
        let ret : base.interp t' := API.interp e2 in
        (* out := translation output for e3 *)
        let out := translate_expr e3 nextn retnames in
        (* retnames don't contain variables we could accidentally overwrite *)
        (forall n,
            (nextn <= n)%nat ->
            PropSet.disjoint
              (PropSet.singleton_set (varname_gen n))
              (varname_set retnames)) ->
        forall (tr : Semantics.trace)
               (mem : Interface.map.rep)
               (R : Interface.map.rep -> Prop),
          (* contexts are equivalent; for every variable in the context list G,
             the fiat-crypto and bedrock2 results match *)
          context_list_equiv G locals mem ->
          (* any lists in retnames are valid *)
          sep (lists_ok locals retnames ret) R mem ->
          (* executing translation output is equivalent to interpreting e *)
          WeakestPrecondition.cmd
            call (snd out) tr mem locals
            (fun tr' mem' locals' =>
               tr = tr'
               /\ sep (equivalent ret (rtype_of_ltype retnames) locals') R mem').
    Proof.
      revert e2 e3 G.
      subst t.
      induction e1_valid;
        try match goal with
            | H : valid_list _ |- _ => inversion H; subst
            end;
      inversion 1; cbv zeta in *; intros.
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
        2 : eapply translate_carries_correct; try eassumption.

        (* use inductive hypothesis *)
        cbn [translate_lhs] in *; cleanup.
        eapply WeakestPreconditionProperties.Proper_cmd;
          [ eapply Proper_call | repeat intro | ].
        2: { eapply IHe1_valid with (R:=R); try eassumption;
             clear IHe1_valid;
             try solve [eauto with lia];
             try match goal with
                 | H : (forall v1 v2 v3,
                           wf3  _ (_ v1) (_ v2) (_ v3)),
                       H' : sep (equivalent ?x _ _) _ _ |- _ =>
                   apply H with (v2:=x)
                 end;
             [ | solve [eapply lists_ok_step; subst; eauto; [ ];
                        apply disjoint_comm, disjoint_union; eauto ] ].
             cbn [context_list_equiv equivalent] in *.
             split;
               [ solve [
                     apply sep_emp_True_r;
                     match goal with H : sep _ _ _ |- _ =>
                                        eapply H end ] | ].
             subst; eexists; split; eauto. }
      { intros; cleanup; subst; tauto. } }
    { (* non-carry let-in *)
      (* simplify one translation step *)
      cbn [translate_expr].
      erewrite translate_carries_None by eassumption.
      cleanup.

      (* assert that translate_lhs is well-behaved *)
      match goal with
        |- context [translate_lhs ?t ?n] =>
        pose proof (translate_lhs_mono t n)
      end.
      

      (* simplify fiat-crypto step *)
      intros; cbn [expr.interp type.app_curried].
      cbv [Rewriter.Util.LetIn.Let_In]. cleanup.

      (* simplify bedrock2 step *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      (* N.B. putting below line in the [ | | ] above makes eassumption fail *)
      2 : eapply assign_correct; try eassumption; [ ];
        eapply translate_inner_expr_correct; eassumption.

      (* use inductive hypothesis *)
      cbn [translate_lhs] in *; cleanup.
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      2: { eapply IHe1_valid with (R:=R); try eassumption;
             clear IHe1_valid;
             try solve [eauto with lia];
             try match goal with
                 | H : (forall v1 v2 v3,
                           wf3  _ (_ v1) (_ v2) (_ v3)),
                       H' : sep (equivalent ?x _ _) _ _ |- _ =>
                   apply H with (v2:=x)
                 end;
             [ | solve [eapply lists_ok_step; subst; eauto; [ ];
                        apply disjoint_comm, disjoint_translate_lhs; eauto ] ].
           cbn [context_list_equiv equivalent] in *.
             split;
             [ solve [
                   apply sep_emp_True_r;
                   match goal with H : sep _ _ _ |- _ =>
                                   eapply H end ] | ].
           subst; eexists; split; eauto. }
      { intros; cleanup; subst; tauto. } }
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

      Search translate_list.
      eapply translate_list_correct.
      2:eassumption.
      1:eassumption.
      1: admit. (* make disjoint_singleton iff *)
      {
      cbn [lists_ok] in *.
      cbv [zarray] in *. cbn [array map] in *.
      cleanup.

      repeat match goal with
             | H : sep (Lift1Prop.ex1 _) _ _ |- _ =>
               apply sep_ex1_l in H; destruct H
             | H : sep (sep _ _) _ _ |- _ =>
               apply sep_assoc in H
             | H : sep (fun mem => sep _ _ mem) _ _ |- _ =>
               apply sep_assoc in H
             | H : sep (emp _) _ _ |- _ =>
               apply sep_emp_l in H; cleanup
             end.

      do 2 eexists; split; eauto. }

      repeat match goal with
             | H : wf3 _ _ _ _ |- _ =>
               match type of H with context [Compilers.ident.cons] =>
                                    inversion H; hammer_wf
               end
             end.
        
      cbn [type.for_each_lhs_of_arrow
             type.app_curried type.final_codomain base_ltype] in *.

      cbn [expr.interp Compilers.ident_interp] in *.
      cbn [lists_ok] in *.
      cbv [zarray] in *. cbn [array map] in *.
      cleanup.

      repeat match goal with
             | H : sep (Lift1Prop.ex1 _) _ _ |- _ =>
               apply sep_ex1_l in H; destruct H
             | H : sep (sep _ _) _ _ |- _ =>
               apply sep_assoc in H
             | H : sep (fun mem => sep _ _ mem) _ _ |- _ =>
               apply sep_assoc in H
             | H : sep (emp _) _ _ |- _ =>
               apply sep_emp_l in H; cleanup
             end.

      (* simplify bedrock2 step *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].

      (* read from variable holding memory location *)
      cbn [WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists; split; [ eassumption | ].

      (* inner_expr creates a valid expression *)
      match goal with
      | H : wf3 ?G ?x1 ?x2 ?x3 |- context [translate_inner_expr ?rc ?x3] =>
        pose proof
             (translate_inner_expr_correct
                x1 x2 x3 rc
                ltac:(assumption) G _ _ H ltac:(eassumption)) as X;
          cbv [equivalent Lift1Prop.ex1] in X
      end.
      cleanup.
      eexists; split; [ eassumption | ].

      (* store expression at head of list *)
      eapply store_word_of_sep; [ | ].
      1: solve [match goal with H : _ |- _ => apply H end].

      intros.
      (* now we need to set the new destination to retnames+1 *)
      eexists. split.
      { eapply WeakestPreconditionProperties.Proper_get;
          [ repeat intro | eassumption ].
        subst; reflexivity. }
      { cbv [coqutil.dlet.dlet].
        cbn [rtype_of_ltype equivalent varname_set] in *.
        cbv [zarray] in *. cbn [array map] in *.

      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      
      2: { eapply IHe1_valid; try eassumption;
           clear IHe1_valid.
           { intros. apply disjoint_singleton.
             rewrite varname_gen_unique. lia. }
           {
             Search m.
             (* we know that context_list_equiv holds on locals/mem/G, now need
                it for (locals ++ (vg n, x0+1))/m/G

                we know almost nothing about m, just have a sep-logic condition
                ideally should have m == mem...
                for mem we have a sep-logic condition that looks similar to the one for m. does that prove mem = m?
                m is introduced with store_word_of_sep
                maybe need to add context_list_equiv to the seplogic condition?
              *)
             admit. }
           { apply sep_ex1_l.
             eexists.
             apply sep_assoc.
             apply sep_emp_l. split; [ solve [apply get_put] | ].
             match goal with
               | H : sep _ (sep ?p _) ?m |- sep ?p _ ?m =>
                 apply sep_comm, sep_assoc in H; apply H
             end. } }
      { intros; cleanup; subst; tauto. } }
        apply Wea
        eapply IHe1_valid.
    Qed.

    Lemma translate_expr_correct {t} (* (e : API.Expr t) *) :
      (* e is valid input to translate_expr *)
      forall e : API.Expr t,
        valid_expr (e _) ->
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
*)
End Compiler.
