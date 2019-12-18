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
            (fst recl, Syntax.cmd.seq (assign (t:=base.type.type_base base.type.Z) n x) (snd recl))
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

  Section Proofs.
    Context {p : parameters} {p_ok : @ok p}.

    Local Instance sem_ok : Semantics.parameters_ok semantics
      := semantics_ok.
    Local Instance mem_ok : Interface.map.ok Semantics.mem
      := Semantics.mem_ok.
    Local Instance varname_eqb_spec x y : BoolSpec _ _ _
      := Semantics.varname_eqb_spec x y.

    (* TODO : fill these in *)
    Axiom valid_carry_expr : forall {t}, @API.expr (fun _ => unit) t -> Prop.

    Inductive valid_inner_expr
      : forall {t},
        bool (* require_casts *) ->
        @API.expr (fun _ => unit) t -> Prop :=
    | valid_inner_cast1 :
        forall rc r x,
          valid_inner_expr false x ->
          range_good r = true ->
          valid_inner_expr (t:=type_Z) rc
                           (expr.App
                              (expr.App (expr.Ident ident.Z_cast)
                                        (expr.Ident (ident.Literal (t:=base.type.zrange) r))) x)
    | valid_inner_cast2 :
        forall (rc : bool) r1 r2 x,
          valid_inner_expr false x ->
          range_good r1 = true ->
          range_good r2 = true ->
          valid_inner_expr (t:=type_ZZ) rc
                           (expr.App
                              (expr.App (expr.Ident ident.Z_cast2)
                                        (expr.App
                                           (expr.App
                                              (expr.Ident ident.pair)
                                              (expr.Ident (ident.Literal (t:=base.type.zrange) r1)))
                                           (expr.Ident (ident.Literal (t:=base.type.zrange) r2)))) x)
    | valid_inner_literalz :
        forall rc z,
          (* either bounded or casts not required *)
          (is_bounded_by_bool z max_range || negb rc = true)%bool ->
          valid_inner_expr (t:=type_Z) rc (expr.Ident (ident.Literal (t:=base.type.Z) z))
    | valid_inner_add :
        forall x y,
          valid_inner_expr true x ->
          valid_inner_expr true y ->
          valid_inner_expr false (expr.App (expr.App (expr.Ident ident.Z_add) x) y)
    | valid_inner_nth_default :
        forall rc d l i,
          valid_inner_expr true d ->
          valid_inner_expr
            (t:=type_Z)
            rc (* casts not required, since a list of vars must be already cast *)
            (expr.App (expr.App (expr.App (expr.Ident ident.List_nth_default) d)
                                (expr.Var (t:=type_listZ) l))
            (expr.Ident (ident.Literal i)))
    | valid_inner_var :
        forall t v, valid_inner_expr (t:=type.base t) false (expr.Var v)
    (* TODO: need many more cases here, one for each in translate_inner_expr --
       this is just a small set to test proof strategies *)
    .

    (* Inductive version: *)
    Inductive valid_expr : forall {t}, @API.expr (fun _ => unit) (type.base t) -> Prop :=
    | valid_LetIn_carry :
        forall {b} x f,
          valid_carry_expr x -> valid_expr (f tt) ->
          valid_expr (expr.LetIn (A:=type_ZZ) (B:=type.base b) x f)
    (* N.B. LetIn is split into cases so that only pairs of type_base and type_base are
      allowed; this is primarily because we don't want lists on the LHS *)
    | valid_LetIn_prod :
        forall {a b c} x f,
          valid_inner_expr true x -> valid_expr (f tt) ->
          valid_expr (expr.LetIn
                        (A:=type.base (base.type.prod
                                         (base.type.type_base a) (base.type.type_base b)))
                        (B:=type.base c) x f)
    | valid_LetIn_base :
        forall {a b} x f,
          valid_inner_expr true x -> valid_expr (f tt) ->
          valid_expr (expr.LetIn (A:=type.base (base.type.type_base a)) (B:=type.base b) x f)
    | valid_cons :
        forall x l,
          valid_inner_expr true x ->
          valid_expr l ->
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
        forall {b} e, valid_expr e -> valid_func (t:=type.base b) e
    .

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
             (locals : Interface.map.rep (map:=Semantics.locals))
      : base.interp t -> (* fiat-crypto value *)
        base_rtype t -> (* bedrock2 value *)
        Prop :=
      match t with
      (* product case *)
      | base.type.prod a b =>
        fun (x : base.interp a * base.interp b)
            (y : base_rtype a * base_rtype b) =>
          equivalent locals (fst x) (fst y)
          /\ equivalent locals (snd x) (snd y)
      (* list case -- only list Z allowed *)
      | base.type.list t2 =>
        (match t2 as t0 return (base.interp t0 -> base_rtype t0 -> Prop) ->
                               base.interp (base.type.list t0) ->
                               base_rtype (base.type.list t0) -> Prop with
         | base.type.type_base base.type.Z =>
           fun eq (x : list Z) (y : list Syntax.expr.expr) =>
             length x = length y
             /\ Forall2 eq x y
         | _ => fun _ _ _ => False
         end) (equivalent (t:=t2) locals)
      (* base type case -- only Z allowed *)
      | base.type.type_base base.type.Z =>
        fun (x : Z) (y : Syntax.expr.expr) =>
          forall mem, (* not allowed to read *)
            WeakestPrecondition.expr mem locals y
                                     (fun w => Interface.word.unsigned w = x)
      | _ => fun _ _ => False
      end.

    Fixpoint varname_set {t} : base_ltype t -> PropSet.set Syntax.varname :=
      match t with
      | base.type.prod a b =>
        fun x => PropSet.union (varname_set (fst x)) (varname_set (snd x))
      | base.type.list (base.type.type_base base.type.Z) =>
        PropSet.of_list
      | _ => fun x => PropSet.singleton_set x
      end.

    Definition varname_not_in_context {var1}
               (v : Syntax.varname)
               (x : {t : API.type & (var1 t * API.interp_type t * ltype t)%type})
      : Prop :=
      match x with
      | existT (type.base b) (w, x, y) =>
        ~ (varname_set y) v
      | existT (type.arrow _ _) _ => False (* no functions allowed *)
      end.

    Definition equivalent_in_context {var1}
               (locals : Interface.map.rep (map:=Semantics.locals))
               (x : {t : API.type & (var1 t * API.interp_type t * ltype t)%type})
      : Prop :=
      match x with
      | existT (type.base b) (w, x, y) =>
        equivalent locals x (rtype_of_ltype y)
      | existT (type.arrow _ _) _ => False (* no functions allowed *)
      end.
   
    Definition context_list_equiv {var1}
             (G : list {t : API.type & (var1 t * API.interp_type t * ltype t)%type})
             (locals : Interface.map.rep (map:=Semantics.locals))
      : Prop :=
      Forall (equivalent_in_context locals) G.


    Lemma equivalent_not_varname_set {t}
          locals1 locals2 vset (varnames : base_ltype t) x :
      Interface.map.only_differ locals1 vset locals2 ->
      (forall v : Syntax.varname, vset v -> ~ varname_set varnames v) ->
      equivalent locals1 x (rtype_of_ltype varnames) ->
      equivalent locals2 x (rtype_of_ltype varnames).
    Proof.
      (* TODO : clean up this proof *)
      intros Hdiffer Hexcl.
      induction t; cbn [rtype_of_ltype varname_set equivalent fst snd]; intros;
        BreakMatch.break_match;
        DestructHead.destruct_head'_and;
        try tauto;
        try solve [
              (* solves all the simple cases where ltype is a varname *)
              specialize (Hexcl varnames); intros;
              destruct (Hdiffer varnames) as [? | Heq];
              cbv [PropSet.singleton_set
                     PropSet.elem_of
                     WeakestPrecondition.expr
                     WeakestPrecondition.expr_body
                     varname_set
                     WeakestPrecondition.get ] in *;
              [ tauto | rewrite <-Heq; eauto ] ].
      { (* prod case *)
        cbn [varname_set] in Hexcl; cbv [PropSet.union PropSet.elem_of] in Hexcl.
        split; [ apply IHt1 | apply IHt2]; auto;
          let x := fresh in
          let y := fresh in
          intros x y; specialize (Hexcl x y); tauto. }
      { (* list case *)
        split; [ assumption | ].
        cbn [varname_set] in Hexcl; cbv [PropSet.union PropSet.of_list] in Hexcl.
        cbn [Language.Compilers.base.interp Compilers.base_interp base_rtype] in *. (* simplify types *)
        rewrite ListUtil.Forall2_forall_iff with (d1:=0) (d2:=Syntax.expr.literal 0) by auto.
        match goal with H : _ |- _ =>
                        intros i Hi;
                          rewrite ListUtil.Forall2_forall_iff
                          with (d1:=0) (d2:=Syntax.expr.literal 0) in H by auto;
                          specialize (H i Hi); revert H
        end.
        rewrite map_length in *.
        apply ListUtil.nth_default_preserves_properties_length_dep; try lia.
        intros.
        assert Syntax.varname as d by (destruct varnames; auto; cbn [length] in *; omega).
        erewrite !ListUtil.map_nth_default with (x:=d) in * by lia.
        apply IHt; eauto.
        cbv [varname_set PropSet.singleton_set].
        let x := fresh in
        let y := fresh in
        intros x y; specialize (Hexcl x y).
        apply ListUtil.nth_default_preserves_properties_length_dep; try lia.
        intros.
        match goal with
          |- ?x <> ?y => destruct (Semantics.varname_eqb_spec x y); subst
        end; tauto. }
    Qed.

    Lemma equivalent_not_in_context {var1} locals1 locals2 vset x :
      Interface.map.only_differ locals1 vset locals2 ->
      (forall v, vset v -> varname_not_in_context v x) ->
      equivalent_in_context (var1:=var1) locals1 x ->
      equivalent_in_context locals2 x.
    Proof.
      intros; cbv [equivalent_in_context varname_not_in_context] in *.
      destruct x as [x [ [? ?] ?] ]; destruct x; [ | tauto ].
      eauto using equivalent_not_varname_set.
    Qed.

    Lemma equivalent_not_in_context_forall {var1} locals1 locals2 vset G :
      Interface.map.only_differ locals1 vset locals2 ->
      (forall v, vset v -> Forall (varname_not_in_context v) G) ->
      Forall (equivalent_in_context (var1:=var1) locals1) G ->
      Forall (equivalent_in_context locals2) G.
    Proof.
      intros Hdiffer Hexcl; induction G; intros; constructor;
        match goal with
          | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end.
      { eapply equivalent_not_in_context; eauto.
        intros x y; specialize (Hexcl x y); inversion Hexcl; auto. }
      { apply IHG; auto.
        intros x y; specialize (Hexcl x y); inversion Hexcl; auto. }
    Qed.

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
          context_list_equiv G locals ->
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
               /\ sep (emp (equivalent locals' (API.interp e2) (rtype_of_ltype (snd gr))))
                      R mem').
    Admitted.

    Lemma assign_correct {t} :
      forall (x : base.interp t)
             (lhs : base_ltype t) (rhs : base_rtype t)
             (tr : Semantics.trace)
             (mem locals : Interface.map.rep)
             (R : Interface.map.rep -> Prop),
        (* rhs == x *)
        equivalent locals x rhs ->
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
             /\ sep (emp (equivalent locals' x (rtype_of_ltype lhs))) R mem').
    Admitted.

    Lemma translate_inner_expr_correct {t}
          (* three exprs, representing the same Expr with different vars *)
          (e1 : @API.expr (fun _ => unit) (type.base t))
          (e2 : @API.expr API.interp_type (type.base t))
          (e3 : @API.expr ltype (type.base t))
          (require_cast : bool) :
      (* e1 is a valid input to translate_carries_correct *)
      valid_inner_expr require_cast e1 ->
      forall G locals,
        wf3 G e1 e2 e3 ->
        let out := translate_inner_expr require_cast e3 in
        context_list_equiv G locals ->
        equivalent locals (API.interp e2) out.
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
      ~ ks k ->
      WeakestPrecondition.get m1 k P <-> WeakestPrecondition.get m2 k P.
    Admitted.

    Lemma expr_untouched mem1 mem2 l1 l2 vars v P :
      Interface.map.only_differ l2 vars l1 ->
      ~ vars v ->
      WeakestPrecondition.expr mem1 l1 (Syntax.expr.var v) P <->
      WeakestPrecondition.expr mem2 l2 (Syntax.expr.var v) P.
    Proof.
      intros.
      cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body].
      rewrite get_untouched; eauto; reflexivity.
    Qed.

    Lemma get_put m k v :
      WeakestPrecondition.get (Interface.map.put m k v) k (eq v).
    Proof.
      cbv [WeakestPrecondition.get]; exists v; split;
        rewrite ?Interface.map.get_put_same; reflexivity.
    Qed.

    Lemma translate_lhs_mono t :
      forall nextn, (nextn <= fst (translate_lhs t nextn))%nat.
    Proof.
      induction t; cbn [translate_lhs]; break_match; cbn [fst]; eauto with lia; [ ].
      intros; etransitivity; [ | apply IHt2]; eauto.
    Qed.

    Lemma disjoint_translate_lhs s t :
      forall nextn,
        (forall n : nat,
            (nextn <= n)%nat ->
            PropSet.disjoint (PropSet.singleton_set (varname_gen n)) s) ->
        PropSet.disjoint (varname_set (snd (translate_lhs t nextn))) s.
    Proof.
      induction t; cbn [translate_lhs]; break_match; cbn [varname_set fst snd]; eauto; [ | ].
      { intros nextn Hdisj. pose proof (translate_lhs_mono t1 nextn).
        apply disjoint_union; split; eauto with lia. }
      { cbv [PropSet.disjoint PropSet.of_list]; intros.
        tauto. }
    Qed.

    Definition return_variables_valid {t} : base_ltype t -> base.interp t -> Prop :=
      match t with
      | base.type.list (base.type.type_base base.type.Z) =>
        fun retnames ret => length retnames = length ret /\ NoDup retnames
      | _ => fun _ _ => True
      end.

    Definition used_varnames nextn final_nextn : PropSet.set Syntax.varname :=
      fun v => exists n, varname_gen n = v /\ (nextn <= n < final_nextn)%nat.

    Lemma used_varnames_step nextn final_nextn :
      (nextn < final_nextn)%nat ->
      forall v,
        used_varnames nextn final_nextn v <->
        PropSet.union (PropSet.singleton_set (varname_gen nextn))
                      (used_varnames (S nextn) final_nextn) v.
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
        (forall v n,
            varname_set retnames v ->
            (nextn <= n)%nat ->
            varname_gen n <> v) ->
        (* G doesn't contain variables we could accidentally overwrite *)
        (forall n,
            (nextn <= n)%nat ->
            Forall (varname_not_in_context (varname_gen n)) G) ->
        (* G doesn't contain variables that retnames will overwrite *)
        (forall v,
            varname_set retnames v ->
            Forall (varname_not_in_context v) G) ->
        (* if return value is a list, retnames contains enough variables *)
        return_variables_valid retnames ret -> 
        forall (tr : Semantics.trace)
               (mem : Interface.map.rep)
               (R : Interface.map.rep -> Prop),
          (* contexts are equivalent; for every variable in the context list G,
             the fiat-crypto and bedrock2 results match *)
          context_list_equiv G locals ->
          (* executing translation output is equivalent to interpreting e *)
          WeakestPrecondition.cmd
            call (snd out) tr mem locals
            (fun tr' mem' locals' =>
               tr = tr' /\
               mem = mem' /\
               (* locals and locals' only differ on variables that are in the
               return-variable-names list, or in the range between nextn and the
               first output value (which represents the next fresh variable name
               after the function) *)
               Interface.map.only_differ
                 locals
                 (PropSet.union (varname_set retnames)
                                (used_varnames nextn (fst out)))
                 locals' /\
          sep (emp (equivalent locals' ret (rtype_of_ltype retnames))) R mem').
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
        intros; cbn [expr.interp type.app_curried] in *.
        cbv [Rewriter.Util.LetIn.Let_In] in *. cleanup.

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

        2: { eapply IHe1_valid with (R:=R);
             clear IHe1_valid;
             try match goal with H : _ |- _ => solve [apply H] end;
             match goal with H : sep (emp _) _ _ |- _ => apply sep_emp_l in H end;
             cleanup; eauto with lia.

             { (* proof that new context doesn't contain variables that could be
                  overwritten in the future *)
               intros; apply Forall_cons; eauto with lia; [ ].
               cbn [varname_not_in_context varname_set fst snd].
               cbv [PropSet.union PropSet.singleton_set PropSet.elem_of].
               setoid_rewrite varname_gen_unique.
               lia. }
             { (* proof that new context doesn't contain variables that retnames
                  will overwrite *)
               intros; apply Forall_cons; eauto with lia; [ ].
               cbn [varname_not_in_context varname_set fst snd].
               cbv [PropSet.union PropSet.singleton_set PropSet.elem_of].
               match goal with
                 |- ~ (?A \/ ?B) =>
                 assert (~ A /\ ~ B); [split|tauto]
               end; eauto. }
             { (* proof that context_list_equiv continues to hold *)
               cbv [context_list_equiv] in *; apply Forall_cons; eauto; [ ].
               eapply equivalent_not_in_context_forall; eauto.
               cbv [varname_set fst snd PropSet.union PropSet.singleton_set PropSet.elem_of].
               destruct 1; subst; eauto. } }
        { admit. (* TODO *) } }
        (* { intros; cleanup; subst; tauto. } } *)
    { (* let-in (product of base types) *)
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
      intros; cbn [expr.interp type.app_curried] in *.
      cbv [Rewriter.Util.LetIn.Let_In] in *. cleanup.

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
      2: { eapply IHe1_valid with (R:=R);
           clear IHe1_valid;
           try match goal with H : _ |- _ => solve [apply H] end;
           match goal with H : sep (emp _) _ _ |- _ => apply sep_emp_l in H end;
           cleanup; eauto with lia.
             { (* proof that new context doesn't contain variables that could be
                  overwritten in the future *)
               intros; apply Forall_cons; eauto with lia; [ ].
               cbn [varname_not_in_context varname_set fst snd].
               cbv [PropSet.union PropSet.singleton_set PropSet.elem_of].
               setoid_rewrite varname_gen_unique.
               lia. }
             { (* proof that new context doesn't contain variables that retnames
                  will overwrite *)
               intros; apply Forall_cons; eauto with lia; [ ].
               cbn [varname_not_in_context varname_set fst snd].
               cbv [PropSet.union PropSet.singleton_set PropSet.elem_of].
               match goal with
                 |- ~ (?A \/ ?B) =>
                 assert (~ A /\ ~ B); [split|tauto]
               end; eauto. }
           { (* proof that context_list_equiv continues to hold *)
             cbv [context_list_equiv] in *; apply Forall_cons; eauto; [ ].
             eapply equivalent_not_in_context_forall; eauto.
             cbv [varname_set fst snd PropSet.union PropSet.singleton_set PropSet.elem_of].
             destruct 1; subst; eauto. } }
        { admit. (* TODO *) } }
        (* { intros; cleanup; subst; tauto. } } *)
    { (* let-in (base type) *)
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
      intros; cbn [expr.interp type.app_curried] in *.
      cbv [Rewriter.Util.LetIn.Let_In] in *. cleanup.

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
      2: { eapply IHe1_valid with (R:=R);
           clear IHe1_valid;
           try match goal with H : _ |- _ => solve [apply H] end;
           match goal with H : sep (emp _) _ _ |- _ => apply sep_emp_l in H end;
           cleanup; eauto with lia.

           { (* proof that new context doesn't contain variables that could be
                overwritten in the future *)
             intros; apply Forall_cons; eauto with lia; [ ].
             cbn [varname_not_in_context varname_set fst snd].
             cbv [PropSet.union PropSet.singleton_set PropSet.elem_of].
             setoid_rewrite varname_gen_unique.
             lia. }
           { (* proof that new context doesn't contain variables that retnames
                will overwrite *)
             intros; apply Forall_cons; eauto with lia; [ ].
             cbn [varname_not_in_context varname_set fst snd].
             cbv [PropSet.union PropSet.singleton_set PropSet.elem_of].
             eauto. }
           { (* proof that context_list_equiv continues to hold *)
             cbv [context_list_equiv] in *; apply Forall_cons; eauto; [ ].
             eapply equivalent_not_in_context_forall; eauto.
             cbv [varname_set fst snd PropSet.union PropSet.singleton_set PropSet.elem_of].
             destruct 1; subst; eauto. } }
      { intros; cleanup.
        repeat split; try (subst; tauto); [ ].
        (* TODO *)
        (* locals only_differs from a2 on nextn *)
        (* a2 only_differs from a5 on retnames + S nextn...out *)
        (* therefore locals only_differs from a5 on retnames + nextn...out *)

        admit. (* TODO *) } }
      (* { intros; cleanup; subst; tauto. } } *)
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

      (* simplify fiat-crypto step *)
      intros; cbn [expr.interp type.app_curried Compilers.ident_interp] in *.
      cbv [Rewriter.Util.LetIn.Let_In] in *. cleanup.

      (* use the hypothesis proving retnames has enough variables *)
      cbn [return_variables_valid length] in *. cleanup.
      break_match; [ cbn [length] in *; congruence | ].
      cleanup.

      (* simplify bedrock2 step *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      (* N.B. putting below line in the [ | | ] above makes eassumption fail *)
      2 : eapply assign_correct; try eassumption; [ ];
        eapply translate_inner_expr_correct; eassumption.

      (* use inductive hypothesis *)
      cleanup.
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      2: { eapply IHe1_valid with (R:=R); clear IHe1_valid.
           all:try match goal with H : _ |- _ => solve [apply H] end.
           all: match goal with
                  H : sep (emp _) _ _ |- _ => apply sep_emp_l in H end.
           all:cleanup.

           { (* proof that retnames doesn't contain names that could be
                overwritten later *)
             intros.
             match goal with
               H : context [varname_set (_ :: _)] |- _ =>
                             apply H; [|solve[auto] .. ]
             end.
             (* TODO : make a lemma for this? *)
             cbn [varname_set PropSet.of_list In] in *.
             cbv [PropSet.of_list] in *.
             tauto. }
           { (* proof that new context doesn't contain variables that retnames
                will overwrite *)
             intros.
             match goal with
               H : context [varname_set (_ :: _)] |- _ =>
                             apply H; [|solve[auto] .. ]
             end.
             (* TODO : make a lemma for this? *)
             cbn [varname_set PropSet.of_list In] in *.
             cbv [PropSet.of_list] in *.
             tauto. }
           { (* proof that retnames are still valid *)
             match goal with H : NoDup (_ :: _) |- _ => inversion H end.
             cbn [length] in *; split; auto. }
           { (* proof that context_list_equiv continues to hold *)
             cbv [context_list_equiv] in *.
             eapply equivalent_not_in_context_forall; eauto.
             cbv [varname_set fst snd PropSet.union PropSet.singleton_set PropSet.elem_of].

             intros. subst; eauto.
             match goal with
               H : context [varname_set (_ :: _)] |- _ =>
                             apply H; [|solve[auto] .. ]
             end.
             cbn [varname_set PropSet.of_list In] in *.
             cbv [PropSet.of_list] in *.
             tauto. } }
      {
        repeat split; intros; cleanup; try (subst; tauto); [ | ].
        { admit. (* TODO *)
          }
        {
          clear IHe1_valid.
        apply sep_emp_l.
        repeat match goal with H : sep (emp _) _ _ |- _ => apply sep_emp_l in H end.
        cbn [equivalent rtype_of_ltype fst snd] in *.
        cleanup.
        cbn [length map Compilers.base_interp] in *.
        repeat split; try congruence; [ ].
        apply Forall2_cons; [|eassumption].
        match goal with H : NoDup (_ :: _) |- _ => inversion H end.
        subst. (* TODO: remove the subst *)

        intros; eapply expr_untouched; eauto; [ ].
        cbn. cbv [PropSet.union PropSet.of_list PropSet.elem_of].
        match goal with
          |- ~ (?A \/ ?B) =>
          assert (~ A /\ ~ B); [split|tauto]
        end; eauto; [ ].
        cbv [used_varnames]. intro. cleanup.
        match goal with H : context [varname_set (?v :: retnames)] |- _ =>
                        eapply (H v) end; eauto; [ ].
        (* TODO : make a lemma for this? *)
        cbn [varname_set PropSet.of_list In] in *.
        cbv [PropSet.of_list] in *.
        tauto. } } }
    { (* nil *)
      admit. (* TODO *)
    }
    Qed.
  End Proofs.
End Compiler.

(* THOUGHTS

Instead of passing retnames as an argument, maybe return them -- then have a
reassign pass that can allow custom ones

*)