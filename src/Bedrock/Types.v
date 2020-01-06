Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require bedrock2.Syntax.
Require bedrock2.Semantics.
Require bedrock2.WeakestPrecondition.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Array bedrock2.Scalars.
Require Import Crypto.Language.API.
Import ListNotations. Local Open Scope Z_scope.

Import API.Compilers.

(*** This file contains the setup for the bedrock2 backend; the type
system, the parameter class, and some shorthand notations. ***)

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

(* Notations for commonly-used types in the fiat-crypto language *)
Module Notations.
  Notation base_range := (base.type.type_base base.type.zrange).
  Notation base_nat := (base.type.type_base base.type.nat).
  Notation base_Z := (base.type.type_base base.type.Z).
  Notation base_listZ := (base.type.list base_Z).
  Notation base_range2 := (base.type.prod base_range base_range).
  Notation base_ZZ := (base.type.prod base_Z base_Z).

  Notation type_range := (type.base base_range).
  Notation type_nat := (type.base base_nat).
  Notation type_Z := (type.base base_Z).
  Notation type_listZ := (type.base base_listZ).
  Notation type_range2 := (type.base base_range2).
  Notation type_ZZ := (type.base base_ZZ).
End Notations.

Module Types.
  Import Notations.
  Module rep.
    Section rep.
      Context {p : parameters}.

      Class rep (t : base.type) :=
        { ltype : Type; (* type for LHS of assignment *)
          rtype : Type; (* type for RHS of assignment *)
          rtype_of_ltype : ltype -> rtype;
          dummy_ltype : ltype;
          make_error : rtype;
          equiv :
            base.interp t -> rtype ->
            Interface.map.rep (map:=Semantics.locals) ->
            Interface.map.rep (map:=Semantics.mem) ->
            Prop }.

      (* store a list in local variables; each element of the list is
       represented as a separate variable *)
      Instance listZ_local {zrep : rep base_Z} : rep base_listZ :=
        { ltype := list ltype;
          rtype := list rtype;
          rtype_of_ltype := map rtype_of_ltype;
          dummy_ltype := nil;
          make_error := [make_error];
          equiv :=
            fun (x : list Z) (y : list rtype) locals _ =>
              length x = length y
              /\ Forall2 (fun a b => forall mem,
                              equiv a b locals mem) x y
        }.

      (* store a list in memory; the list is represented by one Z, which
       is the location of the head of the list *)
      Instance listZ_mem {zrep : rep base_Z} : rep base_listZ :=
        { ltype := ltype;
          rtype := rtype;
          rtype_of_ltype := rtype_of_ltype;
          dummy_ltype := dummy_ltype;
          make_error := make_error;
          equiv :=
            fun (x : list Z) (y : rtype) locals =>
              Lift1Prop.ex1
                (fun start : Z =>
                  let size := Interface.word.of_Z (Z.of_nat (length x)) in
                  sep (fun mem : Interface.map.rep (map:=Semantics.mem) =>
                         equiv start y locals mem)
                      (array scalar size
                             (Interface.word.of_Z start)
                             (map Interface.word.of_Z x)))
        }.

      Instance Z : rep base_Z :=
        { ltype := Syntax.varname;
          rtype := Syntax.expr.expr;
          rtype_of_ltype := Syntax.expr.var;
          dummy_ltype := varname_gen 0%nat;
          make_error := error;
          equiv :=
            fun (x : Z) (y : Syntax.expr.expr) locals _ =>
              forall mem, (* not allowed to read *)
                WeakestPrecondition.expr
                  mem locals y
                  (fun w => Interface.word.unsigned w = x)
        }.
    End rep.
  End rep.

  Section defs.
    Context {p : parameters}
            (* list representation -- could be local or in-memory *)
            {listZ : rep.rep base_listZ}.
    Existing Instance rep.Z.

    (* Types that appear in the bedrock2 expressions on the left-hand-side of
     assignments (or in return values). For example, if we want to assign three
     integers, we need three [Syntax.varname]s.

     Functions can't appear on the left-hand-side, so we return garbage output
     (the unit type). *)
    Fixpoint base_ltype (t : base.type) : Type :=
      match t with
      | base.type.prod a b => base_ltype a * base_ltype b
      | base_listZ => rep.ltype (rep:=listZ)
      | _ => rep.ltype (rep:=rep.Z)
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
      | base_listZ => rep.rtype (rep:=listZ)
      | _ => rep.rtype (rep:=rep.Z)
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
      | base.type.prod a b =>
        fun x => (rtype_of_ltype (fst x), rtype_of_ltype (snd x))
      | base_listZ => rep.rtype_of_ltype
      | _ => Syntax.expr.var
      end.

    (* error creation *)
    Fixpoint base_make_error t : base_rtype t :=
      match t with
      | base.type.prod a b => (base_make_error a, base_make_error b)
      | base_listZ => rep.make_error
      |  _ => rep.make_error
      end.
    Fixpoint make_error t : rtype t :=
      match t with
      | type.base a => base_make_error a
      | type.arrow a b => fun _ => make_error b
      end.

    (* These should only be used to fill holes in unreachable cases;
     nothing about them should need to be proven *)
    Fixpoint dummy_base_ltype (t : base.type) : base_ltype t :=
      match t with
      | base.type.prod a b => (dummy_base_ltype a, dummy_base_ltype b)
      | base_listZ => rep.dummy_ltype
      | _ => rep.dummy_ltype
      end.
    Definition dummy_ltype (t : API.type) : ltype t :=
      match t with
      | type.base a => dummy_base_ltype a
      | type.arrow a b => tt
      end.

    (* relation that states whether a fiat-crypto value and a bedrock2 value are
       equivalent in a given bedrock2 context *)
    Fixpoint equivalent {t}
      : base.interp t -> (* fiat-crypto value *)
        base_rtype t -> (* bedrock2 value *)
        Interface.map.rep (map:=Semantics.locals) -> (* local variables *)
        Interface.map.rep (map:=Semantics.mem) -> (* memory *)
        Prop :=
      match t with
      | base.type.prod a b =>
        fun (x : base.interp a * base.interp b)
            (y : base_rtype a * base_rtype b) locals =>
          sep (equivalent (fst x) (fst y) locals)
              (equivalent (snd x) (snd y) locals)
      | base_listZ => rep.equiv
      | base_Z => rep.equiv
      |  _ => fun _ _ _ _ => False
      end.

    Definition locally_equivalent {t} x y locals :=
      forall mem, @equivalent t x y locals mem.
  End defs.
End Types.