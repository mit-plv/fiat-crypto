Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require bedrock2.Syntax.
Require bedrock2.Semantics.
Require bedrock2.WeakestPrecondition.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Array bedrock2.Scalars.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import Crypto.Language.API.
Import ListNotations. Local Open Scope Z_scope.

Import API.Compilers.

(*** This file contains the setup for the bedrock2 backend; the type
system, the parameter class, and some shorthand notations. ***)

Class parameters :=
  {
    semantics :> Semantics.parameters;
    varname_gen : nat -> String.string;
    error : Syntax.expr.expr;
    (* TODO: define word_size_in_bytes using Memory.bytes_per *)
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
          varname_set : ltype -> PropSet.set string;
          equiv :
            base.interp t -> rtype ->
            option Syntax.access_size -> (* memory size, if applicable *)
            Semantics.locals ->
            Semantics.mem -> Prop }.

      (* store a list in local variables; each element of the list is
       represented as a separate variable *)
      Instance listZ_local {zrep : rep base_Z} : rep base_listZ :=
        { ltype := list ltype;
          rtype := list rtype;
          rtype_of_ltype := map rtype_of_ltype;
          dummy_ltype := nil;
          make_error := [make_error];
          varname_set :=
            fold_right
              (fun x s =>
                 PropSet.union (varname_set x) s) PropSet.empty_set;
          equiv :=
            fun (x : list Z) (y : list rtype) _ locals _ =>
              Forall2 (fun a b => equiv a b None locals map.empty) x y
        }.

      (* store a list in memory; the list is represented by one Z, which
         is the location of the head of the list *)
      Instance listZ_mem {zrep : rep base_Z} : rep base_listZ :=
        { ltype := ltype;
          rtype := rtype;
          rtype_of_ltype := rtype_of_ltype;
          dummy_ltype := dummy_ltype;
          make_error := make_error;
          varname_set := varname_set;
          equiv :=
            fun (x : list Z) (y : rtype) size locals =>
              match size with
              | Some sz =>
                Lift1Prop.ex1
                  (fun start : Semantics.word =>
                     sep (map:=Semantics.mem)
                         (sep
                            (emp
                               (Forall
                                  (fun z => (0 <= z < 2 ^ Semantics.width)%Z)
                                  x))
                            (fun mem : Semantics.mem =>
                               forall sz,
                                 equiv (word.unsigned start) y sz locals mem))
                         (array (truncated_scalar sz)
                                (word.of_Z word_size_in_bytes)
                                start x))
              | None => emp False
              end
        }.

      Instance Z : rep base_Z :=
        { ltype := String.string;
          rtype := Syntax.expr.expr;
          rtype_of_ltype := Syntax.expr.var;
          dummy_ltype := varname_gen 0%nat;
          make_error := error;
          varname_set := PropSet.singleton_set;
          equiv :=
            fun (x : Z) (y : Syntax.expr.expr) _ locals =>
              emp ((0 <= x < 2 ^ Semantics.width)%Z /\
                   WeakestPrecondition.dexpr
                     map.empty locals y (word.of_Z x))
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
     integers, we need three strings.

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

    (* convert ltypes to rtypes (used for renaming variables) - the opposite
     direction is not permitted *)
    Fixpoint base_rtype_of_ltype {t} : base_ltype t -> base_rtype t :=
      match t with
      | base.type.prod a b =>
        fun x => (base_rtype_of_ltype (fst x),
                  base_rtype_of_ltype (snd x))
      | base_listZ => rep.rtype_of_ltype
      | _ => Syntax.expr.var
      end.
    Fixpoint rtype_of_ltype t
      : ltype t -> rtype t :=
      match t as t0 return ltype t0 -> rtype t0 with
      | type.base b => base_rtype_of_ltype
      | type.arrow a b =>
        (* garbage; not a valid ltype *)
        fun (_:unit) =>
          fun (x : rtype a) =>
            rtype_of_ltype b (dummy_ltype b)
      end.

    (* Set of variable names used by an ltype *)
    Fixpoint varname_set_base {t}
      : base_ltype t -> PropSet.set string :=
      match t with
      | base.type.prod a b =>
        fun x => PropSet.union (varname_set_base (fst x))
                               (varname_set_base (snd x))
      | base_listZ => rep.varname_set
      | _ => rep.varname_set
      end.
    Fixpoint varname_set_args {t}
      : type.for_each_lhs_of_arrow ltype t ->
        PropSet.set string :=
      match t as t0 return type.for_each_lhs_of_arrow _ t0 -> _ with
      | type.base b => fun _:unit => PropSet.empty_set
      | type.arrow (type.base a) b =>
        fun (x:base_ltype a * _) =>
          PropSet.union (varname_set_base (fst x))
                        (varname_set_args (snd x))
      | _ => fun _ => PropSet.empty_set (* garbage; invalid argument *)
      end.
    Definition varname_set {t} : ltype t -> PropSet.set string :=
      match t with
      | type.base _ => varname_set_base
      | _ => fun _ => PropSet.empty_set
      end.

    Fixpoint base_access_sizes t :=
      match t with
      | base.type.prod a b =>
        (base_access_sizes a * base_access_sizes b)%type
      | base_listZ => option Syntax.access_size
      | _ => option Syntax.access_size
      end.
    Definition access_sizes t :=
      match t with
      | type.base b => base_access_sizes b
      | _ => unit
      end.

    Fixpoint base_empty_access_sizes t : base_access_sizes t :=
      match t with
      | base.type.prod a b =>
        (base_empty_access_sizes a, base_empty_access_sizes b)
      | base_listZ => None
      | _ => None
      end.
    Definition empty_access_sizes t : access_sizes t :=
      match t with
      | type.base b => base_empty_access_sizes b
      | _ => tt
      end.
    Fixpoint empty_access_sizes_args t :
      type.for_each_lhs_of_arrow access_sizes t :=
      match t with
      | type.base _ => tt
      | type.arrow s d =>
        (empty_access_sizes s, empty_access_sizes_args d)
      end.

    (* relation that states whether a fiat-crypto value and a bedrock2 value are
       equivalent in a given bedrock2 context *)
    Fixpoint equivalent_base {t}
      : base.interp t -> (* fiat-crypto value *)
        base_rtype t -> (* bedrock2 value *)
        base_access_sizes t -> (* size in memory (if applicable) *)
        Semantics.locals ->
        Semantics.mem -> Prop :=
      match t with
      | base.type.prod a b =>
        fun (x : base.interp a * base.interp b)
            (y : base_rtype a * base_rtype b)
            (s : base_access_sizes a * base_access_sizes b)
            locals =>
          sep (equivalent_base (fst x) (fst y) (fst s) locals)
              (equivalent_base (snd x) (snd y) (snd s) locals)
      | base_listZ => rep.equiv
      | base_Z => rep.equiv
      |  _ => fun _ _ _ _ => emp False
      end.

    (* produces a separation-logic condition stating that the values of arguments are equivalent *)
    Fixpoint equivalent_args {t}
      : type.for_each_lhs_of_arrow
          API.interp_type t -> (* fiat-crypto value *)
        type.for_each_lhs_of_arrow rtype t -> (* bedrock2 value *)
        type.for_each_lhs_of_arrow
          access_sizes t -> (* sizes in memory *)
        Semantics.locals ->
        Semantics.mem -> Prop :=
      match t with
      | type.base b => fun _ _ _ _ => emp True
      | type.arrow (type.base a) b =>
        fun (x : base.interp a * _) (y : base_rtype a * _)
            (s : base_access_sizes a * _) locals =>
          sep (equivalent_base (fst x) (fst y) (fst s) locals)
              (equivalent_args (snd x) (snd y) (snd s) locals)
      | _ => fun _ _ _ _ => emp False
      end.

    Definition locally_equivalent_base {t} x y locals :=
      @equivalent_base t x y (base_empty_access_sizes t) locals map.empty.

    Definition locally_equivalent_args {t} x y locals :=
      @equivalent_args t x y (empty_access_sizes_args t) locals map.empty.

    (* wrapper that uses non-base types *)
    Fixpoint equivalent {t : API.type}
      : API.interp_type t -> (* fiat-crypto value *)
        rtype t -> (* bedrock2 value *)
        access_sizes t -> (* sizes in memory *)
        Semantics.locals ->
        Semantics.mem -> Prop :=
      match t with
      | type.base b => equivalent_base
      | _ => fun _ _ _ _ _ => False
      end.
    Definition locally_equivalent {t} x y locals :=
      @equivalent t x y (empty_access_sizes t) locals map.empty.

    Fixpoint equivalent_flat_base {t}
      : base.interp t ->
        list Semantics.word ->
        base_access_sizes t ->
        Semantics.mem -> Prop :=
      match t with
      | base.type.prod a b =>
        fun (x : base.interp a * base.interp b) words sizes =>
          Lift1Prop.ex1
            (fun i =>
               sep (equivalent_flat_base (fst x) (firstn i words) (fst sizes))
                   (equivalent_flat_base (snd x) (skipn i words) (snd sizes)))
      | base_listZ =>
        fun (x : list Z) words (sizes : option Syntax.access_size) =>
          (* since this is in-memory representation, [words] should be one word
             that indicates the memory location of the head of the list *)
          sep
            (map:=Semantics.mem)
            (emp (length words = 1%nat))
            (let addr := word.unsigned (hd (word.of_Z 0%Z) words) in
             rep.equiv (rep:=rep.listZ_mem)
                       x (Syntax.expr.literal addr) sizes map.empty)
      | base_Z =>
        fun (x : Z) words sizes =>
          sep
            (map:=Semantics.mem)
            (emp (length words = 1%nat))
            (let w := word.unsigned (hd (word.of_Z 0%Z) words) in
             rep.equiv (t:=base_Z) x (Syntax.expr.literal w) None map.empty)
      | _ => fun _ _ _ => emp False
      end.

    Fixpoint equivalent_flat_args {t}
      : type.for_each_lhs_of_arrow API.interp_type t ->
        list Semantics.word ->
        type.for_each_lhs_of_arrow access_sizes t ->
        Semantics.mem -> Prop :=
      match t as t0
            return type.for_each_lhs_of_arrow _ t0 -> _ ->
                   type.for_each_lhs_of_arrow _ t0 -> _
      with
      | type.base _ => fun (_:unit) words _ => emp (words = nil)
      | type.arrow (type.base a) b =>
        fun x words sizes =>
          Lift1Prop.ex1
            (fun i =>
               sep
                 (equivalent_flat_base (fst x) (firstn i words) (fst sizes))
                 (equivalent_flat_args (snd x) (skipn i words) (snd sizes)))
      | _ => fun _ _ _ => emp False (* invalid argument *)
      end.

    (* Types for partitioning return values into list and non-list *)
    Fixpoint base_listonly (T : Type) t : Type :=
      match t with
      | base.type.prod a b =>
        (base_listonly T a * base_listonly T b)
      | base_listZ => T
      | _ => unit
      end.
    Fixpoint base_listexcl (f : base.type -> Type) t : Type :=
      match t with
      | base.type.prod a b =>
        base_listexcl f a * base_listexcl f b
      | base_listZ => unit
      | _ => f t
      end.

    Fixpoint baseonly (f : base.type -> Type) t : Type :=
      match t with
      | type.base b => f b
      | type.arrow _ _ => unit
      end.
    Definition listonly T := baseonly (base_listonly T).
    Definition listexcl f := baseonly (base_listexcl f).

    Definition list_lengths (t : API.type) :=
      listonly nat t.
    Definition listonly_base_ltype t :=
      base_listonly (base_ltype base_listZ) t.
    Definition listexcl_base_ltype t :=
      base_listexcl base_ltype t.
    Definition listonly_base_rtype t :=
      base_listonly (base_rtype base_listZ) t.
    Definition listexcl_base_rtype t :=
      base_listexcl base_rtype t.

    Fixpoint map_listonly {A B t} (f : A -> B)
      : base_listonly A t -> base_listonly B t :=
      match t as t0 return
            base_listonly A t0 -> base_listonly B t0 with
      | base.type.prod a b =>
        fun x =>
          (map_listonly f (fst x), map_listonly f (snd x))
      | base_listZ => f
      | _ => fun _ => tt
      end.
    Fixpoint map_listexcl {t}
             {f g : base.type -> Type}
             (F : forall t, f t -> g t)
      : base_listexcl f t -> base_listexcl g t :=
      match t as t0 return
            base_listexcl f t0 -> base_listexcl g t0 with
      | base.type.prod a b =>
        fun x =>
          (map_listexcl F (fst x), map_listexcl F (snd x))
      | base_listZ => fun _ => tt
      | _ => F _
      end.


    Fixpoint varname_set_listonly {t}
      : base_ltype t ->
        PropSet.set string :=
      match t with
      | base.type.prod a b =>
        fun x => PropSet.union (varname_set_listonly (fst x))
                               (varname_set_listonly (snd x))
      | base_listZ => rep.varname_set
      | _ => fun _ => PropSet.empty_set
      end.
    Fixpoint varname_set_listexcl {t}
      : base_ltype t ->
        PropSet.set string :=
      match t with
      | base.type.prod a b =>
        fun x => PropSet.union (varname_set_listexcl (fst x))
                               (varname_set_listexcl (snd x))
      | base_listZ => fun _ => PropSet.empty_set
      | _ => rep.varname_set
      end.

    Fixpoint equivalent_listonly {t}
      : base.interp t -> (* fiat-crypto value *)
        listonly_base_rtype t -> (* bedrock2 value *)
        base_access_sizes t ->
        Semantics.locals ->
        Semantics.mem -> Prop :=
      match t with
      | base.type.prod a b =>
        fun x y s locals =>
          sep (equivalent_listonly (fst x) (fst y) (fst s) locals)
              (equivalent_listonly (snd x) (snd y) (snd s) locals)
      | base_listZ => rep.equiv
      | base_Z => fun _ _ _ _ => emp True
      |  _ => fun _ _ _ _ => emp False
      end.

    Fixpoint equivalent_listexcl {t}
      : base.interp t -> (* fiat-crypto value *)
        listexcl_base_rtype t -> (* bedrock2 value *)
        base_access_sizes t ->
        Semantics.locals ->
        Semantics.mem -> Prop :=
      match t with
      | base.type.prod a b =>
        fun x y s locals =>
          sep (equivalent_listexcl (fst x) (fst y) (fst s) locals)
              (equivalent_listexcl (snd x) (snd y) (snd s) locals)
      | base_listZ => fun _ _ _ _ => emp True
      | base_Z => rep.equiv
      |  _ => fun _ _ _ _ => emp False
      end.

    Fixpoint equivalent_listexcl_flat_base {t}
      : base.interp t ->
        list Semantics.word ->
        base_access_sizes t ->
        Semantics.mem -> Prop :=
      match t as t0 return
            base.interp t0 -> _ -> base_access_sizes t0
            -> Semantics.mem -> Prop with
      | base.type.prod a b =>
        fun (x : base.interp a * base.interp b) words s=>
          Lift1Prop.ex1
            (fun i =>
               sep (equivalent_listexcl_flat_base
                      (fst x) (firstn i words) (fst s))
                   (equivalent_listexcl_flat_base
                      (snd x) (skipn i words) (snd s)))
      | base_listZ => fun _ words _ => emp (words = nil)
      | base_Z => equivalent_flat_base
      | _ => fun _ _ _ => emp False
      end.

    Fixpoint equivalent_listonly_flat_base {t}
      : base.interp t ->
        list Semantics.word ->
        base_access_sizes t ->
        Semantics.mem -> Prop :=
      match t as t0 return
            base.interp t0 -> _ -> base_access_sizes t0
            -> Semantics.mem -> Prop with
      | base.type.prod a b =>
        fun (x : base.interp a * base.interp b) words sizes =>
          Lift1Prop.ex1
            (fun i =>
               sep (equivalent_listonly_flat_base
                      (fst x) (firstn i words) (fst sizes))
                   (equivalent_listonly_flat_base
                      (snd x) (skipn i words) (snd sizes)))
      | base_listZ => equivalent_flat_base
      | base_Z => fun _ words _ => emp (words = nil)
      | _ => fun _ _ _ => emp False
      end.
  End defs.
End Types.
