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

(* Notations for commonly-used types in the fiat-crypto language *)
Module Import Notations.
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

Class parameters
  {width: Z} {BW: Bitwidth.Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}
  {locals: map.map String.string word}
  {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}
  {ext_spec: bedrock2.Semantics.ExtSpec}
  {varname_gen : nat -> String.string}
  {error : Syntax.expr.expr} := parameters_sentinel : unit.

Section WithParameters.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters
     width BW word mem locals env ext_spec varname_gen error}.
  Local Notation parameters := (ltac:(let t := type of parameters_sentinel in exact t)) (only parsing).
  Class ok {parameters_sentinel : parameters} :=
    {
      (* semantics_ok : Semantics.parameters_ok semantics *)
      word_ok :> word.ok word;
      mem_ok :> map.ok mem;
      locals_ok :> map.ok locals;
      env_ok :> map.ok env;
      ext_spec_ok :> Semantics.ext_spec.ok ext_spec;

      varname_gen_unique :
        forall i j : nat, varname_gen i = varname_gen j <-> i = j;
    }.

  Context {ok : ok}.
  Lemma word_size_in_bytes_pos : 0 < Memory.bytes_per_word width.
  Proof. destruct Bitwidth.width_cases as [H|H]; rewrite H; cbv; trivial. Qed.
  Lemma width_0mod_8 : width mod 8 = 0.
  Proof. destruct Bitwidth.width_cases as [H|H]; rewrite H; cbv; trivial. Qed.
End WithParameters.

Module rep.
  Section rep.
    Context 
      {width BW word mem locals env ext_spec varname_gen error}
     `{parameters_sentinel : @parameters
       width BW word mem locals env ext_spec varname_gen error}.
    Local Notation parameters := (ltac:(let t := type of parameters_sentinel in exact t)) (only parsing).

    Class rep {parameters_sentinel : parameters} (t : base.type) :=
      { ltype : Type; (* type for LHS of assignment *)
        rtype : Type; (* type for RHS of assignment *)
        size : Type; (* amount of space taken in memory, if applicable *)
        rtype_of_ltype : ltype -> rtype;
        dummy_ltype : ltype;
        make_error : rtype;
        dummy_size : size;
        varname_set : ltype -> PropSet.set string;
        equiv : base.interp t -> rtype -> size -> locals -> mem -> Prop }.

    (* store a list in local variables; each element of the list is
       represented as a separate variable *)
    Instance listZ_local {zrep : rep base_Z} : rep base_listZ :=
      { ltype := list ltype;
        rtype := list rtype;
        size := size;
        rtype_of_ltype := map rtype_of_ltype;
        dummy_ltype := nil;
        make_error := [make_error];
        dummy_size := dummy_size;
        varname_set :=
          fold_right
            (fun x s =>
               PropSet.union (varname_set x) s) PropSet.empty_set;
        equiv :=
          fun (x : list Z) (y : list rtype) sz locals _ =>
            Forall2 (fun a b => equiv a b sz locals map.empty) x y
      }.

    (* store a list in memory; the list is represented by one Z, which
         is the location of the head of the list *)
    Instance listZ_mem {zrep : rep base_Z} : rep base_listZ :=
      { ltype := ltype;
        rtype := rtype;
        size := Syntax.access_size;
        rtype_of_ltype := rtype_of_ltype;
        dummy_ltype := dummy_ltype;
        make_error := make_error;
        dummy_size := Syntax.access_size.one;
        varname_set := varname_set;
        equiv :=
          fun (x : list Z) (y : rtype) sz locals =>
            Lift1Prop.ex1
              (fun start : word =>
                 Lift1Prop.ex1
                   (fun ws : list word =>
                      let bytes :=
                          Z.of_nat (Memory.bytes_per (width:=width) sz) in
                      sep (map:=mem)
                          (sep
                             (emp (map word.unsigned ws = x /\
                                   Forall
                                     (fun z =>
                                        (0 <= z < 2 ^ (bytes * 8))%Z)
                                     x))
                             (fun mem : mem =>
                                equiv (word.unsigned start) y
                                      (dummy_size (rep:=zrep))
                                      locals mem))
                          (array (truncated_scalar sz)
                                 (word.of_Z bytes) start
                                 (map word.unsigned ws))))
      }.

    Instance Z : rep base_Z :=
      { ltype := String.string;
        rtype := Syntax.expr.expr;
        size := unit;
        rtype_of_ltype := Syntax.expr.var;
        dummy_ltype := varname_gen 0%nat;
        make_error := error;
        dummy_size := tt;
        varname_set := PropSet.singleton_set;
        equiv :=
          fun (x : Z) (y : Syntax.expr.expr) _ locals =>
            Lift1Prop.ex1
              (fun w : word =>
                 emp (word.unsigned w = x /\
                      WeakestPrecondition.dexpr
                        map.empty locals y w))
      }.
  End rep.
End rep.

Section defs.
  Context
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters
     width BW word mem locals env ext_spec varname_gen error}.
  Local Notation parameters := (ltac:(let t := type of parameters_sentinel in exact t)) (only parsing).
  Context
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
  Definition ltype (t : type.type base.type) : Type :=
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

  Fixpoint base_access_sizes t :=
    match t with
    | base.type.prod a b =>
      (base_access_sizes a * base_access_sizes b)%type
    | base_listZ => rep.size (rep:=listZ)
    | _ => rep.size (rep:=rep.Z)
    end.
  Definition access_sizes t :=
    match t with
    | type.base b => base_access_sizes b
    | _ => unit
    end.

  Fixpoint base_dummy_access_sizes t : base_access_sizes t :=
    match t with
    | base.type.prod a b =>
      (base_dummy_access_sizes a, base_dummy_access_sizes b)
    | base_listZ => rep.dummy_size
    | _ => rep.dummy_size
    end.
  Definition dummy_access_sizes t : access_sizes t :=
    match t with
    | type.base b => base_dummy_access_sizes b
    | _ => tt
    end.
  Fixpoint dummy_access_sizes_args t :
    type.for_each_lhs_of_arrow access_sizes t :=
    match t with
    | type.base _ => tt
    | type.arrow s d =>
      (dummy_access_sizes s, dummy_access_sizes_args d)
    end.

  Definition baseonly (f : base.type -> Type) t : Type :=
    match t with
    | type.base b => f b
    | type.arrow _ _ => unit
    end.

  (* Types for partitioning return values into list and non-list *)
  Section ListOnlyListExcl.
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
  End ListOnlyListExcl.
End defs.
