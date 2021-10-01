Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Language.API.
Local Open Scope Z_scope.

Import API.Compilers.
Import Types.Notations.

Section VarnameSet.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters
     width BW word mem locals env ext_spec varname_gen error}.
  Context {listZ : rep.rep base_listZ}.
  Existing Instance rep.Z.

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
End VarnameSet.
