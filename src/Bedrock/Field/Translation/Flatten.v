(* IF YOU CHANGE THIS FILE YOU MUST ALSO CHANGE src/Bedrock/Field/Stringification/FlattenVarData.v ! *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Array.
Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Language.API.
Import ListNotations. Local Open Scope Z_scope.

Import API.Compilers.
Import Types.Notations.

(* For argument and return variable names, fiat-crypto expects a nested
   structure while bedrock2 expects flat lists; this file contains mechanical
   conversions between the two. *)

Section Flatten.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  (* these conversions should happen before loading arguments and after
       storing return values, so they use in-memory lists *)
  Local Existing Instance rep.listZ_mem.
  Local Existing Instance rep.Z.

  Fixpoint flatten_base_ltype {t}
    : base_ltype t -> list string :=
    match t with
    | base.type.prod a b =>
      fun x : base_ltype a * base_ltype b =>
        (flatten_base_ltype (fst x) ++ flatten_base_ltype (snd x))
    | base_listZ => fun x : string => [x]
    | _ => fun x : string => [x]
    end.

  Fixpoint flatten_base_rtype {t}
    : base_rtype t -> list Syntax.expr :=
    match t as t0 return base_rtype t0 -> _ with
    | base.type.prod a b =>
      fun x : base_rtype a * base_rtype b =>
        (flatten_base_rtype (fst x) ++ flatten_base_rtype (snd x))
    | base_listZ => fun x : Syntax.expr => [x]
    | _ => fun x : Syntax.expr => [x]
    end.

  Fixpoint flatten_argnames {t}
    : type.for_each_lhs_of_arrow ltype t -> list string :=
    match t with
    | type.base b => fun _ : unit => []
    | type.arrow (type.base a) b =>
      fun x : base_ltype a * _ =>
        flatten_base_ltype (fst x) ++ flatten_argnames (snd x)
    | _ => fun _ => [] (* garbage; function arguments not allowed *)
    end.

  Fixpoint flatten_args {t}
    : type.for_each_lhs_of_arrow rtype t -> list Syntax.expr :=
    match t as t0 return type.for_each_lhs_of_arrow rtype t0 -> _ with
    | type.base b => fun _ => []
    | type.arrow (type.base a) b =>
      fun x : base_rtype a * _ =>
        flatten_base_rtype (fst x) ++ flatten_args (snd x)
    | _ => fun _ => [] (* garbage; function arguments not allowed *)
    end.

  Definition flatten_retnames {t}
    : base_ltype t -> list string :=
    flatten_base_ltype.

  Definition flatten_rets {t}
    : base_rtype t -> list Syntax.expr :=
    flatten_base_rtype.

  Fixpoint flatten_listonly_base_ltype {t}
    : listonly_base_ltype t -> list string :=
    match t with
    | base.type.prod a b =>
      fun x =>
        (flatten_listonly_base_ltype (fst x))
          ++ flatten_listonly_base_ltype (snd x)
    | base_listZ => fun x => [x]
    | _ => fun _ => []
    end.

  Fixpoint flatten_listexcl_base_ltype {t}
    : listexcl_base_ltype t -> list string :=
    match t with
    | base.type.prod a b =>
      fun x =>
        (flatten_listexcl_base_ltype (fst x))
          ++ flatten_listexcl_base_ltype (snd x)
    | base_listZ => fun _ => []
    | _ => fun x => [x]
    end.
End Flatten.
