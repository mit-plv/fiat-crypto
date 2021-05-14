(* This file is a duplicate of Flatten.v, but talks about var_data instead of ltype *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Stringification.Language.
Require Crypto.Stringification.C.
Require Crypto.Stringification.IR.
Require Import Crypto.Language.API.
Require Import Crypto.Bedrock.Field.Common.Types.
Import ListNotations. Local Open Scope Z_scope.

Import API.Compilers.
Import Bedrock.Field.Common.Types.Notations.
Import Language.Compilers.ToString Language.Compilers.ToString.OfPHOAS.
Import C.Compilers.ToString IR.Compilers.ToString.

(* For argument and return variable names, fiat-crypto expects a nested
   structure while bedrock2 expects flat lists; this file contains mechanical
   conversions between the two. *)

(** TODO: MOVE ME (WHERE?) *)
Notation name_with_type := (string * option int.type)%type (only parsing).
Definition print_name (n : name_with_type) : string := fst n.
Definition print_type (n : name_with_type) : string
  := let _ := Compilers.Options.default_language_naming_conventions in
     C.String.type.primitive.to_string "" IR.type.Z (snd n).
Definition print_ptr_type (n : name_with_type) : string
  := let _ := Compilers.Options.default_language_naming_conventions in
     C.String.type.primitive.to_string "" IR.type.Zptr (snd n).
Definition print_cast (n : name_with_type) : string
  := ("(" ++ print_type n ++ ")")%string.
Definition print_ptr_cast (n : name_with_type) : string
  := ("(" ++ print_ptr_type n ++ ")")%string.

Section Flatten.
  Fixpoint flatten_base_var_data {t}
  : base_var_data t -> list name_with_type :=
    match t return base_var_data t -> _ with
    | base.type.prod a b =>
      fun x : base_var_data a * base_var_data b =>
        (flatten_base_var_data (fst x) ++ flatten_base_var_data (snd x))
    | base.type.list _ => fun '(n, ty, len, _typedef) => [(n, ty)]
    | base_Z => fun '(n, is_ptr, ty, _typedef) => [(n, ty)]
    | _ => fun _ => []
    end.

  Fixpoint flatten_argnames_of_var_data {t}
    : type.for_each_lhs_of_arrow var_data t -> list name_with_type :=
    match t with
    | type.base b => fun _ : unit => []
    | type.arrow (type.base a) b =>
      fun x : base_var_data a * _ =>
        flatten_base_var_data (fst x) ++ flatten_argnames_of_var_data (snd x)
    | _ => fun _ => [] (* garbage; function arguments not allowed *)
    end.

  Definition flatten_retnames_of_var_data {t}
    : base_var_data t -> list name_with_type :=
    flatten_base_var_data.

  Fixpoint flatten_listonly_base_var_data {t}
    : base_listonly (base_var_data base_listZ) t -> list name_with_type :=
    match t with
    | base.type.prod a b =>
      fun x =>
        (flatten_listonly_base_var_data (fst x))
          ++ flatten_listonly_base_var_data (snd x)
    | base_listZ => flatten_base_var_data
    | _ => fun _ => []
    end.

  Fixpoint flatten_listexcl_base_var_data {t}
    : base_listexcl base_var_data t -> list name_with_type :=
    match t with
    | base.type.prod a b =>
      fun x =>
        (flatten_listexcl_base_var_data (fst x))
          ++ flatten_listexcl_base_var_data (snd x)
    | base_listZ => fun _ => []
    | _ => flatten_base_var_data
    end.
End Flatten.
