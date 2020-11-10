(* This file is a partial duplicate of LoadStoreList.v, but talks about var_data instead of ltype *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Stringification.Language.
Require Import Crypto.Language.API.
Require Import Crypto.Bedrock.Field.Common.Types.
Import ListNotations. Local Open Scope Z_scope.

Import API.Compilers.
Import Types.Notations.
Import Language.Compilers.ToString.OfPHOAS.

Section Lists.
  Fixpoint extract_list_var_data {t}
    : base_var_data t ->
      base_listonly (base_var_data base_listZ) t * base_listexcl base_var_data t
    :=
      match t return base_var_data t -> base_listonly _ t * base_listexcl _ t with
      | base.type.prod a b =>
        fun x =>
          let p1 := extract_list_var_data (fst x) in
          let p2 := extract_list_var_data (snd x) in
          ((fst p1, fst p2), (snd p1, snd p2))
      | base_listZ => fun x => (x, tt)
      | _ => fun x => (tt, x)
      end.
End Lists.
