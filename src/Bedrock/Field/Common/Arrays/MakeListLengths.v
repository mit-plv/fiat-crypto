Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Language.API.
Require Import Crypto.Util.Option.

Import Language.API.Compilers AbstractInterpretation.Compilers.
Import Types.Notations.
Existing Instances rep.Z rep.listZ_mem.

Section with_parameters.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.

  Fixpoint list_lengths_repeat_base (n : nat) t : base_listonly nat t :=
    match t as t0 return base_listonly nat t0 with
    | base.type.prod a b =>
      (list_lengths_repeat_base n a, list_lengths_repeat_base n b)
    | base_listZ => n
    | _ => tt
    end.
  Fixpoint list_lengths_repeat_args (n : nat) t
    : type.for_each_lhs_of_arrow list_lengths t :=
    match t as t0 return type.for_each_lhs_of_arrow list_lengths t0 with
    | type.base b => tt
    | type.arrow (type.base s) d =>
      (list_lengths_repeat_base n s, list_lengths_repeat_args n d)
    | type.arrow s d => (tt, list_lengths_repeat_args n d)
    end.

  (* mostly a duplicate of list_lengths_from_value, just with ZRange interp *)
  Fixpoint list_lengths_from_bounds {t}
    : ZRange.type.base.option.interp t -> option (base_listonly nat t) :=
    match t as t0 return
          ZRange.type.base.option.interp t0 -> option (base_listonly nat t0) with
    | base.type.prod a b =>
      fun x =>
        (x1 <- list_lengths_from_bounds (fst x);
           x2 <- list_lengths_from_bounds (snd x);
           Some (x1, x2))%option
    | base_listZ =>
      fun x : option (list _) => option_map (@List.length _) x
    | _ => fun _ => Some tt
    end.
  Fixpoint list_lengths_from_argbounds {t}
    : type.for_each_lhs_of_arrow ZRange.type.option.interp t ->
      option (type.for_each_lhs_of_arrow list_lengths t) :=
    match t as t0 return
          type.for_each_lhs_of_arrow _ t0 ->
          option (type.for_each_lhs_of_arrow _ t0) with
    | type.base b => fun _ => Some tt
    | type.arrow (type.base a) b =>
      fun x =>
        (x1 <- list_lengths_from_bounds (fst x);
           x2 <- list_lengths_from_argbounds (snd x);
           Some (x1, x2))%option
    | type.arrow a b => fun _ => None
    end.
End with_parameters.
