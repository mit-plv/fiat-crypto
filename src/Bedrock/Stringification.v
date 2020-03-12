Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Stringification.Language.
Import Stringification.Language.Compilers.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Axiom Bedrock2_ToFunctionLines
  : forall {relax_zrange : relax_zrange_opt}
           (do_bounds_check : bool) (static : bool) (prefix : string) (name : string)
           {t}
           (e : @API.Expr t)
           (comment : type.for_each_lhs_of_arrow ToString.OfPHOAS.var_data t -> ToString.OfPHOAS.var_data (type.base (type.final_codomain t)) -> list string)
           (name_list : option (list string))
           (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
           (outbounds : ZRange.type.base.option.interp (type.final_codomain t)),
    (list string * ToString.ident_infos) + string.

Definition OutputBedrock2API : ToString.OutputLanguageAPI :=
  {|
    ToString.comment_block s
    := List.map (fun line => "/* " ++ line ++ " */")%string s;

    ToString.ToFunctionLines := @Bedrock2_ToFunctionLines;

    ToString.header := fun _ _ _ => [];

    ToString.footer := fun _ _ _ => [];

    (** No special handling for any functions *)
    ToString.strip_special_infos infos := infos;

  |}.
