Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.Bedrock.Types.
Require Crypto.Bedrock.Parameters.Defaults32.
Require Crypto.Bedrock.Parameters.Defaults64.
Local Open Scope string_scope.
Import ListNotations.
Import Types.

Existing Instances
         Defaults32.default_parameters_ok
         Defaults64.default_parameters_ok.

(* pairs machine word size choices with parameters instances *)
Definition parameter_choices : list (Z * parameters) :=
  [(32%Z, Defaults32.default_parameters);
     (64%Z, Defaults64.default_parameters)].

Definition select_parameters wordsize : parameters + string :=
  match find (fun x => Z.eqb wordsize (fst x)) parameter_choices with
  | Some x => inl (snd x)
  | None =>
    let wordsize_choices := List.map fst parameter_choices in
    let wordsize_choices_str :=
        List.map Decimal.Z.to_string wordsize_choices in
    inr ("Invalid machine word size ("
           ++  Decimal.Z.to_string wordsize
           ++ "); valid choices are "
           ++ String.concat "," wordsize_choices_str)%string
  end.
