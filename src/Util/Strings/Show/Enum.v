Require Import Crypto.Util.Strings.Show.
Require Import Ltac2.Ltac2.
Require Import Ltac2.Printf.
Require Import Ltac2.Constr.
Require Import coqutil.Tactics.reference_to_string.

Ltac2 prove_Show_enum () :=
  lazy_match! goal with
  | [ |- Show ?ty ]
    => let t := Fresh.in_goal @t in
       let v := Fresh.in_goal @v in
       intro t;
       pose &t as v;
       (destruct &t)
       > [ let v := (eval cbv delta [&v] in &v) in
           let v := constr_string_basename_of_constr_reference v in
           exact $v
                 .. ]
  | [ |- ?g ]
    => Control.zero (Tactic_failure (Some (fprintf "prove_Show_enum: Goal is not %t: %t" '(Show ?[ty]) g)))
  end.

Ltac prove_Show_enum _ := ltac2:(prove_Show_enum ()).
