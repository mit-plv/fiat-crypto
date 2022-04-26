Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Crypto.Util.Strings.String.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope char_scope.

Definition subscript_map :=
  Eval cbv in
    List.combine
      ["("; ")"; "+"; "-";
       "0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9";
       "=";
       "a"; "e"; "h"; "i"; "j"; "k"; "l"; "m"; "n"; "o"; "p"; "r"; "s"; "t"; "u"; "v"; "x"; "y"]%char
      ["₍"; "₎"; "₊"; "₋";
       "₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉";
       "₌";
       "ₐ"; "ₑ"; "ₕ"; "ᵢ"; "ⱼ"; "ₖ"; "ₗ"; "ₘ"; "ₙ"; "ₒ"; "ₚ"; "ᵣ"; "ₛ"; "ₜ"; "ᵤ"; "ᵥ"; "ₓ"; "ᵧ"]%string.

Module Ascii.
  Definition to_subscript_opt (c : ascii) : option string
    := option_map snd (find (fun '(ch, _) => Ascii.eqb c ch) subscript_map).
  Definition to_subscript (c : ascii) : string
    := match to_subscript_opt c with
       | Some s => s
       | None => String c EmptyString
       end.
End Ascii.

Module Export WORKAROUND_EXTRACTION_DONT_SHADOW_OCAML_STRING.
Module String.
  Definition to_subscript (s : string) : string
    := string_of_list_ascii (List.flat_map (fun a => list_ascii_of_string (Ascii.to_subscript a)) (list_ascii_of_string s)).
End String.
End WORKAROUND_EXTRACTION_DONT_SHADOW_OCAML_STRING.
