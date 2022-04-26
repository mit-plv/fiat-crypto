Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Crypto.Util.Strings.String.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope char_scope.

Definition superscript_map :=
  Eval cbv in
    List.combine
      ["("; ")"; "+"; "-";
       "0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9";
       "=";
       "A"; "B"; "C"; "D"; "E"; "F"; "G"; "H"; "I"; "J"; "K"; "L"; "M"; "N"; "O"; "P"; "R"; "S"; "T"; "U"; "V"; "W"; "X"; "Y"; "Z";
       "a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"; "m"; "n"; "o"; "p"; "r"; "s"; "t"; "u"; "v"; "w"; "x"; "y"; "z"]%char
      ["⁽"; "⁾"; "⁺"; "⁻";
       "⁰"; "¹"; "²"; "³"; "⁴"; "⁵"; "⁶"; "⁷"; "⁸"; "⁹";
       "⁼";
       "ᴬ"; "ᴮ"; "ᶜ"; "ᴰ"; "ᴱ"; "ᶠ"; "ᴳ"; "ᴴ"; "ᴵ"; "ᴶ"; "ᴷ"; "ᴸ"; "ᴹ"; "ᴺ"; "ᴼ"; "ᴾ"; "ᴿ"; "ˢ"; "ᵀ"; "ᵁ"; "ⱽ"; "ᵂ"; "ˣ"; "ʸ"; "ᶻ";
       "ᵃ"; "ᵇ"; "ᶜ"; "ᵈ"; "ᵉ"; "ᶠ"; "ᵍ"; "ʰ"; "ᶦ"; "ʲ"; "ᵏ"; "ˡ"; "ᵐ"; "ⁿ"; "ᵒ"; "ᵖ"; "ʳ"; "ˢ"; "ᵗ"; "ᵘ"; "ᵛ"; "ʷ"; "ˣ"; "ʸ"; "ᶻ"]%string.

Module Ascii.
  Definition to_superscript_opt (c : ascii) : option string
    := option_map snd (find (fun '(ch, _) => Ascii.eqb c ch) superscript_map).
  Definition to_superscript (c : ascii) : string
    := match to_superscript_opt c with
       | Some s => s
       | None => String c EmptyString
       end.
End Ascii.

Module Export WORKAROUND_EXTRACTION_DONT_SHADOW_OCAML_STRING.
Module String.
  Definition to_superscript (s : string) : string
    := string_of_list_ascii (List.flat_map (fun a => list_ascii_of_string (Ascii.to_superscript a)) (list_ascii_of_string s)).
End String.
End WORKAROUND_EXTRACTION_DONT_SHADOW_OCAML_STRING.
