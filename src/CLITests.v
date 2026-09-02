From Coq Require Import Ascii List String.
Require Import Crypto.CLI.
Import ListNotations.

Local Open Scope string_scope.

Definition newline : string :=
  String.string_of_list_ascii [Ascii.ascii_of_nat 10].

Definition tab : string :=
  String.string_of_list_ascii [Ascii.ascii_of_nat 9].

Example quote_newline :
  ForExtraction.quote ("left" ++ newline ++ "right") =
  "'left" ++ newline ++ "right'".
Proof. vm_compute. reflexivity. Qed.

Example quote_tab :
  ForExtraction.quote ("left" ++ tab ++ "right") =
  "'left" ++ tab ++ "right'".
Proof. vm_compute. reflexivity. Qed.

Example quote_single_quote :
  ForExtraction.quote "it's" = "'it'""'""'s'".
Proof. vm_compute. reflexivity. Qed.

Example quote_plain_argument_unchanged :
  ForExtraction.quote "mul" = "mul".
Proof. vm_compute. reflexivity. Qed.

Example quote_typical_invocation_unchanged :
  List.map ForExtraction.quote
    ["src/ExtractionOCaml/word_by_word_montgomery"; "p256"; "64"; "mul"] =
  ["'src/ExtractionOCaml/word_by_word_montgomery'"; "p256"; "64"; "mul"].
Proof. vm_compute. reflexivity. Qed.
