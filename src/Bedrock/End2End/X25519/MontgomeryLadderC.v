(* sh -c 'ulimit -s unlimited; "coqc"   -q '-w' '+implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+variable-collision,+omega-is-deprecated,+deprecated-instantiate-syntax,+non-recursive' -w -notation-overridden,-undeclared-scope,-deprecated-hint-rewrite-without-locality,-deprecated-hint-constr,-fragile-hint-constr,-native-compiler-disabled,-ambiguous-paths  "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" -R src Crypto src/Bedrock/End2End/X25519/MontgomeryLadderPrint.v' | less *)
Require Import Crypto.Bedrock.End2End.X25519.MontgomeryLadder.
Require Import Coq.Strings.String.

Require Import bedrock2.Bytedump.
Local Open Scope bytedump_scope.
Goal True.
  Time
  let e := eval vm_compute in ((*list_byte_of_string*) (ToCString.c_module funcs)) in
  idtac (* e *) .
Abort.
