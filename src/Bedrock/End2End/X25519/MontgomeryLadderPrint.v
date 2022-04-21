Require Import Crypto.Bedrock.End2End.X25519.MontgomeryLadder.
Require Import Coq.Strings.String Coq.ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Import List.ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Unset Printing Coercions.
Local Set Printing Depth 212131231.

Goal True.
  Time
  let e := eval vm_compute in funcs in
  idtac (* e *) .
Abort.
