Require Import Crypto.Bedrock.End2End.X25519.MontgomeryLadder.
Require Import compiler.Pipeline.
Require Import riscv.Utility.InstructionNotations.
Local Unset Printing Coercions.

Goal True.
  Time
  let e := eval vm_compute in ((*list_byte_of_string*) (compile (string_keyed_map:=SortedListString.map) MMIO.compile_ext_call (map.of_list funcs))) in
  idtac (* e *) .
Abort.
