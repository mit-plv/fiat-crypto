Require Import Crypto.Bedrock.Field.Synthesis.Examples.riscv.Prelude.

Definition probe_mem := [[
  (* stack pointer starts at end of stack, 0x4000000 *)
  Addi sp zero 1;
  Slli sp sp 30;

  (* heap starts at 0x20000000 *)
  Addi gp zero 1;
  Slli gp gp 29;

  (* size of stack and heap is 1MB each *)
  Addi t0 zero 1;
  Slli t0 t0 20;

  (* some magic constants *)
  Addi s1 zero 9;
  Addi s2 zero 10;
  Addi s3 zero 11;
  Addi s4 zero 12;

  (* write to highest stack addr: *)
  Sw sp s1 (-4);
  (* write to lowest stack addr: *)
  Sub sp sp t0;
  Sw sp s2 (0);
  (* write to lowest heap addr: *)
  Sw gp s3 (0);
  (* write to highest heap addr: *)
  Add gp gp t0;
  Sw gp s4 (-4);
  (* replacing any of the above (0)s by a (-4) or vice versa will result in a segfault *)

  (* read back values: *)
  Lw a2 sp (0);
  Add sp sp t0;
  Lw a1 sp (-4);
  Lw a4 gp (-4);
  Sub gp gp t0;
  Lw a3 gp (0);

  Add a0 zero a1;
  Add a0 a0 a2;
  Add a0 a0 a3;
  Add a0 a0 a4;

  (* exit(a0) *)
  Addi a7 zero __NR_exit;
  Ecall
]].

(* Note: this must be Coq.Init.Byte.byte, not coqutil.Byte.byte,
   which is a Notation for `(Coq.Init.Byte.byte: Type)` and doesn't
   work with bedrock2.Hexdump. *)
Definition as_bytes: list Coq.Init.Byte.byte := instrencode probe_mem.

Module PrintBytes.
  Import bedrock2.Hexdump.
  Local Open Scope hexdump_scope.
  Set Printing Width 100.
  Goal True. let x := eval vm_compute in as_bytes in idtac x. Abort.
End PrintBytes.
