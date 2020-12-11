Require Import Coq.Strings.String. Open Scope string_scope.

Require Import Crypto.Bedrock.Field.Synthesis.Examples.riscv_with_c.asm_wrappers.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.riscv_with_c.signer_compile.

Definition asm_str: string := asm_wrappers e (snd compiled) "signer.bin".

From bedrock2 Require Import ToCString Bytedump.
Local Open Scope bytedump_scope.
Goal True.
  let c_code := eval vm_compute in (byte_list_of_string asm_str) in idtac c_code.
Abort.
