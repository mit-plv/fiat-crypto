Require Import Crypto.Bedrock.Field.Synthesis.Examples.riscv.Prelude.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.riscv.hello_src.
Require Import compiler.ToplevelLoop.
Require Import riscv.Utility.InstructionNotations.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import coqutil.Map.SortedList.
Require Import coqutil.Map.SortedListString.
Require Import compiler.StringNameGen.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Z.HexNotation.

Existing Instance DefaultRiscvState.

Axiom TODO: forall {T: Type}, T.

Existing Instance coqutil.Map.SortedListString.map.
Existing Instance coqutil.Map.SortedListString.ok.

Instance flatToRiscvDef_params: FlatToRiscvDef.FlatToRiscvDef.parameters := {
  funname_env := _;
  iset := RV32I;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call _ _ _ s :=
    match s with
    | FlatImp.SInteract resvars fname argvars =>
      (* TODO save and restore registers!! *)
      if string_dec fname "write" then
        match resvars, argvars with
        | [nWritten], [fileNo; s; n] =>
            [[Addi a0 fileNo 0;
              Addi a1 s 0;
              Addi a2 n 0;
              Addi a7 zero __NR_write;
              Ecall]]
        | _, _ => []
        end
      else if string_dec fname "exit" then
        match resvars, argvars with
        | [], [exitCode] =>
            [[Addi a0 exitCode 0;
              Addi a7 zero __NR_exit;
              Ecall]]
        | _, _ => []
        end
      else
        []
    | _ => []
    end;
}.

Instance pipeline_params : Pipeline.parameters. simple refine {|
  Pipeline.W := Words32Naive;
  Pipeline.string_keyed_map := _;
  Pipeline.Registers := _;
  Pipeline.compile_ext_call := FlatToRiscvDef.FlatToRiscvDef.compile_ext_call;
  Pipeline.ext_spec _ _ := TODO;
  Pipeline.PRParams := TODO;
|}. all: unshelve (try exact _); apply TODO. Defined.

Instance pipeline_assumptions: @Pipeline.assumptions pipeline_params. Admitted.

Definition allFuns: list Syntax.func := [init; hello_str; loop].

Definition e := map.putmany_of_list allFuns map.empty.

Definition ml: MemoryLayout := {|
  MemoryLayout.code_start    := word.of_Z (Ox"10000000");
  MemoryLayout.code_pastend  := word.of_Z (Ox"10000000" + 2^10);
  MemoryLayout.heap_start    := word.of_Z (Ox"20000000");
  MemoryLayout.heap_pastend  := word.of_Z (Ox"20000000" + 2^20);
  MemoryLayout.stack_start   := word.of_Z (Ox"40000000" - 2^20);
  MemoryLayout.stack_pastend := word.of_Z (Ox"40000000");
|}.

Definition asm: list Instruction.
  let r := eval vm_compute in (ToplevelLoop.compile_prog ml e) in set (res := r).
  match goal with
  | res := Some (?x, _) |- _ => exact x
  end.
Defined.

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Goal True. let r := eval unfold asm in asm in idtac (* r *). Abort.
  (* Note: the InvalidInstructions are expected, they are the embedded "hello" data *)
End PrintAssembly.

(* Note: this must be Coq.Init.Byte.byte, not coqutil.Byte.byte,
   which is a Notation for `(Coq.Init.Byte.byte: Type)` and doesn't
   work with bedrock2.Hexdump. *)
Definition as_bytes: list Coq.Init.Byte.byte := instrencode asm.

Module PrintBytes.
  Import bedrock2.Hexdump.
  Local Open Scope hexdump_scope.
  Set Printing Width 100.
  Goal True. let x := eval vm_compute in as_bytes in idtac x. Abort.
End PrintBytes.
