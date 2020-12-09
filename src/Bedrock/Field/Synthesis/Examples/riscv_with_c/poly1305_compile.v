(* Before opening this file in PG, run `RISCV_COMPILATION=1 make bedrock2-backend` in
   the fiat-crypto root directory, which will build all dependencies, including
   bedrock2, riscv-coq, the bedrock2 compiler, and all the required fiat-crypto files,
   and make sure to accept the COQPATH updates in .dir-locals.el *)

Require Import Crypto.Bedrock.Field.Synthesis.Examples.X1305_32.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import compiler.Pipeline.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import riscv.Utility.Monads.
Require Import compiler.util.Common.
Require Import coqutil.Decidable.
Require        riscv.Utility.InstructionNotations.
Require Import riscv.Platform.MinimalLogging.
Require Import bedrock2.MetricLogging.
Require Import riscv.Platform.MetricMinimal.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import coqutil.Map.SortedList.
Require Import compiler.StringNameGen.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MetricRiscvMachine.
Require bedrock2.Hexdump.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope ilist_scope.

Existing Instance DefaultRiscvState.

Axiom TODO: forall {T: Type}, T.

Instance flatToRiscvDef_params: FlatToRiscvDef.FlatToRiscvDef.parameters := {
  funname_env T := TODO;
  iset := RV32I;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call _ _ _ s :=
    match s with
    | FlatImp.SInteract _ fname _ =>
      if string_dec fname "nop" then
        [[Addi Register0 Register0 0]]
      else
        nil
    | _ => []
    end;
}.

Existing Instance coqutil.Map.SortedListString.map.
Existing Instance coqutil.Map.SortedListString.ok.

Instance pipeline_params : Pipeline.parameters. simple refine {|
  Pipeline.string_keyed_map := _;
  Pipeline.Registers := _;
  Pipeline.ext_spec _ _ := TODO;
  Pipeline.PRParams := TODO;
|}; unshelve (try exact _); apply TODO. Defined.

Instance pipeline_assumptions: @Pipeline.assumptions pipeline_params. Admitted.

Definition allFuns: list Syntax.func := [
  UnsaturatedSolinas.carry_mul;
  UnsaturatedSolinas.carry_square;
  UnsaturatedSolinas.carry;
  UnsaturatedSolinas.add;
  UnsaturatedSolinas.sub;
  UnsaturatedSolinas.opp;
  UnsaturatedSolinas.selectznz;
  UnsaturatedSolinas.to_bytes;
  UnsaturatedSolinas.from_bytes
].

Notation src_env := (SortedListString.map (list string * list string * Syntax.cmd.cmd)).

Definition e: src_env := map.of_list allFuns.

(* stack grows from high addreses to low addresses, first stack word will be written to
   (stack_pastend-8), next stack word to (stack_pastend-16) etc *)
Definition stack_pastend: Z := 2048.

Definition ml: MemoryLayout := {|
  MemoryLayout.code_start    := word.of_Z 0;
  MemoryLayout.code_pastend  := word.of_Z (4*2^10);
  MemoryLayout.heap_start    := word.of_Z (4*2^10);
  MemoryLayout.heap_pastend  := word.of_Z (8*2^10);
  MemoryLayout.stack_start   := word.of_Z (8*2^10);
  MemoryLayout.stack_pastend := word.of_Z (16*2^10);
|}.

Unset Printing Coercions. (* https://github.com/mit-plv/fiat-crypto/issues/899 *)

Definition compiled := Eval vm_compute in (compile ml e).

Definition asm: list Instruction :=
  match compiled with
  | Some (l, _) => l
  | None => []
  end.

Notation MapStrZ := (SortedListString.map Z).

Definition positions: MapStrZ :=
  match compiled with
  | Some (_, e) => e
  | None => map.empty
  end.

Definition LF : string := String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".

Definition ZToStr(z: Z): string := DecimalString.NilZero.string_of_int (BinInt.Z.to_int z).
Definition natToStr(n: nat): string := ZToStr (Z.of_nat n).

Fixpoint save_arg_regs(n: nat): string :=
  match n with
  | O => ""
  | S m => save_arg_regs m ++ "  sw sp, a" ++ natToStr m ++ ", (" ++ ZToStr (-4 * Z.of_nat n) ++ ")" ++ LF
  end.

Fixpoint load_res_regs(n: nat)(offset: Z): string :=
  match n with
  | O => ""
  | S m => load_res_regs m offset ++
           "  lw a" ++ natToStr m ++ ", sp, (" ++ ZToStr (offset + -4 * Z.of_nat n) ++ ")" ++ LF
  end.

Definition call(mypos: Z)(e_src: src_env)(e_pos: MapStrZ)(f: string): (string * Z) :=
  match map.get e_src f, map.get e_pos f with
  | Some (argvars, resvars, body), Some funpos => (
  "  addi sp, sp, (-4)" ++ LF ++
  "  sw sp, ra, (0)" ++ LF ++
  save_arg_regs (List.length argvars) ++
  "  jalr ra, (" ++ ZToStr (funpos - (mypos + 4 * (2 + Z.of_nat (List.length argvars)))) ++ ")" ++ LF ++
  load_res_regs (List.length resvars) (- Z.of_nat (List.length argvars)) ++
  "  lw ra, sp, (0)" ++ LF ++
  "  addi sp, sp, (4)" ++ LF ++
  "  ret" ++ LF,
  4 * (Z.of_nat (2 + List.length argvars + 1 + List.length resvars + 3)))
  | _, _ => ("ERROR: " ++ f ++ " not found", -1)
  end.

Fixpoint wrappers(mypos: Z)(e_src: src_env)(e_pos: MapStrZ)(fs: list string): string :=
  match fs with
  | f :: rest => let '(s, l) := call mypos e_src e_pos f in
                 f ++ ":" ++ LF ++ s ++ wrappers (mypos + l) e_src e_pos rest
  | nil => ""
  end.

Definition asm_str: string :=
  Eval vm_compute in
  ".section .text" ++ LF ++
  "bedrock2functions: .incbin ""tmp.bin""" ++ LF ++
  wrappers (4 * (Z.of_nat (List.length asm))) e positions (map.keys positions).

From bedrock2 Require Import ToCString Bytedump.
Local Open Scope bytedump_scope.
Goal True.
  let c_code := eval vm_compute in (byte_list_of_string asm_str) in idtac c_code.
Abort.

Definition valid_instructions: list Instruction -> Prop :=
  Forall (fun i : Instruction => verify i RV32IM).

Lemma valid_cons: forall h t,
    verify h RV32IM ->
    valid_instructions t ->
    valid_instructions (h :: t).
Proof.
  unfold valid_instructions.
  intros. apply Forall_cons; assumption.
Qed.

(* Note: this works, but takes >10min and >13GB of RAM -- TODO write a reflective checker
Lemma valid: Forall (fun i : Instruction => verify i RV32IM) asm.
Proof.
  unfold asm.
  repeat (time (apply valid_cons; [vm_compute; try intuition discriminate|])).
  apply Forall_nil.
  all: fail.
*)

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Goal True. let r := eval unfold asm in asm in idtac (* r *). Abort.
End PrintAssembly.

Require Import Crypto.Bedrock.Field.Synthesis.Examples.riscv.SyscallNumbers.
Import RegisterNames Decode.

Definition STDIN_FILENO: Z := 0.
Definition STDOUT_FILENO: Z := 1.
Definition STDERR_FILENO: Z := 2.

Definition asm1 := [[
  (* write two values onto the stack: *)
  Addi a0 zero 15;
  Sw sp a0 (-4);
  Addi a0 zero 28;
  Sw sp a0 (-8);

  (* read them back and add them up: *)
  Lw a1 sp (-4);
  Lw a2 sp (-8);
  Add a0 a1 a2;

  (* exit(a0) *)
  Addi a7 zero __NR_exit;
  Ecall
]].

Definition asm20 := [[
  (* a2 = 2 ^ 12 *)
  Addi a2 zero 1;
  Slli a2 a2 12;

  (* a1 = sp with the 12 lowest bits set to 0 *)
  Addi t0 a2 (-1);
  Xori t0 t0 (-1);
  And a1 sp t0;

  (* ssize_t write(int fd, const void *buf, size_t nbytes); *)
  (* write(STDOUT_FILENO, a1, a2) *)
  Addi a0 zero STDOUT_FILENO;
  Addi a7 zero __NR_write;
  Ecall;

  (* exit(0) *)
  Addi a0 zero 0;
  Addi a7 zero __NR_exit;
  Ecall
]].

Definition asm21 := [[
  (* a2 = 2 ^ 12 *)
  Addi a2 zero 1;
  Slli a2 a2 12;

  (* a1 = sp with the 12 lowest bits set to 0 *)
  Addi t0 a2 (-1);
  Xori t0 t0 (-1);
  And a1 sp t0;

  (* a1 = assumed beginning (pastend) of stack *)
  Add a1 a1 a2;
  (* a2 = size of existing stack *)
  Sub a2 a1 sp;
  (* a1 = sp *)
  Addi a1 sp 0;

  (* ssize_t write(int fd, const void *buf, size_t nbytes); *)
  (* write(STDOUT_FILENO, a1, a2) *)
  Addi a0 zero STDOUT_FILENO;
  Addi a7 zero __NR_write;
  Ecall;

  (* exit(11) *)
  Addi a0 zero 11;
  Addi a7 zero __NR_exit;
  Ecall
]].

Definition asm2 := [[
  Addi s1 sp 0;

  (* ssize_t write(int fd, const void *buf, size_t nbytes); *)
  (* write(STDOUT_FILENO, a1, a2) *)
  Addi a0 zero STDOUT_FILENO;
  Addi a1 s1 0;
  Addi a2 zero 4;
  Addi a7 zero __NR_write;
  Ecall;
  Addi s1 s1 4;
  Jal zero (-24);

  (* exit(11) *)
  Addi a0 zero 11;
  Addi a7 zero __NR_exit;
  Ecall
]].

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

(* The stack already contains the environment variables and the command line arguments
   (contents of argv) and some other stuff, and sp points past that stuff, so we don't
   get the whole stack amount we required

https://interrupt.memfault.com/blog/how-to-write-linker-scripts-for-firmware

and use objcopy to turn the binary file into a .o file that can be referenced in a linker script
https://www.devever.net/~hl/incbin
*)

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
