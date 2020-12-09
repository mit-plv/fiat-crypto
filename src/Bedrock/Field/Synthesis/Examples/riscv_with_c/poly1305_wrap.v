(* Before opening this file in PG, run `RISCV_COMPILATION=1 make bedrock2-backend` in
   the fiat-crypto root directory, which will build all dependencies, including
   bedrock2, riscv-coq, the bedrock2 compiler, and all the required fiat-crypto files,
   and make sure to accept the COQPATH updates in .dir-locals.el *)

Set Warnings "-notation-incompatible-format".

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
  | S m => save_arg_regs m ++ "  sw a" ++ natToStr m ++ ", " ++ ZToStr (-4 * Z.of_nat n) ++ "(sp)" ++ LF
  end.

Fixpoint load_res_regs(n: nat)(offset: Z): string :=
  match n with
  | O => ""
  | S m => load_res_regs m offset ++
           "  lw a" ++ natToStr m ++ ", " ++ ZToStr (offset + -4 * Z.of_nat n) ++ "(sp)" ++ LF
  end.

Definition call(e_src: src_env)(e_pos: MapStrZ)(f: string): string :=
  match map.get e_src f, map.get e_pos f with
  | Some (argvars, resvars, body), Some funpos =>
  "  addi sp, sp, -4" ++ LF ++
  "  sw ra, 0(sp)" ++ LF ++
  save_arg_regs (List.length argvars) ++
  "  jal ra, bedrock2functions+" ++ ZToStr funpos ++ LF ++
  load_res_regs (List.length resvars) (- Z.of_nat (List.length argvars)) ++
  "  lw ra, 0(sp)" ++ LF ++
  "  addi sp, sp, 4" ++ LF ++
  "  ret" ++ LF
  | _, _ => "ERROR: " ++ f ++ " not found"
  end.

Fixpoint wrappers(e_src: src_env)(e_pos: MapStrZ)(fs: list string): string :=
  match fs with
  | f :: rest => let s := call e_src e_pos f in
                 ".globl " ++ f ++ LF ++
                 f ++ ":" ++ LF ++
                 s ++
                 wrappers e_src e_pos rest
  | nil => ""
  end.

Definition asm_str: string :=
  Eval vm_compute in
  ".section .text" ++ LF ++
  "bedrock2functions: .incbin ""poly1305.bin""" ++ LF ++
  wrappers e positions (map.keys positions).

From bedrock2 Require Import ToCString Bytedump.
Local Open Scope bytedump_scope.
Goal True.
  let c_code := eval vm_compute in (byte_list_of_string asm_str) in idtac c_code.
Abort.
