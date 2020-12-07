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

Definition e := map.of_list allFuns.

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

Definition asm: list Instruction.
  Time (let r := eval vm_compute in (compile ml e) in
            match r with
            | Some (?x, _) => exact x
            end). (* 2.328 secs *)
Defined.

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

(* Note: this must be Coq.Init.Byte.byte, not coqutil.Byte.byte,
   which is a Notation for `(Coq.Init.Byte.byte: Type)` and doesn't
   work with bedrock2.Hexdump. *)
Definition as_bytes: list Coq.Init.Byte.byte := instrencode asm.

Module PrintBytes.
  Import bedrock2.Hexdump.
  Local Open Scope hexdump_scope.
  Set Printing Width 100.
  Goal True. let x := eval vm_compute in as_bytes in idtac (* x *). Abort.
End PrintBytes.
