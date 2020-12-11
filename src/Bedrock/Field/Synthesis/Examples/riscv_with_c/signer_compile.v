(* Before opening this file in PG, run `RISCV_COMPILATION=1 make bedrock2-backend` in
   the fiat-crypto root directory, which will build all dependencies, including
   bedrock2, riscv-coq, the bedrock2 compiler, and all the required fiat-crypto files,
   and make sure to accept the COQPATH updates in .dir-locals.el *)

Require Import Crypto.Bedrock.Field.Synthesis.Examples.X25519_32.

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

Unset Printing Coercions. (* https://github.com/mit-plv/fiat-crypto/issues/899 *)

Definition compiled := Eval vm_compute in
      match composed_compile e with
        (* Note: stack_needed is 0 because the current stack size computation only considers
           functions without arguments as entry points, and there are none *)
      | Some (insts, positions, stack_needed) => (insts, positions)
      | None => (nil, map.empty)
      end.

Definition asm: list Instruction := fst compiled.

Notation MapStrZ := (SortedListString.map Z).

Definition positions: MapStrZ := snd compiled.

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
