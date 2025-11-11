From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import NArith.
From Coq Require Import ZArith.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.Parse.
Require Import Crypto.Assembly.Equivalence.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.Notations.

Set Printing Coercions.
Set Printing Notations.
Import ListNotations.
Import API.Compilers.API APINotations.Compilers AbstractInterpretation.ZRange.Compilers.

Local Open Scope zrange_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope symex_scope.

Existing Instance default_equivalence_checker_options.

(* ============================================================================
   Assembly-to-Assembly Equivalence Testing

   This file demonstrates how to compare two assembly programs directly without
   requiring a PHOAS expression. This is useful for testing symbolic execution
   of specific instructions.
   ============================================================================ *)

(* ============================================================================
   Test 1: XOR register with itself vs MOV zero

   Both set a register to zero:
   - xor rax, rax  (XOR a register with itself yields 0)
   - mov rax, 0    (Directly move 0 into register)
   ============================================================================ *)

(* Program 1: xor rax, rax *)
Definition xor_zero_prog1 : list string := ["xor rax, rax"; "ret"].

(* Program 2: mov rax, 0 *)
Definition xor_zero_prog2 : list string := ["mov rax, 0"; "ret"].

(* Parse both programs *)
Definition xor_zero_asm1 : ErrorT ParseValidatedError (list (string * Lines)) :=
  ErrorT.map (fun lines => [("xor_version", lines)]) (parse_validated xor_zero_prog1).

Definition xor_zero_asm2 : ErrorT ParseValidatedError (list (string * Lines)) :=
  ErrorT.map (fun lines => [("mov_version", lines)]) (parse_validated xor_zero_prog2).

(* No inputs needed for this test *)
Definition xor_test_input_types : type_spec := [].

(* Single 64-bit output in rax *)
Definition xor_test_output_types : type_spec := [None].

(* Run the equivalence check *)
Definition check_xor_equivalence :
    ErrorT ParseValidatedError
      (ErrorT (option (string * Lines) * EquivalenceCheckingError) unit) :=
  asm1 <- xor_zero_asm1;
  asm2 <- xor_zero_asm2;
  Success (check_asm_equivalence asm1 asm2
            xor_test_input_types xor_test_output_types).

(* This should succeed if both programs produce the same symbolic output *)
Compute check_xor_equivalence.

(* ============================================================================
   Test 2: SUB register from itself vs MOV zero

   Both set a register to zero:
   - sub rax, rax  (Subtract a register from itself yields 0)
   - mov rax, 0    (Directly move 0 into register)
   ============================================================================ *)

Definition sub_zero_prog1 : list string := ["sub rax, rax"; "ret"].
Definition sub_zero_prog2 : list string := ["mov rax, 0"; "ret"].

Definition sub_zero_asm1 : ErrorT ParseValidatedError (list (string * Lines)) :=
  ErrorT.map (fun lines => [("sub_version", lines)]) (parse_validated sub_zero_prog1).

Definition sub_zero_asm2 : ErrorT ParseValidatedError (list (string * Lines)) :=
  ErrorT.map (fun lines => [("mov_version", lines)]) (parse_validated sub_zero_prog2).

Definition check_sub_equivalence :
    ErrorT ParseValidatedError
      (ErrorT (option (string * Lines) * EquivalenceCheckingError) unit) :=
  asm1 <- sub_zero_asm1;
  asm2 <- sub_zero_asm2;
  Success (check_asm_equivalence asm1 asm2
            xor_test_input_types xor_test_output_types).

Compute check_sub_equivalence.

(* ============================================================================
   Test 3: Identity function - two ways

   Both return the input unchanged:
   - mov rax, rdi; ret  (Move input from rdi to rax)
   - mov rax, rdi; mov rax, rax; ret  (Same but with redundant mov)
   ============================================================================ *)

Definition id_prog1 : list string := ["mov rax, rdi"; "ret"].
Definition id_prog2 : list string := ["mov rax, rdi"; "mov rax, rax"; "ret"].

Definition id_asm1 : ErrorT ParseValidatedError (list (string * Lines)) :=
  ErrorT.map (fun lines => [("id_v1", lines)]) (parse_validated id_prog1).

Definition id_asm2 : ErrorT ParseValidatedError (list (string * Lines)) :=
  ErrorT.map (fun lines => [("id_v2", lines)]) (parse_validated id_prog2).

(* One 64-bit input in rdi *)
Definition id_test_input_types : type_spec := [None].

(* One 64-bit output in rax *)
Definition id_test_output_types : type_spec := [None].

Definition check_id_equivalence :
    ErrorT ParseValidatedError
      (ErrorT (option (string * Lines) * EquivalenceCheckingError) unit) :=
  asm1 <- id_asm1;
  asm2 <- id_asm2;
  Success (check_asm_equivalence (dereference_output_scalars:=false) asm1 asm2
            id_test_input_types id_test_output_types
            assembly_calling_registers
            assembly_callee_saved_registers
            0).

Compute check_id_equivalence.

(* ============================================================================
   Test 4: Addition with two inputs

   Both add two registers:
   - add rax, rbx; ret  (Add rbx to rax)
   - mov rcx, rax; add rcx, rbx; mov rax, rcx; ret  (Same via intermediate reg)
   ============================================================================ *)

Definition add_prog1 : list string := ["add rax, rbx"; "ret"].
Definition add_prog2 : list string := ["mov rcx, rax"; "add rcx, rbx"; "mov rax, rcx"; "ret"].

Definition add_asm1 : ErrorT ParseValidatedError (list (string * Lines)) :=
  ErrorT.map (fun lines => [("add_v1", lines)]) (parse_validated add_prog1).

Definition add_asm2 : ErrorT ParseValidatedError (list (string * Lines)) :=
  ErrorT.map (fun lines => [("add_v2", lines)]) (parse_validated add_prog2).

(* Two 64-bit inputs: rax and rbx *)
Definition add_test_input_types : type_spec := [None; None].

(* One 64-bit output in rax *)
Definition add_test_output_types : type_spec := [None].

Definition check_add_equivalence :
    ErrorT ParseValidatedError
      (ErrorT (option (string * Lines) * EquivalenceCheckingError) unit) :=
  asm1 <- add_asm1;
  asm2 <- add_asm2;
  Success (check_asm_equivalence (dereference_output_scalars:=false) asm1 asm2
            add_test_input_types add_test_output_types
            assembly_calling_registers
            assembly_callee_saved_registers
            0).

Compute check_add_equivalence.

(* ============================================================================
   Test 5: Negative test - Non-equivalent programs

   These should NOT be equivalent:
   - add rax, rbx; ret  (Addition)
   - sub rax, rbx; ret  (Subtraction)
   ============================================================================ *)

Definition add_prog : list string := ["add rax, rbx"; "ret"].
Definition sub_prog : list string := ["sub rax, rbx"; "ret"].

Definition add_asm : ErrorT ParseValidatedError (list (string * Lines)) :=
  ErrorT.map (fun lines => [("add_op", lines)]) (parse_validated add_prog).

Definition sub_asm : ErrorT ParseValidatedError (list (string * Lines)) :=
  ErrorT.map (fun lines => [("sub_op", lines)]) (parse_validated sub_prog).

Definition check_add_sub_nonequivalence :
    ErrorT ParseValidatedError
      (ErrorT (option (string * Lines) * EquivalenceCheckingError) unit) :=
  asm1 <- add_asm;
  asm2 <- sub_asm;
  Success (check_asm_equivalence (dereference_output_scalars:=false) asm1 asm2
            add_test_input_types add_test_output_types
            assembly_calling_registers
            assembly_callee_saved_registers
            0).

(* This should return an Error showing Unable_to_unify *)
Compute check_add_sub_nonequivalence.

(* ============================================================================
   Usage Notes:

   To test a specific instruction:
   1. Write two assembly programs: one using the instruction, one without
   2. Parse both programs with parse_validated
   3. Define appropriate input_types and output_types
   4. Call check_asm_equivalence with both programs
   5. Use Compute to see if they're equivalent

   Type specifications:
   - [None]: single scalar value (Z)
   - [None; None]: two scalar values
   - [Some n]: array of n elements
   - [None; Some 4]: scalar followed by 4-element array

   Register conventions (from default_equivalence_checker_options):
   - assembly_calling_registers: [rdi; rsi; rdx; rcx; r8; r9; rax; ...]
   - assembly_callee_saved_registers: [rbx; rsp; rbp; r12; r13; r14; r15]
   ============================================================================ *)
