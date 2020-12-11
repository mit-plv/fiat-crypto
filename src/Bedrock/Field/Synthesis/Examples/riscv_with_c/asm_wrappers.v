Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Map.Interface.
Require Import bedrock2.Syntax.
Require Import coqutil.Map.SortedList.
Require Import coqutil.Map.SortedListString.

Open Scope Z_scope.
Open Scope string_scope.

Notation src_env := (SortedListString.map (list string * list string * Syntax.cmd.cmd)).
Notation pos_env := (SortedListString.map Z).

Definition LF : string := String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".

Definition ZToStr(z: Z): string := DecimalString.NilZero.string_of_int (BinInt.Z.to_int z).
Definition natToStr(n: nat): string := ZToStr (Z.of_nat n).

Fixpoint save_arg_regs(pastLastName: nat)(pastLastOffset: Z): string :=
  match pastLastName with
  | O => ""
  | S lastName => save_arg_regs lastName (pastLastOffset-4) ++
                  "  sw a" ++ natToStr lastName ++ ", " ++ ZToStr (pastLastOffset-4) ++ "(sp)" ++ LF
  end.

Fixpoint load_res_regs(pastLastName: nat)(pastLastOffset: Z): string :=
  match pastLastName with
  | O => ""
  | S lastName => load_res_regs lastName (pastLastOffset-4) ++
                  "  lw a" ++ natToStr lastName ++ ", " ++ ZToStr (pastLastOffset-4) ++ "(sp)" ++ LF
  end.

Definition call(e_src: src_env)(e_pos: pos_env)(f: string): string :=
  match map.get e_src f, map.get e_pos f with
  | Some (argvars, resvars, body), Some funpos =>
  "  addi sp, sp, -4" ++ LF ++
  "  sw ra, 0(sp)" ++ LF ++
  save_arg_regs (List.length argvars) 0 ++
  "  jal ra, bedrock2functions+" ++ ZToStr funpos ++ LF ++
  load_res_regs (List.length resvars) (- Z.of_nat (List.length argvars)) ++
  "  lw ra, 0(sp)" ++ LF ++
  "  addi sp, sp, 4" ++ LF ++
  "  ret" ++ LF
  | _, _ => "ERROR: " ++ f ++ " not found"
  end.

Fixpoint wrappers(e_src: src_env)(e_pos: pos_env)(fs: list string): string :=
  match fs with
  | f :: rest => let s := call e_src e_pos f in
                 ".globl " ++ f ++ LF ++
                 f ++ ":" ++ LF ++
                 s ++
                 wrappers e_src e_pos rest
  | nil => ""
  end.

Definition asm_wrappers(e_src: src_env)(e_pos: pos_env)(binfilename: string): string :=
  ".section .text" ++ LF ++
  "bedrock2functions: .incbin """ ++ binfilename ++ """" ++ LF ++
  wrappers e_src e_pos (map.keys e_pos).
