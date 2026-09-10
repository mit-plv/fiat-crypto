From Coq Require Import List.
From Coq Require Import String.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Parse.
Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.

Definition parsed_second_argument_rip_relative (line_index : nat) (asm : list string)
  : option rip_relative_kind :=
  match parse asm with
  | Success lines =>
      match List.nth_error lines line_index with
      | Some line =>
          match line.(rawline) with
          | INSTR instr =>
              match instr.(args) with
              | _ :: mem operand :: _ => Some operand.(rip_relative)
              | _ => None
              end
          | _ => None
          end
      | None => None
      end
  | Error _ => None
  end.

Example parse_explicit_rip_relative_operand :
  parsed_second_argument_rip_relative 0 ["lea rcx, [rip + 0x26]"] =
  Some explicitly_rip_relative.
Proof. vm_compute. reflexivity. Qed.

Example parse_default_rel_operand :
  parsed_second_argument_rip_relative 1 ["DEFAULT REL"; "lea rcx, [0x26]"] =
  Some implicitly_rip_relative.
Proof. vm_compute. reflexivity. Qed.
