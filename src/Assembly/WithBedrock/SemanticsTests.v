(** Regression tests for the concrete semantics' treatment of memory
    operands it cannot model.  The machine state has no instruction
    pointer, so RIP-relative and label-based operands have no
    denotation; this mirrors the error raised by [Symbolic.Address]
    (scrutineer finding #2516) and is what keeps the soundness proof
    in [SymbolicProofs] honest about such operands. *)
From Coq Require Import ZArith.
From Coq Require Import String.
From Coq Require Import List.
Import ListNotations.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.WithBedrock.Semantics.

Local Open Scope Z_scope.

Definition operand (k : rip_relative_kind) (lbl : option String.string) : MEM
  := {| mem_bits_access_size := None
      ; mem_base_reg := None
      ; mem_scale_reg := None
      ; mem_base_label := lbl
      ; mem_offset := Some 0x26
      ; rip_relative := k |}.

Example absolute_displacement_ok st
  : DenoteAddress 64 st (operand not_rip_relative None) = Some 0x26.
Proof. vm_compute; reflexivity. Qed.

Example explicitly_rip_relative_undefined st
  : DenoteAddress 64 st (operand explicitly_rip_relative None) = None.
Proof. reflexivity. Qed.

Example implicitly_rip_relative_undefined st
  : DenoteAddress 64 st (operand implicitly_rip_relative None) = None.
Proof. reflexivity. Qed.

Example label_undefined st
  : DenoteAddress 64 st (operand not_rip_relative (Some "foo"%string)) = None.
Proof. reflexivity. Qed.

Example load_rip_relative_undefined st
  : DenoteOperand 64 64 st (mem (operand explicitly_rip_relative None)) = None.
Proof. reflexivity. Qed.

Example store_rip_relative_undefined st v
  : SetOperand 64 64 st (mem (operand implicitly_rip_relative None)) v = None.
Proof. reflexivity. Qed.

(** [lea] is the instruction that never touches memory, so it is the
    one for which the address itself is the result. *)
Example lea_rip_relative_undefined st
  : DenoteNormalInstruction st {| prefix := None ; op := lea ; args := [reg rcx; mem (operand explicitly_rip_relative None)] |} = None.
Proof. reflexivity. Qed.
