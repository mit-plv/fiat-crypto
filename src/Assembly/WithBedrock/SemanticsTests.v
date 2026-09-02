From Coq Require Import NArith.
From Coq Require Import ZArith.
From Coq Require Import List.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.WithBedrock.Semantics.
Import ListNotations.

Local Open Scope N_scope.
Local Open Scope Z_scope.

Section RipRelativeAddressing.
  Context (st : machine_state).

  Definition explicit_rip_relative_memory : MEM :=
    {| mem_bits_access_size := None;
       mem_base_reg := None;
       mem_scale_reg := None;
       mem_base_label := None;
       mem_offset := Some 0x26;
       rip_relative := explicitly_rip_relative |}.

  Definition implicit_rip_relative_memory : MEM :=
    {| mem_bits_access_size := None;
       mem_base_reg := None;
       mem_scale_reg := None;
       mem_base_label := None;
       mem_offset := Some 0x26;
       rip_relative := implicitly_rip_relative |}.

  Example explicit_rip_relative_address_is_unsupported :
    AddressSupported explicit_rip_relative_memory = false.
  Proof. reflexivity. Qed.

  Example implicit_rip_relative_address_is_unsupported :
    AddressSupported implicit_rip_relative_memory = false.
  Proof. reflexivity. Qed.

  Example reading_rip_relative_memory_is_unsupported :
    DenoteOperand 64 64 st (mem implicit_rip_relative_memory) = None.
  Proof. reflexivity. Qed.

  Example writing_rip_relative_memory_is_unsupported (v : Z) :
    SetOperand 64 64 st (mem explicit_rip_relative_memory) v = None.
  Proof. reflexivity. Qed.

  Example lea_with_rip_relative_address_is_unsupported :
    DenoteNormalInstruction st
      {| Syntax.prefix := None;
         Syntax.op := Syntax.lea;
         Syntax.args := [Syntax.reg Syntax.rcx; Syntax.mem explicit_rip_relative_memory] |} = None.
  Proof. reflexivity. Qed.
End RipRelativeAddressing.

Section SymbolicRipRelativeAddressing.
  Context {opts : symbolic_options_computed_opt}.
  Context {descr : description}.
  Context {sa : AddressSize}.
  Context (st : symbolic_state).

  Example symbolic_rip_relative_address_is_unsupported :
    @Address opts descr sa explicit_rip_relative_memory st =
    ErrorT.Error (error.unsupported_rip_relative_addressing, st).
  Proof. reflexivity. Qed.
End SymbolicRipRelativeAddressing.
