(** Regression tests for the symbolic executor's treatment of memory
    operands that it cannot model.

    The symbolic machine has no instruction pointer, so RIP-relative
    memory operands (explicit [\[rip + disp\]] or implicit via
    [DEFAULT REL]) and label-based operands must be rejected rather
    than silently interpreted as absolute displacements.  Before this
    was checked, [lea rcx, \[rip + 0x26\]] was symbolically executed as
    [mov rcx, 0x26], which let the equivalence checker certify
    assembly that computes something else on real hardware
    (scrutineer finding #2516). *)
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import ZArith.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Parse.
Require Import Crypto.Assembly.Equality.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.Equivalence.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Local Instance test_opts : symbolic_options_computed_opt
  := {| asm_rewriting_passes := default_rewriting_passes (rewriting_pipeline:=default_rewrite_pass_order) (rewriting_pass_filter:=fun _ => true)
      ; asm_debug_symex_asm_first_computed := false
      ; asm_node_reveal_depth_computed := default_node_reveal_depth |}.

(** Parse [asm] and symbolically execute it from the initial state
    used by [symex_asm_func] (every 64-bit register holds a fresh
    symbolic value, memory and flags are empty). *)
Definition symex (asm : list string) : ErrorT (list string) (ErrorT (error * symbolic_state) (unit * symbolic_state))
  := match parse asm with
     | Success lines => Success (SymexLines lines (init_symbolic_state dag.empty))
     | Error errs => Error errs
     end.

Definition symex_rejected_as_rip_relative (asm : list string) : bool
  := match symex asm with
     | Success (Error (error.unsupported_rip_relative_addressing _, _)) => true
     | _ => false
     end.

Definition symex_rejected_as_label (asm : list string) : bool
  := match symex asm with
     | Success (Error (error.unsupported_label_in_memory _, _)) => true
     | _ => false
     end.

Definition symex_succeeds (asm : list string) : bool
  := match symex asm with
     | Success (Success _) => true
     | _ => false
     end.

(** Sanity check that the harness actually reaches symbolic execution:
    an ordinary register-relative [lea] goes through.  (Loads and
    stores cannot be checked this way because the initial symbolic
    memory is empty.) *)
Example lea_reg_relative_ok
  : symex_succeeds ["lea rcx, [rax + 0x26]"] = true.
Proof. vm_compute; reflexivity. Qed.

(** [lea] never touches memory, so before the check it silently
    produced the displacement as a constant. *)
Example lea_rip_relative_rejected
  : symex_rejected_as_rip_relative ["lea rcx, [rip + 0x26]"] = true.
Proof. vm_compute; reflexivity. Qed.
Example lea_rip_relative_neg_rejected
  : symex_rejected_as_rip_relative ["lea rcx, [rip - 0x26]"] = true.
Proof. vm_compute; reflexivity. Qed.

(** Loads and stores are rejected with the same explicit error, rather
    than by accidentally failing to find the address in symbolic memory. *)
Example load_rip_relative_rejected
  : symex_rejected_as_rip_relative ["mov rax, [rip + 0x26]"] = true.
Proof. vm_compute; reflexivity. Qed.
Example store_rip_relative_rejected
  : symex_rejected_as_rip_relative ["mov [rip + 0x26], rax"] = true.
Proof. vm_compute; reflexivity. Qed.
Example load_rip_relative_sized_rejected
  : symex_rejected_as_rip_relative ["mov rax, qword ptr [rip + 0x26]"] = true.
Proof. vm_compute; reflexivity. Qed.

(** The [DEFAULT REL] directive itself is rejected as an unsupported
    line, so implicitly RIP-relative operands never reach [Address]
    through [SymexLines]; check [Address] directly on such an operand
    (as produced by parsing under [default_rel := true]). *)
Example default_rel_line_rejected
  : match symex ["DEFAULT REL"; "mov rax, [0x26]"] with
    | Success (Error (error.unsupported_line DEFAULT_REL, _)) => true
    | _ => false
    end = true.
Proof. vm_compute; reflexivity. Qed.

Definition implicitly_rip_relative_operand : MEM
  := {| mem_bits_access_size := None
      ; mem_base_reg := None
      ; mem_scale_reg := None
      ; mem_base_label := None
      ; mem_offset := Some 0x26%Z
      ; rip_relative := implicitly_rip_relative |}.

Example parse_default_rel_is_implicitly_rip_relative
  : match @parse_Lines {| default_rel := true |} ["mov rax, [0x26]"] with
    | Success [ {| rawline := INSTR {| args := [_; mem m] |} |} ]
      => MEM_beq m implicitly_rip_relative_operand
    | _ => false
    end = true.
Proof. vm_compute; reflexivity. Qed.

Example address_implicitly_rip_relative_rejected
  : match @Address _ (Build_description "test" false) 64%N implicitly_rip_relative_operand (init_symbolic_state dag.empty) with
    | Error (error.unsupported_rip_relative_addressing _, _) => true
    | _ => false
    end = true.
Proof. vm_compute; reflexivity. Qed.

(** Label-based operands were already rejected; keep it that way. *)
Example lea_label_rejected
  : symex_rejected_as_label ["lea rcx, [foo]"] = true.
Proof. vm_compute; reflexivity. Qed.
