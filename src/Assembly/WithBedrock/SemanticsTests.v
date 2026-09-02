(** Regression tests for the semantics of one-operand [mul] and [imul].

    The one-operand form of [imul] is a *signed* widening multiply
    (rdx:rax := signed(rax) * signed(src)), whereas [mul] is unsigned.  The
    two agree on the low half of the product but not on the high half
    whenever an operand has its top bit set.  The concrete semantics
    ([Semantics.DenoteNormalInstruction]) and the symbolic executor
    ([Symbolic.SymexNormalInstruction]) used to share a single unsigned
    branch for both mnemonics (scrutineer finding #2514); these tests pin
    down the hardware behaviour for both models, on the same inputs.

    The expected values were obtained by executing the instructions on
    x86-64 hardware. *)
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import String.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.Equivalence.
Require Import Crypto.Assembly.WithBedrock.Semantics.
Require Import coqutil.Map.Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.

(** ** Concrete semantics *)

Definition initial_machine_state (rax_val rcx_val : Z) : machine_state
  := {| machine_reg_state := Semantics.set_reg (Semantics.set_reg (Tuple.repeat 0 _) rax rax_val) rcx rcx_val
      ; machine_flag_state := havoc_flags
      ; machine_mem_state := map.empty |}.

Definition denote_one (instr : NormalInstruction) (rax_val rcx_val : Z) (out : REG) : option Z
  := option_map (fun st : machine_state => Semantics.get_reg st out) (DenoteNormalInstruction (initial_machine_state rax_val rcx_val) instr).

Definition mul_rcx  : NormalInstruction := {| Syntax.prefix := None ; Syntax.op := Syntax.mul  ; Syntax.args := [reg rcx] |}.
Definition imul_rcx : NormalInstruction := {| Syntax.prefix := None ; Syntax.op := Syntax.imul ; Syntax.args := [reg rcx] |}.
Definition mul_cl   : NormalInstruction := {| Syntax.prefix := None ; Syntax.op := Syntax.mul  ; Syntax.args := [reg cl] |}.
Definition imul_cl  : NormalInstruction := {| Syntax.prefix := None ; Syntax.op := Syntax.imul ; Syntax.args := [reg cl] |}.

(** rax = 0xffffffff00000001 (the top limb of the P-256 prime; bit 63 set), rcx = 3 *)
Example denote_mul_rcx_hi  : denote_one mul_rcx  0xffffffff00000001 3 rdx = Some 0x2.                Proof. vm_compute; reflexivity. Qed.
Example denote_mul_rcx_lo  : denote_one mul_rcx  0xffffffff00000001 3 rax = Some 0xfffffffd00000003. Proof. vm_compute; reflexivity. Qed.
Example denote_imul_rcx_hi : denote_one imul_rcx 0xffffffff00000001 3 rdx = Some 0xffffffffffffffff. Proof. vm_compute; reflexivity. Qed.
Example denote_imul_rcx_lo : denote_one imul_rcx 0xffffffff00000001 3 rax = Some 0xfffffffd00000003. Proof. vm_compute; reflexivity. Qed.

(** both operands with bit 63 set: rax = -2, rcx = -2^63+1 as signed values *)
Example denote_mul_rcx_hi'  : denote_one mul_rcx  0xfffffffffffffffe 0x8000000000000001 rdx = Some 0x7fffffffffffffff. Proof. vm_compute; reflexivity. Qed.
Example denote_imul_rcx_hi' : denote_one imul_rcx 0xfffffffffffffffe 0x8000000000000001 rdx = Some 0x0.                Proof. vm_compute; reflexivity. Qed.
Example denote_mul_rcx_lo'  : denote_one mul_rcx  0xfffffffffffffffe 0x8000000000000001 rax = Some 0xfffffffffffffffe. Proof. vm_compute; reflexivity. Qed.
Example denote_imul_rcx_lo' : denote_one imul_rcx 0xfffffffffffffffe 0x8000000000000001 rax = Some 0xfffffffffffffffe. Proof. vm_compute; reflexivity. Qed.

(** no top bit set: signed and unsigned agree *)
Example denote_mul_rcx_hi''  : denote_one mul_rcx  0x123456789 0x23456789a rdx = Some 0x2. Proof. vm_compute; reflexivity. Qed.
Example denote_imul_rcx_hi'' : denote_one imul_rcx 0x123456789 0x23456789a rdx = Some 0x2. Proof. vm_compute; reflexivity. Qed.

(** 8-bit form writes ah:al; al = 0xff (-1), cl = 3 *)
Example denote_mul_cl_ah  : denote_one mul_cl  0xff 3 ah = Some 0x2.  Proof. vm_compute; reflexivity. Qed.
Example denote_mul_cl_al  : denote_one mul_cl  0xff 3 al = Some 0xfd. Proof. vm_compute; reflexivity. Qed.
Example denote_imul_cl_ah : denote_one imul_cl 0xff 3 ah = Some 0xff. Proof. vm_compute; reflexivity. Qed.
Example denote_imul_cl_al : denote_one imul_cl 0xff 3 al = Some 0xfd. Proof. vm_compute; reflexivity. Qed.
(** the untouched upper bytes of rax are preserved *)
Example denote_imul_cl_rax : denote_one imul_cl 0x11223344556677ff 3 rax = Some 0x112233445566fffd. Proof. vm_compute; reflexivity. Qed.

(** ** Symbolic executor *)

Local Instance test_symbolic_options : symbolic_options_computed_opt
  := {| asm_rewriting_passes := default_rewriting_passes (rewriting_pipeline:=default_rewrite_pass_order) (rewriting_pass_filter:=fun _ => true)
      ; asm_debug_symex_asm_first_computed := false
      ; asm_node_reveal_depth_computed := default_node_reveal_depth |}.

(** Symbolically execute [instr] from a state where every register holds a
    fresh symbol, then evaluate the requested output register with the
    symbols for [rax] and [rcx] instantiated to the given values (and every
    other register to [0]). *)
Definition symex_one (instr : NormalInstruction) (rax_val rcx_val : Z) (out : REG) : option Z
  := let st := init_symbolic_state dag.empty in
     let ctx : symbol -> option Z
       := fun n => if (n =? reg_index rax)%N then Some rax_val
                   else if (n =? reg_index rcx)%N then Some rcx_val
                        else Some 0 in
     match (_ <- SymexNormalInstruction (descr:=Build_description "SemanticsTests" true) instr;
            GetReg (descr:=Build_description "SemanticsTests" true) out)%x86symex st with
     | Success (i, st) => interp_expr ctx (reveal st 100 i)
     | Error _ => None
     end.

Example symex_mul_rcx_hi  : symex_one mul_rcx  0xffffffff00000001 3 rdx = Some 0x2.                Proof. vm_compute; reflexivity. Qed.
Example symex_mul_rcx_lo  : symex_one mul_rcx  0xffffffff00000001 3 rax = Some 0xfffffffd00000003. Proof. vm_compute; reflexivity. Qed.
Example symex_imul_rcx_hi : symex_one imul_rcx 0xffffffff00000001 3 rdx = Some 0xffffffffffffffff. Proof. vm_compute; reflexivity. Qed.
Example symex_imul_rcx_lo : symex_one imul_rcx 0xffffffff00000001 3 rax = Some 0xfffffffd00000003. Proof. vm_compute; reflexivity. Qed.

Example symex_mul_rcx_hi'  : symex_one mul_rcx  0xfffffffffffffffe 0x8000000000000001 rdx = Some 0x7fffffffffffffff. Proof. vm_compute; reflexivity. Qed.
Example symex_imul_rcx_hi' : symex_one imul_rcx 0xfffffffffffffffe 0x8000000000000001 rdx = Some 0x0.                Proof. vm_compute; reflexivity. Qed.
Example symex_mul_rcx_lo'  : symex_one mul_rcx  0xfffffffffffffffe 0x8000000000000001 rax = Some 0xfffffffffffffffe. Proof. vm_compute; reflexivity. Qed.
Example symex_imul_rcx_lo' : symex_one imul_rcx 0xfffffffffffffffe 0x8000000000000001 rax = Some 0xfffffffffffffffe. Proof. vm_compute; reflexivity. Qed.

Example symex_mul_rcx_hi''  : symex_one mul_rcx  0x123456789 0x23456789a rdx = Some 0x2. Proof. vm_compute; reflexivity. Qed.
Example symex_imul_rcx_hi'' : symex_one imul_rcx 0x123456789 0x23456789a rdx = Some 0x2. Proof. vm_compute; reflexivity. Qed.

Example symex_mul_cl_ah  : symex_one mul_cl  0xff 3 ah = Some 0x2.  Proof. vm_compute; reflexivity. Qed.
Example symex_mul_cl_al  : symex_one mul_cl  0xff 3 al = Some 0xfd. Proof. vm_compute; reflexivity. Qed.
Example symex_imul_cl_ah : symex_one imul_cl 0xff 3 ah = Some 0xff. Proof. vm_compute; reflexivity. Qed.
Example symex_imul_cl_al : symex_one imul_cl 0xff 3 al = Some 0xfd. Proof. vm_compute; reflexivity. Qed.
Example symex_imul_cl_rax : symex_one imul_cl 0x11223344556677ff 3 rax = Some 0x112233445566fffd. Proof. vm_compute; reflexivity. Qed.
