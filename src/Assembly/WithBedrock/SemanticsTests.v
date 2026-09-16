From Coq Require Import List ZArith.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.WithBedrock.Semantics.
Require coqutil.Map.Interface.
Import ListNotations.

Local Open Scope list_scope.
Local Open Scope x86symex_scope.

Definition imul_test_lhs : Z := 0xffffffff00000001.
Definition imul_test_rhs : Z := 3.

Definition imul_test_instruction (opc : OpCode) : NormalInstruction :=
  {| prefix := None; Syntax.op := opc; args := [reg rcx] |}.

Definition imul_test_machine_state : machine_state :=
  {| machine_reg_state :=
       set_reg (set_reg (Crypto.Util.Tuple.repeat 0%Z _) rax imul_test_lhs)
               rcx imul_test_rhs;
     machine_flag_state := havoc_flags;
     machine_mem_state := coqutil.Map.Interface.map.empty |}.

Definition concrete_mul_result (opc : OpCode) : option (Z * Z) :=
  match DenoteNormalInstruction imul_test_machine_state
          (imul_test_instruction opc) with
  | Some st => Some (get_reg st rax, get_reg st rdx)
  | None => None
  end.

Example one_operand_imul_is_signed_concrete :
  concrete_mul_result imul =
    Some (0xfffffffd00000003%Z, 0xffffffffffffffff%Z).
Proof. vm_compute. reflexivity. Qed.

Example one_operand_mul_remains_unsigned_concrete :
  concrete_mul_result Syntax.mul = Some (0xfffffffd00000003%Z, 2%Z).
Proof. vm_compute. reflexivity. Qed.

Local Instance imul_test_options : symbolic_options_computed_opt :=
  {| asm_rewriting_passes := RewritePass.default_rewrite_pass_order;
     asm_debug_symex_asm_first_computed := false;
     asm_node_reveal_depth_computed := default_node_reveal_depth |}.
Local Instance imul_test_description : description := no_description.

Definition imul_test_symbolic_state : symbolic_state :=
  {| dag_state := dag.empty;
     symbolic_reg_state := Crypto.Util.Tuple.repeat None _;
     symbolic_flag_state := Crypto.Util.Tuple.repeat None _;
     symbolic_mem_state := [] |}.

Definition symbolic_mul (opc : OpCode) : M (Z * Z) :=
  lhs <- App (const imul_test_lhs, []);
  rhs <- App (const imul_test_rhs, []);
  _ <- SetReg64 (reg_index rax) lhs;
  _ <- SetReg64 (reg_index rcx) rhs;
  _ <- SymexNormalInstruction (imul_test_instruction opc);
  lo <- GetReg rax;
  hi <- GetReg rdx;
  lo <- RevealConst lo;
  hi <- RevealConst hi;
  ret (lo, hi).

Definition symbolic_mul_result (opc : OpCode) : option (Z * Z) :=
  match symbolic_mul opc imul_test_symbolic_state with
  | Success (result, _) => Some result
  | Error _ => None
  end.

Example one_operand_imul_is_signed_symbolic :
  symbolic_mul_result imul =
    Some (0xfffffffd00000003%Z, 0xffffffffffffffff%Z).
Proof. vm_compute. reflexivity. Qed.

Example one_operand_mul_remains_unsigned_symbolic :
  symbolic_mul_result Syntax.mul = Some (0xfffffffd00000003%Z, 2%Z).
Proof. vm_compute. reflexivity. Qed.
