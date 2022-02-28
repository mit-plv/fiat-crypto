Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Crypto.Util.Tuple.
Require Crypto.Util.OptionList.
Import ListNotations.

Local Open Scope list_scope.

Local Set Implicit Arguments.
Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.
Local Set Primitive Projections.

Inductive REG :=
|     rax |     rcx |     rdx |     rbx | rsp  | rbp  | rsi  | rdi  | r8  | r9  | r10  | r11  | r12  | r13  | r14  | r15
|     eax |     ecx |     edx |     ebx | esp  | ebp  | esi  | edi  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d
|      ax |      cx |      dx |      bx |  sp  |  bp  |  si  |  di  | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w
| ah | al | ch | cl | dh | dl | bh | bl |  spl |  bpl |  sil |  dil | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b
.

Definition CONST := Z.
Coercion CONST_of_Z (x : Z) : CONST := x.

Record MEM := { mem_is_byte : bool ; mem_reg : REG ; mem_extra_reg : option REG ; mem_offset : option Z }.

Inductive FLAG := CF | PF | AF | ZF | SF | OF.

Inductive OpCode :=
| adc
| adcx
| add
| adox
| and
| bzhi
| clc
| cmovc
| cmovnz
| dec
| imul
| inc
| lea
| mov
| movzx
| mulx
| ret
| sar
| rcr
| sbb
| setc
| seto
| shl
| shlx
| shr
| shrd
| sub
| test
| xchg
| xor
.

Inductive ARG := reg (r : REG) | mem (m : MEM) | const (c : CONST).
Coercion reg : REG >-> ARG.
Coercion mem : MEM >-> ARG.
Coercion const : CONST >-> ARG.

Record NormalInstruction := { op : OpCode ; args : list ARG }.

Inductive RawLine :=
| SECTION (name : string)
| GLOBAL (name : string)
| LABEL (name : string)
| EMPTY
| INSTR (instr : NormalInstruction)
.
Coercion INSTR : NormalInstruction >-> RawLine.
Record Line := { indent : string ; rawline :> RawLine ; pre_comment_whitespace : string ; comment : option string }.
Definition Lines := list Line.

Definition reg_size (r : REG) : N :=
      match r with
      |(    rax |     rcx |     rdx |     rbx | rsp  | rbp  | rsi  | rdi  | r8  | r9  | r10  | r11  | r12  | r13  | r14  | r15 )
       => 64
      |(    eax |     ecx |     edx |     ebx | esp  | ebp  | esi  | edi  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d)
       => 32
      |(     ax |      cx |      dx |      bx |  sp  |  bp  |  si  |  di  | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w)
       => 16
      |(ah | al | ch | cl | dh | dl | bh | bl |  spl |  bpl |  sil |  dil | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b)
       => 8
      end.

Definition standalone_operand_size (x : ARG) : option N :=
  match x with
  | reg r => Some (reg_size r)
  | mem m => if m.(mem_is_byte)
             then Some 8
             else None
  | const c => None
  end%N.

Definition opcode_size (op : OpCode) :=
  match op with
  | seto | setc => Some 8
  | ret => Some 64 (* irrelevant? *)
  | clc => Some 1 (* irrelevant? *)
  | _ => None
  end%N.

Definition operation_size instr :=
  match opcode_size instr.(op) with
  | Some s => Some s | None =>
  let argsizes := List.map standalone_operand_size instr.(args) in
  match OptionList.Option.List.lift argsizes with
  | Some szs => match szs with
                | nil => None (* unspecified *)
                | _ => Some (List.fold_right N.max 0%N szs) (* fully specified *)
                end
  | _ => match OptionList.Option.List.map id argsizes with
         | nil => None (* unspecified *)
         | szs =>
             let m := List.fold_right N.max 0%N szs in
             let n := List.fold_right N.min m szs in
             if N.eqb m n (* uniquely inferred from annotations *)
             then Some n
             else None (* inference needed but ambiguous *)
         end
  end
  end.

Definition operand_size (x : ARG) (operation_size : N) : N :=
  match standalone_operand_size x with
  | Some s => s
  | None => operation_size
  end.


Definition reg_index (r : REG) : nat
  :=  match r with
      |     rax
      |     eax
      |      ax
      |(ah | al)
       => 0
      |     rcx
      |     ecx
      |      cx
      |(ch | cl)
       => 1
      |     rdx
      |     edx
      |      dx
      |(dh | dl)
       => 2
      |     rbx
      |     ebx
      |      bx
      |(bh | bl)
       => 3
      | rsp
      | esp
      |  sp
      |( spl)
       => 4
      | rbp
      | ebp
      |  bp
      |( bpl)
       => 5
      | rsi
      | esi
      |  si
      |( sil)
       => 6
      | rdi
      | edi
      |  di
      |( dil)
       => 7
      | r8
      | r8d
      | r8w
      | r8b
        => 8
      | r9
      | r9d
      | r9w
      | r9b
        => 9
      | r10
      | r10d
      | r10w
      | r10b
        => 10
      | r11
      | r11d
      | r11w
      | r11b
        => 11
      | r12
      | r12d
      | r12w
      | r12b
        => 12
      | r13
      | r13d
      | r13w
      | r13b
        => 13
      | r14
      | r14d
      | r14w
      | r14b
        => 14
      | r15
      | r15d
      | r15w
      | r15b
        => 15
      end.
Definition reg_offset (r : REG) : N :=
      match r with
      |(    rax |     rcx |     rdx |     rbx | rsp  | rbp  | rsi  | rdi  | r8  | r9  | r10  | r11  | r12  | r13  | r14  | r15 )
      |(    eax |     ecx |     edx |     ebx | esp  | ebp  | esi  | edi  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d)
      |(     ax |      cx |      dx |      bx |  sp  |  bp  |  si  |  di  | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w)
      |(     al |      cl |      dl |      bl |  spl |  bpl |  sil |  dil | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b)
       => 0
      |(ah      | ch      | dh      | bh      )
       => 8
      end.
Definition index_and_shift_and_bitcount_of_reg (r : REG) :=
  (reg_index r, reg_offset r, reg_size r).

(** convenience printing function *)
Definition widest_register_of_index (n : nat) : REG
  := match n with
     | 0 => rax
     | 1 => rcx
     | 2 => rdx
     | 3 => rbx
     | 4 => rsp
     | 5 => rbp
     | 6 => rsi
     | 7 => rdi
     | 8 => r8
     | 9 => r9
     | 10 => r10
     | 11 => r11
     | 12 => r12
     | 13 => r13
     | 14 => r14
     | 15 => r15
     | _ => rax
     end%nat.
Lemma widest_register_of_index_correct
  : forall n,
    (~exists r, reg_index r = n)
    \/ (let r := widest_register_of_index n in reg_index r = n
       /\ forall r', reg_index r' = n -> r = r' \/ (reg_size r' < reg_size r)%N).
Proof.
  intro n; set (r := widest_register_of_index n).
  cbv in r.
  repeat match goal with r := context[match ?n with _ => _ end] |- _ => destruct n; [ right | ] end;
    [ .. | left; intros [ [] H]; cbv in H; congruence ].
  all: subst r; split; [ reflexivity | ].
  all: intros [] H; cbv in H; try (exfalso; congruence).
  all: try (left; reflexivity).
  all: try (right; vm_compute; reflexivity).
Qed.
