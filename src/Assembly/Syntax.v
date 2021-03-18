Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Crypto.Util.Tuple.
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
| clc
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
| sbb
| setc
| seto
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

Definition operand_size (x : ARG) : option N :=
  match x with
  | reg r => Some (reg_size r)
  | mem m => if m.(mem_is_byte)
             then Some 8
             else None
  | const c => None
  end%N.
Definition unify_operand_size (a : option N)  (b : option (option N)) : option (option N) :=
  match a with
  | None => b
  | Some s =>
      match b with
      | None => None
      | Some None => Some (Some s)
      | Some (Some s') => if N.eqb s s' then Some (Some s) else None
      end
  end.
(* None => contradiction, Some None => underconstrained, Some Some s => size s *)
Definition operation_size (instr : NormalInstruction) : option (option N) :=
  List.fold_right unify_operand_size (Some None) (List.map operand_size instr.(args)).
