From Coq Require Import ZArith.
From Coq Require Import NArith.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Derive.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Bool.Reflect.
Require Crypto.Util.Tuple.
Require Crypto.Util.OptionList.
Import ListNotations.

Local Open Scope list_scope.

Local Set Implicit Arguments.
Local Set Primitive Projections.

Inductive REG :=
(* XMM/YMM/ZMM registers *)
| zmm0  | zmm1  | zmm2  | zmm3  | zmm4  | zmm5  | zmm6  | zmm7  | zmm8  | zmm9  | zmm10  | zmm11  | zmm12  | zmm13  | zmm14  | zmm15 | zmm16 | zmm17 | zmm18 | zmm19 | zmm20 | zmm21 | zmm22 | zmm23 | zmm24 | zmm25 | zmm26  | zmm27  | zmm28  | zmm29  | zmm30  | zmm31
| ymm0  | ymm1  | ymm2  | ymm3  | ymm4  | ymm5  | ymm6  | ymm7  | ymm8  | ymm9  | ymm10  | ymm11  | ymm12  | ymm13  | ymm14  | ymm15
| xmm0  | xmm1  | xmm2  | xmm3  | xmm4  | xmm5  | xmm6  | xmm7  | xmm8  | xmm9  | xmm10  | xmm11  | xmm12  | xmm13  | xmm14  | xmm15
(* Segment registers *)
| cs | ds | es | fs | gs | ss
(* Control registers *)
| cr0 | cr1 | cr2 | cr3 | cr4 | cr8 | cr9 | cr10 | cr11 | cr12 | cr13 | cr14 | cr15
| msw
| mxcsr
(* Debug registers *)
| dr0 | dr1 | dr2 | dr3 | dr4 | dr5 | dr6 | dr7 | dr8 | dr9 | dr10 | dr11 | dr12 | dr13 | dr14 | dr15
(* General purpose registers (64/32/16/8 bit) *)
|     rax |     rcx |     rdx |     rbx | rsp  | rbp  | rsi  | rdi  | r8  | r9  | r10  | r11  | r12  | r13  | r14  | r15  | rip
|     eax |     ecx |     edx |     ebx | esp  | ebp  | esi  | edi  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d | eip
|      ax |      cx |      dx |      bx |  sp  |  bp  |  si  |  di  | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w | ip
| ah | al | ch | cl | dh | dl | bh | bl |  spl |  bpl |  sil |  dil | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b
(* MMX registers *)
| mm0 | mm1 | mm2 | mm3 | mm4 | mm5 | mm6 | mm7
(* Special registers *)
(*| st0 | st1 | st2 | st3 | st4 | st5 | st6 | st7  (* FPU stack registers *)*)
| k0 | k1 | k2 | k3 | k4 | k5 | k6 | k7          (* AVX-512 mask registers *)
| gdtr | idtr | ldtr | tr
| cw | sw | tw | fp_cs | fp_opc | fp_ds
(* Flags registers *)
| rflags
| eflags
| flags
.

Definition CONST := Z.
Coercion CONST_of_Z (x : Z) : CONST := x.
Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.
Inductive AccessSize := byte | word | dword | qword | xmmword | ymmword | zmmword.
Local Unset Boolean Equality Schemes.
Local Unset Decidable Equality Schemes.
Coercion bits_of_AccessSize (x : AccessSize) : N
  := match x with
     | byte => 8
     | word => 16
     | dword => 32
     | qword => 64
     | xmmword => 128
     | ymmword => 256
     | zmmword => 512
     end.

Record MEM := { mem_bits_access_size : option AccessSize ; mem_constant_location_label : option string ; mem_base_reg : option REG ; mem_scale_reg : option (Z * REG) ; mem_base_label : option string ; mem_offset : option Z }.

Definition mem_of_reg (r : REG) : MEM :=
  {| mem_base_reg := Some r ; mem_constant_location_label := None ; mem_offset := None ; mem_scale_reg := None ; mem_bits_access_size := None ; mem_base_label := None |}.

Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.
Inductive FLAG := CF | PF | AF | ZF | SF | OF.

Inductive OpPrefix :=
| rep
| repz
| repnz
.

Inductive OpCode :=
| adc
| adcx
| add
| adox
| and
| bzhi
| call
| clc
| cmovb
| cmovc
| cmove    (* Conditional move if equal *)
| cmovne   (* Conditional move if not equal *)
| cmovnz
| cmovo
| cmp
| db
| dd
| dec
| dq
| dw
| imul
| inc
| je
| jmp
| lea
| leave     (* Function epilogue instruction *)
| mov
| movabs    (* Move absolute value into register *)
| movdqa    (* Move aligned packed data *)
| movdqu    (* Move unaligned packed data *)
| movq      (* Move quadword *)
| movd      (* Move doubleword *)
| movsx     (* Move with sign extension *)
| movups    (* Move unaligned packed single-precision floating-point values *)
| movzx
| mul
| mulx
| neg       (* Two's complement negation *)
| nop       (* No operation *)
| not       (* Bitwise NOT *)
| or
| paddq     (* Add packed quadword integers *)
| pop
| psubq     (* Subtract packed quadword integers *)
| pshufd    (* Shuffle packed doublewords *)
| pshufw    (* Shuffle packed words *)
| punpcklqdq (* Unpack and interleave low quadwords *)
| punpckhqdq (* Unpack and interleave high quadwords *)
| pslld     (* Shift packed single-precision floating-point values left *)
| psrld     (* Shift packed single-precision floating-point values right *)
| pand      (* Bitwise AND *)
| pandn     (* Bitwise AND NOT *)
| por       (* Bitwise OR *)
| pxor      (* Bitwise XOR *)
| psrad     (* Shift packed signed integers right arithmetic *)
| push
| rcr
| ret
| rol       (* Rotate left *)
| ror       (* Rotate right *)
| sal       (* Shift arithmetic left (functionally equivalent to shl) *)
| sar       (* Shift arithmetic right *)
| sbb       (* Subtract with borrow *)
| setc
| sete      (* Set byte if equal *)
| setne     (* Set byte if not equal *)
| seto
| shl
| shlx
| shld
| shr
| shrx
| shrd
| sub
| test
| xchg
| xor
.

Record JUMP_LABEL := { jump_near : bool ; label_name : string }.

Inductive ARG := reg (r : REG) | mem (m : MEM) | const (c : CONST) | label (l : JUMP_LABEL).
Coercion reg : REG >-> ARG.
Coercion mem : MEM >-> ARG.
Coercion const : CONST >-> ARG.

Record NormalInstruction := { prefix : option OpPrefix ; op : OpCode ; args : list ARG }.

Inductive RawLine :=
| SECTION (name : string)
| GLOBAL (name : string)
| LABEL (name : string)
| ALIGN (amount : string)
| DEFAULT_REL
| EMPTY
| INSTR (instr : NormalInstruction)
.
Coercion INSTR : NormalInstruction >-> RawLine.
Record Line := { indent : string ; rawline :> RawLine ; pre_comment_whitespace : string ; comment : option string ; line_number : N}.
Definition Lines := list Line.

Definition reg_size (r : REG) : N :=
      match r with
      |(xmm0 | xmm1 | xmm2 | xmm3 | xmm4 | xmm5 | xmm6 | xmm7 | xmm8 | xmm9 | xmm10 | xmm11 | xmm12 | xmm13 | xmm14 | xmm15)
       => 128
      |(zmm0 | zmm1 | zmm2 | zmm3 | zmm4 | zmm5 | zmm6 | zmm7 | zmm8 | zmm9 | zmm10 | zmm11 | zmm12 | zmm13 | zmm14 | zmm15 | zmm16 | zmm17 | zmm18 | zmm19 | zmm20 | zmm21 | zmm22 | zmm23 | zmm24 | zmm25 | zmm26  | zmm27  | zmm28  | zmm29  | zmm30  | zmm31)
       => 512
      |(ymm0 | ymm1 | ymm2 | ymm3 | ymm4 | ymm5 | ymm6 | ymm7 | ymm8 | ymm9 | ymm10 | ymm11 | ymm12 | ymm13 | ymm14 | ymm15)
       => 256
      |(    rax |     rcx |     rdx |     rbx | rsp  | rbp  | rsi  | rdi  | r8  | r9  | r10  | r11  | r12  | r13  | r14  | r15  | rip | rflags)
       => 64
      |(    eax |     ecx |     edx |     ebx | esp  | ebp  | esi  | edi  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d | eip | eflags)
       => 32
      |(     ax |      cx |      dx |      bx |  sp  |  bp  |  si  |  di  | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w | ip | flags)
       => 16
      |(cs | ds | es | fs | gs | ss)
       => 16
      |(ah | al | ch | cl | dh | dl | bh | bl |  spl |  bpl |  sil |  dil | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b)
       => 8
      |(cr0 | cr1 | cr2 | cr3 | cr4 | cr8 | cr9 | cr10 | cr11 | cr12 | cr13 | cr14 | cr15)
       => 64
      |(dr0 | dr1 | dr2 | dr3 | dr4 | dr5 | dr6 | dr7 | dr8 | dr9 | dr10 | dr11 | dr12 | dr13 | dr14 | dr15)
       => 64
      |(mm0 | mm1 | mm2 | mm3 | mm4 | mm5 | mm6 | mm7)
       => 64
      (* |(st0 | st1 | st2 | st3 | st4 | st5 | st6 | st7)
       => 80 *)
      |(k0 | k1 | k2 | k3 | k4 | k5 | k6 | k7)
       => 64
      |(gdtr | idtr | ldtr | tr)
       => 16
      |(cw | sw | tw | fp_cs | fp_opc | fp_ds)
       => 16
      | msw => 16
      | mxcsr => 32
      end.

Definition standalone_operand_size (x : ARG) : option N :=
  match x with
  | reg r => Some (reg_size r)
  | mem m => option_map bits_of_AccessSize m.(mem_bits_access_size)
  | const c => None
  | label _ => None
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


Definition reg_index (r : REG) : N
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
      | rip
      | eip
      | ip
        => 16
      | rflags
      | eflags
      | flags
        => 17
      | xmm0
      | ymm0
      | zmm0
        => 18
      | xmm1
      | ymm1
      | zmm1
        => 19
      | xmm2
      | ymm2
      | zmm2
        => 20
      | xmm3
      | ymm3
      | zmm3
        => 21
      | xmm4
      | ymm4
      | zmm4
        => 22
      | xmm5
      | ymm5
      | zmm5
        => 23
      | xmm6
      | ymm6
      | zmm6
        => 24
      | xmm7
      | ymm7
      | zmm7
        => 25
      | xmm8
      | ymm8
      | zmm8
        => 26
      | xmm9
      | ymm9
      | zmm9
        => 27
      | xmm10
      | ymm10
      | zmm10
        => 28
      | xmm11
      | ymm11
      | zmm11
        => 29
      | xmm12
      | ymm12
      | zmm12
        => 30
      | xmm13
      | ymm13
      | zmm13
        => 31
      | xmm14
      | ymm14
      | zmm14
        => 32
      | xmm15
      | ymm15
      | zmm15
        => 33
      | zmm16 => 34
      | zmm17 => 35
      | zmm18 => 36
      | zmm19 => 37
      | zmm20 => 38
      | zmm21 => 39
      | zmm22 => 40
      | zmm23 => 41
      | zmm24 => 42
      | zmm25 => 43
      | zmm26 => 44
      | zmm27 => 45
      | zmm28 => 46
      | zmm29 => 47
      | zmm30 => 48
      | zmm31 => 49
      | cr0
      | msw
        => 50
      | cr1
        => 51
      | cr2
        => 52
      | cr3
        => 53
      | cr4
        => 54
      | cr8
        => 55
      | cr9
        => 56
      | cr10
        => 57
      | cr11
        => 58
      | cr12
        => 59
      | cr13
        => 60
      | cr14
        => 61
      | cr15
        => 62
      | mm0
      (* | st0 *)
        => 63
      | mm1
      (* | st1 *)
        => 64
      | mm2
      (* | st2 *)
        => 65
      | mm3
      (* | st3 *)
        => 66
      | mm4
      (* | st4 *)
        => 67
      | mm5
      (* | st5 *)
        => 68
      | mm6
      (* | st6 *)
        => 69
      | mm7
      (* | st7 *)
        => 70
      | k0
        => 71
      | k1
        => 72
      | k2
        => 73
      | k3
        => 74
      | k4
        => 75
      | k5
        => 76
      | k6
        => 77
      | k7
        => 78
      | gdtr
        => 79
      | idtr
        => 80
      | ldtr
        => 81
      | tr
        => 82
      | fp_cs
        => 83
      | fp_opc
        => 84
      | fp_ds
        => 85
      | mxcsr
        => 86
      | dr0
        => 87
      | dr1
        => 88
      | dr2
        => 89
      | dr3
        => 90
      | dr4
        => 91
      | dr5
        => 92
      | dr6
        => 93
      | dr7
        => 94
      | dr8
        => 95
      | dr9
        => 96
      | dr10
        => 97
      | dr11
        => 98
      | dr12
        => 99
      | dr13
        => 100
      | dr14
        => 101
      | dr15
        => 102
      | cs
        => 103
      | ds
        => 104
      | es
        => 105
      | fs
        => 106
      | gs
        => 107
      | ss
        => 108
      | cw
        => 109
      | sw
        => 110
      | tw
        => 111
      end%N.

Definition reg_offset (r : REG) : N :=
      match r with
      |(ah      | ch      | dh      | bh      )
       => 8
      | _ => 0
      end.
Definition index_and_shift_and_bitcount_of_reg (r : REG) :=
  (reg_index r, reg_offset r, reg_size r).

Definition regs_of_index (index : N) : list (list REG) :=
  match index with
  |  0 => [ [  al ; ah] ; [  ax]  ; [ eax]  ; [rax] ]
  |  1 => [ [  cl ; ch] ; [  cx]  ; [ ecx]  ; [rcx] ]
  |  2 => [ [  dl ; dh] ; [  dx]  ; [ edx]  ; [rdx] ]
  |  3 => [ [  bl ; bh] ; [  bx]  ; [ ebx]  ; [rbx] ]
  |  4 => [ [ spl     ] ; [  sp]  ; [ esp]  ; [rsp] ]
  |  5 => [ [ bpl     ] ; [  bp]  ; [ ebp]  ; [rbp] ]
  |  6 => [ [ sil     ] ; [  si]  ; [ esi]  ; [rsi] ]
  |  7 => [ [ dil     ] ; [  di]  ; [ edi]  ; [rdi] ]
  |  8 => [ [ r8b     ] ; [ r8w]  ; [ r8d]  ; [r8 ] ]
  |  9 => [ [ r9b     ] ; [ r9w]  ; [ r9d]  ; [r9 ] ]
  | 10 => [ [r10b     ] ; [r10w]  ; [r10d]  ; [r10] ]
  | 11 => [ [r11b     ] ; [r11w]  ; [r11d]  ; [r11] ]
  | 12 => [ [r12b     ] ; [r12w]  ; [r12d]  ; [r12] ]
  | 13 => [ [r13b     ] ; [r13w]  ; [r13d]  ; [r13] ]
  | 14 => [ [r14b     ] ; [r14w]  ; [r14d]  ; [r14] ]
  | 15 => [ [r15b     ] ; [r15w]  ; [r15d]  ; [r15] ]
  | 16 => [ []          ; [ip]    ; [eip]   ; [rip] ]
  | 17 => [ []          ; [flags] ; [eflags]; [rflags] ]
  | 18 => [ []          ; []      ; []      ; []    ; [xmm0] ; [ymm0] ; [zmm0] ]
  | 19 => [ []          ; []      ; []      ; []    ; [xmm1] ; [ymm1] ; [zmm1] ]
  | 20 => [ []          ; []      ; []      ; []    ; [xmm2] ; [ymm2] ; [zmm2] ]
  | 21 => [ []          ; []      ; []      ; []    ; [xmm3] ; [ymm3] ; [zmm3] ]
  | 22 => [ []          ; []      ; []      ; []    ; [xmm4] ; [ymm4] ; [zmm4] ]
  | 23 => [ []          ; []      ; []      ; []    ; [xmm5] ; [ymm5] ; [zmm5] ]
  | 24 => [ []          ; []      ; []      ; []    ; [xmm6] ; [ymm6] ; [zmm6] ]
  | 25 => [ []          ; []      ; []      ; []    ; [xmm7] ; [ymm7] ; [zmm7] ]
  | 26 => [ []          ; []      ; []      ; []    ; [xmm8] ; [ymm8] ; [zmm8] ]
  | 27 => [ []          ; []      ; []      ; []    ; [xmm9] ; [ymm9] ; [zmm9] ]
  | 28 => [ []          ; []      ; []      ; []    ; [xmm10]; [ymm10]; [zmm10] ]
  | 29 => [ []          ; []      ; []      ; []    ; [xmm11]; [ymm11]; [zmm11] ]
  | 30 => [ []          ; []      ; []      ; []    ; [xmm12]; [ymm12]; [zmm12] ]
  | 31 => [ []          ; []      ; []      ; []    ; [xmm13]; [ymm13]; [zmm13] ]
  | 32 => [ []          ; []      ; []      ; []    ; [xmm14]; [ymm14]; [zmm14] ]
  | 33 => [ []          ; []      ; []      ; []    ; [xmm15]; [ymm15]; [zmm15] ]
  | 34 => [ []          ; []      ; []      ; []    ; []     ; []     ; [zmm16] ]
  | 36 => [ []          ; []      ; []      ; []    ; []     ; []     ; [zmm18] ]
  | 35 => [ []          ; []      ; []      ; []    ; []     ; []     ; [zmm17] ]
  | 37 => [ []          ; []      ; []      ; []    ; []     ; []     ; [zmm19] ]
  | 38 => [ []          ; []      ; []      ; []    ; []     ; []     ; [zmm20] ]
  | 39 => [ []          ; []      ; []      ; []    ; []     ; []     ; [zmm21] ]
  | 40 => [ []          ; []      ; []      ; []    ; []     ; []     ; [zmm22] ]
  | 41 => [ []          ; []      ; []      ; []    ; []     ; []     ; [zmm23] ]
  | 42 => [ []          ; []      ; []      ; []    ; []     ; []     ; [zmm24] ]
  | 43 => [ []          ; []      ; []      ; []    ; []     ; []     ; [zmm25] ]
  | 44 => [ []          ; []      ; []      ; []    ; []     ; []     ; [zmm26] ]
  | 45 => [ []          ; []      ; []      ; []    ; []     ; []     ; [zmm27] ]
  | 46 => [ []          ; []      ; []      ; []    ; []     ; []     ; [zmm28] ]
  | 47 => [ []          ; []      ; []      ; []    ; []     ; []     ; [zmm29] ]
  | 48 => [ []          ; []      ; []      ; []    ; []     ; []     ; [zmm30] ]
  | 49 => [ []          ; []      ; []      ; []    ; []     ; []     ; [zmm31] ]
  | 50 => [ []          ; [msw]   ; []      ; [cr0] ]
  | 51 => [ []          ; []      ; []      ; [cr1] ]
  | 52 => [ []          ; []      ; []      ; [cr2] ]
  | 53 => [ []          ; []      ; []      ; [cr3] ]
  | 54 => [ []          ; []      ; []      ; [cr4] ]
  | 55 => [ []          ; []      ; []      ; [cr8] ]
  | 56 => [ []          ; []      ; []      ; [cr9] ]
  | 57 => [ []          ; []      ; []      ; [cr10] ]
  | 58 => [ []          ; []      ; []      ; [cr11] ]
  | 59 => [ []          ; []      ; []      ; [cr12] ]
  | 60 => [ []          ; []      ; []      ; [cr13] ]
  | 61 => [ []          ; []      ; []      ; [cr14] ]
  | 62 => [ []          ; []      ; []      ; [cr15] ]
  | 63 => [ []          ; []      ; []      ; [mm0] ]
  | 64 => [ []          ; []      ; []      ; [mm1] ]
  | 65 => [ []          ; []      ; []      ; [mm2] ]
  | 66 => [ []          ; []      ; []      ; [mm3] ]
  | 67 => [ []          ; []      ; []      ; [mm4] ]
  | 68 => [ []          ; []      ; []      ; [mm5] ]
  | 69 => [ []          ; []      ; []      ; [mm6] ]
  | 70 => [ []          ; []      ; []      ; [mm7] ]
  | 71 => [ []          ; []      ; []      ; [k0] ]
  | 72 => [ []          ; []      ; []      ; [k1] ]
  | 73 => [ []          ; []      ; []      ; [k2] ]
  | 74 => [ []          ; []      ; []      ; [k3] ]
  | 75 => [ []          ; []      ; []      ; [k4] ]
  | 76 => [ []          ; []      ; []      ; [k5] ]
  | 77 => [ []          ; []      ; []      ; [k6] ]
  | 78 => [ []          ; []      ; []      ; [k7] ]
  | 79 => [ []          ; [gdtr]  ; []      ; []    ]
  | 80 => [ []          ; [idtr]  ; []      ; []    ]
  | 81 => [ []          ; [ldtr]  ; []      ; []    ]
  | 82 => [ []          ; [tr]    ; []      ; []    ]
  | 83 => [ []          ; [fp_cs] ; []      ; []    ]
  | 84 => [ []          ; [fp_opc]; []      ; []    ]
  | 85 => [ []          ; [fp_ds] ; []      ; []    ]
  | 86 => [ []          ; []      ; [mxcsr] ; []    ]
  | 87 => [ []          ; []      ; []      ; [dr0] ]
  | 88 => [ []          ; []      ; []      ; [dr1] ]
  | 89 => [ []          ; []      ; []      ; [dr2] ]
  | 90 => [ []          ; []      ; []      ; [dr3] ]
  | 91 => [ []          ; []      ; []      ; [dr4] ]
  | 92 => [ []          ; []      ; []      ; [dr5] ]
  | 93 => [ []          ; []      ; []      ; [dr6] ]
  | 94 => [ []          ; []      ; []      ; [dr7] ]
  | 95 => [ []          ; []      ; []      ; [dr8] ]
  | 96 => [ []          ; []      ; []      ; [dr9] ]
  | 97 => [ []          ; []      ; []      ; [dr10] ]
  | 98 => [ []          ; []      ; []      ; [dr11] ]
  | 99 => [ []          ; []      ; []      ; [dr12] ]
  | 100 => [ []         ; []      ; []      ; [dr13] ]
  | 101 => [ []         ; []      ; []      ; [dr14] ]
  | 102 => [ []         ; []      ; []      ; [dr15] ]
  | 103 => [ []         ; [cs]    ; []      ; []    ]
  | 104 => [ []         ; [ds]    ; []      ; []    ]
  | 105 => [ []         ; [es]    ; []      ; []    ]
  | 106 => [ []         ; [fs]    ; []      ; []    ]
  | 107 => [ []         ; [gs]    ; []      ; []    ]
  | 108 => [ []         ; [ss]    ; []      ; []    ]
  | 109 => [ []         ; [cw]    ; []      ; []    ]
  | 110 => [ []         ; [sw]    ; []      ; []    ]
  | 111 => [ []         ; [tw]    ; []      ; []    ]
  | _  => []
  end%N.

(** convenience printing function *)
Definition widest_register_of_index (n : N) : REG
  := List.hd rax (List.rev (List.concat (regs_of_index n))).

Definition reg_of_index_and_shift_and_bitcount_opt :=
  fun '(index, offset, size) =>
    let sz := N.log2 (size / 8) in
    let offset_n := (offset / 8)%N in
    if ((8 * 2^sz =? size) && (offset =? offset_n * 8))%N%bool
    then (rs <- nth_error (regs_of_index index) (N.to_nat sz);
          nth_error rs (N.to_nat offset_n))%option
    else None.
Definition reg_of_index_and_shift_and_bitcount :=
  fun '(index, offset, size) =>
    match reg_of_index_and_shift_and_bitcount_opt (index, offset, size) with
    | Some r => r
    | None => widest_register_of_index index
    end.

Local Coercion N.of_nat : nat >-> N.

Lemma widest_register_of_index_correct
  : forall n,
    (~exists r, reg_index r = n)
    \/ (let r := widest_register_of_index n in reg_index r = n
       /\ forall r', reg_index r' = n -> r = r' \/ (reg_size r' < reg_size r)%N).
Proof.
  intro n; set (r := widest_register_of_index n).
  cbv in r.
  repeat match goal with r := context[match ?n with _ => _ end] |- _ => is_var n; destruct n end.
  all: try (right; vm_compute; split; [ reflexivity | ]).
  all: try (intros [] H; cbv in H; try (exfalso; congruence)).
  all: try (constructor; reflexivity).
  all: try (left; intros [ [] H ]; cbv in H; congruence).
Qed.

Lemma reg_of_index_and_shift_and_bitcount_opt_of_index_and_shift_and_bitcount_of_reg : forall r : REG, reg_of_index_and_shift_and_bitcount_opt (index_and_shift_and_bitcount_of_reg r) = Some r.
Proof. destruct r; vm_compute; try reflexivity. Defined.

Lemma reg_of_index_and_shift_and_bitcount_of_index_and_shift_and_bitcount_of_reg : forall r : REG, reg_of_index_and_shift_and_bitcount (index_and_shift_and_bitcount_of_reg r) = r.
Proof. destruct r; vm_compute; reflexivity. Defined.


Lemma reg_of_index_and_shift_and_bitcount_opt_correct v r
  : reg_of_index_and_shift_and_bitcount_opt v = Some r <-> index_and_shift_and_bitcount_of_reg r = v.
Proof.
  split; [ | intro; subst; destruct r; vm_compute; reflexivity ].
  cbv [index_and_shift_and_bitcount_of_reg]; destruct v as [ [index shift] bitcount ].
  cbv [reg_of_index_and_shift_and_bitcount_opt].
  generalize (shift / 8)%N (N.log2 (bitcount / 8)); intros *.
  repeat first [ congruence
               | progress subst
               | match goal with
                 | [ H : _ /\ _ |- _ ] => destruct H
                 | [ H : N.to_nat _ = _ |- _ ] => apply (f_equal N.of_nat) in H; rewrite N2Nat.id in H; subst
                 | [ |- Some _ = Some _ -> _ ] => inversion 1; subst
                 | [ |- context[match ?x with _ => _ end] ] => destruct x eqn:?; subst
                 end
               | progress cbv [regs_of_index]
               | match goal with
                 | [ |- context[nth_error _ ?n] ] => destruct n eqn:?; cbn [nth_error Option.bind]
                 end
               | rewrite Bool.andb_true_iff, ?N.eqb_eq in * |- ].
  all: vm_compute; reflexivity.
Qed.

Lemma reg_of_index_and_shift_and_bitcount_of_reg r
  : reg_of_index_and_shift_and_bitcount (index_and_shift_and_bitcount_of_reg r) = r.
Proof. destruct r; vm_compute; reflexivity. Qed.

Lemma reg_of_index_and_shift_and_bitcount_eq v r
  : reg_of_index_and_shift_and_bitcount v = r
    -> (index_and_shift_and_bitcount_of_reg r = v
        \/ ((~exists r, index_and_shift_and_bitcount_of_reg r = v)
            /\ r = widest_register_of_index (fst (fst v)))).
Proof.
  cbv [reg_of_index_and_shift_and_bitcount].
  destruct v as [ [index offset] size ].
  destruct reg_of_index_and_shift_and_bitcount_opt eqn:H;
    [ left | right; split; [ intros [r' H'] | ] ]; subst; try reflexivity.
  { rewrite reg_of_index_and_shift_and_bitcount_opt_correct in H; assumption. }
  { rewrite <- reg_of_index_and_shift_and_bitcount_opt_correct in H'; congruence. }
Qed.
