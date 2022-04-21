Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.derive.Derive.
Require Import Crypto.Util.Option.
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

Inductive AccessSize := byte | word | dword | qword.
Coercion bits_of_AccessSize (x : AccessSize) : N
  := match x with
     | byte => 8
     | word => 16
     | dword => 32
     | qword => 64
     end.

Record MEM := { mem_bits_access_size : option AccessSize ; mem_base_reg : option REG ; mem_scale_reg : option (Z * REG) ; mem_base_label : option string ; mem_offset : option Z }.

Definition mem_of_reg (r : REG) : MEM :=
  {| mem_base_reg := Some r ; mem_offset := None ; mem_scale_reg := None ; mem_bits_access_size := None ; mem_base_label := None |}.

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
| cmovnz
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
| mov
| movzx
| mul
| mulx
| pop
| push
| rcr
| ret
| sar
| sbb
| setc
| seto
| shl
| shlx
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

Definition regs_of_index (index : nat) : list (list REG) :=
  match index with
  |  0 => [ [  al ; ah] ; [  ax] ; [ eax] ; [rax] ]
  |  1 => [ [  cl ; ch] ; [  cx] ; [ ecx] ; [rcx] ]
  |  2 => [ [  dl ; dh] ; [  dx] ; [ edx] ; [rdx] ]
  |  3 => [ [  bl ; bh] ; [  bx] ; [ ebx] ; [rbx] ]
  |  4 => [ [ spl     ] ; [  sp] ; [ esp] ; [rsp] ]
  |  5 => [ [ bpl     ] ; [  bp] ; [ ebp] ; [rbp] ]
  |  6 => [ [ sil     ] ; [  si] ; [ esi] ; [rsi] ]
  |  7 => [ [ dil     ] ; [  di] ; [ edi] ; [rdi] ]
  |  8 => [ [ r8b     ] ; [ r8w] ; [ r8d] ; [r8 ] ]
  |  9 => [ [ r9b     ] ; [ r9w] ; [ r9d] ; [r9 ] ]
  | 10 => [ [r10b     ] ; [r10w] ; [r10d] ; [r10] ]
  | 11 => [ [r11b     ] ; [r11w] ; [r11d] ; [r11] ]
  | 12 => [ [r12b     ] ; [r12w] ; [r12d] ; [r12] ]
  | 13 => [ [r13b     ] ; [r13w] ; [r13d] ; [r13] ]
  | 14 => [ [r14b     ] ; [r14w] ; [r14d] ; [r14] ]
  | 15 => [ [r15b     ] ; [r15w] ; [r15d] ; [r15] ]
  | _  => []
  end.

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
