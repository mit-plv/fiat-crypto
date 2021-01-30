Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Bool.Bool.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Notations.
Require Crypto.Util.Tuple.

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

Delimit Scope REG_scope with REG.
Bind Scope REG_scope with REG.

Infix "=?" := REG_beq : REG_scope.

Global Instance REG_beq_spec : reflect_rel (@eq REG) REG_beq | 10
  := reflect_of_beq internal_REG_dec_bl internal_REG_dec_lb.
Definition REG_beq_eq x y : (x =? y)%REG = true <-> x = y := conj (@internal_REG_dec_bl _ _) (@internal_REG_dec_lb _ _).
Lemma REG_beq_neq x y : (x =? y)%REG = false <-> x <> y.
Proof. rewrite <- REG_beq_eq; destruct (x =? y)%REG; intuition congruence. Qed.
Global Instance REG_beq_compat : Proper (eq ==> eq ==> eq) REG_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Definition CONST_beq : CONST -> CONST -> bool := Z.eqb.
Definition CONST_dec_bl (x y : CONST) : CONST_beq x y = true -> x = y := proj1 (Z.eqb_eq x y).
Definition CONST_dec_lb (x y : CONST) : x = y -> CONST_beq x y = true := proj2 (Z.eqb_eq x y).
Definition CONST_eq_dec (x y : CONST) : {x = y} + {x <> y} := Z.eq_dec x y.

Delimit Scope CONST_scope with CONST.
Bind Scope CONST_scope with CONST.

Infix "=?" := CONST_beq : CONST_scope.

Global Instance CONST_beq_spec : reflect_rel (@eq CONST) CONST_beq | 10
  := reflect_of_beq CONST_dec_bl CONST_dec_lb.
Definition CONST_beq_eq x y : (x =? y)%CONST = true <-> x = y := conj (@CONST_dec_bl _ _) (@CONST_dec_lb _ _).
Lemma CONST_beq_neq x y : (x =? y)%CONST = false <-> x <> y.
Proof. rewrite <- CONST_beq_eq; destruct (x =? y)%CONST; intuition congruence. Qed.
Global Instance CONST_beq_compat : Proper (eq ==> eq ==> eq) CONST_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Delimit Scope MEM_scope with MEM.
Bind Scope MEM_scope with MEM.

Definition MEM_beq (x y : MEM) : bool
  := ((Bool.eqb x.(mem_is_byte) y.(mem_is_byte))
      && (x.(mem_reg) =? y.(mem_reg))%REG
      && (option_beq REG_beq x.(mem_extra_reg) y.(mem_extra_reg))
      && (option_beq Z.eqb x.(mem_offset) y.(mem_offset)))%bool.
Global Arguments MEM_beq !_ !_ / .

Infix "=?" := MEM_beq : MEM_scope.

Local Ltac t_dec :=
  lazymatch goal with
  | [ |- ?beq ?x ?y = true -> ?x = ?y ]
    => is_var x; is_var y; destruct x, y; cbv [beq]
  | [ |- ?x = ?y -> ?beq ?x ?y = true ]
    => is_var x; is_var y; destruct x; cbv [beq]; intros; subst
  end;
  simpl;
  rewrite ?Bool.andb_true_iff; intros; destruct_head'_and;
  repeat apply conj; try reflexivity;
  reflect_hyps; subst;
  try solve [ reflexivity
            | exfalso; assumption
            | apply unreflect_bool; reflexivity ].

Lemma MEM_dec_bl (x y : MEM) : MEM_beq x y = true -> x = y.
Proof. t_dec. Qed.
Lemma MEM_dec_lb (x y : MEM) : x = y -> MEM_beq x y = true.
Proof. t_dec. Qed.
Definition MEM_eq_dec (x y : MEM) : {x = y} + {x <> y}
  := (if (x =? y)%MEM as b return (x =? y)%MEM = b -> _
      then fun pf => left (@MEM_dec_bl _ _ pf)
      else fun pf => right (fun pf' => diff_false_true (eq_trans (eq_sym pf) (@MEM_dec_lb _ _ pf'))))
       eq_refl.

Global Instance MEM_beq_spec : reflect_rel (@eq MEM) MEM_beq | 10
  := reflect_of_beq MEM_dec_bl MEM_dec_lb.
Definition MEM_beq_eq x y : (x =? y)%MEM = true <-> x = y := conj (@MEM_dec_bl _ _) (@MEM_dec_lb _ _).
Lemma MEM_beq_neq x y : (x =? y)%MEM = false <-> x <> y.
Proof. rewrite <- MEM_beq_eq; destruct (x =? y)%MEM; intuition congruence. Qed.
Global Instance MEM_beq_compat : Proper (eq ==> eq ==> eq) MEM_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Delimit Scope FLAG_scope with FLAG.
Bind Scope FLAG_scope with FLAG.

Infix "=?" := FLAG_beq : FLAG_scope.

Global Instance FLAG_beq_spec : reflect_rel (@eq FLAG) FLAG_beq | 10
  := reflect_of_beq internal_FLAG_dec_bl internal_FLAG_dec_lb.
Definition FLAG_beq_eq x y : (x =? y)%FLAG = true <-> x = y := conj (@internal_FLAG_dec_bl _ _) (@internal_FLAG_dec_lb _ _).
Lemma FLAG_beq_neq x y : (x =? y)%FLAG = false <-> x <> y.
Proof. rewrite <- FLAG_beq_eq; destruct (x =? y)%FLAG; intuition congruence. Qed.
Global Instance FLAG_beq_compat : Proper (eq ==> eq ==> eq) FLAG_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Delimit Scope OpCode_scope with OpCode.
Bind Scope OpCode_scope with OpCode.

Infix "=?" := OpCode_beq : OpCode_scope.

Global Instance OpCode_beq_spec : reflect_rel (@eq OpCode) OpCode_beq | 10
  := reflect_of_beq internal_OpCode_dec_bl internal_OpCode_dec_lb.
Definition OpCode_beq_eq x y : (x =? y)%OpCode = true <-> x = y := conj (@internal_OpCode_dec_bl _ _) (@internal_OpCode_dec_lb _ _).
Lemma OpCode_beq_neq x y : (x =? y)%OpCode = false <-> x <> y.
Proof. rewrite <- OpCode_beq_eq; destruct (x =? y)%OpCode; intuition congruence. Qed.
Global Instance OpCode_beq_compat : Proper (eq ==> eq ==> eq) OpCode_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Delimit Scope ARG_scope with ARG.
Bind Scope ARG_scope with ARG.

Definition ARG_beq (x y : ARG) : bool
  := match x, y with
     | reg x, reg y => REG_beq x y
     | mem x, mem y => MEM_beq x y
     | const x, const y => CONST_beq x y
     | reg _, _
     | mem _, _
     | const _, _
       => false
     end.
Global Arguments ARG_beq !_ !_ / .

Infix "=?" := ARG_beq : ARG_scope.

Lemma ARG_dec_bl (x y : ARG) : ARG_beq x y = true -> x = y.
Proof. t_dec. Qed.
Lemma ARG_dec_lb (x y : ARG) : x = y -> ARG_beq x y = true.
Proof. t_dec. Qed.
Definition ARG_eq_dec (x y : ARG) : {x = y} + {x <> y}
  := (if (x =? y)%ARG as b return (x =? y)%ARG = b -> _
      then fun pf => left (@ARG_dec_bl _ _ pf)
      else fun pf => right (fun pf' => diff_false_true (eq_trans (eq_sym pf) (@ARG_dec_lb _ _ pf'))))
       eq_refl.

Global Instance ARG_beq_spec : reflect_rel (@eq ARG) ARG_beq | 10
  := reflect_of_beq ARG_dec_bl ARG_dec_lb.
Definition ARG_beq_eq x y : (x =? y)%ARG = true <-> x = y := conj (@ARG_dec_bl _ _) (@ARG_dec_lb _ _).
Lemma ARG_beq_neq x y : (x =? y)%ARG = false <-> x <> y.
Proof. rewrite <- ARG_beq_eq; destruct (x =? y)%ARG; intuition congruence. Qed.
Global Instance ARG_beq_compat : Proper (eq ==> eq ==> eq) ARG_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Delimit Scope NormalInstruction_scope with NormalInstruction.
Bind Scope NormalInstruction_scope with NormalInstruction.

Definition NormalInstruction_beq (x y : NormalInstruction) : bool
  := ((x.(op) =? y.(op))%OpCode
      && list_beq _ ARG_beq x.(args) y.(args))%bool.
Global Arguments NormalInstruction_beq !_ !_ / .

Infix "=?" := NormalInstruction_beq : NormalInstruction_scope.

Lemma NormalInstruction_dec_bl (x y : NormalInstruction) : NormalInstruction_beq x y = true -> x = y.
Proof. t_dec. Qed.
Lemma NormalInstruction_dec_lb (x y : NormalInstruction) : x = y -> NormalInstruction_beq x y = true.
Proof. t_dec. Qed.
Definition NormalInstruction_eq_dec (x y : NormalInstruction) : {x = y} + {x <> y}
  := (if (x =? y)%NormalInstruction as b return (x =? y)%NormalInstruction = b -> _
      then fun pf => left (@NormalInstruction_dec_bl _ _ pf)
      else fun pf => right (fun pf' => diff_false_true (eq_trans (eq_sym pf) (@NormalInstruction_dec_lb _ _ pf'))))
       eq_refl.

Global Instance NormalInstruction_beq_spec : reflect_rel (@eq NormalInstruction) NormalInstruction_beq | 10
  := reflect_of_beq NormalInstruction_dec_bl NormalInstruction_dec_lb.
Definition NormalInstruction_beq_eq x y : (x =? y)%NormalInstruction = true <-> x = y := conj (@NormalInstruction_dec_bl _ _) (@NormalInstruction_dec_lb _ _).
Lemma NormalInstruction_beq_neq x y : (x =? y)%NormalInstruction = false <-> x <> y.
Proof. rewrite <- NormalInstruction_beq_eq; destruct (x =? y)%NormalInstruction; intuition congruence. Qed.
Global Instance NormalInstruction_beq_compat : Proper (eq ==> eq ==> eq) NormalInstruction_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Delimit Scope RawLine_scope with RawLine.
Bind Scope RawLine_scope with RawLine.

Definition RawLine_beq (x y : RawLine) : bool
  := match x, y with
     | SECTION x, SECTION y => String.eqb x y
     | GLOBAL x, GLOBAL y => String.eqb x y
     | LABEL x, LABEL y => String.eqb x y
     | EMPTY, EMPTY => true
     | INSTR x, INSTR y => NormalInstruction_beq x y
     | SECTION _, _
     | GLOBAL _, _
     | LABEL _, _
     | EMPTY, _
     | INSTR _, _
       => false
     end.
Global Arguments RawLine_beq !_ !_ / .

Infix "=?" := RawLine_beq : RawLine_scope.

Lemma RawLine_dec_bl (x y : RawLine) : RawLine_beq x y = true -> x = y.
Proof. t_dec. Qed.
Lemma RawLine_dec_lb (x y : RawLine) : x = y -> RawLine_beq x y = true.
Proof. t_dec. Qed.
Definition RawLine_eq_dec (x y : RawLine) : {x = y} + {x <> y}
  := (if (x =? y)%RawLine as b return (x =? y)%RawLine = b -> _
      then fun pf => left (@RawLine_dec_bl _ _ pf)
      else fun pf => right (fun pf' => diff_false_true (eq_trans (eq_sym pf) (@RawLine_dec_lb _ _ pf'))))
       eq_refl.

Global Instance RawLine_beq_spec : reflect_rel (@eq RawLine) RawLine_beq | 10
  := reflect_of_beq RawLine_dec_bl RawLine_dec_lb.
Definition RawLine_beq_eq x y : (x =? y)%RawLine = true <-> x = y := conj (@RawLine_dec_bl _ _) (@RawLine_dec_lb _ _).
Lemma RawLine_beq_neq x y : (x =? y)%RawLine = false <-> x <> y.
Proof. rewrite <- RawLine_beq_eq; destruct (x =? y)%RawLine; intuition congruence. Qed.
Global Instance RawLine_beq_compat : Proper (eq ==> eq ==> eq) RawLine_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Delimit Scope Line_scope with Line.
Bind Scope Line_scope with Line.

Definition Line_beq (x y : Line) : bool
  := ((x.(indent) =? y.(indent))%string
      && (x.(rawline) =? y.(rawline))%RawLine
      && (x.(pre_comment_whitespace) =? y.(pre_comment_whitespace))%string
      && option_beq String.eqb x.(comment) y.(comment))%bool.
Global Arguments Line_beq !_ !_ / .

Infix "=?" := Line_beq : Line_scope.

Lemma Line_dec_bl (x y : Line) : Line_beq x y = true -> x = y.
Proof. t_dec. Qed.
Lemma Line_dec_lb (x y : Line) : x = y -> Line_beq x y = true.
Proof. t_dec. Qed.
Definition Line_eq_dec (x y : Line) : {x = y} + {x <> y}
  := (if (x =? y)%Line as b return (x =? y)%Line = b -> _
      then fun pf => left (@Line_dec_bl _ _ pf)
      else fun pf => right (fun pf' => diff_false_true (eq_trans (eq_sym pf) (@Line_dec_lb _ _ pf'))))
       eq_refl.

Global Instance Line_beq_spec : reflect_rel (@eq Line) Line_beq | 10
  := reflect_of_beq Line_dec_bl Line_dec_lb.
Definition Line_beq_eq x y : (x =? y)%Line = true <-> x = y := conj (@Line_dec_bl _ _) (@Line_dec_lb _ _).
Lemma Line_beq_neq x y : (x =? y)%Line = false <-> x <> y.
Proof. rewrite <- Line_beq_eq; destruct (x =? y)%Line; intuition congruence. Qed.
Global Instance Line_beq_compat : Proper (eq ==> eq ==> eq) Line_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Delimit Scope Lines_scope with Lines.
Bind Scope Lines_scope with Lines.

Definition Lines_beq (x y : Lines) : bool
  := list_beq _ Line_beq x y.
Global Arguments Lines_beq !_ !_ / .

Infix "=?" := Lines_beq : Lines_scope.

Lemma Lines_dec_bl (x y : Lines) : Lines_beq x y = true -> x = y.
Proof. t_dec. Qed.
Lemma Lines_dec_lb (x y : Lines) : x = y -> Lines_beq x y = true.
Proof. t_dec. Qed.
Definition Lines_eq_dec (x y : Lines) : {x = y} + {x <> y}
  := (if (x =? y)%Lines as b return (x =? y)%Lines = b -> _
      then fun pf => left (@Lines_dec_bl _ _ pf)
      else fun pf => right (fun pf' => diff_false_true (eq_trans (eq_sym pf) (@Lines_dec_lb _ _ pf'))))
       eq_refl.

Global Instance Lines_beq_spec : reflect_rel (@eq Lines) Lines_beq | 10
  := reflect_of_beq Lines_dec_bl Lines_dec_lb.
Definition Lines_beq_eq x y : (x =? y)%Lines = true <-> x = y := conj (@Lines_dec_bl _ _) (@Lines_dec_lb _ _).
Lemma Lines_beq_neq x y : (x =? y)%Lines = false <-> x <> y.
Proof. rewrite <- Lines_beq_eq; destruct (x =? y)%Lines; intuition congruence. Qed.
Global Instance Lines_beq_compat : Proper (eq ==> eq ==> eq) Lines_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

(** denotational semantics *)

Definition flag_state := Tuple.tuple (option bool) 6.
Definition get_flag (st : flag_state) (f : FLAG) : option bool
  := let '(cfv, pfv, afv, zfv, sfv, ofv) := st in
     match f with
     | CF => cfv
     | PF => pfv
     | AF => afv
     | ZF => zfv
     | SF => sfv
     | OF => ofv
     end.
Definition set_flag_internal (st : flag_state) (f : FLAG) (v : option bool) : flag_state
  := let '(cfv, pfv, afv, zfv, sfv, ofv) := st in
     (match f with CF => v | _ => cfv end,
      match f with PF => v | _ => pfv end,
      match f with AF => v | _ => afv end,
      match f with ZF => v | _ => zfv end,
      match f with SF => v | _ => sfv end,
      match f with OF => v | _ => ofv end).
Definition set_flag (st : flag_state) (f : FLAG) (v : bool) : flag_state
  := set_flag_internal st f (Some v).
Definition havoc_flag (st : flag_state) (f : FLAG) : flag_state
  := set_flag_internal st f None.
Definition havoc_flags (st : flag_state) : flag_state
  := (None, None, None, None, None, None).

Definition reg_state := list N.
Definition index_and_shift_and_bitcount_of_reg (r : REG) : nat * N * N
  := (match r with
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
      end,
      match r with
      |(    rax |     rcx |     rdx |     rbx | rsp  | rbp  | rsi  | rdi  | r8  | r9  | r10  | r11  | r12  | r13  | r14  | r15 )
      |(    eax |     ecx |     edx |     ebx | esp  | ebp  | esi  | edi  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d)
      |(     ax |      cx |      dx |      bx |  sp  |  bp  |  si  |  di  | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w)
      |(     al |      cl |      dl |      bl |  spl |  bpl |  sil |  dil | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b)
       => 0
      |(ah      | ch      | dh      | bh      )
       => 8
      end%N,
      match r with
      |(    rax |     rcx |     rdx |     rbx | rsp  | rbp  | rsi  | rdi  | r8  | r9  | r10  | r11  | r12  | r13  | r14  | r15 )
       => 64
      |(    eax |     ecx |     edx |     ebx | esp  | ebp  | esi  | edi  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d)
       => 32
      |(     ax |      cx |      dx |      bx |  sp  |  bp  |  si  |  di  | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w)
       => 16
      |(ah | al | ch | cl | dh | dl | bh | bl |  spl |  bpl |  sil |  dil | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b)
       => 8
      end%N).
Definition bitmask_of_reg (r : REG) : N
  := let '(idx, shift, bitcount) := index_and_shift_and_bitcount_of_reg r in
     N.shiftl (N.ones bitcount) shift.
Definition get_reg (st : reg_state) (r : REG) : N
  := let '(idx, shift, bitcount) := index_and_shift_and_bitcount_of_reg r in
     let rv := nth_default 0%N st idx in
     N.land (N.shiftr rv shift) (N.ones bitcount).
Definition set_reg (st : reg_state) (r : REG) (v : N) : reg_state
  := let '(idx, shift, bitcount) := index_and_shift_and_bitcount_of_reg r in
     let bitmask := bitmask_of_reg r in
     ListUtil.update_nth
       idx
       (fun curv => N.lor (N.land bitmask (N.shiftl v shift))
                          (N.ldiff curv bitmask))
       st.

Record mem_state := { mem_bytes_state :> PositiveMap.t Byte.byte }.
Definition get_mem_byte (st : mem_state) (addr : Z) : option Byte.byte
  := match addr with
     | Zpos p => PositiveMap.find p st.(mem_bytes_state)
     | _ => None
     end.
Definition set_mem_byte (st : mem_state) (addr : positive) (b : Byte.byte) : mem_state
  := {| mem_bytes_state := PositiveMap.add addr b st.(mem_bytes_state) |}.
Definition set_mem_byte_error (st : mem_state) (addr : Z) (b : Byte.byte) : option mem_state
  := match addr with
     | Zpos addr => Some (set_mem_byte st addr b)
     | _ => None
     end.
Definition set_mem_byte_default (st : mem_state) (addr : Z) (b : Byte.byte) : mem_state
  := match set_mem_byte_error st addr b with
     | Some st => st
     | None => st
     end.
Fixpoint get_mem_bytes (st : mem_state) (addr : Z) (nbytes : nat) : option (list Byte.byte)
  := match nbytes with
     | O => Some nil
     | S nbytes => match get_mem_byte st addr, get_mem_bytes st (addr + 1) nbytes with
                   | Some b, Some bs => Some (b :: bs)
                   | _, _ => None
                   end
     end.
Fixpoint set_mem_bytes (st : mem_state) (addr : positive) (v : list Byte.byte) : mem_state
  := match v with
     | nil => st
     | v :: vs => let st := set_mem_byte st addr v in
                  set_mem_bytes st (addr + 1) vs
     end.
Definition set_mem_bytes_error (st : mem_state) (addr : Z) (v : list Byte.byte) : option mem_state
  := match addr with
     | Zpos addr => Some (set_mem_bytes st addr v)
     | _ => None
     end.
Definition set_mem_bytes_default (st : mem_state) (addr : Z) (v : list Byte.byte) : mem_state
  := match set_mem_bytes_error st addr v with
     | Some st => st
     | None => st
     end.
(* x86 is little-endian according to https://stackoverflow.com/a/25939262/377022, so we have l[0] + 8*l[1] + ... *)
Fixpoint mem_bytes_to_N (bytes : list Byte.byte) : N
  := match bytes with
     | nil => 0
     | b :: bs => Byte.to_N b + 8 * mem_bytes_to_N bs
     end%N.
(* returns the carry as well *)
Fixpoint mem_bytes_of_N_split (nbytes : nat) (v : N) : list Byte.byte * N
  := match nbytes with
     | O => (nil, v)
     | S nbytes => let '(vh, vl) := (N.shiftr v 8, N.land v (N.ones 8)) in
                   let '(bs, carry) := mem_bytes_of_N_split nbytes vh in
                   let vl := match Byte.of_N vl with
                             | Some vl => vl
                             | None (* should be impossible *) => Byte.x00
                             end in
                   (vl :: bs, carry)
     end%N.
Definition mem_bytes_of_N_error (nbytes : nat) (v : N) : option (list Byte.byte)
  := let '(bs, carry) := mem_bytes_of_N_split nbytes v in
     if (carry =? 0)%N then Some bs else None.
Definition mem_bytes_of_N_masked (nbytes : nat) (v : N) : list Byte.byte
  := let '(bs, carry) := mem_bytes_of_N_split nbytes v in bs.
Definition get_mem (st : mem_state) (addr : Z) (nbytes : nat) : option N
  := option_map mem_bytes_to_N (get_mem_bytes st addr nbytes).
Definition set_mem_error (st : mem_state) (addr : Z) (nbytes : nat) (v : N) : option mem_state
  := (bs <- mem_bytes_of_N_error nbytes v;
     set_mem_bytes_error st addr bs)%option.
Definition set_mem_masked_error (st : mem_state) (addr : Z) (nbytes : nat) (v : N) : option mem_state
  := set_mem_bytes_error st addr (mem_bytes_of_N_masked nbytes v).
Definition set_mem_default (st : mem_state) (addr : Z) (nbytes : nat) (v : N) : mem_state
  := Option.value (set_mem_masked_error st addr nbytes v) st.

Record machine_state := { machine_reg_state :> reg_state ; machine_flag_state :> flag_state ; machine_mem_state :> mem_state }.
Definition update_reg_with (st : machine_state) (f : reg_state -> reg_state) : machine_state
  := {| machine_reg_state := f st.(machine_reg_state) ; machine_flag_state := st.(machine_flag_state) ; machine_mem_state := st.(machine_mem_state) |}.
Definition update_flag_with (st : machine_state) (f : flag_state -> flag_state) : machine_state
  := {| machine_reg_state := st.(machine_reg_state) ; machine_flag_state := f st.(machine_flag_state) ; machine_mem_state := st.(machine_mem_state) |}.
Definition update_mem_with (st : machine_state) (f : mem_state -> mem_state) : machine_state
  := {| machine_reg_state := st.(machine_reg_state) ; machine_flag_state := st.(machine_flag_state) ; machine_mem_state := f st.(machine_mem_state) |}.
(*
Definition DenoteNormalInstruction (st : machine_state) (instr : NormalInstruction) : option machine_state.
  refine match instr.(op), instr.(args) with
         | adc, _ => _
         | adcx, _ => _
         | add, _ => _
         | adox, _ => _
         | and, _ => _
         | clc, _ => _
         | cmovnz, _ => _
         | dec, _ => _
         | imul, _ => _
         | inc, _ => _
         | lea, _ => _
         | mov, _ => _
         | movzx, _ => _
         | mulx, _ => _
         | ret, _ => _
         | sar, _ => _
         | sbb, _ => _
         | setc, _ => _
         | seto, _ => _
         | shr, _ => _
         | shrd, _ => _
         | sub, _ => _
         | test, _ => _
         | xchg, _ => _
         | xor, _ => _
         end.
*)
