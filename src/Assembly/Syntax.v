From Coq Require Import ZArith.
From Coq Require Import NArith.
From Coq Require Import Ascii.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Derive.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Listable.
Require Import Crypto.Util.ListUtil.
Require Crypto.Util.Tuple.
Require Crypto.Util.OptionList.
Require Import Crypto.Util.Strings.String.
Require Crypto.Util.Strings.Ascii.
Import ListNotations.

Local Open Scope list_scope.

Local Set Implicit Arguments.
Local Set Primitive Projections.

Inductive REG :=
|     rax |     rcx |     rdx |     rbx | rsp  | rbp  | rsi  | rdi  | r8  | r9  | r10  | r11  | r12  | r13  | r14  | r15
|     eax |     ecx |     edx |     ebx | esp  | ebp  | esi  | edi  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d
|      ax |      cx |      dx |      bx |  sp  |  bp  |  si  |  di  | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w
| ah | al | ch | cl | dh | dl | bh | bl |  spl |  bpl |  sil |  dil | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b
.

Derive REG_Listable SuchThat (@FinitelyListable REG REG_Listable) As REG_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances REG_Listable REG_FinitelyListable.
Definition REG_beq : REG -> REG -> bool := eqb_of_listable.
Definition REG_dec_bl : forall x y, REG_beq x y = true -> x = y := eqb_of_listable_bl.
Definition REG_dec_lb : forall x y, x = y -> REG_beq x y = true := eqb_of_listable_lb.
Definition REG_eq_dec : forall x y : REG, {x = y} + {x <> y} := eq_dec_of_listable.

Definition CONST := Z.
Coercion CONST_of_Z (x : Z) : CONST := x.

Inductive AccessSize := byte | word | dword | qword.

Derive AccessSize_Listable SuchThat (@FinitelyListable AccessSize AccessSize_Listable) As AccessSize_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances AccessSize_Listable AccessSize_FinitelyListable.
Definition AccessSize_beq : AccessSize -> AccessSize -> bool := eqb_of_listable.
Definition AccessSize_dec_bl : forall x y, AccessSize_beq x y = true -> x = y := eqb_of_listable_bl.
Definition AccessSize_dec_lb : forall x y, x = y -> AccessSize_beq x y = true := eqb_of_listable_lb.
Definition AccessSize_eq_dec : forall x y : AccessSize, {x = y} + {x <> y} := eq_dec_of_listable.

Coercion bits_of_AccessSize (x : AccessSize) : N
  := match x with
     | byte => 8
     | word => 16
     | dword => 32
     | qword => 64
     end.

Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.
Variant rip_relative_kind := explicitly_rip_relative | implicitly_rip_relative | not_rip_relative.
Local Unset Boolean Equality Schemes.
Local Unset Decidable Equality Schemes.
Global Coercion bool_of_rip_relative_kind (x : rip_relative_kind) : bool :=
  match x with
  | explicitly_rip_relative => true
  | implicitly_rip_relative => true
  | not_rip_relative => false
  end.
Record MEM := { mem_bits_access_size : option AccessSize ; mem_base_reg : option REG ; mem_scale_reg : option (Z * REG) ; mem_base_label : option string ; mem_offset : option Z ; rip_relative : rip_relative_kind }.

Definition mem_of_reg (r : REG) : MEM :=
  {| mem_base_reg := Some r ; mem_offset := None ; mem_scale_reg := None ; mem_bits_access_size := None ; mem_base_label := None ; rip_relative := not_rip_relative |}.

Inductive FLAG := CF | PF | AF | ZF | SF | OF.

Derive FLAG_Listable SuchThat (@FinitelyListable FLAG FLAG_Listable) As FLAG_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances FLAG_Listable FLAG_FinitelyListable.
Definition FLAG_beq : FLAG -> FLAG -> bool := eqb_of_listable.
Definition FLAG_dec_bl : forall x y, FLAG_beq x y = true -> x = y := eqb_of_listable_bl.
Definition FLAG_dec_lb : forall x y, x = y -> FLAG_beq x y = true := eqb_of_listable_lb.
Definition FLAG_eq_dec : forall x y : FLAG, {x = y} + {x <> y} := eq_dec_of_listable.

Inductive OpPrefix :=
| rep
| repz
| repnz
.

Derive OpPrefix_Listable SuchThat (@FinitelyListable OpPrefix OpPrefix_Listable) As OpPrefix_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances OpPrefix_Listable OpPrefix_FinitelyListable.
Definition OpPrefix_beq : OpPrefix -> OpPrefix -> bool := eqb_of_listable.
Definition OpPrefix_dec_bl : forall x y, OpPrefix_beq x y = true -> x = y := eqb_of_listable_bl.
Definition OpPrefix_dec_lb : forall x y, x = y -> OpPrefix_beq x y = true := eqb_of_listable_lb.
Definition OpPrefix_eq_dec : forall x y : OpPrefix, {x = y} + {x <> y} := eq_dec_of_listable.

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
| dw
| dd
| dq
| dec
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
| sar
| sbb
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

Derive OpCode_Listable SuchThat (@FinitelyListable OpCode OpCode_Listable) As OpCode_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances OpCode_Listable OpCode_FinitelyListable.
Definition OpCode_beq : OpCode -> OpCode -> bool := eqb_of_listable.
Definition OpCode_dec_bl : forall x y, OpCode_beq x y = true -> x = y := eqb_of_listable_bl.
Definition OpCode_dec_lb : forall x y, x = y -> OpCode_beq x y = true := eqb_of_listable_lb.
Definition OpCode_eq_dec : forall x y : OpCode, {x = y} + {x <> y} := eq_dec_of_listable.

Definition accesssize_of_declaration (opc : OpCode) : option AccessSize :=
  match opc with
  | db => Some byte
  | dd => Some dword
  | dq => Some qword
  | dw => Some word
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
  | cmove
  | cmovne
  | cmovnz
  | cmovo
  | cmp
  | dec
  | imul
  | inc
  | je
  | jmp
  | lea
  | leave
  | mov
  | movabs
  | movdqa
  | movdqu
  | movq
  | movd
  | movsx
  | movups
  | movzx
  | mul
  | mulx
  | neg
  | nop
  | not
  | or
  | paddq
  | pop
  | psubq
  | pshufd
  | pshufw
  | punpcklqdq
  | punpckhqdq
  | pslld
  | psrld
  | pand
  | pandn
  | por
  | pxor
  | psrad
  | push
  | rcr
  | ret
  | rol
  | ror
  | sal
  | sar
  | sbb
  | setc
  | sete
  | setne
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
    => None
  end.

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
| DIRECTIVE (d : string)
| ASCII_ (null_terminated : bool) (s : string)
.
Notation ASCII := (ASCII_ false).
Notation ASCIZ := (ASCII_ true).
Coercion INSTR : NormalInstruction >-> RawLine.
Record Line := { indent : string ; rawline :> RawLine ; pre_comment_whitespace : string ; comment : option string ; line_number : N}.
Definition Lines := list Line.

(** ** Inert assembler directives

    A [DIRECTIVE] line is an assembler directive that the parser
    recognizes but does not otherwise interpret.  The symbolic
    executor ([Crypto.Assembly.Symbolic.SymexRawLine]) and the
    concrete semantics ([Crypto.Assembly.WithBedrock.Semantics.DenoteRawLine])
    treat a directive inside a function body as a no-op if and only if
    [inert_directive] returns [true] on it; every other directive is
    rejected (fail closed).

    Only directives that provably cannot change the machine code
    emitted for the surrounding instructions belong here: CFI unwind
    information, debug line information, symbol metadata, and the
    like.  Directives that emit bytes into the current section
    ([.byte], [.ascii], [.asciz], [.fill], [.zero], [.incbin], ...)
    must never be listed, because inside a function body those bytes
    are placed in the instruction stream and executed as instructions
    that the checker never saw.  Some otherwise-harmless directives
    are inert only for certain argument forms; those are checked
    explicitly below:

    - [.p2align n[, fill[, max]]] pads code sections with no-ops when
      no fill value is given, but inserts copies of [fill] otherwise.
    - [.intel_syntax prefix] would change how every subsequent operand
      is assembled relative to what the parser assumed.
    - [.text subsection] moves the following instructions into another
      subsection, i.e. out of the fall-through path.
    - [.type sym, @gnu_indirect_function] turns the function into an
      IFUNC resolver whose return value is called instead. *)

(** Split a directive line into its lower-cased mnemonic and its
    (trimmed) arguments. *)
Definition directive_mnemonic_and_args (d : string) : string * string
  := let '(mnemonic, args) := String.take_while_drop_while (fun c0 => negb (Ascii.is_whitespace c0)) (String.trim d) in
     (String.to_lower mnemonic, String.trim args).

(** Directives that are inert regardless of their arguments. *)
Definition inert_directives_with_any_args : list string
  := [".addrsig"
      ; ".addrsig_sym"
      ; ".cfi_def_cfa"
      ; ".cfi_def_cfa_offset"
      ; ".cfi_def_cfa_register"
      ; ".cfi_endproc"
      ; ".cfi_offset"
      ; ".cfi_startproc"
      ; ".file"
      ; ".ident"
      ; ".loc"
      ; ".size"
     ]%string.

(** Symbol types accepted in [.type sym, <type>].  GAS accepts the
    type with a [@], [%], or [#] prefix, in double quotes, or bare. *)
Definition inert_symbol_types : list string
  := ["function"; "stt_func"; "object"; "stt_object"; "notype"; "stt_notype"]%string.

Definition strip_symbol_type_decoration (ty : string) : string
  := let ty := String.trim ty in
     let ty := match ty with
               | String c0 rest
                 => if (Ascii.eqb c0 "@" || Ascii.eqb c0 "%" || Ascii.eqb c0 "#")%bool
                    then rest
                    else ty
               | EmptyString => ty
               end in
     if (String.startswith """" ty && String.endswith """" ty && (2 <=? String.length ty)%nat)%bool
     then String.substring 1 (String.length ty - 2) ty
     else ty.

Definition inert_directive (d : string) : bool
  := let '(mnemonic, args) := directive_mnemonic_and_args d in
     let fields := List.map String.trim (String.split "," args) in
     if List.existsb (String.eqb mnemonic) inert_directives_with_any_args
     then true
     else if (mnemonic =? ".text")%string
     then (args =? EmptyString)%string
     else if (mnemonic =? ".intel_syntax")%string
     then (String.to_lower args =? "noprefix")%string
     else if (mnemonic =? ".type")%string
     then match fields with
          | [_; ty] => List.existsb (String.eqb (String.to_lower (strip_symbol_type_decoration ty))) inert_symbol_types
          | _ => false
          end
     else if (mnemonic =? ".p2align")%string
     then match fields with
          | [_] | [_; EmptyString] | [_; EmptyString; _] => true
          | _ => false
          end
     else false.

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
  | ret | nop => Some 64 (* irrelevant? *)
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

Definition reg_offset (r : REG) : N :=
    match r with
    |(ah      | ch      | dh      | bh      )
      => 8
    | _ => 0
    end.

Definition widest_register_of (r : REG) : REG :=
  match r with
  | ((al | ah) | ax | eax | rax) => rax
  | ((cl | ch) | cx | ecx | rcx) => rcx
  | ((dl | dh) | dx | edx | rdx) => rdx
  | ((bl | bh) | bx | ebx | rbx) => rbx
  | (spl | sp | esp | rsp) => rsp
  | (bpl | bp | ebp | rbp) => rbp
  | (sil | si | esi | rsi) => rsi
  | (dil | di | edi | rdi) => rdi
  | (r8b | r8w | r8d | r8) => r8
  | (r9b | r9w | r9d | r9) => r9
  | (r10b | r10w | r10d | r10) => r10
  | (r11b | r11w | r11d | r11) => r11
  | (r12b | r12w | r12d | r12) => r12
  | (r13b | r13w | r13d | r13) => r13
  | (r14b | r14w | r14d | r14) => r14
  | (r15b | r15w | r15d | r15) => r15
  end.

Definition widest_registers := Eval lazy in List.filter (fun x => REG_beq x (widest_register_of x)) (list_all REG).

Definition wide_reg_index_pairs := Eval lazy in List.map (fun '(n, r) => (N.of_nat n, r)) (List.enumerate widest_registers).

Definition eta_reg {A} : (REG -> A) -> (REG -> A).
Proof.
  intros f r; pose (f r) as fr; destruct r.
  all: let v := eval cbv in fr in exact v.
Defined.

Definition reg_index (r : REG) : N := Eval lazy in
  eta_reg (fun r =>
    Option.value
      (option_map (@fst _ _) (find (fun '(n, r') => REG_beq (widest_register_of r) r') wide_reg_index_pairs))
      0%N)
    r.

Definition widest_register_of_index_opt (n : N) : option REG
  := List.nth_error (List.map (@snd _ _) wide_reg_index_pairs) (N.to_nat n).

(** convenience printing function *)
Definition widest_register_of_index (n : N) : REG
  := Option.value (widest_register_of_index_opt n) rax.

Definition widest_reg_size_of (r : REG) : N :=
  reg_size (widest_register_of_index (reg_index r)).

Definition index_and_shift_and_bitcount_of_reg (r : REG) :=
  (reg_index r, reg_offset r, reg_size r).

Definition overlapping_registers (r : REG) : list REG := Eval lazy in eta_reg
  (fun r => List.filter (fun r' => REG_beq (widest_register_of r) (widest_register_of r')) (list_all REG))
  r.

Definition reg_of_index_and_shift_and_bitcount_opt :=
  fun '(index, offset, size) =>
    (wr <- widest_register_of_index_opt index;
    let rs := overlapping_registers wr in
    List.find (fun r => ((reg_size r =? size) && (reg_offset r =? offset))%N%bool) rs)%option.

Definition reg_of_index_and_shift_and_bitcount :=
  fun '(index, offset, size) =>
    match reg_of_index_and_shift_and_bitcount_opt (index, offset, size) with
    | Some r => r
    | None => widest_register_of_index index
    end.

Class assembly_program_options := {
  default_rel : bool ;
}.
