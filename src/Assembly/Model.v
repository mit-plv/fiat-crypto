Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Bool.Bool.
Require Import Crypto.Util.Bool.Reflect.
(*
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Listable.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
 *)
Local Set Implicit Arguments.
Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.

Inductive REG :=
|     rax |     rcx |     rdx |     rbx | rsp  | rbp  | rsi  | rdi  | r8  | r9  | r10  | r11  | r12  | r13  | r14  | r15
|     eax |     ecx |     edx |     ebx | esp  | ebp  | esi  | edi  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d
|      ax |      cx |      dx |      bx |  sp  |  bp  |  si  |  di  | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w
| ah | al | ch | cl | dh | dl | bh | bl |  spl |  bpl |  sil |  dil | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b
.

Definition CONST := Z.

Record MEM := { mem_is_byte : bool ; mem_reg : REG ; mem_extra_reg : option REG ; mem_offset : option Z }.

Declare Scope REG_scope.
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

Declare Scope CONST_scope.
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

Lemma MEM_dec_bl (x y : MEM) : MEM_beq x y = true -> x = y.
Proof. destruct x, y; cbn.
  := proj1 (Z.eqb_eq x y).
Definition MEM_dec_lb (x y : MEM) : x = y -> MEM_beq x y = true := proj2 (Z.eqb_eq x y).
Definition MEM_eq_dec (x y : MEM) : {x = y} + {x <> y} := Z.eq_dec x y.

Declare Scope MEM_scope.
Delimit Scope MEM_scope with MEM.
Bind Scope MEM_scope with MEM.

Infix "=?" := MEM_beq : MEM_scope.

Global Instance MEM_beq_spec : reflect_rel (@eq MEM) MEM_beq | 10
  := reflect_of_beq MEM_dec_bl MEM_dec_lb.
Definition MEM_beq_eq x y : (x =? y)%MEM = true <-> x = y := conj (@MEM_dec_bl _ _) (@MEM_dec_lb _ _).
Lemma MEM_beq_neq x y : (x =? y)%MEM = false <-> x <> y.
Proof. rewrite <- MEM_beq_eq; destruct (x =? y)%MEM; intuition congruence. Qed.
Global Instance MEM_beq_compat : Proper (eq ==> eq ==> eq) MEM_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

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

Print internal_

Definition parse_quotes_around {A} (literal : ParserAction A) : ParserAction A
  := """" ;;->{ fun _ v => v } literal ;;->{ fun v _ => v } """".

Definition maybe_parse_quotes_around {A} (with_quotes : bool) : ParserAction A -> ParserAction A
  := (if with_quotes then parse_quotes_around else fun x => x).

Definition parse_REG_list : list (string * REG)
  := Eval vm_compute in
      List.map
        (fun r => (show false r, r))
        (list_all REG).

Definition parse_REG (with_quotes : bool) : ParserAction REG
  := maybe_parse_quotes_around with_quotes (parse_strs parse_REG_list).

Definition parse_FLAG_list : list (string * FLAG)
  := Eval vm_compute in
      List.map
        (fun r => (show false r, r))
        (list_all FLAG).

Definition parse_FLAG (with_quotes : bool) : ParserAction FLAG
  := maybe_parse_quotes_around with_quotes (parse_strs parse_FLAG_list).

Definition parse_MEM (with_quotes : bool) : ParserAction MEM
  := maybe_parse_quotes_around
       with_quotes
       (parse_map
          (fun '(has_byte, (r, (r', maybe_pm_z)))
           => {| mem_is_byte := if has_byte:option _ then true else false
                 ; mem_reg := r
                 ; mem_extra_reg := r'
                 ; mem_offset := match maybe_pm_z with
                                 | inl (inl _ (* plus *), z) => Some z
                                 | inl (inr _ (* minus *), z) => Some (-z)
                                 | inr _ (* only whitespace *) => None
                                 end%Z |})
          (((strip_whitespace_after "byte ")?) ;;
           (strip_whitespace_after "[" ;;R
            parse_REG false ;;
            ((strip_whitespace_around "+" ;;R parse_REG false)?) ;;
            ((strip_whitespace_before ("+" ||->{id} "-") ;; parse_Z_arith_strict) ||->{id} parse_any_whitespace) ;;L
            "]"))).

Definition parse_CONST (const_keyword : bool) (with_quotes : bool) : ParserAction CONST
  := maybe_parse_quotes_around
       with_quotes
       (if const_keyword
        then "CONST " ;;R parse_Z_arith_strict ;;L parse_lookahead_not parse_one_whitespace
        else parse_lookahead_not parse_one_whitespace ;;R parse_Z_arith_strict ;;L parse_lookahead_not parse_one_whitespace).

Definition parse_ARG (const_keyword : bool) (with_quotes : bool) : ParserAction ARG
  := parse_alt_list
       [parse_map reg (parse_REG with_quotes)
        ; parse_map mem (parse_MEM with_quotes)
        ; parse_map const (parse_CONST const_keyword with_quotes)
        ; parse_map flag (parse_FLAG with_quotes)].

Definition parse_OpCode_list : list (string * OpCode)
  := Eval vm_compute in
      List.map
        (fun r => (show false r, r))
        (list_all OpCode).

Definition parse_OpCode (with_quotes : bool) : ParserAction OpCode
  := maybe_parse_quotes_around with_quotes (parse_strs parse_OpCode_list).

Definition parse_name (with_quotes : bool) : ParserAction name
  := maybe_parse_quotes_around
       with_quotes
       ((parse_map string_of_list_ascii ([a-zA-Z]+))
          ;;->{ fun s n => {| name_prefix := s ; name_number := digits_to_N 10 n |} }
          ((parse_digits_gen_step 10)* )).
