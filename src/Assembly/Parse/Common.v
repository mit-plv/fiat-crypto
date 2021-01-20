Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Strings.Parse.Common.
Require Import Crypto.Util.Strings.ParseArithmetic.
Require Import Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.Listable.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope parse_scope.

Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.

Inductive REG :=
|     rax |     rcx |     rdx |     rbx | rsp  | rbp  | rsi  | rdi  | r8  | r9  | r10  | r11  | r12  | r13  | r14  | r15
|     eax |     ecx |     edx |     ebx | esp  | ebp  | esi  | edi  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d
|      ax |      cx |      dx |      bx |  sp  |  bp  |  si  |  di  | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w
| ah | al | ch | cl | dh | dl | bh | bl |  spl |  bpl |  sil |  dil | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b
.
Derive REG_Listable SuchThat (@FinitelyListable REG REG_Listable) As REG_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances REG_Listable REG_FinitelyListable.

(* M-x query-replace-regex RET ([^ ]+) => _ RET \1 => "\1" *)
Global Instance show_REG : Show REG
  := fun with_parens reg
     => match reg with
        | rax => "rax"
        | rcx => "rcx"
        | rdx => "rdx"
        | rbx => "rbx"
        | rsp => "rsp"
        | rbp => "rbp"
        | rsi => "rsi"
        | rdi => "rdi"
        | r8 => "r8"
        | r9 => "r9"
        | r10 => "r10"
        | r11 => "r11"
        | r12 => "r12"
        | r13 => "r13"
        | r14 => "r14"
        | r15 => "r15"
        | eax => "eax"
        | ecx => "ecx"
        | edx => "edx"
        | ebx => "ebx"
        | esp => "esp"
        | ebp => "ebp"
        | esi => "esi"
        | edi => "edi"
        | r8d => "r8d"
        | r9d => "r9d"
        | r10d => "r10d"
        | r11d => "r11d"
        | r12d => "r12d"
        | r13d => "r13d"
        | r14d => "r14d"
        | r15d => "r15d"
        | ax => "ax"
        | cx => "cx"
        | dx => "dx"
        | bx => "bx"
        | sp => "sp"
        | bp => "bp"
        | si => "si"
        | di => "di"
        | r8w => "r8w"
        | r9w => "r9w"
        | r10w => "r10w"
        | r11w => "r11w"
        | r12w => "r12w"
        | r13w => "r13w"
        | r14w => "r14w"
        | r15w => "r15w"
        | ah => "ah"
        | al => "al"
        | ch => "ch"
        | cl => "cl"
        | dh => "dh"
        | dl => "dl"
        | bh => "bh"
        | bl => "bl"
        | spl => "spl"
        | bpl => "bpl"
        | sil => "sil"
        | dil => "dil"
        | r8b => "r8b"
        | r9b => "r9b"
        | r10b => "r10b"
        | r11b => "r11b"
        | r12b => "r12b"
        | r13b => "r13b"
        | r14b => "r14b"
        | r15b => "r15b"
        end.

Definition CONST := Z.

Record MEM := { mem_is_byte : bool ; mem_reg : REG ; mem_extra_reg : option REG ; mem_offset : option Z }.

Inductive FLAG := CF | PF | AF | ZF | SF.
Derive FLAG_Listable SuchThat (@FinitelyListable FLAG FLAG_Listable) As FLAG_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances FLAG_Listable FLAG_FinitelyListable.

(* M-x query-replace-regex RET ([^ ]+) => _ RET \1 => "\1" *)
Global Instance show_FLAG : Show FLAG
  := fun with_parens flag
     => match flag with
        | CF => "CF"
        | PF => "PF"
        | AF => "AF"
        | ZF => "ZF"
        | SF => "SF"
        end.

Inductive OpCode := adc | adcx | add | adox | and | clc | cmovnz | dec | imul | inc | lea | mov | movzx | mulx | ret| sar | sub | sbb | setc | seto | shrd | shr | test | xchg | xor.
Derive OpCode_Listable SuchThat (@FinitelyListable OpCode OpCode_Listable) As OpCode_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances OpCode_Listable OpCode_FinitelyListable.

(* M-x query-replace-regex RET ([^ ]+) => _ RET \1 => "\1" *)
Global Instance show_OpCode : Show OpCode
  := fun with_parens opc
     => match opc with
        | adc => "adc"
        | adcx => "adcx"
        | add => "add"
        | adox => "adox"
        | and => "and"
        | clc => "clc"
        | cmovnz => "cmovnz"
        | dec => "dec"
        | imul => "imul"
        | inc => "inc"
        | lea => "lea"
        | mov => "mov"
        | movzx => "movzx"
        | mulx => "mulx"
        | ret => "ret"
        | sar => "sar"
        | sub => "sub"
        | sbb => "sbb"
        | setc => "setc"
        | seto => "seto"
        | shrd => "shrd"
        | shr => "shr"
        | test => "test"
        | xchg => "xchg"
        | xor => "xor"
        end.

Record name := { name_prefix : string ; name_number : N }.

Inductive ARG := reg (r : REG) | mem (m : MEM) | const (c : CONST) | flag (f : FLAG).

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
