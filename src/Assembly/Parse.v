Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Equality.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.Strings.Parse.Common.
Require Import Crypto.Util.Strings.ParseArithmetic.
Require Import Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.Listable.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sum.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope parse_scope.

Derive REG_Listable SuchThat (@FinitelyListable REG REG_Listable) As REG_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances REG_Listable REG_FinitelyListable.

(* M-x query-replace-regex RET \([^ ]+\) => _ RET \1 => "\1" *)
Global Instance show_REG : Show REG
  := fun reg
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
Global Instance show_lvl_REG : ShowLevel REG := show_REG.

Derive FLAG_Listable SuchThat (@FinitelyListable FLAG FLAG_Listable) As FLAG_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances FLAG_Listable FLAG_FinitelyListable.

(* M-x query-replace-regex RET \([^ ]+\) => _ RET \1 => "\1" *)
Global Instance show_FLAG : Show FLAG
  := fun flag
     => match flag with
        | CF => "CF"
        | PF => "PF"
        | AF => "AF"
        | ZF => "ZF"
        | SF => "SF"
        | OF => "OF"
        end.
Global Instance show_lvl_FLAG : ShowLevel FLAG := show_FLAG.

Derive OpCode_Listable SuchThat (@FinitelyListable OpCode OpCode_Listable) As OpCode_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances OpCode_Listable OpCode_FinitelyListable.

(* M-x query-replace-regex RET \([^ ]+\) => _ RET \1 => "\1" *)
Global Instance show_OpCode : Show OpCode
  := fun opc
     => match opc with
        | adc => "adc"
        | adcx => "adcx"
        | add => "add"
        | adox => "adox"
        | and => "and"
        | bzhi => "bzhi"
        | call => "call"
        | clc => "clc"
        | cmovb => "cmovb"
        | cmovc => "cmovc"
        | cmovnz => "cmovnz"
        | cmp => "cmp"
        | db => "db"
        | dd => "dd"
        | dec => "dec"
        | dq => "dq"
        | dw => "dw"
        | imul => "imul"
        | inc => "inc"
        | je => "je"
        | jmp => "jmp"
        | lea => "lea"
        | mov => "mov"
        | movzx => "movzx"
        | mul => "mul"
        | mulx => "mulx"
        | pop => "pop"
        | push => "push"
        | rcr => "rcr"
        | ret => "ret"
        | sar => "sar"
        | sbb => "sbb"
        | setc => "setc"
        | seto => "seto"
        | shl => "shl"
        | shlx => "shlx"
        | shr => "shr"
        | shrx => "shrx"
        | shrd => "shrd"
        | sub => "sub"
        | test => "test"
        | xchg => "xchg"
        | xor => "xor"
        end.
Global Instance show_lvl_OpCode : ShowLevel OpCode := show_OpCode.

Derive OpPrefix_Listable SuchThat (@FinitelyListable OpPrefix OpPrefix_Listable) As OpPrefix_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances OpPrefix_Listable OpPrefix_FinitelyListable.

(* M-x query-replace-regex RET \([^ ]+\) => _ RET \1 => "\1" *)
Global Instance show_OpPrefix : Show OpPrefix
  := fun opp
     => match opp with
        | rep => "rep"
        | repz => "repz"
        | repnz => "repnz"
        end.
Global Instance show_lvl_OpPrefix : ShowLevel OpPrefix := show_OpPrefix.

Definition parse_REG_list : list (string * REG)
  := Eval vm_compute in
      List.map
        (fun r => (show r, r))
        (list_all REG).

Definition parse_REG : ParserAction REG
  := parse_strs parse_REG_list.

Definition parse_FLAG_list : list (string * FLAG)
  := Eval vm_compute in
      List.map
        (fun r => (show r, r))
        (list_all FLAG).

Definition parse_FLAG : ParserAction FLAG
  := parse_strs parse_FLAG_list.

Derive AccessSize_Listable SuchThat (@FinitelyListable AccessSize AccessSize_Listable) As AccessSize_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances AccessSize_Listable AccessSize_FinitelyListable.

(* M-x query-replace-regex RET \([^ ]+\) => _ RET \1 => "\1" *)
Global Instance show_AccessSize : Show AccessSize
  := fun sz
     => match sz with
        | byte => "byte"
        | word => "word"
        | dword => "dword"
        | qword => "qword"
        end.
Global Instance show_lvl_AccessSize : ShowLevel AccessSize := show_AccessSize.

Definition parse_AccessSize_list : list (string * AccessSize)
  := Eval vm_compute in
      List.map
        (fun r => (show r, r))
        (list_all AccessSize).

Definition parse_AccessSize : ParserAction AccessSize
  := (parse_strs_casefold parse_AccessSize_list ;;L (casefold " ptr")?).


(* Do we want to support anything else from the printable characters?
!""#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~ *)
(* According to https://www.nasm.us/xdoc/2.15.05/html/nasmdoc3.html:
Valid characters in labels are letters, numbers, _, $, #, @, ~, ., and ?. The only characters which may be used as the first character of an identifier are letters, . (with special meaning: see section 3.9), _ and ?. An identifier may also be prefixed with a $ to indicate that it is intended to be read as an identifier and not a reserved word; thus, if some other module you are linking with defines a symbol called eax, you can refer to $eax in NASM code to distinguish the symbol from the register. Maximum length of an identifier is 4095 characters. *)
Definition parse_label : ParserAction string
  := let parse_any_ascii s := parse_alt_list (List.map parse_ascii (list_ascii_of_string s)) in
     parse_map
       (fun '(char, ls) => string_of_list_ascii (char :: ls))
       (([a-zA-Z] || parse_any_ascii "._?$") ;;
        (([a-zA-Z] || parse_any_ascii "0123456789_$#@~.?")* )).

Definition parse_MEM : ParserAction MEM
  := parse_map
       (fun '(access_size, (br (*base reg*), sr (*scale reg, including z *), offset, base_label))
        => {| mem_bits_access_size := access_size:option AccessSize
           ; mem_base_reg := br:option REG
           ; mem_base_label := base_label
           ; mem_scale_reg := sr:option (Z * REG)
           ; mem_offset := offset:option Z |})
       (((strip_whitespace_after parse_AccessSize)?) ;;
        (parse_option_list_map
           (fun '(offset, vars)
            => (vars <-- List.map (fun '(c, (v, e), vs) => match vs, e with [], 1%Z => Some (c, v) | _, _ => None end) vars;
                let regs : list (Z * REG) := Option.List.map (fun '(c, v) => match v with inl v => Some (c, v) | inr _ => None end) vars in
                let labels : list (Z * string) := Option.List.map (fun '(c, v) => match v with inr v => Some (c, v) | inl _ => None end) vars in
                base_label <- match labels with
                              | [] => Some None
                              | [(1%Z, lbl)] => Some (Some lbl)
                              | _ => None
                              end;
                let offset := if (0 =? offset)%Z then None else Some offset in
                base_scale_reg <- match regs with
                                  | [] => Some (None, None)
                                  | [(1%Z, r)] => Some (Some r, None)
                                  | [(s, r)] => Some (None, Some (s, r))
                                  | [(1%Z, r1); (s, r2)]
                                  | [(s, r2); (1%Z, r1)]
                                    => Some (Some r1, Some (s, r2))
                                  | _ => None
                                  end;
                let '(br, sr) := base_scale_reg in
                Some (br (*base reg*), sr (*scale reg, including z *), offset, base_label))%option)
           ("[" ;;R parse_Z_poly_strict (sum_beq _ _ REG_beq String.eqb) (parse_or_else_gen (fun x => x) parse_REG parse_label) ;;L "]"))).

Definition parse_CONST (const_keyword : bool) : ParserAction CONST
  := if const_keyword
     then "CONST " ;;R parse_Z_arith_strict ;;L parse_lookahead_not parse_one_whitespace
     else parse_lookahead_not parse_one_whitespace ;;R parse_Z_arith_strict ;;L parse_lookahead_not parse_one_whitespace.

Definition parse_JUMP_LABEL : ParserAction JUMP_LABEL
  := parse_map
       (fun '(near, lbl)
        => {| jump_near := if near:option _ then true else false
           ; label_name := lbl : string
           |})
       ((strip_whitespace_after "NEAR ")? ;; parse_label).

(* we only parse something as a label if it cannot possibly be anything else, because asm is terrible and has ambiguous parses otherwise :-( *)
Definition parse_ARG (const_keyword : bool) : ParserAction ARG
  := parse_or_else
       (parse_alt_list
          [parse_map reg parse_REG
           ; parse_map mem parse_MEM
           ; parse_map const (parse_CONST const_keyword)])
       (parse_map label parse_JUMP_LABEL).

Definition parse_OpCode_list : list (string * OpCode)
  := Eval vm_compute in
      List.map
        (fun r => (show r, r))
        (list_all OpCode).

Definition parse_OpCode : ParserAction OpCode
  := parse_strs_case_insensitive parse_OpCode_list.

Definition parse_OpPrefix_list : list (string * OpPrefix)
  := Eval vm_compute in
      List.map
        (fun r => (show r, r))
        (list_all OpPrefix).

Definition parse_OpPrefix : ParserAction OpPrefix
  := parse_strs parse_OpPrefix_list.

(** assumes no leading nor trailing whitespace and no comment *)
Definition parse_RawLine : ParserAction RawLine
  := fun s
     => let s := String.trim s in
        (* get the first space-separated opcode *)
        let '(mnemonic, args) := String.take_while_drop_while (fun ch => negb (Ascii.is_whitespace ch)) s in
        let args := String.trim args in
        if (String.to_upper mnemonic =? "SECTION")
        then [(SECTION args, "")]
        else if (String.to_upper mnemonic =? "GLOBAL")
        then [(GLOBAL args, "")]
        else if (String.to_upper mnemonic =? "ALIGN")
        then [(ALIGN args, "")]
        else if (String.to_upper mnemonic =? "DEFAULT") && (String.to_upper args =? "REL")
        then [(DEFAULT_REL, "")]
        else if String.endswith ":" s
        then [(LABEL (substring 0 (pred (String.length s)) s), "")]
        else if (s =? "")
        then [(EMPTY, "")]
        else let parsed_prefix := (parse_OpPrefix ;;L ε) mnemonic in
             List.flat_map
               (fun '(parsed_prefix, mnemonic, args)
                => let parsed_mnemonic := (parse_OpCode ;;L ε) mnemonic in
                   let parsed_args := (parse_list_gen "" "," "" (parse_ARG false) ;;L ε) args in
                   List.flat_map
                     (fun '(opc, _)
                      => List.map
                           (fun '(argsv, _) => (INSTR {| prefix := parsed_prefix ; op := opc ; args := argsv |}, ""))
                           parsed_args)
                     parsed_mnemonic)
               match parsed_prefix with
               | []
                 => [(None, mnemonic, args)]
               | _
                 => List.map
                      (fun '(parsed_prefix, _)
                       => let '(mnemonic, args) := String.take_while_drop_while (fun ch => negb (Ascii.is_whitespace ch)) args in
                          let args := String.trim args in
                          (Some parsed_prefix, mnemonic, args))
                      parsed_prefix
               end.

Definition parse_Line : ParserAction Line
  := fun s
     => let '(indentv, rest_linev) := take_while_drop_while Ascii.is_whitespace s in
        let '(precommentv, commentv)
            := match String.split ";" rest_linev with
               | [] => ("", None)
               | [precommentv] => (String.rtrim precommentv, None)
               | precommentv::commentv => (precommentv, Some (String.concat ";" commentv))
               end in
        let '(rev_trailing_whitespacev, rev_rawlinev) := take_while_drop_while Ascii.is_whitespace (String.rev precommentv) in
        let rawlinev := String.rev rev_rawlinev in
        let trailing_whitespacev := String.rev rev_trailing_whitespacev in
        List.map
          (fun '(r, rem) => ({| indent := indentv ; rawline := r ; pre_comment_whitespace := trailing_whitespacev ; comment := commentv |}, rem))
          (parse_RawLine rawlinev).

(* the error is the unparsable lines *)
Fixpoint parse_Lines' (l : list string) : ErrorT (list string) Lines
  := match l with
     | [] => Success []
     | l :: ls
       => match finalize parse_Line l, parse_Lines' ls with
          | None, Error ls => Error (l :: ls)
          | None, Success _ => Error (l :: nil)
          | Some _, Error ls => Error ls
          | Some l, Success ls => Success (l :: ls)
          end
     end.

Definition parse_Lines (l : list string) := parse_Lines' (String.split_newlines l).

Notation parse := parse_Lines (only parsing).

Global Instance show_lvl_MEM : ShowLevel MEM
  := fun m
     => (match m.(mem_bits_access_size) with
         | Some n
           => show_lvl_app (fun 'tt => if n =? 8 then "byte" else if n =? 64 then "QWORD PTR" else "BAD SIZE")%N (* TODO: Fix casing and stuff *)
         | None => show_lvl
         end)
          (fun 'tt
           => let reg_part
                := (match m.(mem_base_reg), m.(mem_scale_reg) with
                    | (*"[Reg]"          *) Some br, None         => show_REG br
                    | (*"[Reg + Z * Reg]"*) Some br, Some (z, sr) => show_REG br  ++ " + " ++  Decimal.show_Z z  ++ " * " ++ show_REG sr (*only matching '+' here, because there cannot be a negative scale. *)
                    | (*"[      Z * Reg]"*) None,    Some (z, sr) =>                           Decimal.show_Z z  ++ " * " ++ show_REG sr
                    | (*"[             ]"*) None,    None         => "" (* impossible, because only offset is invalid, but we seem to need it for coq because both are option's*)
                    end%Z) in
              let offset_part
                := (match m.(mem_offset) with
                      | None => ""
                      | Some offset
                        => (if offset <? 0 then " - " else " + ")
                             ++ (let offset := Z.abs offset in
                                 if (Z.modulo offset 8 =? 0)%Z
                                 then "0x08 * " ++ Decimal.show_Z (offset / 8)
                                 else Hex.show_Z offset)
                    end%Z) in
              "[" ++ match m.(mem_base_label) with
                     | None => reg_part ++ offset_part
                     | Some l => "((" ++ l ++ offset_part ++ "))"
                     end
                  ++ "]").
Global Instance show_MEM : Show MEM := show_lvl_MEM.

Global Instance show_lvl_JUMP_LABEL : ShowLevel JUMP_LABEL
  := fun l _
     => ((if l.(jump_near) then "NEAR " else "")
           ++ l.(label_name)).
Global Instance show_JUMP_LABEL : Show JUMP_LABEL := show_lvl_JUMP_LABEL.

Global Instance show_lvl_ARG : ShowLevel ARG
  := fun a
     => match a with
        | reg r => show_lvl r
        | mem m => show_lvl m
        | const c => show_lvl c
        | label l => show_lvl l
        end.
Global Instance show_ARG : Show ARG := show_lvl_ARG.

Global Instance show_NormalInstruction : Show NormalInstruction
  := fun i
     => match i.(prefix) with
        | None => ""
        | Some prefix => show prefix ++ " "
        end
          ++ (show i.(op))
          ++ match i.(args) with
             | [] => ""
             | _ => " " ++ String.concat ", " (List.map show i.(args))
             end.

Global Instance show_RawLine : Show RawLine
  := fun l
     => match l with
        | SECTION name => "SECTION " ++ name
        | GLOBAL name => "GLOBAL " ++ name
        | ALIGN args => "ALIGN " ++ args
        | DEFAULT_REL => "DEFAULT REL"
        | LABEL name => name ++ ":"
        | EMPTY => ""
        | INSTR instr => show instr
        end.

Global Instance show_Line : Show Line
  := fun l
     => l.(indent) ++ show l.(rawline) ++ l.(pre_comment_whitespace) ++ match l.(comment) with
                                                                        | Some c => ";" ++ c
                                                                        | None => ""
                                                                        end.
Global Instance show_lines_Lines : ShowLines Lines
  := fun ls => List.map show ls.

Definition parse_correct_on (v : list string)
  := forall res, parse v = Success res -> parse v = parse (show_lines res).

Inductive ParseError :=
| Parse_error (msgs : list string)
.

Inductive ParseValidatedError :=
| Initial_parse_error (err : ParseError)
| Reparse_error (new_asm : list string) (err : ParseError)
| Lengths_not_equal (old_asm : Lines) (new_asm : Lines)
| Lines_not_equal (mismatched_lines : list (Line * Line))
| Duplicate_labels (name_counts : list (string * nat))
.
Global Coercion Initial_parse_error : ParseError >-> ParseValidatedError.

Global Instance show_lines_ParseError : ShowLines ParseError
  := fun err => match err with
                | Parse_error err => err
                end.
Global Instance show_ParseError : Show ParseError := _.
Global Instance show_lines_ParseValidatedError : ShowLines ParseValidatedError
  := fun err => match err with
                | Initial_parse_error err
                  => match show_lines err with
                     | [] => ["Unknown error while parsing assembly"]
                     | [err] => ["Error while parsing assembly: " ++ err]%string
                     | lines => "Error while parsing assembly:" :: lines
                     end
                | Reparse_error new_asm err
                  => match show_lines err with
                     | [] => ["Unknown error while reparsing assembly:"] ++ new_asm
                     | [err] => (["Error while reparsing assembly: " ++ err
                                  ; "New assembly being parsed:"]%string)
                                  ++ new_asm
                     | lines => ["Error while parsing assembly:"]
                                  ++ lines
                                  ++ [""]
                                  ++ ["New assembly being parsed:"]
                                  ++ new_asm
                     end
                | Lengths_not_equal old_asm new_asm
                  => ["Reparsing the assembly:"]
                       ++ show_lines old_asm
                       ++ [""]
                       ++ ["Yielded non-equal assembly:"]
                       ++ show_lines new_asm
                       ++ [""]
                       ++ (["The number of lines was not equal (" ++ show (List.length old_asm) ++ " ≠ " ++ show (List.length new_asm) ++ ")"]%string)
                | Lines_not_equal mismatched_lines
                  => ["When reparsing assembly for validation, the following lines were not equal:"]
                       ++ (List.flat_map (fun '(old, new) => ["- " ++ show old; "+ " ++ show new; ""]%string)
                                         mismatched_lines)
                | Duplicate_labels nil
                  => ["Internal error: Duplicate_labels []"]
                | Duplicate_labels [(name, count)]
                  => ["Label occurs multiple times: " ++ name ++ " occurs " ++ show count ++ " times"]%string
                | Duplicate_labels name_counts
                  => ["Labels occurs multiple times:"]
                       ++ List.map (fun '(name, count) => name ++ " occurs " ++ show count ++ " times")%string name_counts
                end%list.
Global Instance show_ParseValidatedError : Show ParseValidatedError := _.

Definition parse_validated (v : list string) : ErrorT ParseValidatedError Lines
  := match parse v with
     | Success v
       => let new_asm := show_lines v in
          match parse new_asm with
          | Success v'
            => let labels := Option.List.map (fun l => match l.(rawline) with
                                                       | LABEL n => Some n
                                                       | _ => None
                                                       end) v' in
               let counts := List.map (fun l => (l, List.count_occ string_dec labels l)) labels in
               let big_counts := List.filter (fun '(l, n) => (1 <? n)%nat) counts in
               match big_counts with
               | nil
                 => if (List.length v =? List.length v')%nat
                    then match List.filter (fun '(x, y) => negb (Line_beq x y)) (List.combine v v') with
                         | nil => Success v
                         | mismatched_lines => Error (Lines_not_equal mismatched_lines)
                         end
                    else Error (Lengths_not_equal v v')
               | _ => Error (Duplicate_labels big_counts)
               end
          | Error e
            => Error (Reparse_error new_asm (Parse_error e))
          end
     | Error e => Error (Initial_parse_error (Parse_error e))
     end.

Definition parse_correct_on_bool (v : list string) : bool
  := match parse v, parse_validated v with
     | Success _, Success _ => true
     | Error _, _ => true
     | Success _, Error _ => false
     end.

Definition parse_validated_correct_on v
  := forall res, parse_validated v = Success res <-> parse v = Success res.

Lemma parse_validated_correct_on_iff v : parse_validated_correct_on v <-> parse_correct_on v.
Proof.
  cbv [parse_validated_correct_on parse_correct_on parse_validated].
  destruct (parse_Lines v) eqn:Hp; [ | split; [ congruence | split; congruence ] ].
  destruct (parse_Lines (show_lines _)) eqn:Hp2; (split; [ intros H res Hres; inversion Hres; subst | intro H; specialize (H _ eq_refl); rewrite <- H in Hp2; inversion Hp2; subst ]); rewrite ?Nat.eqb_refl, ?combine_same; try congruence.
  all: repeat first [ progress destruct_head' iff
                    | congruence
                    | progress subst
                    | progress rewrite ?Nat.eqb_eq in *
                    | match goal with
                      | [ H : forall x, _ <-> Success ?y = Success x |- _ ] => specialize (H y)
                      | [ H : ?x = ?x |- _ ] => clear H
                      | [ H : Success ?x = Success ?y |- _ ] => inversion H; clear H
                      | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
                      end
                    | break_innermost_match_hyps_step
                    | progress break_match_hyps
                    | progress break_match
                    | progress intros
                    | apply conj ].
Abort.

Lemma parse_correct_on_bool_iff v : parse_correct_on_bool v = true <-> parse_correct_on v.
Proof.
  assert (parse_validated_correct_on_iff : forall v, parse_validated_correct_on v <-> parse_correct_on v) by admit.
  rewrite <- parse_validated_correct_on_iff.
  cbv [parse_correct_on_bool parse_validated_correct_on].
  destruct (parse_Lines v) eqn:Heq1, (parse_validated v) eqn:Heq2; split; try split; try congruence.
Abort.

(* This version allows for easier debugging because it highlights the differences *)
Definition parse_correct_on_debug (v : list string)
  := match parse v with
     | Success v => match parse (show_lines v) with
                    | Success v'
                      => if (List.length v =? List.length v')%nat
                         then List.filter (fun '(x, y) => negb (Line_beq x y)) (List.combine v v') = nil
                         else List.length v = List.length v'
                    | Error e => forall x, e = x -> False
                    end
     | Error e => forall x, e = x -> False
     end.
Theorem parse_correct : forall v, parse_correct_on v.
Proof. Abort.

(** Some extra utility functions for processing assembly files *)
(** We assume that the asm file contains GLOBAL declarations for each
    function.  The function name must match the name which would be
    generated by fiat-crypto.  The function names declare the labels
    that break up instructions into functions.  We currently associate
    lines (including blank and comment lines) before a label to the
    previous label, though plausibly there should be some other
    heuristic for dealing with comments. *)

Definition find_globals (ls : Lines) : list string
  := Option.List.map
       (fun l => match l.(rawline) with
                 | GLOBAL name => Some name
                 | _ => None
                 end)
       ls.

Fixpoint split_code_to_functions' (globals : list string) (ls : Lines) : Lines (* prefix *) * list (string (* global name *) * Lines)
  := match ls with
     | [] => ([], [])
     | l :: ls
       => let '(prefix, rest) := split_code_to_functions' globals ls in
          let default := (l :: prefix, rest) in
          match l.(rawline) with
          | LABEL name => if List.existsb (fun n => name =? n)%string globals
                          then ([], (name, l::prefix) :: rest)
                          else default
          | _ => default
          end
     end.

Definition split_code_to_functions (ls : Lines) : Lines (* prefix *) * list (string (* global name *) * Lines)
  := let globals := find_globals ls in
     split_code_to_functions' globals ls.
