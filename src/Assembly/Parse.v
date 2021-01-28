Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.Assembly.Model.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.Strings.Parse.Common.
Require Import Crypto.Util.Strings.ParseArithmetic.
Require Import Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.Listable.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.ListUtil.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope parse_scope.

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
        | OF => "OF"
        end.

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

Definition parse_REG_list : list (string * REG)
  := Eval vm_compute in
      List.map
        (fun r => (show false r, r))
        (list_all REG).

Definition parse_REG : ParserAction REG
  := parse_strs parse_REG_list.

Definition parse_FLAG_list : list (string * FLAG)
  := Eval vm_compute in
      List.map
        (fun r => (show false r, r))
        (list_all FLAG).

Definition parse_FLAG : ParserAction FLAG
  := parse_strs parse_FLAG_list.

Definition parse_MEM : ParserAction MEM
  := parse_map
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
          parse_REG ;;
          ((strip_whitespace_around "+" ;;R parse_REG)?) ;;
          ((strip_whitespace_before ("+" ||->{id} "-") ;; parse_Z_arith_strict) ||->{id} parse_any_whitespace) ;;L
          "]")).

Definition parse_CONST (const_keyword : bool) : ParserAction CONST
  := if const_keyword
     then "CONST " ;;R parse_Z_arith_strict ;;L parse_lookahead_not parse_one_whitespace
     else parse_lookahead_not parse_one_whitespace ;;R parse_Z_arith_strict ;;L parse_lookahead_not parse_one_whitespace.

Definition parse_ARG (const_keyword : bool) : ParserAction ARG
  := parse_alt_list
       [parse_map reg parse_REG
        ; parse_map mem parse_MEM
        ; parse_map const (parse_CONST const_keyword)].

Definition parse_OpCode_list : list (string * OpCode)
  := Eval vm_compute in
      List.map
        (fun r => (show false r, r))
        (list_all OpCode).

Definition parse_OpCode : ParserAction OpCode
  := parse_strs parse_OpCode_list.

(** assumes no leading nor trailing whitespace and no comment *)
Definition parse_RawLine : ParserAction RawLine
  := fun s
     => let s := String.trim s in
        (* get the first space-separated opcode *)
        let '(mnemonic, args) := String.take_while_drop_while (fun ch => negb (Ascii.is_whitespace ch)) s in
        let args := String.trim args in
        if (mnemonic =? "SECTION")
        then [(SECTION args, "")]
        else if (mnemonic =? "GLOBAL")
             then [(GLOBAL args, "")]
             else if String.endswith ":" s
                  then [(LABEL (substring 0 (pred (String.length s)) s), "")]
                  else if (s =? "")
                       then [(EMPTY, "")]
                       else let parsed_mnemonic := (parse_OpCode ;;L ε) mnemonic in
                            let parsed_args := (parse_list_gen "" "," "" (parse_ARG false) ;;L ε) args in
                            List.flat_map
                              (fun '(opc, _)
                               => List.map
                                    (fun '(argsv, _) => (INSTR {| op := opc ; args := argsv |}, ""))
                                    parsed_args)
                              parsed_mnemonic.

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

Global Instance show_MEM : Show MEM
  := fun with_parens m
     => maybe_wrap_parens
          with_parens
          ((if m.(mem_is_byte) then "byte " else "")
             ++ "[" ++ (show false m.(mem_reg))
             ++ (match m.(mem_extra_reg) with
                 | None => ""
                 | Some r => " + " ++ show false r
                 end)
             ++ (match m.(mem_offset) with
                 | None => ""
                 | Some offset
                   => (if offset <? 0 then " - " else " + ")
                        ++ (let offset := Z.abs offset in
                            if (Z.modulo offset 8 =? 0)%Z
                            then "0x08 * " ++ Decimal.show_Z false (offset / 8)
                            else Hex.show_Z false offset)
                 end%Z)
             ++ "]").

Global Instance show_ARG : Show ARG
  := fun with_parens a
     => match a with
        | reg r => show with_parens r
        | mem m => show with_parens m
        | const c => show with_parens c
        end.

Global Instance show_NormalInstruction : Show NormalInstruction
  := fun with_parens i
     => show false i.(op) ++ match i.(args) with
                             | [] => ""
                             | _ => " " ++ String.concat ", " (List.map (show false) i.(args))
                             end.

Global Instance show_RawLine : Show RawLine
  := fun with_parens l
     => match l with
        | SECTION name => "SECTION " ++ name
        | GLOBAL name => "GLOBAL " ++ name
        | LABEL name => name ++ ":"
        | EMPTY => ""
        | INSTR instr => show with_parens instr
        end.

Global Instance show_Line : Show Line
  := fun with_parens l
     => l.(indent) ++ show false l.(rawline) ++ l.(pre_comment_whitespace) ++ match l.(comment) with
                                                                              | Some c => ";" ++ c
                                                                              | None => ""
                                                                              end.

Global Instance show_lines_Lines : ShowLines Lines
  := fun with_parens ls => List.map (show false) ls.

Definition parse_correct_on (v : list string)
  := forall res, parse v = Success res -> parse v = parse (show_lines false res).
Definition parse_correct_on_bool (v : list string) : bool
  := match parse v with
     | Success res => match parse (show_lines false res) with
                      | Success res' => Lines_beq res res'
                      | Error _ => false
                      end
     | Error _ => true
     end.
Lemma parse_correct_on_bool_iff v : parse_correct_on_bool v = true <-> parse_correct_on v.
Proof.
  cbv [parse_correct_on_bool parse_correct_on].
  destruct (parse_Lines v) eqn:Hp; [ | split; [ congruence | reflexivity ] ].
  destruct (parse_Lines (show_lines false _)) eqn:Hp2; (split; [ intros H res Hres; inversion Hres; subst | intro H; specialize (H _ eq_refl); rewrite <- H in Hp2; inversion Hp2; subst ]); try congruence.
Abort.

(* This version allows for easier debugging because it highlights the differences *)
Definition parse_correct_on_debug (v : list string)
  := match parse v with
     | Success v => match parse (show_lines false v) with
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
