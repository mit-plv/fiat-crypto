Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Strings.Parse.Common.
Require Import Crypto.Util.Strings.String.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Assembly.Parse.Common.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ListUtil.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope parse_scope.

Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.

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
                       else let parsed_mnemonic := (parse_OpCode false ;;L ε) mnemonic in
                            let parsed_args := (parse_list_gen "" "," "" (parse_ARG false false) ;;L ε) args in
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
        | flag f => show with_parens f
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

Definition Lines_beq : Lines -> Lines -> bool := list_beq _ Line_beq.
Lemma Lines_beq_eq x y : Lines_beq x y = true <-> x = y.
Proof. cbv [Lines_beq]; split; first [ apply internal_list_dec_lb | apply internal_list_dec_bl ]. Abort.

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
