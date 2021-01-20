Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Strings.Parse.Common.
Require Import Crypto.Assembly.Parse.Common.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope parse_scope.

Record Instruction := { op : OpCode ; dst_args : list ARG ; src_args : list ARG ; names : list name }.

Definition Instructions := list Instruction.

Definition parse_literal_key (key : string) : ParserAction _
  := """" ;; key ;; """" ;; strip_whitespace_around ":".

Definition parse_literal_key_then {A} (key : string) (parse_k : ParserAction A) : ParserAction A
  := parse_literal_key key ;;->{ fun _ v => v } parse_k.

Definition parse_field_sep : ParserAction _ := strip_whitespace_around ",".

Definition ParseJSONInstruction : ParserAction Instruction
  := parse_map
       (fun '(opv, (dstv, (srcv, namesv)))
        => {| op := opv ; dst_args := dstv ; src_args := srcv ; names := match namesv with None => [] | Some v => v end |})
       (strip_whitespace_after "{" ;;R
      ((parse_literal_key "instruction" ;;R parse_OpCode true) ;;
       (parse_field_sep ;;R parse_literal_key "dst" ;;R parse_list_gen_no_leading_trailing_space "[" "," "]" (parse_ARG true true)) ;;
       (parse_field_sep ;;R parse_literal_key "src" ;;R parse_list_gen_no_leading_trailing_space "[" "," "]" (parse_ARG true true)) ;;
       ((parse_field_sep ;;R parse_literal_key "name" ;;R parse_list_gen_no_leading_trailing_space "[" "," "]" (parse_name true))?) ;;L
       (parse_field_sep?)) ;;L
       (strip_whitespace_before "}")).

Definition ParseJSONInstructions : ParserAction Instructions
  := parse_list_gen
       "[" "," "]"
       ParseJSONInstruction.

Definition parse : string -> option Instructions
  := finalize ParseJSONInstructions.

(* TEST CASE: *)
Redirect "log"
         Compute
         parse
         "
[
{""instruction"" : ""sub"",
""dst"": [ ""rsp"" ],
""src"": [ ""CONST 0x38"" ],
""name"": [""x5""]
}
]"
.
