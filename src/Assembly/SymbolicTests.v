(** Regression tests for the treatment of non-instruction lines by the
    symbolic executor (see scrutineer finding #2512).

    Every line inside a function body that is accepted by the
    equivalence checker is emitted verbatim as certified machine
    code, so lines that can carry arbitrary bytes ([.ascii], [.asciz],
    [.byte], ...) or otherwise change the emitted code must be
    rejected rather than silently skipped. *)
From Coq Require Import NArith.
From Coq Require Import String.
From Coq Require Import List.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Parse.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.Equivalence.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** [inert_directive] *)

Definition inert_directive_cases : list (string * bool)
  := [(* inert regardless of arguments *)
      (".cfi_startproc", true); (".cfi_def_cfa_offset 16", true); (".cfi_offset 6, -16", true)
      ; (".cfi_def_cfa_register 6", true); (".cfi_def_cfa 7, 8", true); (".CFI_ENDPROC", true)
      ; (".loc 1 12 3", true); (".loc", true); (".file ""x.c""", true); (".file 1 ""x.c""", true)
      ; (".ident ""GCC: (GNU) 14.1.0""", true); (".size f, .-f", true); (".addrsig", true); (".addrsig_sym f", true)
      (* inert only for some argument forms *)
      ; (".text", true); (".text 1", false)
      ; (".intel_syntax noprefix", true); (".intel_syntax", false); (".intel_syntax prefix", false)
      ; (".type f, @function", true); (".type f,%function", true); (".type f, ""function""", true)
      ; (".type f, STT_FUNC", true); (".type f, @object", true)
      ; (".type f, @gnu_indirect_function", false); (".type f, @tls_object", false); (".type f", false)
      ; (".p2align 4", true); (".p2align 4,", true); (".p2align 4,,10", true)
      ; (".p2align 4, 0x90", false); (".p2align 4, 0xcc, 10", false)
      (* never inert: these emit bytes or move code *)
      ; (".byte 1", false); (".ascii ""x""", false); (".asciz ""x""", false); (".string ""x""", false)
      ; (".fill 1,1,0xc3", false); (".zero 4", false); (".skip 4", false); (".space 4", false)
      ; (".incbin ""x""", false); (".octa 1", false); (".quad 1", false); (".float 1.0", false); (".double 1.0", false)
      ; (".section .text", false); (".globl f", false); (".align 4", false); (".balign 4", false); ("", false)].

Definition inert_directive_failures
  := List.filter (fun '(d, expected) => negb (Bool.eqb (inert_directive d) expected)) inert_directive_cases.

Goal inert_directive_failures = []. Proof. vm_compute. reflexivity. Qed.

(** ** Parsing of data lines *)

(** The parser decodes [\xNN] escapes, so any byte sequence can be
    written as an [.ascii] string. *)
Definition mov_eax_deadbeef : string := string_of_list_ascii (List.map Ascii.ascii_of_nat [0xb8; 0xef; 0xbe; 0xad; 0xde]).
Goal parse [".ascii ""\xb8\xef\xbe\xad\xde"""]
     = Success [{| indent := ""; rawline := ASCII mov_eax_deadbeef
                 ; pre_comment_whitespace := ""; comment := None; line_number := 1%N |}].
Proof. vm_compute. reflexivity. Qed.

(** ** Symbolic execution of non-instruction lines *)

Local Instance test_symbolic_options : symbolic_options_computed_opt
  := {| asm_rewriting_passes := @default_rewriting_passes default_rewrite_pass_order (fun _ => true)
      ; asm_debug_symex_asm_first_computed := false
      ; asm_node_reveal_depth_computed := default_node_reveal_depth |}.

Definition symex_lines (ls : list string) : ErrorT (list string) (Symbolic.error + unit)
  := match parse ls with
     | Error e => Error e
     | Success ls
       => match SymexLines ls (init_symbolic_state dag.empty) with
          | Success (v, _) => Success (inr v)
          | Error (e, _) => Success (inl e)
          end
     end.

Definition is_success {A B} (v : ErrorT A (B + unit)) : bool
  := match v with Success (inr tt) => true | _ => false end.

(** A straight-line, register-only function body (the trailing [ret]
    is stripped by [strip_ret] before symbolic execution, so it is
    omitted here). *)
Definition body_prefix := ["fiat_test:"; "mov rax, rsi"].
Definition body_suffix := ["add rax, rdi"].
Definition with_line (l : list string) := body_prefix ++ l ++ body_suffix.

(** Inert lines are fine. *)
Goal is_success (symex_lines (with_line [])) = true. Proof. vm_compute. reflexivity. Qed.
Goal is_success (symex_lines (with_line [".cfi_startproc"; ".cfi_def_cfa_offset 16"; ".loc 1 2 3"; "; a comment"; ""; ".Ltmp0:"; ".p2align 4,,10"])) = true.
Proof. vm_compute. reflexivity. Qed.

(** Data-emitting lines must be rejected: the assembler would place
    these bytes in the instruction stream (here they encode
    [mov eax, 0xdeadbeef]). *)
Goal symex_lines (with_line [".ascii ""\xb8\xef\xbe\xad\xde"""])
     = Success (inl (error.data_emitting_line (ASCII mov_eax_deadbeef))).
Proof. vm_compute. reflexivity. Qed.
Goal is_success (symex_lines (with_line [".asciz ""\xb8\xef\xbe\xad\xde"""])) = false. Proof. vm_compute. reflexivity. Qed.
Goal is_success (symex_lines (with_line [".byte 0xb8, 0xef, 0xbe, 0xad, 0xde"])) = false. Proof. vm_compute. reflexivity. Qed.
Goal is_success (symex_lines (with_line [".quad 0xdeadbeef"])) = false. Proof. vm_compute. reflexivity. Qed.

(** Directives that can change the emitted code must be rejected. *)
Goal symex_lines (with_line [".p2align 4, 0xc3"]) = Success (inl (error.unsupported_directive ".p2align 4, 0xc3")).
Proof. vm_compute. reflexivity. Qed.
Goal is_success (symex_lines (with_line [".text 1"])) = false. Proof. vm_compute. reflexivity. Qed.
Goal is_success (symex_lines (with_line [".type fiat_test, @gnu_indirect_function"])) = false. Proof. vm_compute. reflexivity. Qed.
Goal is_success (symex_lines (with_line [".intel_syntax prefix"])) = false. Proof. vm_compute. reflexivity. Qed.
Goal is_success (symex_lines (with_line ["ALIGN 16"])) = false. Proof. vm_compute. reflexivity. Qed.
Goal is_success (symex_lines (with_line ["SECTION .data"])) = false. Proof. vm_compute. reflexivity. Qed.

(** Directives the parser does not know about are already rejected at
    parse time. *)
Goal match parse (with_line [".fill 16, 1, 0xc3"]) with Error _ => true | Success _ => false end = true.
Proof. vm_compute. reflexivity. Qed.
Goal match parse (with_line [".incbin ""payload.bin"""]) with Error _ => true | Success _ => false end = true.
Proof. vm_compute. reflexivity. Qed.

(** The error messages are displayed. *)
Goal show_lines (error.data_emitting_line (ASCII "abc"))
     = ["error.data_emitting_line .ascii ""abc""";
        "Lines that emit raw bytes (.ascii, .asciz, .byte, ...) are not allowed inside a function being checked, because the assembler would place those bytes in the instruction stream where they would execute as instructions that the checker did not model."].
Proof. vm_compute. reflexivity. Qed.
