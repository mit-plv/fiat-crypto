Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Crypto.Util.Strings.String.
Require Import Crypto.CLI.
Require Import Crypto.Util.Notations.
Require Import Crypto.StandaloneOCamlMain.
Import ListNotations. Local Open Scope string_scope.

Module debugging_no_asm.
  Import StandaloneOCamlMain.UnsaturatedSolinas.
  Import Coq.ZArith.ZArith.
  Open Scope Z_scope.
  Goal True.
    pose main as v.
    cbv beta iota zeta delta [main main_gen] in v.
    set (k := map _ sys_argv) in (value of v).
    assert (k = ["./src/ExtractionOCaml/unsaturated_solinas"; "25519"; "64"; "5"; "2^255-19"; "carry_mul"; "--no-primitives"; "--hints-file"; "t.asm"]) by admit.
    clearbody k; subst k.
    cbv beta iota zeta delta [ForExtraction.UnsaturatedSolinas.PipelineMain ForExtraction.Parameterized.PipelineMain] in v.
    vm_compute Arg.parse_argv in v.
    cbv beta iota in v.
    vm_compute Arg.split_type_of_list' in v.
    cbv beta iota in v.
    cbv [ForExtraction.parse_common_optional_options] in v.
    cbv [ForExtraction.hint_file_names] in v.
    cbn [map fst snd] in v.
    cbn [ForExtraction.with_read_concat_asm_files_cps] in v.
    set (k := ForExtraction.with_read_file "t.asm") in (value of v).
    assert (k = (fun k => k ["SECTION .text"
;"        GLOBAL 451_run80000of100000_ratio07298_seed1612328584_mul_curve25519"
;""
;"451_run80000of100000_ratio07298_seed1612328584_mul_curve25519:"
;"        sub rsp, 0x70"
;"        mov [ rsp + 0x38 ], rbx; saving to stack"
;"        mov [ rsp + 0x40 ], rbp; saving to stack"
;"        mov [ rsp + 0x48 ], r12; saving to stack"
;"        mov [ rsp + 0x50 ], r13; saving to stack"
;"        mov [ rsp + 0x58 ], r14; saving to stack"
           ])) by admit.
    clearbody k; subst k.
    set (k := string_dec _ _) in (value of v) at 1; vm_compute in k; subst k; cbv beta iota in v.
    vm_compute ForExtraction.parse_args in v.
    cbv beta iota zeta in v.
    vm_compute concat in v.
    cbv [ForExtraction.output_file_name ForExtraction.asm_output_file_name] in v.
    cbn [Option.sequence_return nth_error] in v.
    set (k := string_dec _ _) in (value of v).
    vm_compute in k; subst k.
    cbv beta iota zeta in v.
    cbv [ForExtraction.Parameterized.Pipeline] in v.
    cbv [ForExtraction.Parameterized.ProcessedLines] in v.
    cbv [ForExtraction.Parameterized.PipelineLines] in v.
    cbv [ForExtraction.UnsaturatedSolinas.api] in v.
    cbn [fst snd] in v.
    repeat (set (x := ((_ ++ _)%string)) in (value of v) at 1; vm_compute in x; subst x).
    repeat (set (x := string_dec _ _) in (value of v) at 1; vm_compute in x; subst x).
    cbv beta iota zeta in v.
    repeat (set (x := ((_ ++ _)%list)) in (value of v) at 1; vm_compute in x; subst x).
    cbv [ForExtraction.Synthesize] in v.
    cbv [ForExtraction.machine_wordsize ForExtraction.parsed_synthesize_options] in v.
    cbv [UnsaturatedSolinas.Synthesize] in v.
    cbv [BoundsPipeline.typedef_info_of_typedef] in v.
    vm_compute BoundsPipeline.typedef.name in v.
    vm_compute Language.Compilers.ToString.int.option.interp.to_union in v.
    cbv [Primitives.parse_asm_hints] in v.
    cbv [Primitives.Synthesize] in v.
    cbv beta delta [Primitives.parse_asm_hints Primitives.parse_asm_files_lines] in v.
    vm_compute ForExtraction.assembly_hints_lines in v.
    cbv beta iota in v.
    vm_compute Parse.parse_validated in v.
    cbv beta iota in v.
    vm_compute Parse.split_code_to_functions in v.
    cbv beta iota in v.
    set (k := map _ _) in (value of v) at 1.
    cbn [map] in k.
    cbv [UnsaturatedSolinas.known_functions UnsaturatedSolinas.valid_names Primitives.synthesize_of_name] in k.
    cbn [fold_right map] in k.
    set (k' := (_ =? _)%string) in (value of k) at 1; vm_compute in k'; subst k'; cbv beta iota in k.
    cbn [fold_right map List.app] in k.
    cbv [UnsaturatedSolinas.extra_special_synthesis UnsaturatedSolinas.scarry_mul] in k.
    set (cm := UnsaturatedSolinas.carry_mul _ _ _ _) in (value of k).
    vm_compute in cm.
    set (cmv := (fun var => Language.Compilers.expr.Abs _)) in (value of cm).
    subst cm; cbv beta iota in k.
    set (cml := Language.Compilers.ToString.ToFunctionLines _ _ _ _ _ _ _ _ _ _ _ _ _ _) in (value of k).
    vm_compute in cml.
    set (cmlv := _ :: _) in (value of cml) at 1.
    subst cml.
    clearbody cmlv cmv.
    cbv beta iota in k.
    cbn [ErrorT.bind] in k.
    vm_compute String.append in k.
    subst k.
    cbn [ErrorT.bind] in v.
    set (k := Primitives.split_to_assembly_functions _ _) in (value of v).
    clear -k.
    cbv [Primitives.split_to_assembly_functions] in k.
    vm_compute in k; clear -k.
  Abort.
End debugging_no_asm.

Module debugging_typedef_bounds.
  Import StandaloneOCamlMain.UnsaturatedSolinas.
  Goal True.
    pose main as v.
    cbv beta iota zeta delta [main main_gen] in v.
    set (k := map _ sys_argv) in (value of v).
    assert (k = ["./src/ExtractionOCaml/unsaturated_solinas"; "curve25519"; "64"; "5"; "2^255-19"; "add"; "--no-primitives"]) by admit.
    clearbody k; subst k.
    cbv beta iota zeta delta [ForExtraction.UnsaturatedSolinas.PipelineMain ForExtraction.Parameterized.PipelineMain] in v.
    vm_compute Arg.parse_argv in v.
    Import Coq.ZArith.ZArith.
    Open Scope Z_scope.
    cbv beta iota in v.
    vm_compute Arg.split_type_of_list' in v.
    cbv beta iota in v.
    cbv [ForExtraction.parse_common_optional_options] in v.
    cbv [ForExtraction.hint_file_names] in v.
    cbn [map] in v.
    cbn [ForExtraction.with_read_concat_asm_files_cps] in v.
    vm_compute ForExtraction.parse_args in v.
    cbv beta iota zeta in v.
    vm_compute concat in v.
    cbv [ForExtraction.output_file_name ForExtraction.asm_output_file_name] in v.
    cbn [Option.sequence_return nth_error] in v.
    set (k := string_dec _ _) in (value of v).
    vm_compute in k; subst k.
    cbv beta iota zeta in v.
    cbv [ForExtraction.Parameterized.Pipeline] in v.
    cbv [ForExtraction.Parameterized.ProcessedLines] in v.
    cbv [ForExtraction.Parameterized.PipelineLines] in v.
    cbv [ForExtraction.UnsaturatedSolinas.api] in v.
    cbn [fst snd] in v.
    repeat (set (x := ((_ ++ _)%string)) in (value of v) at 1; vm_compute in x; subst x).
    repeat (set (x := string_dec _ _) in (value of v) at 1; vm_compute in x; subst x).
    cbv beta iota zeta in v.
    repeat (set (x := ((_ ++ _)%list)) in (value of v) at 1; vm_compute in x; subst x).
    cbv [ForExtraction.Synthesize] in v.
    cbv [ForExtraction.machine_wordsize ForExtraction.parsed_synthesize_options] in v.
    cbv [UnsaturatedSolinas.Synthesize] in v.
    cbv [BoundsPipeline.typedef_info_of_typedef] in v.
    vm_compute BoundsPipeline.typedef.name in v.
    vm_compute Language.Compilers.ToString.int.option.interp.to_union in v.
    cbv [Primitives.parse_asm_hints] in v.
    cbv [Primitives.Synthesize] in v.
    cbv [Primitives.parse_asm_hints] in v.
    vm_compute ForExtraction.assembly_hints_lines in v.
    cbv beta iota in v.
    cbv beta iota delta [Primitives.Synthesize] in v.
    set (k := ForExtraction.CollectErrors _) in (value of v).
    clear v; rename k into v.
    lazymatch (eval cbv [v] in v) with
    | context[map ?f ["add"] ] => pose (map f ["add"]) as k; change (map f ["add"]) with k in (value of v)
    end.
    clear v; rename k into v.
    cbn [map] in v.
    cbv [Primitives.synthesize_of_name] in v.
    set (k' := map _ _) in (value of v).
    cbv [UnsaturatedSolinas.known_functions] in k'.
    cbn [map] in k'.
    repeat (set (k'' := (_ =? _)%string) in (value of k') at 1; vm_compute in k''; subst k''; cbv beta iota zeta in k').
    set (k'' := UnsaturatedSolinas.sadd _ _ _ _ _) in (value of k').
    clear -k''; rename k'' into v.
    cbn -[UnsaturatedSolinas.sadd] in v.
    cbv [ForExtraction.low_level_rewriter_method] in v.
    cbn -[UnsaturatedSolinas.sadd] in v.
    cbv [UnsaturatedSolinas.sadd] in v.
    vm_compute UnsaturatedSolinas.add in v.
    cbv beta iota zeta in v.
    cbv [Language.Compilers.ToString.ToFunctionLines] in v.
    cbv [C.Compilers.ToString.C.OutputCAPI] in v.
    cbv [C.Compilers.ToString.C.ToFunctionLines] in v.
    vm_compute IR.Compilers.ToString.IR.OfPHOAS.ExprOfPHOAS in v.
    cbv beta iota zeta in v.
    set (k := Language.Compilers.ToString.OfPHOAS.input_bounds_to_string _ _) in (value of v).
    cbv [Language.Compilers.ToString.OfPHOAS.input_bounds_to_string] in k; clear -k.
    cbv [Language.Compilers.ToString.OfPHOAS.bound_to_string] in k.
    Redirect "log" Print Language.Compilers.ToString.OfPHOAS.bound_to_string.
    vm_compute in k.
  Abort.
End debugging_typedef_bounds.
