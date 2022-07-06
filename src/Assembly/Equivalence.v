Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Parse.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Util.Strings.Parse.Common.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.Strings.String.
Require Import Crypto.Language.API.
Require Import Crypto.Language.APINotations.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Crypto.Stringification.Language.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.NUtil.Sorting.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.FoldMap.
Require Import Crypto.Util.ListUtil.CombineExtend.
Require Import Crypto.Util.ListUtil.RemoveN.
Require Import Crypto.Util.MSets.MSetN.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.ErrorT.List.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.Notations.
Import API.Compilers APINotations.Compilers AbstractInterpretation.ZRange.Compilers.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** List of registers used for outputs/inputs *)
Class assembly_calling_registers_opt := assembly_calling_registers' : option (list REG).
Typeclasses Opaque assembly_calling_registers_opt.
Definition default_assembly_calling_registers := [rdi;rsi;rdx;rcx;r8;r9].
Definition assembly_calling_registers {v : assembly_calling_registers_opt} : list REG
  := Option.value v default_assembly_calling_registers.
(** List of callee-saved / non-volatile registers *)
Variant assembly_callee_saved_registers_opt := Microsoft_x64 | System_V_AMD64 | explicit_registers (_ : list REG).
Existing Class assembly_callee_saved_registers_opt.
(* https://en.wikipedia.org/wiki/X86_calling_conventions#Microsoft_x64_calling_convention *)
(* The registers RAX, RCX, RDX, R8, R9, R10, R11 are considered volatile (caller-saved).[22]

The registers RBX, RBP, RDI, RSI, RSP, R12, R13, R14, and R15 are considered nonvolatile (callee-saved).[22]

-----
[22] https://docs.microsoft.com/en-us/cpp/build/x64-calling-convention?view=msvc-170&viewFallbackFrom=vs-2019#callercallee-saved-registers *)
Definition microsoft_x64_assembly_callee_saved_registers := [rbx;rbp;rdi;rsi;rsp;r12;r13;r14;r15].
(* https://en.wikipedia.org/wiki/X86_calling_conventions#System_V_AMD64_ABI *)
(* If the callee wishes to use registers RBX, RSP, RBP, and R12–R15, it must restore their original values before returning control to the caller. All other registers must be saved by the caller if it wishes to preserve their values.[25]: 16

[25] Michael Matz; Jan Hubička; Andreas Jaeger; et al., eds. (2018-01-28). "System V Application Binary Interface: AMD64 Architecture Processor Supplement (With LP64 and ILP32 Programming Models) Version 1.0" (PDF). 1.0. https://github.com/hjl-tools/x86-psABI/wiki/x86-64-psABI-1.0.pdf *)
Definition system_v_amd64_assembly_callee_saved_registers := [rbx;rsp;rbp;r12;r13;r14;r15].
Definition default_assembly_callee_saved_registers := System_V_AMD64.
Definition assembly_callee_saved_registers {v : assembly_callee_saved_registers_opt} : list REG
  := match v with
     | Microsoft_x64 => microsoft_x64_assembly_callee_saved_registers
     | System_V_AMD64 => system_v_amd64_assembly_callee_saved_registers
     | explicit_registers ls => ls
     end.
(** Are output arrays considered to come before input arrays, or after them? *)
Class assembly_output_first_opt := assembly_output_first : bool.
Typeclasses Opaque assembly_output_first_opt.
(** Should we assign registers to the arguments in left-to-right or right-to-left order? *)
Class assembly_argument_registers_left_to_right_opt := assembly_argument_registers_left_to_right : bool.
Typeclasses Opaque assembly_argument_registers_left_to_right_opt.
(** Stack size (in bytes) *)
Class assembly_stack_size_opt := assembly_stack_size' : option N.
Typeclasses Opaque assembly_stack_size_opt.
Definition extra_assembly_stack_size := 0%N.
(** The stack size is taken to be the given command line argument, or
    else inferred to be extra_assembly_stack_size plus the maximum
    statically knowable increase to rsp (via `push`, `pop`, `sub`,
    `add`, and `lea` instructions) *)
Fixpoint assembly_stack_size_at (cur_stack_size : Z) (asm : _) : list Z
  := match asm with
     | [] => []
     | l :: asm
       => let cng := match l.(rawline) with
                     | INSTR {| Syntax.op := sub ; args := [reg rsp; Syntax.const n] |}
                       => n
                     | INSTR {| Syntax.op := Syntax.add ; args := [reg rsp; Syntax.const n] |}
                       => -n
                     | INSTR {| Syntax.op := lea ; args := [reg rsp; Syntax.mem {| mem_base_reg := Some rsp ; mem_offset := Some n ; mem_scale_reg := None ; mem_bits_access_size := None |}] |}
                       => -n
                     | INSTR {| Syntax.op := lea ; args := [reg rsp; Syntax.mem {| mem_base_reg := Some rsp ; mem_offset := Some n ; mem_scale_reg := None ; mem_bits_access_size := Some sz |}] |}
                       => if (sz =? 64)%N
                          then -n
                          else 0
                     | INSTR instr
                       => match Syntax.operation_size instr with
                          | Some s
                            => match instr with
                               | {| Syntax.op := push ; args := [_] |}
                                 => Z.of_N s / 8
                               | {| Syntax.op := pop ; args := [_] |}
                                 => -Z.of_N s / 8
                               | _ => 0
                               end
                          | None => 0
                          end
                     | _ => 0
                     end in
          let new_stack_size := cur_stack_size + cng in
          new_stack_size :: assembly_stack_size_at new_stack_size asm
     end%Z.
Definition assembly_stack_size {v : assembly_stack_size_opt} (asm : _) : N
  := match v with
     | Some v => v
     | None => let extra_ss := Z.of_N extra_assembly_stack_size in
               Z.to_N (fold_right Z.max extra_ss (assembly_stack_size_at extra_ss asm))
     end.

Class assembly_conventions_opt :=
  { assembly_calling_registers_ :> assembly_calling_registers_opt
  ; assembly_stack_size_ :> assembly_stack_size_opt
  ; assembly_output_first_ :> assembly_output_first_opt
  ; assembly_argument_registers_left_to_right_ :> assembly_argument_registers_left_to_right_opt
  ; assembly_callee_saved_registers_ :> assembly_callee_saved_registers_opt
  }.

Global Instance show_assembly_callee_saved_registers_opt : Show assembly_callee_saved_registers_opt | 10
  := fun v => match v with
              | Microsoft_x64 => "Microsoft x64"
              | System_V_AMD64 => "System V AMD64"
              | explicit_registers ls => show ls
              end.

Definition parse_assembly_callee_saved_registers_opt : ParserAction assembly_callee_saved_registers_opt
  := ((parse_strs
         [(show Microsoft_x64, Microsoft_x64); ("Microsoft x64", Microsoft_x64); ("Microsoft_x64", Microsoft_x64); ("Microsoft-x64", Microsoft_x64); ("microsoft", Microsoft_x64); ("Microsoft", Microsoft_x64)
          ; (show System_V_AMD64, System_V_AMD64); ("System V", System_V_AMD64); ("System_V_AMD64", System_V_AMD64); ("system-v", System_V_AMD64); ("System-V-AMD64", System_V_AMD64); ("AMD64", System_V_AMD64); ("amd64", System_V_AMD64); ("system v", System_V_AMD64)])
        ||->{fun v => match v with inl v => v | inr ls => explicit_registers ls end}
        parse_comma_list parse_REG)%parse.

(** N.B. The printer of these error messages will always know the
assembly function lines and the AST used for equivalence checking, so
these error messages need not include this information.  However, they
should include as much information as possible about the local source
of the inequivalence.  It's not out of the question, for example, to
include enough information in the error message to generate .dot files
of the equivalence graphs.  If desired, we can parameterize the error
printing functions on command-lines options indicating how verbose to
be in printing the error message. *)
Inductive EquivalenceCheckingError :=
| Symbolic_execution_failed (_ : Symbolic.error) (_ : symbolic_state)
| Internal_error_output_load_failed (_ : option Symbolic.error) (_ : list ((REG + idx) + idx)) (_ : symbolic_state)
| Internal_error_extra_input_arguments (t : API.type) (unused_arguments : list (idx + list idx))
| Internal_error_lingering_memory (_ : symbolic_state)
| Internal_error_LoadOutputs_length_mismatch (outputaddrs : list ((REG + idx) + idx)) (output_types : list (option nat))
| Not_enough_registers (num_given num_extra_needed : nat)
| Registers_too_narrow (bad_reg : list REG)
| Callee_saved_registers_too_narrow (bad_reg : list REG)
| Duplicate_registers (bad_reg : list REG)
| Incorrect_array_input_dag_node
| Incorrect_Z_input_dag_node
| Not_enough_input_dag_nodes (t : API.type)
| Expected_const_in_reference_code (_ : idx)
| Expected_power_of_two (w : N) (_ : idx)
| Unknown_array_length (t : base.type)
| Registers_not_saved (regs : list (REG * (idx (* before *) * idx (* after *)))) (_ : symbolic_state)
| Invalid_arrow_type (t : API.type)
| Invalid_argument_type (t : API.type)
| Invalid_return_type (t : base.type)
| Invalid_higher_order_application {var} {s d : API.type} (f : API.expr (var:=var) (s -> d)) (x : API.expr (var:=var) s)
| Invalid_higher_order_let {var} {s : API.type} (x : API.expr (var:=var) s)
| Unhandled_identifier {t} (idc : ident t)
| Unhandled_cast (_ _ : Z)
| Unable_to_unify (_ _ : list (idx + list idx)) (first_new_idx_after_all_old_idxs : option idx) (_ : symbolic_state)
| Missing_ret
| Code_after_ret (significant : Lines) (l : Lines)
.

Definition symbolic_state_of_EquivalenceCheckingError (e : EquivalenceCheckingError) : option symbolic_state
  := match e with
     | Symbolic_execution_failed _ s
     | Internal_error_output_load_failed _ _ s
     | Internal_error_lingering_memory s
     | Unable_to_unify _ _ _ s
     | Registers_not_saved _ s
       => Some s
     | Internal_error_extra_input_arguments _ _
     | Internal_error_LoadOutputs_length_mismatch _ _
     | Not_enough_registers _ _
     | Registers_too_narrow _
     | Callee_saved_registers_too_narrow _
     | Duplicate_registers _
     | Incorrect_array_input_dag_node
     | Incorrect_Z_input_dag_node
     | Not_enough_input_dag_nodes _
     | Expected_const_in_reference_code _
     | Expected_power_of_two _ _
     | Unknown_array_length _
     | Invalid_arrow_type _
     | Invalid_argument_type _
     | Invalid_return_type _
     | Invalid_higher_order_application _ _ _ _ _
     | Invalid_higher_order_let _ _ _
     | Unhandled_identifier _ _
     | Unhandled_cast _ _
     | Missing_ret
     | Code_after_ret _ _
       => None
     end.

Definition AnnotatedLine := (Line * dag.eager.t)%type.
Definition AnnotatedLines := (Lines * symbolic_state)%type.

Definition show_annotated_Line : Show AnnotatedLine
  := fun '(l, d)
     => let l := show l in
        (l ++ match dag.eager.description_lookup d l with
              | [] => ""
              | new_idxs
                => String.Tab ++ "; " ++ String.concat ", " (List.map (fun i => "#" ++ show i) new_idxs)
              end)%string.

Global Instance show_lines_AnnotatedLines : ShowLines AnnotatedLines
  := fun '(ls, ss)
     => let d := dag.eager.force ss.(dag_state) in
        List.map (fun l => show_annotated_Line (l, d)) ls.

Fixpoint remove_common_indices {T} (eqb : T -> T -> bool) (xs ys : list T) (start_idx : nat) : list (nat * T) * list T
  := match xs with
     | [] => (List.map (fun '(idx, x) => (start_idx + idx, x)) (List.enumerate xs),
               ys)
     | x :: xs
       => let '(xs', ys') := remove_common_indices eqb xs (List.removen (eqb x) ys 1) (S start_idx) in
          if List.existsb (eqb x) ys
          then (xs', ys')
          else ((start_idx, x) :: xs', ys')
     end.

Definition show_expr_node_lite : Show Symbolic.expr
  := fix show_expr_node_lite (e : Symbolic.expr) : string
    := match e with
       | ExprRef i => "#" ++ show i
       | ExprApp (op, e)
         => "(" ++ show op ++ ", " ++ @show_list _ show_expr_node_lite e ++ ")"
       end%string.

Definition show_node_lite : Show (node idx)
  := fun '(op, e)
     => show_expr_node_lite (ExprApp (op, List.map ExprRef e)).

Definition recursive_deps_list_step
           (recursive_deps : NSet.t -> idx -> NSet.t)
           (so_far : NSet.t)
           (ls : list idx)
  : NSet.t
  := fold_left recursive_deps ls so_far.

Definition recursive_deps_step
           (recursive_deps : NSet.t -> idx -> NSet.t)
           (dag : dag)
           (so_far : NSet.t)
           (i : idx)
  : NSet.t
  := if NSet.mem i so_far
     then so_far
     else let so_far := NSet.add i so_far in
          match dag.lookup dag i with
          | Some (_op, args)
            => recursive_deps_list_step recursive_deps so_far args
          | None => so_far
          end.

Fixpoint recursive_deps
         (fuel : nat)
         (dag : dag)
         (init : NSet.t)
         (i : idx)
  : NSet.t
  := match fuel with
     | 0 => NSet.singleton i
     | S fuel => recursive_deps_step (recursive_deps fuel dag) dag init i
     end.

Definition recursive_deps_list
           (fuel : nat) (dag : dag)
           (init : NSet.t)
           (ls : list idx)
  : NSet.t
  := recursive_deps_list_step (recursive_deps fuel dag) init ls.

Definition at_leaves_fold
           {T} (f : idx -> T -> Symbolic.expr * T)
  := fix at_leaves_fold (e : Symbolic.expr) : T -> Symbolic.expr * T
    := match e with
       | ExprRef i => f i
       | ExprApp (op0, args)
         => fun st => let '(args, st) := List.foldmap at_leaves_fold args st in
                      (ExprApp (op0, args), st)
       end.

Definition at_leaves (f : idx -> Symbolic.expr) (e : Symbolic.expr) : Symbolic.expr
  := fst (at_leaves_fold (fun i 'tt => (f i, tt)) e tt).

Definition reveal_one_except (dag : dag) (except : idx -> bool) (e : Symbolic.expr) : Symbolic.expr * (bool (* revealed something *))
  := at_leaves_fold
       (fun i revealed
        => if except i
           then (ExprRef i, revealed)
           else match dag.lookup dag i with
                | Some (op0, args)
                  => (ExprApp (op0, List.map ExprRef args), true)
                | None => (ExprRef i, revealed)
                end)
       e
       false.

Definition indices_at_leaves_map (ls : list Symbolic.expr) : list idx
  := N.sort (NSet.elements (snd (List.foldmap (at_leaves_fold (fun i idxs => (ExprRef i, NSet.add i idxs))) ls NSet.empty))).

Definition indices_at_leaves (e : Symbolic.expr) : list idx
  := indices_at_leaves_map [e].

Fixpoint make_iteratively_revealed_exprs
         (dag : dag)
         (max_depth : nat)
         (except : idx -> bool)
         (ls : list Symbolic.expr)
  := match max_depth with
     | 0 => [] (* should not get here *)
     | S max_depth
       => let res := List.map (reveal_one_except dag except) ls in
          let ls := List.map fst res in
          let progress := List.existsb (fun b => b) (List.map snd res) in
          if progress
          then ls :: make_iteratively_revealed_exprs dag max_depth except ls
          else []
     end.

Definition describe_idx_from_state
           (show_full : bool)
           (st : symbolic_state) (idx : idx) : list string
  := let description_from_state
       := match reverse_lookup_widest_reg st.(symbolic_reg_state) idx, reverse_lookup_flag st.(symbolic_flag_state) idx, reverse_lookup_mem st.(symbolic_mem_state) idx with
          | Some r, _, _ => Some ("the value of the register " ++ show r)
          | None, Some f, _ => Some ("the value of the flag " ++ show f)
          | None, None, Some (ptr, ptsto) => Some ("the memory location at pseudo-address " ++ Hex.show_N ptr ++ " which points to dag index " ++ show ptsto ++ " which holds the value " ++ show (reveal st.(dag_state) 1 ptsto))
          | None, None, None => None
          end%string in
     let is_old := match reveal st.(dag_state) 1 idx with
                   | ExprApp (old _ _, _) => true
                   | _ => false
                   end in
     match is_old, description_from_state, show_full with
     | true, Some descr, _
     | _, Some descr, true
       => [show idx ++ " is " ++ descr ++ "."]
     | true, None, _
       => [show idx ++ " is a special value no longer present in the symbolic machine state at the end of execution."]
     | _, _, false => []
     | _, None, true
       => [show idx ++ " is " ++ match dag.lookup st.(dag_state) idx with
                                 | Some e => show_node_lite e
                                 | None => "not in the dag"
                                 end]
     end%string.

Definition iteratively_describe_idxs_after
           (first_new_idx_after_all_old_idxs : option idx)
           (dag : dag)
           (describe_idx : idx -> list string)
           (show_initial : bool)
           (idxs : list idx)
  : list string
  := let deps := recursive_deps_list (S (N.to_nat (dag.size dag))) dag NSet.empty idxs in
     let deps := if show_initial then List.fold_right NSet.add deps idxs else deps in
     let deps := List.rev (N.sort (NSet.elements deps)) in
     let deps := match first_new_idx_after_all_old_idxs with
                 | Some first_new_idx_after_all_old_idxs
                   => filter (fun i => (first_new_idx_after_all_old_idxs <=? i)%N) deps
                 | None => deps
                 end in
     List.flat_map describe_idx deps.

Definition iteratively_describe_idx
           (dag : dag)
           (describe_idx : idx -> list string)
           (show_initial : bool)
           (i : idx)
  : list string
  := iteratively_describe_idxs_after None dag describe_idx show_initial [i].

Definition describe_full_idx_from_state (st : symbolic_state) (i : idx)
  : list string
  := iteratively_describe_idx st (describe_idx_from_state true st) true i.

Fixpoint explain_array_unification_error_single
         (dag : dag)
         (first_new_idx_after_all_old_idxs : option idx)
         (singular plural : string)
         (left_descr right_descr : string)
         (explain_idx_unification_error : idx -> idx -> list string)
         (describe_idx : idx -> list string)
         (modulo_commutativity : bool)
         (asm_array PHOAS_array : list idx) (start_idx : nat)
  : list string
  := let recr := explain_array_unification_error_single dag first_new_idx_after_all_old_idxs singular plural left_descr right_descr explain_idx_unification_error describe_idx modulo_commutativity in
     match asm_array, PHOAS_array with
     | [], []
       => ["Internal Error: Unifiable " ++ plural ++ (if modulo_commutativity then " modulo commutativity" else "")]
     | [], PHOAS_array
       => ((["The " ++ right_descr ++ " " ++ singular ++ " contains " ++ show (List.length PHOAS_array) ++ " more values than the " ++ left_descr ++ " " ++ singular ++ "."]%string)
             ++ List.flat_map describe_idx PHOAS_array)%list
     | asm_array, []
       => ((["The " ++ left_descr ++ " " ++ singular ++ " contains " ++ show (List.length asm_array) ++ " more values than the " ++ right_descr ++ " " ++ singular ++ "."]%string)
             ++ List.flat_map describe_idx asm_array)%list
     | asm_value :: asm_array, PHOAS_value :: PHOAS_array
       => if Decidable.dec (asm_value = PHOAS_value)
          then recr asm_array PHOAS_array (S start_idx)
          else
            if modulo_commutativity && List.existsb (N.eqb asm_value) PHOAS_array
            then
              recr asm_array (PHOAS_value :: List.removen (N.eqb asm_value) PHOAS_array 1) (S start_idx)
            else
              ((["index " ++ show start_idx ++ ": " ++ show_expr_node_lite (ExprRef asm_value) ++ " ≠ " ++ show_expr_node_lite (ExprRef PHOAS_value)]%string)
                 (* if there we are entering into territory where all values were computed both by asm and PHOAS, and leaving territory where some values were computed only by the one that ran second, we will print out extra information about the smallest value that ran second *)
                 (* When we transition from an inequality that contains indices appearing only in assembly to an inequality containing indices that appear in both, recursively expand all indices appearing only in asm, before (after?) continuing on describing why the first arguments are not equal *)
                 ++ match first_new_idx_after_all_old_idxs with
                    | None => []
                    | Some first_new_idx_after_all_old_idxs
                      => if ((asm_value <? first_new_idx_after_all_old_idxs) && (PHOAS_value <? first_new_idx_after_all_old_idxs))%N%bool
                         then
                           match filter (fun i => first_new_idx_after_all_old_idxs <=? i)%N (asm_array ++ PHOAS_array) with
                           | [] => []
                           | new_idxs
                             => iteratively_describe_idxs_after
                                  None (* if we don't want to display the ones from only PHOAS, we could pass (Some first_new_idx_after_all_old_idxs) instead *)
                                  dag
                                  describe_idx
                                  true (* show initial *)
                                  new_idxs
                           end
                         else []
                    end
                 ++ explain_idx_unification_error asm_value PHOAS_value
              )%list
     end%string%list%bool.

Definition iteratively_explain_array_unification_error_modulo_commutativity
           (dag : dag)
           (describe_idx : idx -> list string)
           (op : option op)
           (show_initial : bool)
           (asm_array : list (nat * idx)) (PHOAS_array : list idx)
  : list string
  := let recursive_deps := recursive_deps_list (S (N.to_nat (dag.size dag))) dag NSet.empty in
     let asm_deps := recursive_deps (List.map snd asm_array) in
     let PHOAS_deps := recursive_deps PHOAS_array in
     let common_deps := NSet.inter asm_deps PHOAS_deps in
     let make_iteratively_revealed_exprs := make_iteratively_revealed_exprs dag (S (N.to_nat (dag.size dag))) (fun i => NSet.mem i common_deps) in
     let asm_exprs := List.map ExprRef (List.map snd asm_array) in
     let PHOAS_exprs := List.map ExprRef PHOAS_array in
     let asm_reveals := make_iteratively_revealed_exprs asm_exprs in
     let PHOAS_reveals := make_iteratively_revealed_exprs PHOAS_exprs in
     let reveals := List.combine_extend asm_exprs PHOAS_exprs asm_reveals PHOAS_reveals in
     let '(last_asm, last_PHOAS) := List.last reveals (asm_exprs, PHOAS_exprs) in
     (* reveal one more time *)
     let reveal_one_final_time := List.map (at_leaves (reveal dag 1)) in
     let last_asm := reveal_one_final_time last_asm in
     let last_PHOAS := reveal_one_final_time last_PHOAS in
     let reveals := (if show_initial then [(asm_exprs, PHOAS_exprs)] else [])
                      ++ reveals ++ [(last_asm, last_PHOAS)] in
     let show_array array
       := let args := @show_list _ show_expr_node_lite array in
          match op with
          | Some op => "(" ++ show op ++ ", " ++ args ++ ")"
          | None => args
          end%string in
     let show_array_pretty array
       := match op with
          | Some op => show_expr_pretty (ExprApp (op, array))
          | None => @show_list _ show_expr_pretty array
          end%string in
     List.map
       (fun '(asm_array, PHOAS_array)
        => (show_array asm_array ++ " ≠ " ++ show_array PHOAS_array)%string)
       reveals
       ++ [show_array_pretty last_asm ++ " ≠ " ++ show_array_pretty last_PHOAS]%string
       ++ (List.flat_map
             describe_idx
             (indices_at_leaves_map (last_asm ++ last_PHOAS))).

Definition explain_array_unification_error
           (first_new_idx_after_all_old_idxs : option idx)
           (dag : dag)
           (singular plural : string)
           (left_descr right_descr : string)
           (explain_idx_unification_error : idx -> idx -> list string)
           (describe_idx : idx -> list string)
           (op : option op)
           (asm_array PHOAS_array : list idx)
  : list string
  := let modulo_commutativity := match op with Some o => commutative o | None => false end in
     if (modulo_commutativity && negb (List.length asm_array =? List.length PHOAS_array))%nat%bool
     then
       let orig_asm_array := asm_array in
       let orig_PHOAS_array := PHOAS_array in
       match remove_common_indices N.eqb asm_array PHOAS_array 0 with
       | ([], [])
         => ["Internal Error: Unifiable " ++ plural ++ " modulo commutativity"]
       | ([], PHOAS_array)
         => ((["The " ++ right_descr ++ " " ++ singular ++ " contains " ++ show (List.length PHOAS_array) ++ " more values than the " ++ left_descr ++ " " ++ singular ++ "."]%string)
               ++ List.flat_map describe_idx PHOAS_array)%list
       | (asm_array, [])
         => ((["The " ++ left_descr ++ " " ++ singular ++ " contains " ++ show (List.length asm_array) ++ " more values than the " ++ right_descr ++ " " ++ singular ++ "."]%string)
               ++ List.flat_map describe_idx (List.map snd asm_array))%list
       | ([(arr_index, asm_value)], [PHOAS_value])
         => (* there's only one idx on each side, so we can just naively compare them *)
           ((["index " ++ show arr_index ++ ": " ++ show_expr_node_lite (ExprRef asm_value) ++ " ≠ " ++ show_expr_node_lite (ExprRef PHOAS_value)]%string)
              ++ explain_idx_unification_error asm_value PHOAS_value
           )%list
       | (asm_array, PHOAS_array)
         => (* show init state when there are some common indices; otherwise we don't want to duplicate the expression *)
           let show_initial_state := (negb ((List.length asm_array =? List.length orig_asm_array) && (List.length PHOAS_array =? List.length orig_PHOAS_array)))%nat in
           iteratively_explain_array_unification_error_modulo_commutativity
             dag describe_idx op show_initial_state asm_array PHOAS_array
       end%string%list%bool
     else
       explain_array_unification_error_single dag first_new_idx_after_all_old_idxs singular plural left_descr right_descr explain_idx_unification_error describe_idx modulo_commutativity asm_array PHOAS_array 0.

Definition explain_mismatch_from_state
           (left_descr right_descr : string)
           (st : symbolic_state) (asm_idx PHOAS_idx : idx) : list string
  := ((describe_idx_from_state false (*left_descr*) st asm_idx)
        ++ (describe_idx_from_state false (*right_descr*) st PHOAS_idx))%list.

Fixpoint explain_idx_unification_error
         (first_new_idx_after_all_old_idxs : option idx)
         (left_descr right_descr : string)
         (st : symbolic_state) (fuel : nat) (asm_idx PHOAS_idx : idx) {struct fuel} : list string
  := let recr := match fuel with
                 | O => fun _ _ => ["Internal error: out of fuel in explain_expr_unification_error"]
                 | S fuel => explain_idx_unification_error first_new_idx_after_all_old_idxs left_descr right_descr st fuel
                 end in
     let reveal_idx idx := dag.lookup st.(dag_state) idx in
     let reveal_show_idx idx
       := match reveal_idx idx with
          | Some n => show n
          | None => show_expr_node_lite (ExprRef idx)
          end in
     let reveal_show_node '(op, e)
       := ("(" ++ show op ++ ", " ++ @show_list _ reveal_show_idx e ++ ")")%string in
     match reveal_idx asm_idx, reveal_idx PHOAS_idx with
     | None, None
       => ["Internal error: neither expression is in the dag"]
     | None, Some _
       => ["Internal error: assembly index " ++ show asm_idx ++ " is not in the dag"]
     | Some _, None
       => ["Internal error: synthesized index " ++ show PHOAS_idx ++ " is not in the dag"]
     | Some ((asm_o, asm_e) as asm), Some ((PHOAS_o, PHOAS_e) as PHOAS)
       => (([show_node_lite asm ++ " ≠ " ++ show_node_lite PHOAS]%string)
             ++ (if Decidable.dec (asm_o = PHOAS_o)
                 then explain_array_unification_error first_new_idx_after_all_old_idxs st "argument" "arguments" left_descr right_descr recr (describe_idx_from_state false st) (Some asm_o) asm_e PHOAS_e
                 else (([reveal_show_node asm ++ " ≠ " ++ reveal_show_node PHOAS
                         ; "Operation mismatch: " ++ show asm_o ++ " ≠ " ++ show PHOAS_o]%string)
                         ++ explain_mismatch_from_state left_descr right_descr st asm_idx PHOAS_idx)%list))%list
     end%string.

Definition explain_unification_default_fuel (st : symbolic_state) : nat
  := N.to_nat (10 + (2 * dag.size st.(dag_state))) (* we since the dag is acyclic, we shouldn't have to do more recursive lookups than its length; we double and add 10 for safety *).

Fixpoint explain_unification_error (asm_output PHOAS_output : list (idx + list idx)) (first_new_idx_after_all_old_idxs : option idx) (start_idx : nat) (st : symbolic_state)
  : list string
  := let fuel := explain_unification_default_fuel st in
     match asm_output, PHOAS_output with
     | [], []
       => ["Internal Error: Unifiable"]
     | [], PHOAS_output
       => ["The synthesized code returns " ++ show (List.length PHOAS_output) ++ " more values than the assembly code."]
     | asm_output, []
       => ["The assembly code returns " ++ show (List.length asm_output) ++ " more values than the synthesized code."]
     | asm_value :: asm_output, PHOAS_value :: PHOAS_output
       => if Decidable.dec (asm_value = PHOAS_value)
          then explain_unification_error asm_output PHOAS_output first_new_idx_after_all_old_idxs (S start_idx) st
          else let prefix := ("Could not unify the values at index " ++ show start_idx ++ ":")%string in
               match asm_value, PHOAS_value with
               | inl _, inr _ => [prefix; "The assembly code returns a scalar while the synthesized code returns an array."]
               | inr _, inl _ => [prefix; "The assembly code returns an array while the synthesized code returns a scalar."]
               | inl asm_idx, inl PHOAS_idx
                 => (["index  " ++ show start_idx ++ ": " ++ show_expr_node_lite (ExprRef asm_idx) ++ " ≠ " ++ show_expr_node_lite (ExprRef PHOAS_idx)]%string)
                      ++ explain_idx_unification_error first_new_idx_after_all_old_idxs "assembly" "synthesized" st fuel asm_idx PHOAS_idx
               | inr asm_idxs, inr PHOAS_idxs
                 => ([prefix ++ " " ++ @show_list _ show_expr_node_lite (List.map ExprRef asm_idxs) ++ " ≠ " ++ @show_list _ show_expr_node_lite (List.map ExprRef PHOAS_idxs)]%string)
                      ++ (explain_array_unification_error
                            first_new_idx_after_all_old_idxs st "array" "arrays" "assembly" "synthesized" (explain_idx_unification_error first_new_idx_after_all_old_idxs "assembly" "synthesized" st fuel) (describe_idx_from_state false st) None
                            asm_idxs PHOAS_idxs)
               end%list
     end%string%list.

Global Instance show_lines_EquivalenceCheckingError : ShowLines EquivalenceCheckingError
  := fun err => match err with
                | Symbolic_execution_failed l r
                  => ["In combined state:"]
                       ++ show_lines r ++ ["Symbolic execution failed:"] ++ show_lines l
                       ++ match l with
                          | error.load idx s
                          | error.store idx _ s
                          | error.remove idx s
                          | error.remove_has_duplicates idx _ s
                            => describe_full_idx_from_state s idx
                          | _ => []
                          end
                | Internal_error_lingering_memory s
                  => ["In combined state:"] ++ show_lines s ++ ["Some memory remained after all known memory was removed: " ++ show s.(symbolic_mem_state)]%string
                | Internal_error_output_load_failed err l r => ["In combined state:"] ++ show_lines r ++ ["Internal error. Output load failed: " ++ show l ++ match err with Some err => "(" ++ show err ++ ")" | None => "" end]%string
                | Internal_error_extra_input_arguments t unused_arguments
                  => ["Internal error. Too many input arguments for type " ++ show t ++ ". Unused arguments: " ++ show unused_arguments]%string
                | Internal_error_LoadOutputs_length_mismatch l1 l2
                  => ["Internal error. Length mismatch for " ++ show l1 ++ " and " ++ show l2 ++ "."; show (List.length l1) ++ " ≠ " ++ show (List.length l2)]%string
                | Not_enough_registers num_given num_extra_needed
                  => ["Not enough registers available for storing input and output (given " ++ show num_given ++ ", needed an additional " ++ show num_extra_needed ++ "."]%string
                | Registers_too_narrow regs
                  => ["Some registers given were more narrow than 64 bits: " ++ String.concat ", " (List.map (fun r => show r ++ " (width: " ++ show (reg_size r) ++ ")") regs)]%string
                | Callee_saved_registers_too_narrow regs
                  => ["Some callee-saved / non-volatile registers given were more narrow than 64 bits: " ++ String.concat ", " (List.map (fun r => show r ++ " (width: " ++ show (reg_size r) ++ ")") regs)]%string
                | Duplicate_registers regs
                  => ["List of registers contains duplicates: " ++ String.concat ", " (List.map show regs)]%string
                | Incorrect_array_input_dag_node
                  => ["Internal error: Input dag node had an unexpected array."]
                | Incorrect_Z_input_dag_node
                  => ["Internal error: Input dag node had an unexpected Z."]
                | Not_enough_input_dag_nodes t
                  => ["Internal error: Not enough input dag nodes to allocate for type " ++ show t ++ "."]%string
                | Expected_const_in_reference_code i => ["Expected N const in reference code for dag node " ++ show i]%string
                | Expected_power_of_two w i => ["Expected power of 2, got " ++ show w ++ " (index " ++ show i ++ ")"]%string
                | Invalid_argument_type t
                  => ["Invalid type for argument: " ++ show t]%string
                | Invalid_return_type t
                  => ["Invalid type for return: " ++ show t]%string
                | Unknown_array_length t => ["Unknown array length of type " ++ show t ++ "."]%string
                | Invalid_arrow_type t => ["Invalid higher order function involving the type " ++ show t ++ "."]%string
                | Invalid_higher_order_application var s d f x
                  => let __ := @Compilers.ToString.PHOAS.expr.partially_show_expr in
                     ["Invalid higher-order application node with argument of type " ++ show s ++ ":"
                      ; "Function expression: " ++ show f
                      ; "Argument expression: " ++ show x]%string
                | Invalid_higher_order_let var s x
                  => let __ := @Compilers.ToString.PHOAS.expr.partially_show_expr in
                     ["Invalid higher-order let-in node with argument of type " ++ show s ++ ":"
                      ; "Let-bound expression: " ++ show x]%string
                | Unhandled_identifier t idc
                  => ["Identifier not yet handled by symbolic evaluation: " ++ show idc ++ "."]%string
                | Unhandled_cast l u
                  => ["Argument not yet handled by symbolic evaluation: " ++ show (l, u)]%string
                | Registers_not_saved regs r
                  => let reg_before := List.map (fun '(r, (idx_before, idx_after)) => idx_before) regs in
                     let reg_after := List.map (fun '(r, (idx_before, idx_after)) => idx_after) regs in
                     let regs := List.map (fun '(r, (idx_before, idx_after)) => r) regs in
                     (["Unable to establish that callee-saved non-volatile registers were preserved: " ++ String.concat ", " (List.map show regs); "In environment:"]%string)
                       ++ show_lines r
                       ++ ["Unable to establish that callee-saved non-volatile registers were preserved: " ++ String.concat ", " (List.map show regs); "Unable to unify: " ++ show reg_before ++ " == " ++ show reg_after]%string
                       ++ (let first_new_idx_after_all_old_idxs := None in  (* dummy, since we don't know the value here, and it's hard to pipe the info through, and it's not super-important *)
                           explain_array_unification_error
                             first_new_idx_after_all_old_idxs r "list" "lists" "original" "final" (explain_idx_unification_error first_new_idx_after_all_old_idxs "original" "final" r (explain_unification_default_fuel r)) (describe_idx_from_state false r) None
                             reg_before reg_after)
                | Unable_to_unify asm_output PHOAS_output first_new_idx_after_all_old_idxs r
                  => ["Unable to unify:"; "In environment:"]
                       ++ show_lines r
                       ++ ["Unable to unify: " ++ show asm_output ++ " == " ++ show PHOAS_output]%string
                       ++ explain_unification_error asm_output PHOAS_output first_new_idx_after_all_old_idxs 0 r
                | Missing_ret
                  => ["Missing 'ret' at the end of the function"]
                | Code_after_ret significant l
                  => ["Code after ret:"; "In:"] ++ show_lines l ++ ["Found instructions after ret:"] ++ show_lines significant
                end%list.
Global Instance show_EquivalenceCheckingError : Show EquivalenceCheckingError
  := fun err => String.concat String.NewLine (show_lines err).

Definition merge_fresh_symbol {descr:description} : dag.M idx := fun d => merge_node (dag.gensym 64%N d) d.
Definition merge_literal {descr:description} (l:Z) : dag.M idx := merge_node ((const l, nil)).

Definition SetRegFresh {descr:description} (r : REG) : M idx :=
  (idx <- lift_dag merge_fresh_symbol;
  _ <- SetReg r idx;
  Symbolic.ret idx).

(** symbolic evaluations live in the state monad, pushed to the leaves of a PHOAS type *)
Definition symexM T := dag -> ErrorT EquivalenceCheckingError (T * dag).
Definition symex_return {T} (v : T) : symexM T := fun st => Success (v, st).
Definition symex_error {T} err : symexM T := fun st => Error err.
Definition symex_bind {A B} (v : symexM A) (f : A -> symexM B) : symexM B
  := fun st => (v <- v st; let '(a, st) := v in f a st)%error.
Declare Scope symex_scope.
Delimit Scope symex_scope with symex.
Bind Scope symex_scope with symexM.
Notation "'slet' x .. y <- X ; B"  := (symex_bind X (fun x => .. (fun y => B%symex) .. )) : symex_scope.
Notation "A <- X ; B" := (symex_bind X (fun A => B%symex)) : symex_scope.
(* light alias *)
Definition App {descr:description} (e : Symbolic.node idx) : symexM idx := fun st => Success (merge (simplify st e) st).
Definition RevealConstant (i : idx) : symexM N := fun st =>
  match reveal st 1 i with
  | ExprApp (const n, nil) =>
      if Z.leb 0 n then Success (Z.to_N n, st) else Error (Expected_const_in_reference_code i)
  | _ => Error (Expected_const_in_reference_code i)
  end.
Definition RevealWidth (i : idx) : symexM N :=
  s <- RevealConstant i;
  let w := N.log2 s in
  if N.eqb s (N.pow 2 w)
  then symex_return w
  else symex_error (Expected_power_of_two s i).

Definition type_spec := list (option nat). (* list of array lengths; None means not an array *)

(** Convert PHOAS info about types and argument bounds into a simplified specification *)
Fixpoint simplify_base_type
         (t : base.type)
  : forall arg_bounds : ZRange.type.base.option.interp t, ErrorT EquivalenceCheckingError type_spec
  := match t return ZRange.type.base.option.interp t -> _ with
     | base.type.unit
       => fun 'tt => Success []
     | base.type.type_base base.type.Z
       => fun _ => Success [None]
     | base.type.prod A B
       => fun '(bA, bB)
          => (vA <- simplify_base_type A bA;
             vB <- simplify_base_type B bB;
             Success (vA ++ vB))
     | base.type.list (base.type.type_base base.type.Z)
       => fun b
          => match b with
             | None => Error (Unknown_array_length t)
             | Some bs => Success [Some (List.length bs)]
             end
     | base.type.type_base _
     | base.type.option _
     | base.type.list _
       => fun _ => Error (Invalid_argument_type (type.base t))
     end%error.
Definition simplify_type
         (t : API.type)
  : forall arg_bounds : ZRange.type.option.interp t, ErrorT EquivalenceCheckingError type_spec
  := match t with
     | type.base t => simplify_base_type t
     | type.arrow _ _ => fun _ => Error (Invalid_argument_type t)
     end.
Fixpoint simplify_input_type
         (t : API.type)
  : forall arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t, ErrorT EquivalenceCheckingError type_spec
  := match t return type.for_each_lhs_of_arrow ZRange.type.option.interp t -> _ with
     | type.base _ => fun 'tt => Success []
     | type.arrow A B
       => fun '(bA, bB)
          => (vA <- simplify_type A bA;
             vB <- simplify_input_type B bB;
             Success (vA ++ vB))
     end%error.

Definition build_inputarray {descr:description} (len : nat) : dag.M (list idx) :=
  List.foldmap (fun _ => merge_fresh_symbol) (List.seq 0 len).

Fixpoint build_inputs {descr:description} (types : type_spec) : dag.M (list (idx + list idx))
  := match types with
     | [] => dag.ret []
     | None :: tys
       => (idx <- merge_fresh_symbol;
           rest <- build_inputs tys;
           dag.ret (inl idx :: rest))
     | Some len :: tys
       => (idxs <- build_inputarray len;
           rest <- build_inputs tys;
           dag.ret (inr idxs :: rest))
     end%dagM.

(* we factor this out so that conversion is not slow when proving things about this *)
Definition compute_array_address {descr:description} (base : idx) (i : nat)
  := (offset <- Symbolic.App (zconst 64%N (8 * Z.of_nat i), nil);
      Symbolic.App (add 64%N, [base; offset]))%x86symex.

Definition build_merge_array_addresses {descr:description} (base : idx) (items : list idx) : M (list idx)
  := mapM (fun '(i, idx) =>
             (addr <- compute_array_address base i;
              (fun s => Success (addr, update_mem_with s (cons (addr,idx)))))
          )%x86symex (List.enumerate items).

Fixpoint build_merge_base_addresses {descr:description} {dereference_scalar:bool} (items : list (idx + list idx)) (reg_available : list REG) : M (list ((REG + idx) + idx))
  := match items, reg_available with
     | [], _ | _, [] => Symbolic.ret []
     | inr idxs :: xs, r :: reg_available
       => (base <- SetRegFresh r; (* note: overwrites initial value *)
           addrs <- build_merge_array_addresses base idxs; (* note: overwrites initial value *)
           rest <- build_merge_base_addresses (dereference_scalar:=dereference_scalar) xs reg_available;
           Symbolic.ret (inr base :: rest))
     | inl idx :: xs, r :: reg_available =>
          (addr <- (if dereference_scalar
                    then
                      (addr <- SetRegFresh r;
                       fun s => Success (inr addr, update_mem_with s (cons (addr, idx))))
                    else
                      (_ <- SetReg r idx; (* note: overwrites initial value *)
                       ret (inl r)));
           rest <- build_merge_base_addresses (dereference_scalar:=dereference_scalar) xs reg_available;
           Symbolic.ret (inl addr :: rest))
     end%N%x86symex.

Fixpoint dag_gensym_n {descr:description} (n : nat) : dag.M (list symbol) :=
  match n with
  | O => dag.ret nil
  | S n =>
      (i <- merge_fresh_symbol;
       rest <- dag_gensym_n n;
       dag.ret (cons i rest))
  end%dagM.

(** PHOAS var type, storing dag indices or nat literals *)
Fixpoint base_var (t : base.type) : Set
  := match t with
     | base.type.unit
       => unit
     | base.type.type_base base.type.Z => idx
     | base.type.prod A B => base_var A * base_var B
     | base.type.list A => list (base_var A)
     | base.type.type_base base.type.nat => nat
     | base.type.type_base base.type.zrange => ZRange.zrange
     | base.type.type_base _
     | base.type.option _
       => Empty_set (* should not happen *)
     end.
Definition var (t : API.type) : Set
  := match t with
     | type.base t => base_var t
     | type.arrow s d => Empty_set
     end.

(* true iff simplify_base_var (and all other things that process input and output types) can succeed *)
Fixpoint check_base_type_ok (t : base.type) : bool
  := match t with
     | base.type.unit => true
     | base.type.type_base base.type.Z => true
     | base.type.prod A B => check_base_type_ok A && check_base_type_ok B
     | base.type.list (base.type.type_base base.type.Z) => true
     | base.type.list _
     | base.type.type_base _
     | base.type.option _
       => false
     end.
Class base_type_ok t : Prop := base_type_is_ok : check_base_type_ok t = true.
Global Hint Extern 1 (base_type_ok ?t) => abstract vm_cast_no_check (eq_refl true) : typeclass_instances.
Definition check_argument_type_ok (t : API.type) : bool
  := match t with
     | type.base t => check_base_type_ok t
     | type.arrow _ _ => false
     end.
Class argument_type_ok t : Prop := argument_type_is_ok : check_argument_type_ok t = true.
Global Hint Extern 1 (argument_type_ok ?t) => abstract vm_cast_no_check (eq_refl true) : typeclass_instances.
Class type_ok (t : API.type) : Prop
  := type_is_ok : (type.andb_each_lhs_of_arrow check_argument_type_ok t && check_base_type_ok (type.final_codomain t))%bool = true.
Global Hint Extern 1 (type_ok ?t) => abstract vm_cast_no_check (eq_refl true) : typeclass_instances.

Fixpoint simplify_base_var {t : base.type} : base_var t -> ErrorT EquivalenceCheckingError (list (idx + list idx))
  := match t return base_var t -> ErrorT EquivalenceCheckingError (list (idx + list idx)) with
     | base.type.unit
       => fun 'tt => Success []
     | base.type.type_base base.type.Z => fun idx => Success [inl idx]
     | base.type.prod A B => fun ab => (a <- simplify_base_var (fst ab); b <- simplify_base_var (snd ab); Success (a ++ b))
     | base.type.list (base.type.type_base base.type.Z)
       => fun ls : list idx => Success [inr ls]
     | base.type.list _
     | base.type.type_base _
     | base.type.option _
       => fun _ => Error (Invalid_return_type t)
     end%error.

Fixpoint base_var_beq {t : base.type} : base_var t -> base_var t -> bool :=
  match t return base_var t -> base_var t -> bool with
  | base.type.unit => fun _ _ => true
  | base.type.type_base base.type.Z => N.eqb
  | base.type.prod _ _ => fun a b => base_var_beq (fst a) (fst b) && base_var_beq (snd a) (snd b)
  | base.type.list _ => @list_beq _ base_var_beq
  | base.type.type_base base.type.nat => Nat.eqb
  | base.type.type_base base.type.zrange => ZRange.zrange_beq
  | _ => fun _ _ => false
  end%bool.

Fixpoint show_base_var {t : base.type} : Show (base_var t) :=
  match t return base_var t -> string with
  | base.type.unit => @show unit _
  | base.type.type_base base.type.Z => @show N _
  | base.type.prod _ _ => @show_prod _ _ show_base_var show_base_var
  | base.type.list _ => @show_list _ show_base_var
  | base.type.type_base base.type.nat => @show nat _
  | base.type.type_base base.type.zrange => @show ZRange.zrange _
  | _ => fun _ => "..."
  end.
Global Existing Instance show_base_var.

(** From the information about dag nodes for inputs, build up the var
    data we're passing into PHOAS, and return as well the indices that
    we've not consumed *)
Fixpoint build_base_var (t : base.type) (indices : list (idx + list idx))
  : ErrorT EquivalenceCheckingError (base_var t * list (idx + list idx))
  := match t, indices return ErrorT _ (base_var t * list (idx + list idx)) with
     | base.type.unit, _
       => Success (tt, indices)
     | base.type.type_base base.type.Z, inl idx :: indices
       => Success (idx, indices)
     | base.type.prod A B, _
       => (vA <- build_base_var A indices;
          let '(vA, indices) := vA in
          vB <- build_base_var B indices;
          let '(vB, indices) := vB in
          Success ((vA, vB), indices))
     | base.type.list (base.type.type_base base.type.Z), inr idxs :: indices
       => Success (idxs, indices)
     | base.type.type_base base.type.Z, inr _ :: _
       => Error Incorrect_array_input_dag_node
     | base.type.list (base.type.type_base base.type.Z), inl _ :: _
       => Error Incorrect_Z_input_dag_node
     | base.type.type_base _, []
     | base.type.list _, []
       => Error (Not_enough_input_dag_nodes (type.base t))
     | base.type.type_base _, _
     | base.type.option _, _
     | base.type.list _, _ :: _
       => Error (Invalid_argument_type (type.base t))
     end%error.
Definition build_var (t : API.type) (indices : list (idx + list idx))
  : ErrorT EquivalenceCheckingError (var t * list (idx + list idx))
  := match t with
     | type.base t => build_base_var t indices
     | type.arrow _ _ => Error (Invalid_argument_type t)
     end.
Fixpoint build_input_var (t : API.type) (indices : list (idx + list idx))
  : ErrorT EquivalenceCheckingError (type.for_each_lhs_of_arrow var t * list (idx + list idx))
  := match t with
     | type.base _ => Success (tt, indices)
     | type.arrow A B
       => (vA <- build_var A indices;
          let '(vA, indices) := vA in
          vB <- build_input_var B indices;
          let '(vB, indices) := vB in
          Success ((vA, vB), indices))
     end%error.

(** Symbolic evaluation does not support higher-order functions *)
Fixpoint symex_T (t : API.type) : Type
  := match t with
     | type.base t => symexM (base_var t)
     | type.arrow s d => var s -> symex_T d
     end.
Definition symex_T_return {t : API.type} : var t -> symex_T t
  := match t return var t -> symex_T t with
     | type.base t => symex_return
     | type.arrow s d
       => fun f : Empty_set => match f with end
     end.
Fixpoint symex_T_error {t} err : symex_T t
  := match t return symex_T t with
     | type.base t => symex_error err
     | type.arrow s d => fun _ => @symex_T_error d err
     end.
Fixpoint symex_T_bind_base {T t} : symexM T -> (T -> symex_T t) -> symex_T t
  := match t with
     | type.base _ => symex_bind
     | type.arrow s d
       => fun v f x => @symex_T_bind_base T d v (fun w => f w x)
     end.
Fixpoint symex_T_app_curried {t : API.type} : symex_T t -> type.for_each_lhs_of_arrow var t -> symexM (base_var (type.final_codomain t))
  := match t with
     | type.base t => fun f 'tt => f
     | type.arrow s d => fun f '(x, xs) => @symex_T_app_curried d (f x) xs
     end.

Bind Scope symex_scope with symex_T.

Definition symex_ident {descr:description} {t} (idc : ident t) : symex_T t.
Proof.
  refine (let symex_mod_zrange idx '(ZRange.Build_zrange l u) :=
            let u := Z.succ u in
            let lu := Z.log2 u in
            if (Z.eqb l 0 && Z.eqb u (2^lu))%bool
            then
              App (((slice 0 (Z.to_N lu)), [idx]))
            else symex_error (Unhandled_cast l u)
          in
          match idc in ident t return symex_T t with
          | ident.Literal base.type.Z v
            => App (const v, nil)
          | ident.Z_add => fun x y => App (addZ, [x; y])

          | ident.Z_modulo
            => symex_T_error (Unhandled_identifier idc)
          | ident.Z_mul => fun x y => App (mulZ, [x; y])
          | ident.Z_pow
            => symex_T_error (Unhandled_identifier idc)
          | ident.Z_sub => fun x y => y' <- App (negZ, [y]); App (addZ, [x;y'])
          | ident.Z_opp
          | ident.Z_div
          | ident.Z_log2
          | ident.Z_log2_up
          | ident.Z_to_nat
            => symex_T_error (Unhandled_identifier idc)
          | ident.Z_shiftr => fun x y => App (shrZ, [x; y])
          | ident.Z_shiftl => fun x y => App (shlZ, [x; y])
          | ident.Z_land => fun x y => App (andZ, [x; y])
          | ident.Z_lor => fun x y => App (orZ, [x; y])
          | ident.Z_min
          | ident.Z_max
            => symex_T_error (Unhandled_identifier idc)
          | ident.Z_mul_split => fun bs x y =>
            vs <- RevealWidth bs; s <- App (const (Z.of_N vs), nil);
            v <- App (mulZ, [x; y]);
            lo <- App (slice 0 vs, [v]);
            hi <- App (shrZ, [v; s]);
            symex_return (lo, hi)
          | ident.Z_mul_high => fun bs x y =>
            vs <- RevealWidth bs; s <- App (const (Z.of_N vs), nil);
            v <- App (mulZ, [x; y]);
            App (shrZ, [v; s])
          | ident.Z_add_get_carry => fun s x y =>
            s <- RevealWidth s;
            a <- App (add s, [x; y]);
            c <- App (addcarryZ s, [x; y]);
            symex_return (a, c)
          | ident.Z_add_with_carry => fun x y z => App (addZ, [x; y; z])
          | ident.Z_add_with_get_carry => fun s x y z =>
            s <- RevealWidth s;
            a <- App (add s, [x; y; z]);
            c <- App (addcarryZ s, [x; y; z]);
            symex_return (a, c)
          | ident.Z_sub_get_borrow => fun s x y =>
            s <- RevealWidth s;
            y' <- App (neg s, [y]);
            a <- App (add         s, [x;y']);
            c <- App (subborrowZ s, [x;y]);
            symex_return (a, c)
          | ident.Z_sub_with_get_borrow => fun s z x y =>
            s <- RevealWidth s;
            y' <- App (neg s, [y]);
            z' <- App (neg s, [z]);
            a <- App (add s, [x;y';z']);
            c <- App (subborrowZ s, [x;y;z]);
            symex_return (a, c)
          | ident.Z_ltz
            => symex_T_error (Unhandled_identifier idc)
          | ident.Z_zselect => fun c x y => App (Symbolic.selectznz, [c; x; y])
          | ident.Z_add_modulo
            => symex_T_error (Unhandled_identifier idc)
          | ident.Z_truncating_shiftl => fun s x y =>
            s <- RevealConstant s;
            App (shl s, [x; y])
          | ident.Z_bneg
          | ident.Z_lnot_modulo
          | ident.Z_lxor
          | ident.Z_rshi
          | ident.Z_cc_m
          | ident.Z_combine_at_bitwidth
            => symex_T_error (Unhandled_identifier idc)

          | ident.comment _
          | ident.comment_no_keep _
            => fun _ => symex_return tt
          | ident.value_barrier
            => fun v => symex_return v
          | ident.tt
            => symex_return tt
          | ident.Literal base.type.bool _ as idc
          | ident.Literal base.type.string _ as idc
          | ident.None _ as idc
          | ident.Some _ as idc
            => symex_T_error (Unhandled_identifier idc)
          | ident.Literal base.type.zrange v
          | ident.Literal base.type.nat v
            => symex_return v
          | ident.pair _ _
            => fun a b => symex_return (a, b)
          | ident.fst _ _
            => fun a => symex_return (fst a)
          | ident.snd _ _
            => fun a => symex_return (snd a)
          | ident.nil _
            => symex_return []
          | ident.cons _
            => fun x xs => symex_return (x :: xs)
          | ident.Nat_succ as idc
          | ident.Nat_pred as idc
            => fun v => symex_return (ident.interp idc v)
          | ident.Nat_max as idc
          | ident.Nat_mul as idc
          | ident.Nat_add as idc
          | ident.Nat_sub as idc
          | ident.List_seq as idc
            => fun a b => symex_return (ident.interp idc a b)
          | ident.List_nth_default _
          | ident.eager_List_nth_default _
            => fun default ls n => symex_return (List.nth_default default ls n)
          | ident.List_length _
            => fun ls => symex_return (List.length ls)
          | ident.List_firstn _
            => fun n ls => symex_return (List.firstn n ls)
          | ident.List_skipn _
            => fun n ls => symex_return (List.skipn n ls)
          | ident.List_repeat _
            => fun v n => symex_return (List.repeat v n)
          | ident.List_combine _ _
            => fun ls1 ls2 => symex_return (List.combine ls1 ls2)
          | ident.List_app _
            => fun ls1 ls2 => symex_return (List.app ls1 ls2)
          | ident.List_rev _
            => fun ls => symex_return (List.rev ls)
          | ident.Build_zrange (* do we need to handle this? *)
            => fun l r => symex_error (Unhandled_identifier idc)
          (* we should handle these the same way that we handle truncation/modulo *)
          | ident.Z_cast
            => fun r v_idx => idx <- symex_mod_zrange v_idx r; symex_return idx
          | ident.Z_cast2
            => fun '(r1, r2) '(v1_idx, v2_idx)
               => idx1 <- symex_mod_zrange v1_idx r1;
                  idx2 <- symex_mod_zrange v2_idx r2;
                  symex_return (idx1, idx2)
          | ident.Z_of_nat
            => fun n => App (const (Z.of_nat n), nil)

          | ident.Z_eqb
          | ident.Z_leb
          | ident.Z_ltb
          | ident.Z_geb
          | ident.Z_gtb

          | ident.Nat_eqb
          | ident.prod_rect _ _ _
          | ident.bool_rect _
          | ident.bool_rect_nodep _
          | ident.nat_rect _
          | ident.eager_nat_rect _
          | ident.nat_rect_arrow _ _
          | ident.eager_nat_rect_arrow _ _
          | ident.list_rect _ _
          | ident.eager_list_rect _ _
          | ident.list_rect_arrow _ _ _
          | ident.eager_list_rect_arrow _ _ _
          | ident.list_case _ _
          | ident.List_map _ _
          | ident.List_flat_map _ _
          | ident.List_partition _
          | ident.List_fold_right _ _
          | ident.List_update_nth _
          | ident.option_rect _ _
          | ident.zrange_rect _
          | ident.fancy_add
          | ident.fancy_addc
          | ident.fancy_sub
          | ident.fancy_subb
          | ident.fancy_mulll
          | ident.fancy_mullh
          | ident.fancy_mulhl
          | ident.fancy_mulhh
          | ident.fancy_rshi
          | ident.fancy_selc
          | ident.fancy_selm
          | ident.fancy_sell
          | ident.fancy_addm
            => symex_T_error (Unhandled_identifier idc)
          end%symex).
  all: cbn in *.
Defined.

Fixpoint symex_expr {descr:description} {t} (e : API.expr (var:=var) t) : symex_T t
  := let _ := @Compilers.ToString.PHOAS.expr.partially_show_expr in
     match e in expr.expr t return symex_T t with
     | expr.Ident _ idc => symex_ident idc
     | expr.Var _ v => symex_T_return v
     | expr.Abs (type.base _) _ f => fun v => symex_expr (f v)
     | expr.App (type.base _) _ f x
       => let ef := symex_expr f in
          let ex := symex_expr x in
          symex_T_bind_base ex ef
     | expr.LetIn (type.base _) _ x f
       => let ef v := symex_expr (f v) in
          let ex := symex_expr (descr:=Build_description (show x) false) x in
          symex_T_bind_base ex ef
     | expr.App (type.arrow _ _) _ f x
       => symex_T_error (Invalid_higher_order_application f x)
     | expr.LetIn (type.arrow _ _) _ x f
       => symex_T_error (Invalid_higher_order_let x)
     | expr.Abs (type.arrow _ _) _ _
       => fun v : Empty_set => match v with end
     end.

(* takes and returns PHOAS-style things *)
Definition symex_PHOAS_PHOAS {t} (expr : API.Expr t) (input_var_data : type.for_each_lhs_of_arrow _ t) (d : dag)
  : ErrorT EquivalenceCheckingError (base_var (type.final_codomain t) * dag)
  := let ast : API.expr (type.base (type.final_codomain t))
         := invert_expr.smart_App_curried (expr _) input_var_data in
     symex_expr (descr:=no_description) ast d.

(* takes and returns assembly/list style things *)
Definition symex_PHOAS
           {t} (expr : API.Expr t)
           (inputs : list (idx + list idx))
           (d : dag)
  : ErrorT EquivalenceCheckingError (list (idx + list idx) * dag)
  := (input_var_data <- build_input_var t inputs;
     let '(input_var_data, unused_inputs) := input_var_data in
     _ <- (if (List.length unused_inputs =? 0)%nat
           then Success tt
           else Error (Internal_error_extra_input_arguments t unused_inputs));
     symevaled_PHOAS <- symex_PHOAS_PHOAS expr input_var_data d;
     let '(PHOAS_output, d) := symevaled_PHOAS in
     PHOAS_output <- simplify_base_var PHOAS_output;
     Success (PHOAS_output, d)).

Definition init_symbolic_state_descr : description := Build_description "init_symbolic_state" true.

Definition init_symbolic_state (d : dag) : symbolic_state
  := let _ := init_symbolic_state_descr in
     let '(initial_reg_idxs, d) := dag_gensym_n 16 d in
     {|
       dag_state := d;
       symbolic_reg_state := Tuple.from_list_default None 16 (List.map Some initial_reg_idxs);
       symbolic_mem_state := [];
       symbolic_flag_state := Tuple.repeat None 6;
     |}.

Definition compute_stack_base {descr:description} (stack_size : nat) : M idx
  := (rsp_val <- SetRegFresh rsp;
      stack_size <- Symbolic.App (zconst 64 (-8 * Z.of_nat stack_size), []);
      Symbolic.App (add 64%N, [rsp_val; stack_size]))%x86symex.

Definition build_merge_stack_placeholders {descr:description} (stack_size : nat)
  : M idx
  := (stack_placeholders <- lift_dag (build_inputarray stack_size);
      stack_base <- compute_stack_base stack_size;
      _ <- build_merge_array_addresses stack_base stack_placeholders;
      ret stack_base)%x86symex.

Definition LoadArray {descr:description} (base : idx) (len : nat) : M (list idx)
  := mapM (fun i =>
             (addr <- compute_array_address base i;
              Remove64 addr)%x86symex)
          (seq 0 len).

Definition LoadOutputs_internal {descr:description} {dereference_scalar:bool} (outputaddrs : list ((REG + idx) + idx)) (output_types : type_spec)
  : M (list (idx + list idx))
  := (mapM (fun '(ocells, spec) =>
            match ocells, spec with
            | inl _, Some _ | inr _, None => err (error.unsupported_memory_access_size 0)
            | inl addr, None
              => (v <- match addr, dereference_scalar with
                       | inl r, false
                         => GetReg r
                       | inr addr, true
                         => Remove64 addr
                       | inl _, true | inr _, false => err (error.unsupported_memory_access_size 0)
                       end;
                  ret (inl v))
            | inr base, Some len
              => (v <- LoadArray base len;
                  ret (inr v))
            end) (List.combine outputaddrs output_types))%N%x86symex.

Definition LoadOutputs {descr:description} {dereference_scalar:bool} (outputaddrs : list ((REG + idx) + idx)) (output_types : type_spec)
  : M (ErrorT EquivalenceCheckingError (list (idx + list idx)))
  := (* In the following line, we match on the result so we can emit Internal_error_output_load_failed in the calling function, rather than passing through the placeholder error from LoadOutputs *)
  fun s => if (List.length outputaddrs =? List.length output_types)%nat
           then match LoadOutputs_internal (dereference_scalar:=dereference_scalar) outputaddrs output_types s with
                | Success (v, s) => Success (Success v, s)
                | Error (err, s)
                  => Success (Error (Internal_error_output_load_failed
                                       match err with
                                       | error.unsupported_memory_access_size 0%N => None (* placeholder *)
                                       | _ => Some err
                                       end
                                       outputaddrs s), s)
                end
           else
             Success (Error (Internal_error_LoadOutputs_length_mismatch outputaddrs output_types), s).

Definition symex_asm_func_M
           (dereference_input_scalars:=false)
           {dereference_output_scalars:bool}
           (callee_saved_registers : list REG)
           (output_types : type_spec) (stack_size : nat)
           (inputs : list (idx + list idx)) (reg_available : list REG) (asm : Lines)
  : M (ErrorT EquivalenceCheckingError (list (idx + list idx)))
  := (output_placeholders <- lift_dag (build_inputs (descr:=Build_description "output_placeholders" true) output_types);
      let n_outputs := List.length output_placeholders in
      (* to make proofs easier, we merge addresses in reverse order from reading them *)
      inputaddrs <- build_merge_base_addresses (descr:=Build_description "inputaddrs" true) (dereference_scalar:=dereference_input_scalars) inputs (skipn n_outputs reg_available);
      outputaddrs <- build_merge_base_addresses (descr:=Build_description "outputaddrs" true) (dereference_scalar:=dereference_output_scalars) output_placeholders (firstn n_outputs reg_available);
      stack_base <- build_merge_stack_placeholders (descr:=Build_description "stack_base" true) stack_size;
      initial_register_values <- mapM (GetReg (descr:=Build_description "initial_register_values" true)) callee_saved_registers;
      _ <- SymexLines asm;
      final_register_values <- mapM (GetReg (descr:=Build_description "final_register_values" true)) callee_saved_registers;
      _ <- LoadArray (descr:=Build_description "load final stack" true) stack_base stack_size;
      let unsaved_registers : list (REG * (idx * idx)) := List.filter (fun '(r, (init, final)) => negb (init =? final)%N) (List.combine callee_saved_registers (List.combine initial_register_values final_register_values)) in
      asm_output <- LoadOutputs (descr:=Build_description "asm_output" true) (dereference_scalar:=dereference_output_scalars) outputaddrs output_types;
      (* also load inputs, for the sake of the proof *)
      (* reconstruct input types *)
      let input_types := List.map (fun v => match v with inl _ => None | inr ls => Some (List.length ls) end) inputs in
      asm_input <- LoadOutputs (descr:=Build_description "asm_input <- LoadOutputs" true) (dereference_scalar:=dereference_input_scalars) inputaddrs input_types;
      (fun s => Success
                  (match asm_output, asm_input, unsaved_registers, s.(symbolic_mem_state) with
                   | Success asm_output, Success _, [], []
                     => Success asm_output
                   | Error err, _, _, _
                   | _, Error err, _, _
                     => Error err
                   | Success _, Success _, (_ :: _) as unsaved_registers, _
                     => Error (Registers_not_saved unsaved_registers s)
                   | Success _, Success _, _, (_ :: _) as mem_remaining
                     => Error (Internal_error_lingering_memory s)
                   end,
                    s)))%N%x86symex.

Definition symex_asm_func
           {dereference_output_scalars:bool}
           (d : dag) (callee_saved_registers : list REG) (output_types : type_spec) (stack_size : nat)
           (inputs : list (idx + list idx)) (reg_available : list REG) (asm : Lines)
  : ErrorT EquivalenceCheckingError (list (idx + list idx) * symbolic_state)
  := let num_reg_given := List.length reg_available in
     let num_reg_needed := List.length inputs + List.length output_types in
     if (num_reg_given <? num_reg_needed)%nat
     then
       Error (Not_enough_registers num_reg_given num_reg_needed)
     else
       let register_wide_enough := fun reg => (reg_size reg =? 64)%N in
       if negb (forallb register_wide_enough reg_available)
       then
         Error (Registers_too_narrow (filter (fun reg => negb (register_wide_enough reg)) reg_available))
       else
         if negb (forallb register_wide_enough callee_saved_registers)
         then
           Error (Callee_saved_registers_too_narrow (filter (fun reg => negb (register_wide_enough reg)) callee_saved_registers))
         else
           if negb (list_beq _ REG_beq (remove_duplicates REG_beq reg_available) reg_available)
           then
             Error (Duplicate_registers (find_duplicates REG_beq reg_available))
           else
             match symex_asm_func_M (dereference_output_scalars:=dereference_output_scalars) callee_saved_registers output_types stack_size inputs reg_available asm (init_symbolic_state d) with
             | Error (e, s)                    => Error (Symbolic_execution_failed e s)
             | Success (Error err, s)          => Error err
             | Success (Success asm_output, s) => Success (asm_output, s)
             end.

Section check_equivalence.
  Context {assembly_calling_registers' : assembly_calling_registers_opt}
          {assembly_stack_size' : assembly_stack_size_opt}
          {assembly_output_first : assembly_output_first_opt}
          {assembly_argument_registers_left_to_right : assembly_argument_registers_left_to_right_opt}
          {assembly_callee_saved_registers' : assembly_callee_saved_registers_opt}.

  Section with_expr.
    Context {t}
            (asm : list (string (* fname *) * Lines))
            (expr : API.Expr t)
            (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
            (out_bounds : ZRange.type.base.option.interp (type.final_codomain t)).

    Definition strip_ret (asm : Lines) :=
      let isinstr := fun l => match l.(rawline) with INSTR _ => true | _ => false end in
      let notret := fun l => match l.(rawline) with
                             | INSTR {| Syntax.op := Syntax.ret ; Syntax.args := nil |} => false
                             | _ => true
                             end in
      match dropWhile notret asm with
      | nil => Error Missing_ret
      | cons _r trailer =>
          if List.existsb isinstr trailer then Error (Code_after_ret (List.filter isinstr trailer) trailer)
          else Success (takeWhile notret asm)
      end.

    Local Notation map_err_None v := (ErrorT.map_error (fun e => (None, e)) v).
    Local Notation map_err_Some label v := (ErrorT.map_error (fun e => (Some label, e)) v).

    Definition check_equivalence : ErrorT (option (string (* fname *) * Lines (* asm lines *)) * EquivalenceCheckingError) unit :=
      let reg_available := assembly_calling_registers (* registers available for calling conventions *) in
      let d := dag.empty in
      input_types <- map_err_None (simplify_input_type t arg_bounds);
      output_types <- map_err_None (simplify_base_type (type.final_codomain t) out_bounds);
      let '(inputs, d) := build_inputs (descr:=Build_description "build_inputs" true ) input_types d in

      PHOAS_output <- map_err_None (symex_PHOAS expr inputs d);
      let '(PHOAS_output, d) := PHOAS_output in

      let first_new_idx_after_all_old_idxs : option idx := Some (dag.size d) in

      _ <-- (List.map
               (fun '((fname, asm) as label)
                => (asm <- map_err_Some label (strip_ret asm);
                    let stack_size : nat := N.to_nat (assembly_stack_size asm) in
                    symevaled_asm <- map_err_Some label (symex_asm_func (dereference_output_scalars:=false) d assembly_callee_saved_registers output_types stack_size inputs reg_available asm);
                    let '(asm_output, s) := symevaled_asm in

                    if list_beq _ (sum_beq _ _ N.eqb (list_beq _ N.eqb)) asm_output PHOAS_output
                    then Success tt
                    else Error (Some label, Unable_to_unify asm_output PHOAS_output first_new_idx_after_all_old_idxs s)))
               asm);
    Success tt.

    (** We don't actually generate assembly, we just check equivalence and pass assembly through unchanged *)
    Definition generate_assembly_of_hinted_expr : ErrorT (option (string (* fname *) * Lines (* asm lines *)) * EquivalenceCheckingError) (list (string * Lines))
      := match check_equivalence with
         | Success tt => Success asm (* the asm is equivalent, so we can emit this asm *)
         | Error err => Error err
         end.
  End with_expr.
End check_equivalence.
