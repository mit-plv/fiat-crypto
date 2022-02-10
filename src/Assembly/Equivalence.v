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
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.FoldMap.
Require Import Crypto.Util.ListUtil.FilterN.
Require Import Crypto.Util.Sum.
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
Definition default_assembly_stack_size := 0%N.
(** The stack size is taken to be the given command line argument, or
    else inferred to be the literal argument to the first [sub rsp,
    LITERAL] in the code, or else [default_assembly_stack_size] if
    none exists *)
Definition assembly_stack_size {v : assembly_stack_size_opt} (asm : _) : N
  := match v with
     | Some v => v
     | None
       => match Option.List.map
                  (fun l
                   => match l.(rawline) with
                      | INSTR {| Syntax.op := sub ; args := [reg rsp; Syntax.const n] |}
                        => Some (Z.to_N n)
                      | _ => None
                      end)
                  asm
          with
          | n :: _ => n
          | [] => default_assembly_stack_size
          end
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
| Internal_error_output_load_failed (_ : list (option idx)) (_ : symbolic_state)
| Internal_error_extra_input_arguments (t : API.type) (unused_arguments : list (idx + list idx))
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
| Unable_to_unify (_ _ : list (idx + list idx)) (_ : symbolic_state)
| Missing_ret
| Code_after_ret (significant : Lines) (l : Lines)
.

Fixpoint explain_array_unification_error
         (singular plural : string)
         (left_descr right_descr : string)
         (explain_idx_unification_error : idx -> idx -> list string)
         (describe_idx : idx -> list string)
         (asm_array PHOAS_array : list idx) (start_idx : nat)
  : list string
  := match asm_array, PHOAS_array with
     | [], []
       => ["Internal Error: Unifiable " ++ plural]
     | [], PHOAS_array
       => ((["The " ++ right_descr ++ " " ++ singular ++ " contains " ++ show (List.length PHOAS_array) ++ " more values than the " ++ left_descr ++ " " ++ singular ++ "."]%string)
             ++ List.flat_map describe_idx PHOAS_array)%list
     | asm_array, []
       => ((["The " ++ left_descr ++ " " ++ singular ++ " contains " ++ show (List.length asm_array) ++ " more values than the " ++ right_descr ++ " " ++ singular ++ "."]%string)
             ++ List.flat_map describe_idx asm_array)%list
     | asm_value :: asm_array, PHOAS_value :: PHOAS_array
       => if Decidable.dec (asm_value = PHOAS_value)
          then explain_array_unification_error singular plural left_descr right_descr explain_idx_unification_error describe_idx asm_array PHOAS_array (S start_idx)
          else ((["index " ++ show start_idx ++ ": " ++ show asm_value ++ " != " ++ show PHOAS_value]%string)
                  ++ explain_idx_unification_error asm_value PHOAS_value
               )%list
     end%string%list.

Definition describe_idx_from_state
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
     let old_descr
       := match is_old, description_from_state with
          | true, Some descr
            => [show idx ++ " is " ++ descr ++ "."]
          | true, None
            => [show idx ++ " is a special value no longer present in the symbolic machine state at the end of execution."]
          | _, _ => []
          end%string in
     old_descr.

Definition explain_mismatch_from_state
           (left_descr right_descr : string)
           (st : symbolic_state) (asm_idx PHOAS_idx : idx) : list string
  := ((describe_idx_from_state (*left_descr*) st asm_idx)
        ++ (describe_idx_from_state (*right_descr*) st PHOAS_idx))%list.

(* If the operation is commutative, we want to exclude any values that appear on both sides *)
Fixpoint minimize_array_idx_modulo_commutativity
         (asm_array PHOAS_array : list idx)
         {struct asm_array}
  : list idx * list idx
  := match asm_array with
     | [] => ([], PHOAS_array)
     | val :: vals
       => if List.existsb (N.eqb val) PHOAS_array
          then minimize_array_idx_modulo_commutativity vals (List.filtern (N.eqb val) PHOAS_array 1)
          else let '(vals, PHOAS_array) := minimize_array_idx_modulo_commutativity vals PHOAS_array in
               (val :: vals, PHOAS_array)
     end.

Fixpoint explain_idx_unification_error
         (left_descr right_descr : string)
         (st : symbolic_state) (fuel : nat) (asm_idx PHOAS_idx : idx) {struct fuel} : list string
  := let recr := match fuel with
                 | O => fun _ _ => ["Internal error: out of fuel in explain_expr_unification_error"]
                 | S fuel => explain_idx_unification_error left_descr right_descr st fuel
                 end in
     let reveal_idx idx := List.nth_error st.(dag_state) (N.to_nat idx) in
     let reveal_show_idx idx
       := match reveal_idx idx with
          | Some n => show n
          | None => show idx
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
       => (([show asm ++ " != " ++ show PHOAS]%string)
             ++ (if Decidable.dec (asm_o = PHOAS_o)
                 then
                   let '(asm_e', PHOAS_e') :=
                     if commutative asm_o
                     then minimize_array_idx_modulo_commutativity asm_e PHOAS_e
                     else (asm_e, PHOAS_e) in
                   if ((List.length asm_e' =? 0) && (List.length PHOAS_e' =? 0) && (negb ((List.length asm_e =? 0) && (List.length PHOAS_e =? 0))))%nat
                   then ["Arguments of commutative operation differ only in ordering."]
                   else explain_array_unification_error "argument" "arguments" left_descr right_descr recr (describe_idx_from_state st) asm_e' PHOAS_e' 0
                 else (([reveal_show_node asm ++ " != " ++ reveal_show_node PHOAS
                         ; "Operation mismatch: " ++ show asm_o ++ " != " ++ show PHOAS_o]%string)
                         ++ explain_mismatch_from_state left_descr right_descr st asm_idx PHOAS_idx)%list))%list
     end%string.

Definition explain_unification_default_fuel (st : symbolic_state) : nat
  := (10 + (2 * List.length st.(dag_state)))%nat (* we since the dag is acyclic, we shouldn't have to do more recursive lookups than its length; we double and add 10 for safety *).

Fixpoint explain_unification_error (asm_output PHOAS_output : list (idx + list idx)) (start_idx : nat) (st : symbolic_state)
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
          then explain_unification_error asm_output PHOAS_output (S start_idx) st
          else let prefix := ("Could not unify the values at index " ++ show start_idx ++ ":")%string in
               match asm_value, PHOAS_value with
               | inl _, inr _ => [prefix; "The assembly code returns a scalar while the synthesized code returns an array."]
               | inr _, inl _ => [prefix; "The assembly code returns an array while the synthesized code returns a scalar."]
               | inl asm_idx, inl PHOAS_idx
                 => (["index  " ++ show start_idx ++ ": " ++ show asm_idx ++ " != " ++ show PHOAS_idx]%string)
                      ++ explain_idx_unification_error "assembly" "synthesized" st fuel asm_idx PHOAS_idx
               | inr asm_idxs, inr PHOAS_idxs
                 => ([prefix ++ " " ++ show asm_idxs ++ " != " ++ show PHOAS_idxs]%string)
                      ++ (explain_array_unification_error
                            "array" "arrays" "assembly" "synthesized" (explain_idx_unification_error "assembly" "synthesized" st fuel) (describe_idx_from_state st)
                            asm_idxs PHOAS_idxs
                            0)
               end%list
     end%string%list.

Global Instance show_lines_EquivalenceCheckingError : ShowLines EquivalenceCheckingError
  := fun err => match err with
                | Symbolic_execution_failed l r
                  => ["Symbolic execution failed: " ++ show l]%string ++ ["Combined state:"] ++ show_lines r
                | Internal_error_output_load_failed l r => ["Internal error. Output load failed: " ++ show l]%string ++ ["Combined state:"] ++ show_lines r
                | Internal_error_extra_input_arguments t unused_arguments
                  => ["Internal error. Too many input arguments for type " ++ show t ++ ". Unused arguments: " ++ show unused_arguments]%string
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
                       ++ ["Unable to unify: " ++ show reg_before ++ " == " ++ show reg_after]%string
                       ++ explain_array_unification_error
                            "list" "lists" "original" "final" (explain_idx_unification_error "original" "final" r (explain_unification_default_fuel r)) (describe_idx_from_state r)
                            reg_before reg_after
                            0
                | Unable_to_unify asm_output PHOAS_output r
                  => ["Unable to unify:"; "In environment:"]
                       ++ show_lines r
                       ++ ["Unable to unify: " ++ show asm_output ++ " == " ++ show PHOAS_output]%string
                       ++ explain_unification_error asm_output PHOAS_output 0 r
                | Missing_ret
                  => ["Missing 'ret' at the end of the function"]
                | Code_after_ret significant l
                  => ["Code after ret:"; "In:"] ++ show_lines l ++ ["Found instructions:"] ++ show_lines significant
                end%list.
Global Instance show_EquivalenceCheckingError : Show EquivalenceCheckingError
  := fun err => String.concat String.NewLine (show_lines err).

Definition empty_dag : dag := nil.
Definition merge_symbol (s:symbol) : dag.M idx := merge_node ((old 64%N s), nil).
(** We use dag length as a source of fresh symbols *)
Definition gensym (d : dag) : idx := N.of_nat (List.length d).
Definition merge_fresh_symbol : dag.M idx := fun d => merge_symbol (gensym d) d.
Definition merge_literal (l:Z) : dag.M idx := merge_node ((const l, nil)).

Definition SetRegFresh (r : REG) : M idx :=
  (idx <- lift_dag merge_fresh_symbol;
  _ <- SetReg r idx;
  Symbolic.ret idx).

(** symbolic evaluations live in the state monad, pushed to the leaves of a PHOAS type *)
Definition symexM T := dag -> ErrorT EquivalenceCheckingError (T * dag).
Definition symex_return {T} (v : T) : symexM T := fun st => Success (v, st).
Definition symex_error {T} err : symexM T := fun st => Error err.
Definition symex_bind {A B} (v : symexM A) (f : A -> symexM B) : symexM B
  := fun st => (v <- v st; let '(a, st) := v in f a st)%error.
Delimit Scope symex_scope with symex.
Bind Scope symex_scope with symexM.
Notation "'slet' x .. y <- X ; B"  := (symex_bind X (fun x => .. (fun y => B%symex) .. )) : symex_scope.
Notation "A <- X ; B" := (symex_bind X (fun A => B%symex)) : symex_scope.
(* light alias *)
Definition App (e : Symbolic.node idx) : symexM idx := fun st => Success (merge (simplify st e) st).
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

Definition build_inputarray (len : nat) : dag.M (list idx) :=
  List.foldmap (fun _ => merge_fresh_symbol) (List.seq 0 len).

Fixpoint build_inputs (types : type_spec) : dag.M (list (idx + list idx))
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
Definition compute_array_address (base : idx) (i : nat)
  := (offset <- Symbolic.App (zconst 64%N (8 * Z.of_nat i), nil);
      Symbolic.App (add 64%N, [base; offset]))%x86symex.

Definition build_merge_array_addresses (base : idx) (items : list idx) : M (list idx)
  := mapM (fun '(i, idx) =>
             (addr <- compute_array_address base i;
              (fun s => Success (addr, update_mem_with s (cons (addr,idx)))))
          )%x86symex (List.enumerate items).

Fixpoint build_merge_base_addresses (items : list (idx + list idx)) (reg_available : list REG) : M (list (option idx))
  := match items, reg_available with
     | [], _ | _, [] => Symbolic.ret []
     | inr idxs :: xs, r :: reg_available
       => (base <- SetRegFresh r; (* note: overwrites initial value *)
           addrs <- build_merge_array_addresses base idxs; (* note: overwrites initial value *)
           rest <- build_merge_base_addresses xs reg_available;
           Symbolic.ret (Some base :: rest))
     | inl idx :: xs, r :: reg_available =>
          (_ <- SetReg r idx; (* note: overwrites initial value *)
           rest <- build_merge_base_addresses xs reg_available;
           Symbolic.ret (None :: rest))
     end%N%x86symex.

Fixpoint dag_gensym_n (n : nat) : dag.M (list symbol) :=
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

Definition symex_ident {t} (idc : ident t) : symex_T t.
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

Fixpoint symex_expr {t} (e : API.expr (var:=var) t) : symex_T t
  := match e in expr.expr t return symex_T t with
     | expr.Ident _ idc => symex_ident idc
     | expr.Var _ v => symex_T_return v
     | expr.Abs (type.base _) _ f => fun v => @symex_expr _ (f v)
     | expr.App (type.base _) _ f x
       => let ef := @symex_expr _ f in
          let ex := @symex_expr _ x in
          symex_T_bind_base ex ef
     | expr.LetIn (type.base _) _ x f
       => let ef v := @symex_expr _ (f v) in
          let ex := @symex_expr _ x in
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
     symex_expr ast d.

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

Definition init_symbolic_state (d : dag) : symbolic_state
  := let '(initial_reg_idxs, d) := dag_gensym_n 16 d in
     {|
       dag_state := d;
       symbolic_reg_state := Tuple.from_list_default None 16 (List.map Some initial_reg_idxs);
       symbolic_mem_state := [];
       symbolic_flag_state := Tuple.repeat None 6;
     |}.

Definition build_merge_stack_placeholders (stack_size : nat)
  : M unit
  := (stack_placeholders <- lift_dag (build_inputarray stack_size);
      rsp_val <- SetRegFresh rsp;
      stack_size <- Symbolic.App (zconst 64 (-8 * Z.of_nat stack_size), []);
      stack_base <- Symbolic.App (add 64%N, [rsp_val; stack_size]);
      _ <- build_merge_array_addresses stack_base stack_placeholders;
      ret tt)%x86symex.

Definition LoadArray (base : idx) (len : nat) : M (list idx)
  := mapM (fun i =>
             (addr <- compute_array_address base i;
              Load64 addr)%x86symex)
          (seq 0 len).

Definition LoadOutputs (outputaddrs : list (option idx)) (output_types : type_spec)
  : M (list (idx + list idx))
  := (asm_output <- mapM (fun '(ocells, spec) =>
            match ocells, spec with
            | None, None | None, Some _ | Some _, None => err (error.load 0)
            | Some base, Some len
              => LoadArray base len
            end) (List.combine outputaddrs output_types);
      Symbolic.ret (List.map inr asm_output))%N%x86symex.

Definition symex_asm_func_M
           (callee_saved_registers : list REG)
           (output_types : type_spec) (stack_size : nat)
           (inputs : list (idx + list idx)) (reg_available : list REG) (asm : Lines)
  : M (ErrorT EquivalenceCheckingError (list (idx + list idx)))
  := (output_placeholders <- lift_dag (build_inputs output_types);
      argptrs <- build_merge_base_addresses (output_placeholders ++ inputs) reg_available;
      _ <- build_merge_stack_placeholders stack_size;
      initial_register_values <- mapM GetReg callee_saved_registers;
      _ <- SymexLines asm;
      final_register_values <- mapM GetReg callee_saved_registers;
      let unsaved_registers : list (REG * (idx * idx)) := List.filter (fun '(r, (init, final)) => negb (init =? final)%N) (List.combine callee_saved_registers (List.combine initial_register_values final_register_values)) in
      let outputaddrs : list (option idx) := firstn (length argptrs - length inputs) argptrs in
      (* In the following line, we match on the result so we can emit Internal_error_output_load_failed in the calling function, rather than passing through the placeholder error from LoadOutputs *)
      (fun s => match LoadOutputs outputaddrs output_types s, unsaved_registers with
                | Success (asm_output, s), []
                  => Success (Success asm_output, s)
                | Error (_, s), _
                  => Success (Error (Internal_error_output_load_failed outputaddrs s), s)
                | Success (_, s), unsaved_registers
                  => Success (Error (Registers_not_saved unsaved_registers s), s)
                end))%N%x86symex.

Definition symex_asm_func
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
             match symex_asm_func_M callee_saved_registers output_types stack_size inputs reg_available asm (init_symbolic_state d) with
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
            (asm : Lines)
            (expr : API.Expr t)
            (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
            (out_bounds : ZRange.type.base.option.interp (type.final_codomain t)).

    Definition strip_ret (asm : Lines) :=
      let isinstr := fun l => match l.(rawline) with INSTR _ => true | _ => false end in
      let notret := fun l => negb (Equality.RawLine_beq l.(rawline) (INSTR {| Syntax.op := Syntax.ret; Syntax.args := nil |})) in
      match dropWhile notret asm with
      | nil => Error Missing_ret
      | cons _r trailer =>
          if List.existsb isinstr trailer then Error (Code_after_ret (List.filter isinstr trailer) trailer)
          else Success (takeWhile notret asm)
      end.

    Definition check_equivalence : ErrorT EquivalenceCheckingError unit :=
      let reg_available := assembly_calling_registers (* registers available for calling conventions *) in
      let d := empty_dag in
      input_types <- simplify_input_type t arg_bounds;
      output_types <- simplify_base_type (type.final_codomain t) out_bounds;
      let '(inputs, d) := build_inputs input_types d in

      PHOAS_output <- symex_PHOAS expr inputs d;
      let '(PHOAS_output, d) := PHOAS_output in

      asm <- strip_ret asm;
      let stack_size : nat := N.to_nat (assembly_stack_size asm) in
      symevaled_asm <- symex_asm_func d assembly_callee_saved_registers output_types stack_size inputs reg_available asm;
      let '(asm_output, s) := symevaled_asm in

      if list_beq _ (sum_beq _ _ N.eqb (list_beq _ N.eqb)) asm_output PHOAS_output
      then Success tt
      else Error (Unable_to_unify asm_output PHOAS_output s).

    (** We don't actually generate assembly, we just check equivalence and pass assembly through unchanged *)
    Definition generate_assembly_of_hinted_expr : ErrorT EquivalenceCheckingError Lines
      := match check_equivalence with
         | Success tt => Success asm (* the asm is equivalent, so we can emit this asm *)
         | Error err => Error err
         end.
  End with_expr.
End check_equivalence.
