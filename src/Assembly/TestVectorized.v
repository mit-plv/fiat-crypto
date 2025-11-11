From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import NArith.
From Coq Require Import ZArith.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.Parse.
Require Import Crypto.Assembly.Equivalence.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.Notations.

Set Printing Coercions.
Set Printing Notations.
Import ListNotations.
Import API.Compilers.API APINotations.Compilers AbstractInterpretation.ZRange.Compilers.

Local Open Scope zrange_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope symex_scope.

(* Notation "A <- X ; B" := (symex_bind X (fun A => B%symex)) : symex_scope. *)
Existing Instance default_equivalence_checker_options.

Definition typeZ := type.base (base.type.type_base base.type.Z).

(* ============================================================================
   Test 1: Identity function on a single 64-bit integer
   Assembly: mov rax, rdi; ret
   This does nothing - just returns the input value unchanged
   ============================================================================ *)
Section identity.
  (* Type: Z -> Z *)
  Definition t : API.type := type.arrow typeZ typeZ.

  (* PHOAS expression: fun x => x (identity) *)
  Definition expr : API.Expr t :=
    fun (var : API.type -> Type) =>
      expr.Abs (fun x => $$x)%expr.

  (* Bounds for input: 64-bit unsigned *)
  Definition arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t :=
    (Some r[0 ~> 2^64-1], tt).

  (* Bounds for output: 64-bit unsigned *)
  Definition out_bounds : ZRange.type.base.option.interp (type.final_codomain t) :=
    Some r[0 ~> 2^64-1].

  (* Assembly program: identity (mov rdi to rax, then ret) *)
  Definition asm_strings : list string := ["mov rax, rdi"; "ret"].

  (* Parse and name the assembly *)
  Definition asm : list (string * Lines) :=
    Eval compute in 
    match ErrorT.map (fun lines => [("test_id", lines)]) (parse_validated asm_strings) with
    | Error e => []
    | Success asm => asm
    end.

  Print asm. (* should be the actual parsed assembly, no error wrapper *)


  Local Notation map_err_None v := (ErrorT.map_error (fun e => (None, e)) v).
  Local Notation map_err_Some label v := (ErrorT.map_error (fun e => (Some label, e)) v).

  Definition check_id :=
    let d := dag.empty in
    input_types <- map_err_None (simplify_input_type t arg_bounds);
    output_types <- map_err_None (simplify_base_type (type.final_codomain t) out_bounds);
    let '(inputs, d) := build_inputs (descr:=Build_description "build_inputs" true) input_types d in 
    Success d.

  (* Run the equivalence check *)
  (* Definition check_id : ErrorT ParseValidatedError (ErrorT (option (string * Lines) * EquivalenceCheckingError) unit) :=
    match id_asm_func with
    | Error e => Error e
    | Success asm => Success (check_equivalence asm id_expr id_arg_bounds id_out_bounds)
    end. *)

  Compute check_id.
End identity.
(* READ: this fails because the asm DAG has like 200 nodes just doing setup stuff to represent the register initial states, but the PHOAS expr only has like 1 node. *)

(* ============================================================================
   Test 2: Simple addition of two 64-bit integers
   Assembly: add rax, rbx; ret
   Assembly semantics: takes two 64-bit values in rax and rbx, adds them, returns sum in rax
   PHOAS expression: fun (pair : rax, rbx) => rax + rbx
   ============================================================================ *)

(* Type for a pair of Z values *)
Definition pair_Z : API.type := type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)).

(* Type signature: (Z * Z) -> Z *)
Definition add_type : API.type := type.arrow pair_Z typeZ.
(* Locate ident_fst. *)
Print ident.Literal.
(* PHOAS expression: fun (rax, rbx) => (rax + rbx) & 0xFFFFFFFFFFFFFFFF *)
Definition add_expr : API.Expr add_type :=
  fun (var : API.type -> Type) =>
    expr.Abs (fun p =>
      let rax := (#ident.fst @ $$p)%expr in
      let rbx := (#ident.snd @ $$p)%expr in
      (#ident.Z_cast @ #( @ident.Literal base.type.zrange (r[0 ~> 2^64-1])) @ #(rax + rbx))%expr).

(* Bounds for input argument (pair of 64-bit unsigned integers) *)
Definition add_arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp add_type :=
  ((Some r[0 ~> 2^64-1], Some r[0 ~> 2^64-1]), tt).

(* Bounds for output: 64-bit unsigned (truncated by the add instruction) *)
Definition add_out_bounds : ZRange.type.base.option.interp (type.final_codomain add_type) :=
  Some (r[0 ~> 2^64-1]).

(* Assembly program: add rax, rbx; ret *)
Definition prog : list string := ["add rax, rbx"; "ret"].

(* Parse and name the assembly *)
Definition asm_func : ErrorT ParseValidatedError (list (string * Lines)) :=
  ErrorT.map (fun lines => [("test_add", lines)]) (parse_validated prog).

  Set Printing Depth 100.
(* Run the equivalence check *)
Definition check_add : ErrorT ParseValidatedError (ErrorT (option (string * Lines) * EquivalenceCheckingError) unit) :=
  match asm_func with
  | Error e => Error e
  | Success asm => Success (check_equivalence asm add_expr add_arg_bounds add_out_bounds)
  end.

Compute check_add. 


