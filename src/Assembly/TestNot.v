Require Import Coq.ZArith.ZArith.
Require Import Crypto.Assembly.Parse.
Require Import Crypto.Assembly.Equivalence.
Require Import Crypto.Language.API.
Require Import Crypto.Language.APINotations.
Require Import Crypto.AbstractInterpretation.ZRange.

Require Import Crypto.Util.ZRange.		
Locate "r[ _ ~> _ ]".
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Util.ErrorT.
(* Import API.Compilers APINotations.Compilers AbstractInterpretation.ZRange.Compilers. *)
  Import API.Compilers.API APINotations.Compilers AbstractInterpretation.ZRange.Compilers.

Print base.type.

Check API.Expr.
From Coq Require Import String List Ascii NArith ZArith.
From Coq.Program Require Import Tactics.

Import ListNotations.
Open Scope string_scope.
(* Local Open Scope expr_scope. *)
Local Open Scope zrange_scope.

(* PHOAS expression for bitwise NOT, modulo 2^64 *)

(* Definition not_expr : API.Expr (type.Z -> type.Z) := *)
(*   fun var => lam x : Z => (Z.lnot_ x Z.modulo_ (2^64))%expr. *)

Print Scope zrange_scope.
Print Scopes.



(* Definition not_expr : API.Expr (type.Z -> type.Z) := *)
(*   fun var => lam x : Z => (Z.lnot x mod 2^64)%expr. *)

(* Assembly: single instruction "not %rax" *)
(* Definition asm_lines : list string := ["not rax"] : list string. *)
Definition asm_lines2 : list string := ["neg rax"] : list string.
Definition prog := [ "mov eax, ebx"] : list string.
Compute parse_Lines prog.

Compute parse_Lines asm_lines2.


(* Parse assembly *)

Definition parsed_asm2 : ErrorT ParseValidatedError Lines :=
  parse_validated asm_lines2.

Locate parse_validated.

Compute parsed_asm2.
Compute parse_Lines asm_lines2.

(* Input/output bounds: 64-bit integers *)
(* Definition arg_bounds : ZRange.type.option.interp (type.Z -> type.Z) := *)
(*   (Some r[0, 2^64-1], tt). *)

(* Definition out_bounds : ZRange.type.base.option.interp type.Z := *)
(*   Some r[0, 2^64-1]. *)

(* Wrap parsed assembly as a single function *)
(* Definition asm_func : ErrorT ParseValidatedError (list (string * Lines)) := *)
(*   match parsed_asm with *)
(*   | Success lines => Success [("test_not", lines)] *)
(*   | Error e => Error e *)
(*   end. *)


Definition asm_lines : list string := ["not rax"] : list string.
Definition parsed_asm : ErrorT ParseValidatedError Lines :=
  parse_validated asm_lines.


(* give the parsed assembly a name for the function ("test_not"). Check equivalence expects the assembly to name each function, for some reason. *)
Definition asm_func : ErrorT ParseValidatedError (list (string * Lines)) :=
  match parsed_asm with
  | Success lines => Success [("test_not", lines)]
  | Error e => Error e
  end.

Local Open Scope zrange_scope.

Locate "r[ _ ~> _ ]".

(* should now match the parameter type of check_equivalence, but wrapped in an extra ErrorT *)
Check asm_func.
Existing Instance default_equivalence_checker_options.

Definition run_check
           {t}
           (expr : API.Expr t)
           (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
           (out_bounds : ZRange.type.base.option.interp (type.final_codomain t))
  : ErrorT ParseValidatedError (ErrorT (option (string * Lines) * EquivalenceCheckingError) unit) :=
  match asm_func with
  | Error e => Error e
  | Success asm => Success (check_equivalence asm expr arg_bounds out_bounds)
  end.



Check r[0 ~> 2^64-1].     (* Range from 0 to 2^64-1 *)
Check base.type.Z.

(* Definition int_type : API.type := Z. *)

(* Check API.Expr (type.base base.type.Z). *)
(* Check APINotations.tZ. *)
Compute type base.type.
Compute base.type. (* Language.Compilers.base.type Compilers.base : Set *)
Compute type Compilers.base.type.
Compute Compilers.base.type.
Compute Compilers.base.
Compute base.type.type_base Z.
(*Notation API.type := (type (Language.Compilers.base.type Compilers.base)) *)


(* (* Compute type (base.type.type_base Z). *) *)
(* Check type base.type.Z. *)
(* Compute API.Expr (Compilers.Z). *)
(* Definition Double {T: Type} : T -> (T * T) := fun x : T => (x, x). *)
(* Compute @Double nat 1. *)

(* Expression: bitwise NOT mod 2^64 *)
Print base.type.Z.


Definition not_expr : API.Expr(type.arrow (type.base (type_base base.type.Z)) (type.base (type_base base.type.Z))) :=
  fun var => expr.Abs (fun x => (#ident.Z_lnot_modulo @ $$x @ #(@ident.Literal base.type.Z (2^64)%Z))%expr).

(* Input/output ranges: 64-bit unsigned *)
Definition arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp (type.arrow (type.base base.type.Z) (type.base base.type.Z)) :=
  (Some (r[0 ~> 2^64-1]), tt).
Definition out_bounds : ZRange.type.base.option.interp base.type.Z :=
  Some (r[0 ~> 2^64-1]).

Check arg_bounds.

Definition test :=
  check_equivalence parsed_asm not_expr arg_bounds out_bounds.

