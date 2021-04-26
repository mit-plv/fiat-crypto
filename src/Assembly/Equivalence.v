Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Parse.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.Strings.String.
Require Import Crypto.Language.API.
Require Import Crypto.Language.APINotations.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Crypto.Stringification.Language.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
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
(** Are output arrays considered to come before input arrays, or after them? *)
Class assembly_output_first_opt := assembly_output_first : bool.
Typeclasses Opaque assembly_output_first_opt.
(** Should we assign registers to the arguments in left-to-right or right-to-left order? *)
Class assembly_argument_registers_left_to_right_opt := assembly_argument_registers_left_to_right : bool.
Typeclasses Opaque assembly_argument_registers_left_to_right_opt.
(** Stack size (in bytes) *)
Class assembly_stack_size_opt := assembly_stack_size' : option N.
Typeclasses Opaque assembly_stack_size_opt.
Definition default_assembly_stack_size := 40%N.
(** The stack size is taken to be the given command line argument, or
    else inferred to be the literal argument to the first [sub rsp,
    LITERAL] in the code, or else [default_assembly_stack_size] if
    none exists *)
Definition assembly_stack_size {v : assembly_stack_size_opt} (asm : Lines) : N
  := match v with
     | Some v => v
     | None
       => match Option.List.map
                  (fun l
                   => match l.(rawline) with
                      | INSTR {| op := sub ; args := [reg rsp; const n] |}
                        => Some (Z.to_N n)
                      | _ => None
                      end)
                  asm
          with
          | n :: _ => n
          | [] => default_assembly_stack_size
          end
     end.

(** N.B. The printer of these error messages will always know the
assembly function lines and the AST used for equivalence checking, so
these error messages need not include this information.  However, they
should include as much information as possible about the local source
of the inequivalence.  It's not out of the question, for example, to
include enough information in the error message to generate .dot files
of the equivalence graphs.  If desired, we can parameterize the error
printing functions on command-lines options indicating how verbose to
be in printing the error message. *)
Inductive BoundsDataError :=
| Unknown_array_length (t : base.type)
| Invalid_arrow_type (t : API.type)
.
Inductive EquivalenceCheckingError :=
| Could_not_prove_equivalence
| Not_enough_registers (num_given num_extra_needed : nat)
| Invalid_bounds_data (e : BoundsDataError)
| Incorrect_array_input_dag_node
| Incorrect_Z_input_dag_node
| Not_enough_input_dag_nodes (t : Compilers.type.type base.type)
| Invalid_input_type (t : Compilers.type.type base.type)
.

Global Instance show_lines_BoundsDataError : ShowLines BoundsDataError
  := fun err => match err with
                | Unknown_array_length t => ["Unknown array length of type " ++ show t ++ "."]%string
                | Invalid_arrow_type t => ["Invalid higher order function involving the type " ++ show t ++ "."]%string
                end%list.
Global Instance show_BoundsDataError : Show BoundsDataError
  := fun err => String.concat String.NewLine (show_lines err).
Global Instance show_lines_EquivalenceCheckingError : ShowLines EquivalenceCheckingError
  := fun err => match err with
                | Could_not_prove_equivalence
                  => ["Could not prove equivalence of assembly and AST."]
                | Not_enough_registers num_given num_extra_needed
                  => ["Not enough registers available for storing input and output (given " ++ show num_given ++ ", needed an additional " ++ show num_extra_needed ++ "."]%string
                | Incorrect_array_input_dag_node
                  => ["Internal error: Input dag node had an unexpected array."]
                | Incorrect_Z_input_dag_node
                  => ["Internal error: Input dag node had an unexpected Z."]
                | Not_enough_input_dag_nodes t
                  => ["Internal error: Not enough input dag nodes to allocate for type " ++ show t ++ "."]%string
                | Invalid_input_type t
                  => ["Invalid type for input argument " ++ show t ++ "."]%string
                | Invalid_bounds_data err
                  => show_lines err
                end%list.
Global Instance show_EquivalenceCheckingError : Show EquivalenceCheckingError
  := fun err => String.concat String.NewLine (show_lines err).

(** FIXME: remove axioms *)
Definition symbol := N.
Definition gensym_state := N.
Definition gensym_state_init : gensym_state := 0%N.
Definition gensym (st : gensym_state) : symbol * gensym_state := (st, N.succ st).
Definition idx := N.
Axiom dag : Type.
Axiom empty_dag : dag.
Axiom merge : symbol -> dag -> idx * dag.
Axiom merge_literal : Z -> dag -> idx * dag.

Definition input_type_spec := list (option nat). (* list of array lengths; None means not an array *)

(** Convert PHOAS info about types and argument bounds into a simplified specification *)
Fixpoint simplify_base_type
         (t : base.type)
  : forall arg_bounds : ZRange.type.base.option.interp t, ErrorT EquivalenceCheckingError input_type_spec
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
             | None => Error (Invalid_bounds_data (Unknown_array_length t))
             | Some bs => Success [Some (List.length bs)]
             end
     | base.type.type_base _
     | base.type.option _
     | base.type.list _
       => fun _ => Error (Invalid_input_type (type.base t))
     end%error.
Definition simplify_type
         (t : Compilers.type.type base.type)
  : forall arg_bounds : ZRange.type.option.interp t, ErrorT EquivalenceCheckingError input_type_spec
  := match t with
     | type.base t => simplify_base_type t
     | type.arrow _ _ => fun _ => Error (Invalid_input_type t)
     end.
Fixpoint simplify_input_type
         (t : Compilers.type.type base.type)
  : forall arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t, ErrorT EquivalenceCheckingError input_type_spec
  := match t return type.for_each_lhs_of_arrow ZRange.type.option.interp t -> _ with
     | type.base _ => fun 'tt => Success []
     | type.arrow A B
       => fun '(bA, bB)
          => (vA <- simplify_type A bA;
             vB <- simplify_input_type B bB;
             Success (vA ++ vB))
     end%error.

Fixpoint build_inputs (st : dag * gensym_state) (types : input_type_spec) : list (idx + list idx) * (dag * gensym_state)
  := match types with
     | [] => ([], st)
     | None :: tys
       => let '(d, st) := st in
          let '(n, st) := gensym st in
          let '(idx, d) := merge n d in
          let '(rest, (d, st)) := build_inputs (d, st) tys in
          (inl idx :: rest, (d, st))
     | Some len :: tys
       => let '(idxs, (d, st))
              := List.fold_left
                   (fun '(idxs, (d, st)) _
                    => let '(n, st) := gensym st in
                       let '(idx, d) := merge n d in
                       (idx :: idxs, (d, st)))
                   (List.seq 0 len)
                   ([], st) in
          let '(rest, (d, st)) := build_inputs (d, st) tys in
          (inr idxs :: rest, (d, st))
     end.

(** PHOAS var type, storing dag indices *)
Fixpoint base_var (t : base.type) : Set
  := match t with
     | base.type.unit
       => unit
     | base.type.type_base base.type.Z => idx
     | base.type.prod A B => base_var A * base_var B
     | base.type.list A => list (base_var A)
     | base.type.type_base _
     | base.type.option _
       => unit (* should not happen *)
     end.
Definition var (t : Compilers.type.type base.type) : Set
  := match t with
     | type.base t => base_var t
     | type.arrow s d => Empty_set
     end.

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
       => Error (Invalid_input_type (type.base t))
     end%error.
Definition build_var (t : Compilers.type.type base.type) (indices : list (idx + list idx))
  : ErrorT EquivalenceCheckingError (var t * list (idx + list idx))
  := match t with
     | type.base t => build_base_var t indices
     | type.arrow _ _ => Error (Invalid_input_type t)
     end.
Fixpoint build_input_var (t : Compilers.type.type base.type) (indices : list (idx + list idx))
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

(** symbolic evaluations live in the state monad, pushed to the leaves of a PHOAS type *)
Definition symexM T := dag -> ErrorT EquivalenceCheckingError (T * dag).
(* light alias *)
Definition merge_literalM (v : Z) : symexM idx := fun st => Success (merge_literal v st).
Fixpoint symex_T (t : Compilers.type.type base.type) : Type
  := match t with
     | type.base t => symexM (base_var t)
     | type.arrow s d
       => ErrorT EquivalenceCheckingError (symex_T s -> symex_T d)
     end.
Definition symex_return {T} (v : T) : symexM T := fun st => Success (v, st).
Definition symex_bind {A B} (v : symexM A) (f : A -> symexM B) : symexM B
  := fun st => (v <- v st; let '(a, st) := v in f a st)%error.
Definition symex_T_return {t : Compilers.type.type base.type} : var t -> symex_T t
  := match t return var t -> symex_T t with
     | type.base t => symex_return
     | type.arrow s d
       => fun f : Empty_set => match f with end
     end.
Delimit Scope symex_scope with symex.
Bind Scope symex_scope with symexM.
Bind Scope symex_scope with symex_T.
(** TODO: move this to Notations *)
Reserved Notation "'slet' x .. y <- X ; B"
         (at level 200, x binder, y binder, B at level 200, format "'slet'  x .. y  <-  X  ; '//' B").
Notation "'slet' x .. y <- X ; B"  := (symex_bind X (fun x => .. (fun y => B%symex) .. )) : symex_scope.
Notation "A <- X ; B" := (symex_bind X (fun A => B%symex)) : symex_scope.
(*Infix ";;" := sequence : option_scope.
Infix ";;;" := sequence_return : option_scope.*)

Definition symex_ident {t} (idc : ident t) : symex_T t.
  Print IdentifiersBasicGENERATED.Compilers.ident.
  refine match idc in ident t return symex_T t with
         | ident.Literal Compilers.Z v
           => idx <- merge_literalM v;
                symex_return idx
         | ident.Z_add
           => Success (fun x => Success (fun y => x <- x; y <- y; idx <- ?[merge_addition] x y; symex_return idx))
         | _ => ltac:(shelve)
         end%symex; cbn.
Admitted.

Fixpoint symex_expr {t} (e : API.expr (var:=var) t) : symex_T t.
  refine match e in expr.expr t return symex_T t with
     | expr.Ident _ idc => symex_ident idc
     | expr.Var _ v => symex_T_return v
     | expr.Abs _ _ f => Success _
     | expr.App _ _ f x
       => let ef := @symex_expr _ f in
          let ex := @symex_expr _ x in
          _
          (*ef ex*)
     | expr.LetIn _ _ x f
       => let ef := (*@symex_expr _ f*)_ in
          let ex := @symex_expr _ x in
          _
         end%symex; cbn in *; fold symex_T.

  shelve.
  fold symex_T.
  shelve.
Admitted.

Section check_equivalence.
  Context {assembly_calling_registers' : assembly_calling_registers_opt}
          {assembly_stack_size' : assembly_stack_size_opt}
          {assembly_output_first : assembly_output_first_opt}
          {assembly_argument_registers_left_to_right : assembly_argument_registers_left_to_right_opt}.

  Section with_expr.
    Context {t}
            (asm : Lines)
            (expr : API.Expr t)
            (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
            (out_bounds : ZRange.type.base.option.interp (type.final_codomain t)).

    Definition check_equivalence : ErrorT EquivalenceCheckingError unit.
    Proof.
      refine (
          let reg_available := assembly_calling_registers (* registers available for calling conventions *) in
          let d := empty_dag in
          let gensym_st := gensym_state_init in
          input_types <- simplify_input_type t arg_bounds;
          output_types <- simplify_base_type (type.final_codomain t) out_bounds;
          let '(inputs, (d, gensym_st)) := build_inputs (d, gensym_st) input_types in
          input_var_data <- build_input_var t inputs;
          let '(input_var_data, unused_inputs) := input_var_data in
          (* TODO: should we check that there are no unused input nodes? *)
          let ast : API.expr (type.base (type.final_codomain t))
              := invert_expr.smart_App_curried (expr _) input_var_data in
          symevaled_PHOAS <- symex_expr ast d;
          let '(PHOAS_output, PHOAS_dag) := symevaled_PHOAS in
          _)%error.
          (* outputs come first, assuming assembly_output_first *)
          let res := prod_sequence_reg_available
                       [] assembly_output_first
                       (fun reg_available => make_output_reg_data reg_available out_bounds)
                       (fun reg_available => make_input_reg_data reg_available arg_bounds)
                       reg_available in

          (decl <- match res with
                   | inl (Success decl, _reg_available) => Success decl
                   | inl (Error err, _) => Error (Invalid_bounds_data err)
                   | inr n => Error (Not_enough_registers (List.length reg_available) n)
                   end;
           let '(output_registers, input_registers) := decl in
           (* we now construct the inputs to the equivalence checker:
              - the list of registers and array sizes for outputs
              - the list of registers and array sizes for inputs
              - the stack size
              - the expression specialized to some appropriate variable type
              - the assembly expression is available in the context as asm *)
           let output_register_list : list (REG * nat) := reg_list_of_base_reg_data output_registers in
           let input_register_list : list (REG * nat) := reg_list_of_input_reg_data input_registers in
           let stack_size : nat := N.to_nat (assembly_stack_size asm) in
           let ast : API.expr (type.base (type.final_codomain t))
               := invert_expr.smart_App_curried (expr _) (type.map_for_each_lhs_of_arrow (@reg_data_to_var) input_registers) in
           let asm_lines : Lines := asm in

           _)%error).
      refine (if false
              then Success tt
              else Error Could_not_prove_equivalence).
    Defined.

    (** We don't actually generate assembly, we just check equivalence and pass assembly through unchanged *)
    Definition generate_assembly_of_hinted_expr : ErrorT EquivalenceCheckingError Lines
      := match check_equivalence with
         | Success tt => Success asm (* the asm is equivalent, so we can emit this asm *)
         | Error err => Error err
         end.
  End with_expr.
End check_equivalence.
