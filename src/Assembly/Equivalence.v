Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
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
(** TODO(for Andres from Jason): What should this be? *)
Definition default_assembly_stack_size := 40%N.
Definition assembly_stack_size {v : assembly_stack_size_opt} : N
  := Option.value v default_assembly_stack_size.

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
                | Invalid_bounds_data err
                  => show_lines err
                end%list.
Global Instance show_EquivalenceCheckingError : Show EquivalenceCheckingError
  := fun err => String.concat String.NewLine (show_lines err).

(* stores information about registers and array lengths associated to variables *)
Fixpoint base_reg_data (t : base.type) : Set
  := match t with
     | base.type.unit
       => unit
     | base.type.type_base base.type.Z => REG * bool (* is pointer *)
     | base.type.prod A B => base_reg_data A * base_reg_data B
     | base.type.list A => REG * nat (* array length *)
     | base.type.type_base _
     | base.type.option _
       => unit (* should not happen *)
     end.
Definition reg_data (t : Compilers.type.type base.type) : Set
  := match t with
     | type.base t => base_reg_data t
     | type.arrow s d => Empty_set
     end.
(* 0 means immediate *)
Fixpoint reg_list_of_base_reg_data {t} : base_reg_data t -> list (REG * nat)
  := match t return base_reg_data t -> list (REG * nat) with
     | base.type.unit
       => fun _ => []
     | base.type.type_base base.type.Z
       => fun '(r, is_pointer) => [(r, if is_pointer then 1 else 0)]
     | base.type.list _
       => fun '(r, len) => [(r, len)]
     | base.type.prod A B
       => fun x : base_reg_data A * base_reg_data B
          => @reg_list_of_base_reg_data A (fst x) ++ @reg_list_of_base_reg_data B (snd x)
     | base.type.type_base _
     | base.type.option _
       => fun 'tt => []
     end%list.

Definition reg_list_of_reg_data {t} : reg_data t -> list (REG * nat)
  := match t with
     | type.base t => @reg_list_of_base_reg_data t
     | type.arrow _ _ => fun absurd : Empty_set => match absurd with end
     end.

Definition prod_sequence_reg_available' {E A B C}
           (nil : C)
           (f1 : C -> (ErrorT E A * C) + nat)
           (f2 : C -> (ErrorT E B * C) + nat)
  : C -> (ErrorT E (A * B) * C) + nat
  := fun reg_available
     => let '(rsA, reg_available, nA)
            := match f1 reg_available with
               | inl (rs, reg_available) => (Some rs, reg_available, 0%nat)
               | inr n => (None, nil, n)
               end in
        let '(rsB, reg_available, nB)
            := match f2 reg_available with
               | inl (rs, reg_available) => (Some rs, reg_available, 0%nat)
               | inr n => (None, nil, n)
               end in
        match rsA, rsB with
        | None, _ | _, None => inr (nA + nB)%nat
        | Some rsA, Some rsB => inl ((rsA <- rsA; rsB <- rsB; Success (rsA, rsB))%error, reg_available)
        end.
Definition prod_sequence_reg_available {E A B C}
           (nil : C) (in_order : bool)
           (f1 : C -> (ErrorT E A * C) + nat)
           (f2 : C -> (ErrorT E B * C) + nat)
  : C -> (ErrorT E (A * B) * C) + nat
  := if in_order
     then prod_sequence_reg_available' nil f1 f2
     else
       fun c
       => match prod_sequence_reg_available' nil f2 f1 c with
          | inl (Success (b, a), c) => inl (Success (a, b), c)
          | inl (Error e, c) => inl (Error e, c)
          | inr n => inr n
          end.

Fixpoint make_base_reg_data
         {assembly_argument_registers_left_to_right : assembly_argument_registers_left_to_right_opt}
         (is_pointer : bool) {t} (reg_available : list REG)
  : ZRange.type.base.option.interp t -> (ErrorT BoundsDataError (base_reg_data t) * list REG (* remaining *)) + nat (* how many more registers needed? *)
  := match t, reg_available return ZRange.type.base.option.interp t -> (ErrorT BoundsDataError (base_reg_data t) * list REG) + nat with
     | base.type.unit, _
       => fun _ => inl (Success tt, reg_available)
     | base.type.type_base base.type.Z, r :: reg_available
       => fun _ => inl (Success (r, is_pointer), reg_available)
     | base.type.list t, r :: reg_available
       => fun bounds : option (list (ZRange.type.base.option.interp t))
          => inl (match bounds with
                  | Some ls => Success (r, List.length ls)
                  | None => Error (Unknown_array_length t)
                  end,
                  reg_available)
     | base.type.type_base base.type.Z, []
     | base.type.list _, []
       => fun _ => inr 1%nat
     | base.type.prod A B, _
       => fun bounds : ZRange.type.base.option.interp A * ZRange.type.base.option.interp B
          => prod_sequence_reg_available
               [] assembly_argument_registers_left_to_right
               (fun reg_available => make_base_reg_data is_pointer reg_available (fst bounds))
               (fun reg_available => make_base_reg_data is_pointer reg_available (snd bounds))
               reg_available
     | base.type.type_base _, _
     | base.type.option _, _
       => fun _ => inl (Success tt, reg_available)
     end%list.
Definition make_reg_data
          {assembly_argument_registers_left_to_right : assembly_argument_registers_left_to_right_opt}
          (is_pointer : bool) {t} (reg_available : list REG)
  : ZRange.type.option.interp t -> (ErrorT BoundsDataError (reg_data t) * list REG (* remaining *)) + nat (* how many more registers needed? *)
  := match t return ZRange.type.option.interp t -> (ErrorT BoundsDataError (reg_data t) * list REG) + nat with
     | type.base t => make_base_reg_data is_pointer reg_available
     | type.arrow _ _ => fun _ => inl (Error (Invalid_arrow_type t), reg_available)
     end.
Fixpoint make_input_reg_data
         {assembly_argument_registers_left_to_right : assembly_argument_registers_left_to_right_opt}
         {t} (reg_available : list REG) : type.for_each_lhs_of_arrow ZRange.type.option.interp t -> (ErrorT BoundsDataError (type.for_each_lhs_of_arrow reg_data t) * list REG (* remaining *)) + nat (* how many more registers needed? *)
  := match t return type.for_each_lhs_of_arrow ZRange.type.option.interp t -> (ErrorT BoundsDataError (type.for_each_lhs_of_arrow reg_data t) * list REG) + nat with
     | type.base t => fun 'tt => inl (Success tt, reg_available)
     | type.arrow A B
       => fun bounds : ZRange.type.option.interp A * type.for_each_lhs_of_arrow ZRange.type.option.interp B
          => prod_sequence_reg_available
               [] assembly_argument_registers_left_to_right
               (fun reg_available => make_reg_data true reg_available (fst bounds))
               (fun reg_available => make_input_reg_data reg_available (snd bounds))
               reg_available
     end.
Definition make_output_reg_data
           {assembly_argument_registers_left_to_right : assembly_argument_registers_left_to_right_opt}
           {t} (reg_available : list REG)
  : ZRange.type.base.option.interp (type.final_codomain t) -> (ErrorT BoundsDataError (base_reg_data (type.final_codomain t)) * list REG (* remaining *)) + nat (* how many more registers needed? *)
  := make_base_reg_data false reg_available.

Fixpoint reg_list_of_input_reg_data {t} : type.for_each_lhs_of_arrow reg_data t -> list (REG * nat)
  := match t return type.for_each_lhs_of_arrow reg_data t -> list (REG * nat) with
     | type.base t => fun 'tt => []
     | type.arrow A B
       => fun data : reg_data A * type.for_each_lhs_of_arrow reg_data B
          => reg_list_of_reg_data (fst data) ++ @reg_list_of_input_reg_data B (snd data)
     end.

(** the var type for equivalence checking *)
(** right now we just reuse reg_data, but this should be changed (TODO for Andres) *)
Local Notation var t := (reg_data t) (only parsing).

Definition reg_data_to_var {t} (v : reg_data t) : var t
  := v.

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
           let stack_size : nat := N.to_nat assembly_stack_size in
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
