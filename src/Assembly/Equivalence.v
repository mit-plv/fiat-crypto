Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Parse.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.Strings.String.
Require Import Crypto.Language.API.
Require Import Crypto.Language.APINotations.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Crypto.Stringification.Language.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ListUtil.
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
| Internal_error_output_load_failed (_ : list (option (list idx))) (_ : symbolic_state)
| Internal_error_extra_input_arguments (t : API.type) (unused_arguments : list (idx + list idx))
| Not_enough_registers (num_given num_extra_needed : nat)
| Incorrect_array_input_dag_node
| Incorrect_Z_input_dag_node
| Not_enough_input_dag_nodes (t : API.type)
| Expected_const_in_reference_code (_ : idx)
| Expected_power_of_two (w : N) (_ : idx)
| Unknown_array_length (t : base.type)
| Invalid_arrow_type (t : API.type)
| Invalid_argument_type (t : API.type)
| Invalid_return_type (t : base.type)
| Invalid_higher_order_application {var} {s d : API.type} (f : API.expr (var:=var) (s -> d)) (x : API.expr (var:=var) s)
| Invalid_higher_order_let {var} {s : API.type} (x : API.expr (var:=var) s)
| Unhandled_identifier {t} (idc : ident t)
| Unhandled_cast (_ _ : Z)
| Unable_to_unify (_ _ : list (idx + list idx)) (_ : symbolic_state)
.

Global Instance show_lines_EquivalenceCheckingError : ShowLines EquivalenceCheckingError
  := fun err => match err with
                | Symbolic_execution_failed l r
                  => ["Symbolic execution failed: " ++ show l]%string ++ ["Combined state:"] ++ show_lines r
                | Internal_error_output_load_failed l r => ["Internal error. Output load failed: " ++ show l]%string ++ ["Combined state:"] ++ show_lines r
                | Internal_error_extra_input_arguments t unused_arguments
                  => ["Internal error. Too many input arguments for type " ++ show t ++ ". Unused arguments: " ++ show unused_arguments]%string
                | Not_enough_registers num_given num_extra_needed
                  => ["Not enough registers available for storing input and output (given " ++ show num_given ++ ", needed an additional " ++ show num_extra_needed ++ "."]%string
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
                | Unable_to_unify asm_output PHOAS_output r
                  => ["Unable to unify: " ++ show asm_output ++ " == " ++ show PHOAS_output]%string ++ show_lines r
                end%list.
Global Instance show_EquivalenceCheckingError : Show EquivalenceCheckingError
  := fun err => String.concat String.NewLine (show_lines err).

(** FIXME: pick better definitions *)
Definition symbol := N.
Definition gensym_state := N.
Definition gensym_state_init : gensym_state := 0%N.
Definition gensym (st : gensym_state) : symbol * gensym_state := (st, N.succ st).

Definition empty_dag : dag := nil.
Definition merge_symbol (s:symbol) (d:dag) : idx * dag := merge_node ((old 64%N s), nil) d.
Definition merge_literal (l:Z) (d:dag) : idx * dag := merge_node ((const l, nil)) d.

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

Definition build_inputarray (st : dag * gensym_state) (len : nat)  : list idx * (dag * gensym_state) :=
  List.fold_left (fun '(idxs, (d, st)) _
                    => let '(n, st) := gensym st in
                       let '(idx, d) := merge_symbol n d in
                       (idx :: idxs, (d, st)))
                   (List.seq 0 len)
                   ([], st).

Fixpoint build_inputs (st : dag * gensym_state) (types : type_spec) : list (idx + list idx) * (dag * gensym_state)
  := match types with
     | [] => ([], st)
     | None :: tys
       => let '(d, st) := st in
          let '(n, st) := gensym st in
          let '(idx, d) := merge_symbol n d in
          let '(rest, (d, st)) := build_inputs (d, st) tys in
          (inl idx :: rest, (d, st))
     | Some len :: tys
       => let '(idxs, (d, st)) := build_inputarray st len in
          let '(rest, (d, st)) := build_inputs (d, st) tys in
          (inr idxs :: rest, (d, st))
     end.

Fixpoint build_base_addresses {T} (st : dag * gensym_state) (items : list (idx + T)) : list (idx * option T) * (dag * gensym_state)
  := match items with
     | [] => ([], st)
     | inr x :: xs
       => let '(d, st) := st in
          let '(n, st) := gensym st in
          let '(idx, d) := merge_symbol n d in
          let '(rest, (d, st)) := build_base_addresses (d, st) xs in
          ((idx, Some x) :: rest, (d, st))
     | inl idx :: xs =>
          let '(rest, st) := build_base_addresses st xs in
          ((idx, None) :: rest, st)
     end.

Fixpoint dag_gensym_n (n : nat) (s : dag * gensym_state) : list symbol * (dag * gensym_state) :=
  match n with
  | O => (nil, s)
  | S n =>
      let (d, s) := s in
      let (sym, s) := gensym s in
      let (i, d) := merge_symbol sym d in
      let '(rest, (d, s)) := dag_gensym_n n (d, s) in
      (cons i rest, (d, s))
  end.

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

Definition symex_asm_func
           (d : dag) (gensym_st : gensym_state) (output_types : type_spec) (stack_size : nat)
           (inputs : list (idx + list idx)) (reg_available : list REG) (asm : Lines)
  : ErrorT EquivalenceCheckingError (list (idx + list idx) * symbolic_state)
  := let '(output_placeholders, (d, gensym_st)) := build_inputs (d, gensym_st) output_types in
      let '(rsp_idx, gensym_st) := gensym gensym_st in
      let '(stack_placeholders, (d, gensym_st)) := build_inputarray (d, gensym_st) stack_size in
      let '(asminputs, (d, gensym_st)) := build_base_addresses (d, gensym_st) (output_placeholders ++ inputs) in
      let '(initial_reg_idxs, (d, gensym_st)) := dag_gensym_n 16 (d, gensym_st) in
      let s0 :=
        {|
          dag_state := d;
          symbolic_reg_state := Tuple.from_list_default None 16 (List.map Some initial_reg_idxs);
          symbolic_mem_state := [];
          symbolic_flag_state := Tuple.repeat None 6;
        |} in

      match
        (argptrs <- mapM (fun '(r, (base, oarr)) => _ <- SetReg r base; (* note: overwrites initial value *)
          match oarr with None => Symbolic.ret None
          | Some idxs =>
              addrs <- mapM (fun '(i, idx) =>
                offset <- Symbolic.App ((const (8*Z.of_nat i)), nil);
                addr <- Symbolic.App (add 64, [base; offset]);
                (fun s => Success (addr, update_mem_with s (cons (addr,idx))))
              ) (List.enumerate idxs);
              Symbolic.ret (Some addrs)
          end) (List.combine reg_available asminputs);
        _ <- SetReg rsp rsp_idx;
        _ <- mapM_ (fun '(i, idx) =>
            a <- @Address (64%N) {| mem_reg := rsp; mem_offset := Some (Z.opp (Z.of_nat(8*S i))); mem_is_byte := false; mem_extra_reg:=None |};
            (fun s => Success (tt, update_mem_with s (cons (a,idx))))
          ) (List.enumerate stack_placeholders);
        _ <- mapM_ SymexNormalInstruction (Option.List.map invert_rawline asm);
        Symbolic.ret argptrs)%N%x86symex s0
      with
      | Error (e, s) => Error (Symbolic_execution_failed e s)
      | Success (argptrs, s) =>
          let outputaddrs : list (option (list idx))  := firstn (length argptrs - length inputs) argptrs in
          match Option.List.lift (List.map (fun ocells =>
            match ocells with
            | None => None
            | Some cells => Option.List.lift (List.map (fun i => load i s) cells)
            end
          ) outputaddrs) with
          | None => Error (Internal_error_output_load_failed outputaddrs s)
          | Some asm_output =>
              Success (List.map inr asm_output, s)
          end
      end.

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

    Definition check_equivalence : ErrorT EquivalenceCheckingError unit :=
      let reg_available := assembly_calling_registers (* registers available for calling conventions *) in
      let stack_size : nat := N.to_nat (assembly_stack_size asm) in
      let d := empty_dag in
      let gensym_st := gensym_state_init in
      input_types <- simplify_input_type t arg_bounds;
      output_types <- simplify_base_type (type.final_codomain t) out_bounds;
      let '(inputs, (d, gensym_st)) := build_inputs (d, gensym_st) input_types in

      PHOAS_output <- symex_PHOAS expr inputs d;
      let '(PHOAS_output, d) := PHOAS_output in

      symevaled_asm <- symex_asm_func d gensym_st output_types stack_size inputs reg_available asm;
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
