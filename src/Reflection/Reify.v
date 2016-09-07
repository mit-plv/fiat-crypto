(** * Exact reification of PHOAS Representation of Gallina *)
(** The reification procedure goes through [InputSyntax], which allows
    judgmental equality of the denotation of the reified term. *)
Require Import Coq.Strings.String.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.InputSyntax.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

Class reify {varT} (var : varT) {eT} (e : eT) {T : Type} := Build_reify : T.
Definition reify_var_for_in_is base_type_code {T} (x : T) (t : flat_type base_type_code) {eT} (e : eT) := False.
Arguments reify_var_for_in_is _ {T} _ _ {eT} _.

(** [reify] assumes that operations can be reified via the [reify_op]
    typeclass, which gets passed the type family of operations, the
    expression which is headed by an operation, and expects resolution
    to fill in a number of arguments (which [reifyf] will
    automatically curry), as well as the reified operator.

    We also assume that types can be reified via the [reify] typeclass
    with arguments [reify type <type to be reified>]. *)
Class reify_op {opTF} (op_family : opTF) {opExprT} (opExpr : opExprT) (nargs : nat) {opT} (reified_op : opT)
  := Build_reify_op : True.
Ltac strip_type_cast term := lazymatch term with ?term' => term' end.
Ltac reify_type T :=
  lazymatch T with
  | (?A -> ?B)%type
    => let a := reify_type A in
       let b := reify_type B in
       constr:(@Arrow _ a b)
  | prod ?A ?B
    => let a := reify_type A in
       let b := reify_type B in
       constr:(@Prod _ a b)
  | _
    => let v := strip_type_cast (_ : reify type T) in
       constr:(Tbase v)
  end.
Ltac reify_base_type T :=
  let t := reify_type T in
  lazymatch t with
  | Tbase ?t => t
  | ?t => t
  end.

Ltac reifyf_var x mkVar :=
  lazymatch goal with
  | _ : reify_var_for_in_is _ x ?t ?v |- _ => mkVar t v
  | _ => lazymatch x with
         | fst ?x' => reifyf_var x' ltac:(fun t v => lazymatch t with
                                                     | Prod ?A ?B => mkVar A (fst v)
                                                     end)
         | snd ?x' => reifyf_var x' ltac:(fun t v => lazymatch t with
                                                     | Prod ?A ?B => mkVar B (snd v)
                                                     end)
         end
  end.

Inductive reify_result_helper :=
| finished_value {T} (res : T)
| op_info {T} (res : T)
| reification_unsuccessful.

(** Change this with [Ltac reify_debug_level ::= constr:(1).] to get
    more debugging. *)
Ltac reify_debug_level := constr:(0).
Module Import ReifyDebugNotations.
  Open Scope string_scope.
End ReifyDebugNotations.

Ltac debug_enter_reifyf e :=
  let lvl := reify_debug_level in
  match lvl with
  | S (S _) => cidtac2 "reifyf: Attempting to reify:" e
  | _ => constr:(Set)
  end.
Ltac debug_enter_reify_abs e :=
  let lvl := reify_debug_level in
  match lvl with
  | S (S _) => cidtac2 "reify_abs: Attempting to reify:" e
  | _ => constr:(Set)
  end.

Ltac debug_enter_reify_rec :=
  let lvl := reify_debug_level in
  match lvl with
  | S _ => idtac_goal
  | _ => idtac
  end.
Ltac debug_leave_reify_rec e :=
  let lvl := reify_debug_level in
  match lvl with
  | S _ => idtac "<infomsg>reifyf success:" e "</infomsg>"
  | _ => idtac
  end.

Ltac reifyf base_type_code interp_base_type op var e :=
  let reify_rec e := reifyf base_type_code interp_base_type op var e in
  let mkLet ex eC := constr:(Let (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) ex eC) in
  let mkPair ex ey := constr:(Pair (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) ex ey) in
  let mkVar T ex := constr:(Var (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) (t:=T) ex) in
  let mkConst T ex := constr:(Const (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) (t:=T) ex) in
  let mkOp T retT op_code args := constr:(Op (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) (t1:=T) (tR:=retT) op_code args) in
  let mkMatchPair tC ex eC := constr:(MatchPair (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) (tC:=tC) ex eC) in
  let reify_tag := constr:(@exprf base_type_code interp_base_type op var) in
  let dummy := debug_enter_reifyf e in
  lazymatch e with
  | let x := ?ex in @?eC x =>
    let ex := reify_rec ex in
    let eC := reify_rec eC in
    mkLet ex eC
  | pair ?a ?b =>
    let a := reify_rec a in
    let b := reify_rec b in
    mkPair a b
  | (fun x : ?T => ?C) =>
    let t := reify_type T in
    (* Work around Coq 8.5 and 8.6 bug *)
    (* <https://coq.inria.fr/bugs/show_bug.cgi?id=4998> *)
    (* Avoid re-binding the Gallina variable referenced by Ltac [x] *)
    (* even if its Gallina name matches a Ltac in this tactic. *)
    let maybe_x := fresh x in
    let not_x := fresh x in
    lazymatch constr:(fun (x : T) (not_x : var t) (_ : reify_var_for_in_is base_type_code x t not_x) =>
                        (_ : reify reify_tag C)) (* [C] here is an open term that references "x" by name *)
    with fun _ v _ => @?C v => C end
  | match ?ev with pair a b => @?eC a b end =>
    let t := (let T := match type of eC with _ -> _ -> ?T => T end in reify_type T) in
    let v := reify_rec ev in
    let C := reify_rec eC in
    mkMatchPair t v C
  | ?x =>
    let t := lazymatch type of x with ?t => reify_type t end in
    let retv := match constr:(Set) with
                | _ => let retv := reifyf_var x mkVar in constr:(finished_value retv)
                | _ => let op_head := head x in
                       let r := constr:(_ : reify_op op op_head _ _) in
                       let t := type of r in
                       constr:(op_info t)
                | _ => let c := mkConst t x in
                       constr:(finished_value c)
                | _ => constr:(reification_unsuccessful)
                end in
    lazymatch retv with
    | finished_value ?v => v
    | op_info (reify_op _ _ ?nargs ?op_code)
      => let tR := (let tR := type of x in reify_type tR) in
         lazymatch nargs with
         | 1%nat
           => lazymatch x with
              | ?f ?x0
                => let a0T := (let t := type of x0 in reify_type t) in
                   let a0 := reify_rec x0 in
                   mkOp a0T tR op_code a0
              end
         | 2%nat
           => lazymatch x with
              | ?f ?x0 ?x1
                => let a0T := (let t := type of x0 in reify_type t) in
                   let a0 := reify_rec x0 in
                   let a1T := (let t := type of x1 in reify_type t) in
                   let a1 := reify_rec x1 in
                   let args := mkPair a0 a1 in
                   mkOp (@Prod _ a0T a1T) tR op_code args
              end
         | 3%nat
           => lazymatch x with
              | ?f ?x0 ?x1 ?x2
                => let a0T := (let t := type of x0 in reify_type t) in
                   let a0 := reify_rec x0 in
                   let a1T := (let t := type of x1 in reify_type t) in
                   let a1 := reify_rec x1 in
                   let a2T := (let t := type of x2 in reify_type t) in
                   let a2 := reify_rec x2 in
                   let args := let a01 := mkPair a0 a1 in mkPair a01 a2 in
                   mkOp (@Prod _ (@Prod _ a0T a1T) a2T) tR op_code args
              end
         | _ => cfail2 "Unsupported number of operation arguments in reifyf:"%string nargs
         end
    | reification_unsuccessful
      => cfail2 "Failed to reify:"%string x
    end
  end.

Hint Extern 0 (reify (@exprf ?base_type_code ?interp_base_type ?op ?var) ?e)
=> (debug_enter_reify_rec; let e := reifyf base_type_code interp_base_type op var e in debug_leave_reify_rec e; eexact e) : typeclass_instances.

(** For reification including [Abs] *)
Class reify_abs {varT} (var : varT) {eT} (e : eT) {T : Type} := Build_reify_abs : T.
Ltac reify_abs base_type_code interp_base_type op var e :=
  let reify_rec e := reify_abs base_type_code interp_base_type op var e in
  let reifyf_term e := reifyf base_type_code interp_base_type op var e in
  let mkAbs src ef := constr:(Abs (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) (src:=src) ef) in
  let reify_tag := constr:(@exprf base_type_code interp_base_type op var) in
  let dummy := debug_enter_reify_abs e in
  lazymatch e with
  | (fun x : ?T => ?C) =>
    let t := reify_base_type T in
    (* Work around Coq 8.5 and 8.6 bug *)
    (* <https://coq.inria.fr/bugs/show_bug.cgi?id=4998> *)
    (* Avoid re-binding the Gallina variable referenced by Ltac [x] *)
    (* even if its Gallina name matches a Ltac in this tactic. *)
    let maybe_x := fresh x in
    let not_x := fresh x in
    lazymatch constr:(fun (x : T) (not_x : var (Tbase t)) (_ : reify_var_for_in_is base_type_code x (Tbase t) not_x) =>
                        (_ : reify_abs reify_tag C)) (* [C] here is an open term that references "x" by name *)
    with fun _ v _ => @?C v => mkAbs t C end
  | ?x =>
    reifyf_term x
  end.

Hint Extern 0 (reify_abs (@exprf ?base_type_code ?interp_base_type ?op ?var) ?e)
=> (debug_enter_reify_rec; let e := reify_abs base_type_code interp_base_type op var e in debug_leave_reify_rec e; eexact e) : typeclass_instances.

Ltac Reify' base_type_code interp_base_type op e :=
  lazymatch constr:(fun (var : flat_type base_type_code -> Type) => (_ : reify_abs (@exprf base_type_code interp_base_type op var) e)) with
    (fun var => ?C) => constr:(fun (var : flat_type base_type_code -> Type) => C) (* copy the term but not the type cast *)
  end.
Ltac Reify base_type_code interp_base_type op e :=
  let r := Reify' base_type_code interp_base_type op e in
  constr:(InputSyntax.Compile base_type_code interp_base_type op r).

Ltac lhs_of_goal := lazymatch goal with |- ?R ?LHS ?RHS => LHS end.
Ltac rhs_of_goal := lazymatch goal with |- ?R ?LHS ?RHS => RHS end.

Ltac Reify_rhs base_type_code interp_base_type op interp_op :=
  let rhs := rhs_of_goal in
  let RHS := Reify base_type_code interp_base_type op rhs in
  transitivity (Syntax.Interp interp_op RHS);
  [
  | etransitivity; (* first we strip off the [InputSyntax.Compile]
                      bit; Coq is bad at inferring the type, so we
                      help it out by providing it *)
    [ lazymatch goal with
      | [ |- @Syntax.Interp ?base_type_code ?interp_base_type ?op ?interp_op (@Tflat _ ?t) (@Compile _ _ _ _ ?e) = _ ]
        => exact (@InputSyntax.Compile_correct base_type_code interp_base_type op interp_op t e)
      end
    | ((* now we unfold the interpretation function, including the
          parameterized bits; we assume that [hnf] is enough to unfold
          the interpretation functions that we're parameterized
          over. *)
      lazymatch goal with
      | [ |- @InputSyntax.Interp ?base_type_code ?interp_base_type ?op ?interp_op ?t ?e = _ ]
        => let interp_base_type' := (eval hnf in interp_base_type) in
           let interp_op' := (eval hnf in interp_op) in
           change interp_base_type with interp_base_type';
           change interp_op with interp_op'
      end;
      cbv iota beta delta [InputSyntax.Interp interp_type interp_type_gen interp_flat_type_gen interp interpf]; simplify_projections; reflexivity) ] ].
