(** * Exact reification of PHOAS Representation of Gallina *)
(** The reification procedure goes through [InputSyntax], which allows
    judgmental equality of the denotation of the reified term. *)
Require Import Coq.Strings.String.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Relations.
Require Import Crypto.Compilers.InputSyntax.
Require Crypto.Compilers.Tuple.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.DebugPrint.
Require Import Crypto.Util.SideConditions.CorePackages.
(*Require Import Crypto.Util.Tactics.PrintContext.*)
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SubstLet.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.TransparentAssert.

(** Change this with [Ltac reify_debug_level ::= constr:(1).] to get
    more debugging. *)
Ltac reify_debug_level := constr:(0).
Module Import ReifyDebugNotations.
  Export Compilers.Syntax.Notations.
  Export Util.LetIn.
  Open Scope string_scope.
End ReifyDebugNotations.

Tactic Notation "debug_enter_reify_idtac" ident(funname) uconstr(e)
  := idtac funname ": Attempting to reify:" e.
Tactic Notation "debug_leave_reify_success_idtac" ident(funname) uconstr(e) uconstr(ret)
  := idtac funname ": Success in reifying:" e "as" ret.
Tactic Notation "debug_leave_reify_failure_idtac" ident(funname) uconstr(e)
  := idtac funname ": Failure in reifying:" e.
Ltac check_debug_level_then_Set _ :=
  let lvl := reify_debug_level in
  lazymatch type of lvl with
  | nat => constr:(Set)
  | ?T => constr_run_tac ltac:(fun _ => idtac "Error: reify_debug_level should have type nat but instead has type" T)
  end.
Ltac debug0 tac :=
  constr_run_tac tac.
Ltac debug1 tac :=
  let lvl := reify_debug_level in
  lazymatch lvl with
  | S _ => constr_run_tac tac
  | _ => check_debug_level_then_Set ()
  end.
Ltac debug2 tac :=
  let lvl := reify_debug_level in
  lazymatch lvl with
  | S (S _) => constr_run_tac tac
  | _ => check_debug_level_then_Set ()
  end.
Ltac debug3 tac :=
  let lvl := reify_debug_level in
  lazymatch lvl with
  | S (S (S _)) => constr_run_tac tac
  | _ => check_debug_level_then_Set ()
  end.
Ltac debug_enter_reify_flat_type e := debug2 ltac:(fun _ => debug_enter_reify_idtac reify_flat_type e).
Ltac debug_enter_reify_type e := debug2 ltac:(fun _ => debug_enter_reify_idtac reify_type e).
Ltac debug_enter_reifyf e := debug2 ltac:(fun _ => debug_enter_reify_idtac reifyf e).
Ltac debug_leave_reifyf_success e ret := debug3 ltac:(fun _ => debug_leave_reify_success_idtac reifyf e ret).
Ltac debug_leave_reifyf_failure e
  := let dummy := debug0 ltac:(fun _ => debug_leave_reify_failure_idtac reifyf e) in
     constr:(I : I).
Ltac debug_leave_reify_flat_type_failure e
  := let dummy := debug0 ltac:(fun _ => debug_leave_reify_failure_idtac reify_flat_type e) in
     constr:(I : I).
Tactic Notation "idtac_reifyf_case" ident(case) :=
  idtac "reifyf:" case.
Ltac debug_reifyf_case tac :=
  debug3 tac.
Ltac debug_enter_reify_abs e := debug2 ltac:(fun _ => debug_enter_reify_idtac reify_abs e).

Ltac refresh x :=
  (* Work around Coq 8.5 and 8.6 bug *)
  (* <https://coq.inria.fr/bugs/show_bug.cgi?id=4998> *)
  (* Avoid re-binding the Gallina variable referenced by Ltac [x] *)
  (* even if its Gallina name matches a Ltac in this tactic. *)
  let maybe_x := fresh x in
  let maybe_x := fresh x in
  let maybe_x := fresh x in
  let not_x := fresh x in
  not_x.
Class reify_internal {varT} (var : varT) {eT} (e : eT) {T : Type} := Build_reify_internal : T.
Class reify {varT} (var : varT) {eT} (e : eT) {T : Type} := Build_reify : T.
#[global]
Typeclasses Opaque reify_internal reify.
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
(** Override this to get a faster [reify_type] *)
Ltac base_reify_type T :=
  strip_type_cast (_ : reify type T).
Ltac reify_base_type T := base_reify_type T.
Ltac reify_flat_type T :=
  let dummy := debug_enter_reify_flat_type T in
  match goal with
  | _
    => lazymatch T with
       | prod ?A ?B
         => let a := reify_flat_type A in
            let b := reify_flat_type B in
            constr:(@Prod _ a b)
       | Syntax.interp_type _ (Tflat ?T)
         => T
       | Syntax.interp_flat_type _ ?T
         => T
       | Syntax.tuple _ _
         => T
       | Syntax.tuple' _ _
         => T
       | Tuple.tuple ?A ?n
         => let a := reify_flat_type A in
            constr:(@Syntax.tuple _ a n)
       | Tuple.tuple' ?A ?n
         => let a := reify_flat_type A in
            constr:(@Syntax.tuple' _ a n)
       | unit
         => Unit
       | _
         => let v := reify_base_type T in
            constr:(@Tbase _ v)
       end
  | _ => debug_leave_reify_flat_type_failure T
  end.
Ltac reify_input_type T :=
  let dummy := debug_enter_reify_type T in
  lazymatch T with
  | (?A -> ?B)%type
    => let a := reify_flat_type A in
       let b := reify_input_type B in
       constr:(@Arrow _ a b)
  | InputSyntax.interp_type _ ?T
    => T
  end.
Ltac reify_type T :=
  let dummy := debug_enter_reify_type T in
  lazymatch T with
  | (?A -> ?B)%type
    => let a := reify_flat_type A in
       let b := reify_flat_type B in
       constr:(@Syntax.Arrow _ a b)
  | Syntax.interp_type _ ?T
    => T
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
| context_value {TF} (resF : TF) {argT} (arg : argT)
| op_info {T} (res : T)
| reification_unsuccessful.

(** Override this to get a faster [reify_op] *)
Ltac base_reify_op op op_head expr :=
  let r := constr:(_ : reify_op op op_head _ _) in
  type of r.
Ltac reify_op op op_head expr :=
  let t := base_reify_op op op_head expr in
  constr:(op_info t).

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
  let mkLetIn ex eC := constr:(LetIn (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) ex eC) in
  let mkPair ex ey := constr:(Pair (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) ex ey) in
  let mkVar T ex := constr:(Var (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) (t:=T) ex) in
  let mkConst T ex := constr:(Const (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) (t:=T) ex) in
  let mkOp T retT op_code args := constr:(Op (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) (t1:=T) (tR:=retT) op_code args) in
  let mkMatchPair tC ex eC := constr:(MatchPair (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) (tC:=tC) ex eC) in
  let mkFst ex := constr:(Fst (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) ex) in
  let mkSnd ex := constr:(Snd (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) ex) in
  let reify_pretag := constr:(@exprf base_type_code interp_base_type op) in
  let reify_tag := constr:(reify_pretag var) in
  let dummy := debug_enter_reifyf e in
  match goal with
  | [ re := ?rev : reify reify_tag e |- _ ] =>
    (* fast path *)
    let dummy := debug_reifyf_case ltac:(fun _ => idtac_reifyf_case hyp) in
    let ret := rev in
    let dummy := debug_leave_reifyf_success e ret in
    ret
  | _ =>
    let ret :=
        lazymatch e with
        | let x := ?ex in @?eC x =>
          let dummy := debug_reifyf_case ltac:(fun _ => idtac_reifyf_case let_in) in
          let ex := reify_rec ex in
          let eC := reify_rec eC in
          mkLetIn ex eC
        | (dlet x := ?ex in @?eC x) =>
          let dummy := debug_reifyf_case ltac:(fun _ => idtac_reifyf_case dlet_in) in
          let ex := reify_rec ex in
          let eC := reify_rec eC in
          mkLetIn ex eC
        | pair ?a ?b =>
          let dummy := debug_reifyf_case ltac:(fun _ => idtac_reifyf_case pair) in
          let a := reify_rec a in
          let b := reify_rec b in
          mkPair a b
        | (fun x : ?T => ?C) =>
          let dummy := debug_reifyf_case ltac:(fun _ => idtac_reifyf_case function) in
          let t := reify_flat_type T in
          (* Work around Coq 8.5 and 8.6 bug *)
          (* <https://coq.inria.fr/bugs/show_bug.cgi?id=4998> *)
          (* Avoid re-binding the Gallina variable referenced by Ltac [x] *)
          (* even if its Gallina name matches a Ltac in this tactic. *)
          let not_x := refresh x in
          let C' := match constr:(Set) with
                    | _ => constr:(fun (x : T) (not_x : var t) (_ : reify_var_for_in_is base_type_code x t not_x) =>
                                     (_ : reify_internal reify_tag C)) (* [C] here is an open term that references "x" by name *)
                    | _ => constr_run_tac_fail ltac:(fun _ => idtac "Error: reifyf: Failed to reify by typeclasses:" e)
                    end in
          match constr:(Set) with
          | _ => lazymatch C'
                 with fun _ v _ => @?C v => C end
          | _ => constr_run_tac_fail ltac:(fun _ => idtac "Error: reifyf: Failed to eliminate function dependencies of:" C')
          end
        | match ?ev with pair a b => @?eC a b end =>
          let dummy := debug_reifyf_case ltac:(fun _ => idtac_reifyf_case matchpair) in
          let T := type of eC in
          let t := (let T := match (eval cbv beta in T) with _ -> _ -> ?T => T end in reify_flat_type T) in
          let v := reify_rec ev in
          let C := reify_rec eC in
          let ret := mkMatchPair t v C in
          ret
        | @fst ?A ?B ?ev =>
          let dummy := debug_reifyf_case ltac:(fun _ => idtac_reifyf_case fst) in
          let v := reify_rec ev in
          mkFst v
        | @snd ?A ?B ?ev =>
          let dummy := debug_reifyf_case ltac:(fun _ => idtac_reifyf_case snd) in
          let v := reify_rec ev in
          mkSnd v
        | ?x =>
          let dummy := debug_reifyf_case ltac:(fun _ => idtac_reifyf_case generic) in
          let t := type of x in
          let t := reify_flat_type t in
          let retv := match constr:(Set) with
                      | _ => let retv := reifyf_var x mkVar in constr:(finished_value retv)
                      | _ => let op_head := head x in
                             reify_op op op_head x
                      | _ => lazymatch x with
                             | ?F ?args
                               => lazymatch goal with
                                  | [ rF : forall x not_x, reify reify_tag (F x) |- _ ]
                                    => constr:(context_value rF args)
                                  | [ rF : forall var' x (not_x : var' _), reify (reify_pretag var') (F x) |- _ ]
                                    => constr:(context_value (rF var) args)
                                  end
                             end
                      | _ => let c := mkConst t x in
                             constr:(finished_value c)
                      | _ => constr:(reification_unsuccessful)
                      end in
          lazymatch retv with
          | finished_value ?v => v
          | context_value ?rFH ?eargs
            => let dummy := debug_reifyf_case ltac:(fun _ => idtac_reifyf_case context_value) in
               let args := reify_rec eargs in
               let F_head := head rFH in
               let F := lazymatch (eval cbv beta delta [F_head] in rFH) with
                        | fun _ => ?C => C
                        end in
               mkLetIn args F
          | op_info (reify_op _ _ ?nargs ?op_code)
            =>
            let tR := (let tR := type of x in reify_flat_type tR) in
               lazymatch nargs with
               | 1%nat
                 => lazymatch x with
                    | ?f ?x0
                      => let a0T := (let t := type of x0 in reify_flat_type t) in
                         let a0 := reify_rec x0 in
                         mkOp a0T tR op_code a0
                    end
               | 2%nat
                 => lazymatch x with
                    | ?f ?x0 ?x1
                      => let a0T := (let t := type of x0 in reify_flat_type t) in
                         let a0 := reify_rec x0 in
                         let a1T := (let t := type of x1 in reify_flat_type t) in
                         let a1 := reify_rec x1 in
                         let args := mkPair a0 a1 in
                         mkOp (@Prod _ a0T a1T) tR op_code args
                    end
               | 3%nat
                 => lazymatch x with
                    | ?f ?x0 ?x1 ?x2
                      => let a0T := (let t := type of x0 in reify_flat_type t) in
                         let a0 := reify_rec x0 in
                         let a1T := (let t := type of x1 in reify_flat_type t) in
                         let a1 := reify_rec x1 in
                         let a2T := (let t := type of x2 in reify_flat_type t) in
                         let a2 := reify_rec x2 in
                         let args := let a01 := mkPair a0 a1 in mkPair a01 a2 in
                         mkOp (@Prod _ (@Prod _ a0T a1T) a2T) tR op_code args
                    end
               | 4%nat
                 => lazymatch x with
                    | ?f ?x0 ?x1 ?x2 ?x3
                      => let a0T := (let t := type of x0 in reify_flat_type t) in
                         let a0 := reify_rec x0 in
                         let a1T := (let t := type of x1 in reify_flat_type t) in
                         let a1 := reify_rec x1 in
                         let a2T := (let t := type of x2 in reify_flat_type t) in
                         let a2 := reify_rec x2 in
                         let a3T := (let t := type of x3 in reify_flat_type t) in
                         let a3 := reify_rec x3 in
                         let args := let a01 := mkPair a0 a1 in let a012 := mkPair a01 a2 in mkPair a012 a3 in
                         mkOp (@Prod _ (@Prod _ (@Prod _ a0T a1T) a2T) a3T) tR op_code args
                    end
               | _ => constr_run_tac_fail ltac:(fun _ => idtac "Error: Unsupported number of operation arguments in reifyf:" nargs)
               end
          | reification_unsuccessful
            => constr_run_tac_fail ltac:(fun _ => idtac "Error: Failed to reify:" x)
          end
        end in
    let dummy := debug_leave_reifyf_success e ret in
    ret
  | _ => debug_leave_reifyf_failure e
  end.

Ltac do_reifyf_goal _ :=
  debug_enter_reify_rec;
  let e := lazymatch goal with
           | [ |- reify (@exprf ?base_type_code ?interp_base_type ?op ?var) ?e ]
             => reifyf base_type_code interp_base_type op var e
           | [ |- reify_internal (@exprf ?base_type_code ?interp_base_type ?op ?var) ?e ]
             => reifyf base_type_code interp_base_type op var e
           end in
  debug_leave_reify_rec e;
  eexact e.

Global Hint Extern 0 (reify (@exprf ?base_type_code ?interp_base_type ?op ?var) ?e)
=> do_reifyf_goal () : typeclass_instances.
Global Hint Extern 0 (reify_internal (@exprf ?base_type_code ?interp_base_type ?op ?var) ?e)
=> do_reifyf_goal () : typeclass_instances.

(** For reification including [Abs] *)
Class reify_abs_internal {varT} (var : varT) {eT} (e : eT) {T : Type} := Build_reify_abs_internal : T.
Class reify_abs {varT} (var : varT) {eT} (e : eT) {T : Type} := Build_reify_abs : T.
#[global]
Typeclasses Opaque reify_abs_internal reify_abs.
Ltac reify_abs base_type_code interp_base_type op var e :=
  let reify_rec e := reify_abs base_type_code interp_base_type op var e in
  let reifyf_term e := reifyf base_type_code interp_base_type op var e in
  let mkReturn ef := constr:(Return (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) ef) in
  let mkAbs src ef := constr:(Abs (base_type_code:=base_type_code) (interp_base_type:=interp_base_type) (op:=op) (var:=var) (src:=src) ef) in
  let reify_pretag := constr:(@exprf base_type_code interp_base_type op) in
  let reify_tag := constr:(reify_pretag var) in
  let dummy := debug_enter_reify_abs e in
  lazymatch goal with
  | [ re := ?rev : forall var' (x : ?T) (not_x : var' _), reify (reify_pretag var') (e x) |- _ ] =>
    (* fast path *)
    let t := reify_flat_type T in
    let F := lazymatch (eval cbv beta in (rev var)) with
             | fun _ => ?C => C
             end in
    mkAbs t F
  | _ =>
    lazymatch e with
    | (fun x : ?T => ?C) =>
      let t := reify_flat_type T in
      let not_x := refresh x in
      let C' := match constr:(Set) with
                | _ => constr:(fun (x : T) (not_x : var t) (_ : reify_var_for_in_is base_type_code x t not_x) =>
                                 (_ : reify_abs_internal reify_tag C)) (* [C] here is an open term that references "x" by name *)
                | _ => constr_run_tac_fail ltac:(fun _ => idtac "Error: reify_abs: Failed to reify by typeclasses:" e)
                end in
      let C := match constr:(Set) with
               | _ => lazymatch C'
                      with fun _ v _ => @?C v => C end
               | _ => constr_run_tac_fail ltac:(fun _ => idtac "Error: reify_abs: Failed to eliminate function dependencies of:" C')
               end in
      mkAbs t C
    | ?x =>
      let xv := reifyf_term x in
      mkReturn xv
    end
  end.

Ltac do_reify_abs_goal _ :=
  debug_enter_reify_rec;
  let e := lazymatch goal with
           | [ |- reify_abs (@exprf ?base_type_code ?interp_base_type ?op ?var) ?e ]
             => reify_abs base_type_code interp_base_type op var e
           | [ |- reify_abs_internal (@exprf ?base_type_code ?interp_base_type ?op ?var) ?e ]
             => reify_abs base_type_code interp_base_type op var e
           end in
  debug_leave_reify_rec e;
  eexact e.

Global Hint Extern 0 (reify_abs (@exprf ?base_type_code ?interp_base_type ?op ?var) ?e)
=> do_reify_abs_goal () : typeclass_instances.
Global Hint Extern 0 (reify_abs_internal (@exprf ?base_type_code ?interp_base_type ?op ?var) ?e)
=> do_reify_abs_goal () : typeclass_instances.

Ltac Reify' base_type_code interp_base_type op e :=
  lazymatch constr:(fun (var : flat_type base_type_code -> Type) => (_ : reify_abs_internal (@exprf base_type_code interp_base_type op var) e)) with
    (fun var => ?C) => constr:(fun (var : flat_type base_type_code -> Type) => C) (* copy the term but not the type cast *)
  end.
Ltac Reify base_type_code interp_base_type op make_const e :=
  let r := Reify' base_type_code interp_base_type op e in
  let r := lazymatch type of r with
           | forall var, exprf _ _ _ _ => constr:(fun var => Abs (src:=Unit) (fun _ => r var))
           | _ => r
           end in
  constr:(@InputSyntax.Compile base_type_code interp_base_type op make_const _ r).

Ltac rhs_of_goal :=
  lazymatch goal with
  | [ |- ?R ?LHS ?RHS ] => RHS
  | [ |- forall x, ?R (@?LHS x) (@?RHS x) ] => RHS
  end.

Ltac transitivity_tt term :=
  first [ transitivity term
        | transitivity (term tt)
        | let x := fresh in intro x; transitivity (term x); revert x  ].

Ltac Reify_rhs_gen Reify prove_interp_compile_correct interp_op try_tac :=
  Tuple.unfold_flat_interp_tuple ();
  let rhs := rhs_of_goal in
  let RHS := Reify rhs in
  let RHS' := (eval vm_compute in RHS) in
  transitivity_tt (Syntax.Interp interp_op RHS');
  [
  | transitivity_tt (Syntax.Interp interp_op RHS);
    [ lazymatch goal with
      | [ |- ?R ?x ?y ]
        => cut (x = y)
      | [ |- forall k, ?R (?x k) (?y k) ]
        => cut (x = y)
      end;
      [ let H := fresh in
        intro H; rewrite H; reflexivity
      | apply f_equal; vm_compute; reflexivity ]
    | intros; etransitivity; (* first we strip off the [InputSyntax.Compile]
                                bit; Coq is bad at inferring the type, so we
                                help it out by providing it *)
      [ cbv [InputSyntax.compilet];
        prove_interp_compile_correct ()
      | try_tac
          ltac:(fun _
                => (* now we unfold the interpretation function,
                      including the parameterized bits; we assume that
                      [hnf] is enough to unfold the interpretation
                      functions that we're parameterized over. *)
                  clear;
                  abstract (
                      lazymatch goal with
                      | [ |- context[@InputSyntax.Interp ?base_type_code ?interp_base_type ?op ?interp_op ?t ?e] ]
                        => let interp_base_type' := (eval hnf in interp_base_type) in
                           let interp_op' := (eval hnf in interp_op) in
                           change interp_base_type with interp_base_type';
                           change interp_op with interp_op'
                      end;
                      subst_let;
                      cbv iota beta delta [InputSyntax.Interp interp_type interp_type_gen interp_type_gen_hetero interp_flat_type interp interpf InputSyntax.Fst InputSyntax.Snd]; reflexivity)) ] ] ].

Ltac prove_compile_correct_using tac :=
  fun _ => intros;
           lazymatch goal with
           | [ |- @Syntax.Interp ?base_type_code ?interp_base_type ?op ?interp_op _ (@Compile _ _ _ ?make_const (InputSyntax.Arrow ?src (Tflat ?dst)) ?e) ?x = _ ]
             => apply (fun pf => @InputSyntax.Compile_correct base_type_code interp_base_type op make_const interp_op pf src dst e x);
                solve [ tac () ]
           | [ |- @Syntax.Interp ?base_type_code ?interp_base_type ?op ?interp_op _ (@Compile _ _ _ ?make_const (Tflat ?T) ?e) ?x = _ ]
             => apply (fun pf => @InputSyntax.Compile_flat_correct_flat base_type_code interp_base_type op make_const interp_op pf T e x);
                solve [ tac () ]
           end.
Ltac prove_compile_correct :=
  prove_compile_correct_using
    ltac:(fun _ => let T := fresh in intro T; destruct T; reflexivity).

Ltac Reify_rhs base_type_code interp_base_type op make_const interp_op :=
  Reify_rhs_gen
    ltac:(Reify base_type_code interp_base_type op make_const)
           prove_compile_correct
           interp_op
           ltac:(fun tac => tac ()).

Definition Reify_evar_package
           {base_type_code interp_base_type op}
           (make_const : forall t : base_type_code,
               interp_base_type t -> op ()%ctype (Tbase t))
           (interp_op : forall s d : flat_type base_type_code, op s d -> interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d)
           {t}
           (f : Syntax.interp_type interp_base_type t)
  := evar_rel_package
       f (Compilers.Syntax.Expr _ op t)
       (fun e f
        => forall x, Compilers.Syntax.Interp interp_op e x = f x).

Definition Interp_Reify_evar_package
           {base_type_code interp_base_type op make_const interp_op t f}
           (pkg : @Reify_evar_package base_type_code interp_base_type op make_const interp_op t f)
  : forall x, Compilers.Syntax.Interp interp_op (val pkg) x = f x
  := evar_package_pf pkg.

Ltac autosolve else_tac :=
  lazymatch goal with
  | [ |- @Reify_evar_package ?base_type_code ?interp_base_type ?op ?make_const ?interp_op _ _ ]
    => eexists; cbv beta; Reify_rhs base_type_code interp_base_type op make_const interp_op; reflexivity
  | _ => else_tac ()
  end.

Ltac SideConditions.CorePackages.autosolve ::= autosolve.

(** Reification of context variables of the form [F := _ :
    Syntax.interp_type _ _] *)
Ltac unique_reify_context_variable base_type_code interp_base_type op F Fbody rT :=
  let reify_pretag := constr:(@exprf base_type_code interp_base_type op) in
  lazymatch goal with
  | [ H : forall var x not_x, reify _ (F x) |- _ ]
    => fail
  | _
    => let H' := fresh in
       let src := lazymatch rT with Syntax.Arrow ?src ?dst => src end in
       lazymatch Fbody with
       | fun x : ?X => ?Fbody'
         => let not_x := refresh x in
            let rF := lazymatch constr:(fun var' (x : X) (not_x : var' src) (_ : reify_var_for_in_is base_type_code x src not_x)
                                        => (_ : reify_internal (reify_pretag var') Fbody'))
                      with
                      | fun (var' : ?VAR) (x : ?X) (v : ?V) _ => ?C
                        => constr:(fun (var' : VAR) (v : V) => C)
                      end in
            let F' := fresh F in
            pose rF as F';
            pose ((fun var (x : X) => F' var) : forall var (x : X) (not_x : var src), reify (reify_pretag var) (F x)) as H';
            cbv beta in (value of H')
       end
  end.
Ltac prereify_context_variables interp_base_type :=
  (** N.B. this assumes that [interp_base_type] is a transparent
     definition; minor reorganization may be needed if this is changed
     (moving the burden of reifying [interp_base_type T] to
     [reify_base_type], rather than keeping it here) *)
  cbv beta iota delta [interp_base_type] in *.
Ltac reify_context_variable base_type_code interp_base_type op :=
  (** [match reverse] so that we respect the chain of dependencies in
      context variables; otherwise we're going to be trying the last
      context variable many times, and bottlenecking there. *)
  match reverse goal with
  | [ F := ?Fbody : Syntax.interp_type _ ?rT  |- _ ]
    => unique_reify_context_variable base_type_code interp_base_type op F Fbody rT
  end.
Ltac lazy_reify_context_variable base_type_code interp_base_type op :=
  lazymatch reverse goal with
  | [ F := ?Fbody : Syntax.interp_type _ ?rT  |- _ ]
    => unique_reify_context_variable base_type_code interp_base_type op F Fbody rT
  end.
Ltac reify_context_variables base_type_code interp_base_type op :=
  prereify_context_variables interp_base_type;
  repeat reify_context_variable base_type_code interp_base_type op.
