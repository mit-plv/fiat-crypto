Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Language.API.
Require Import Crypto.Language.APINotations.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Semantics.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.Equivalence.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Import API.Compilers APINotations.Compilers AbstractInterpretation.ZRange.Compilers.
Import ListNotations.
Local Open Scope list_scope.

(*
Require Import Crypto.Assembly.Parse.
Require Import Crypto.Util.Strings.String.
Require Import Crypto.Stringification.Language.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Import API.Compilers APINotations.Compilers AbstractInterpretation.ZRange.Compilers.
Local Open Scope string_scope.
 *)
Fixpoint eval_base_var (dag : dag) {t : base.type} : base_var t -> API.interp_type (type.base t) -> Prop :=
  match t with
  | base.type.unit => fun _ _ => True
  | base.type.type_base base.type.Z => fun idx v => exists n, Z.of_N n = v /\ eval dag (ExprRef idx) n
  | base.type.prod _ _ => fun a b => eval_base_var dag (fst a) (fst b) /\ eval_base_var dag (snd a) (snd b)
  | base.type.list _ => List.Forall2 (eval_base_var dag)
  | base.type.type_base base.type.nat => @eq _
  | base.type.type_base base.type.zrange => @eq _
  | _ => fun _ _ => False
  end%bool.

Definition eval_var (dag : dag) {t : API.type} : var t -> API.interp_type t -> Prop
  := match t with
     | type.base _ => eval_base_var dag
     | type.arrow _ _ => fun _ _ => False
     end.

Check @symex_expr.
Print symex_T.
(* TODO(Jason?): figure out this lemma statement, reduce proof to ident case *)
(*Theorem symex_expr_correct
        {t} (expr : API.Expr t)
  : ???.
 *)
Theorem symex_PHOAS_PHOAS_correct
        {t} (expr : API.Expr t)
        (input_var_data : type.for_each_lhs_of_arrow var t)
        (d : dag)
        (rets : base_var (type.final_codomain t))
        (d' : dag)
        (Hwf : API.Wf expr)
        (H : symex_PHOAS_PHOAS expr input_var_data d = Success (rets, d'))
        (d_ok : dag_ok d)
  : (forall (input_runtime_var : type.for_each_lhs_of_arrow API.interp_type t),
        type.and_for_each_lhs_of_arrow (@eval_var d) input_var_data input_runtime_var
        -> eval_base_var d' rets (type.app_curried (API.Interp expr) input_runtime_var))
    /\ dag_ok d'
    /\ (forall e n, eval d e n -> eval d' e n).
Proof.
  cbv [symex_PHOAS_PHOAS] in H.
  (* TODO(Jason): Prove this from [symex_expr_correct] *)
Admitted.

Definition eval_idx_Z (dag : dag) (idx : idx) (v : Z) : Prop
  := exists n, Z.of_N n = v /\ eval dag (ExprRef idx) n.
Definition eval_idx_or_list_idx (d : dag) (v1 : idx + list idx) (v2 : Z + list Z)
  : Prop
  := match v1, v2 with
     | inl idx, inl v => eval_idx_Z d idx v
     | inr idxs, inr vs => Forall2 (eval_idx_Z d) idxs vs
     | inl _, inr _ | inr _, inl _ => False
     end.

Fixpoint build_base_runtime (t : base.type) (values : list (Z + list Z))
  : option (base.interp t * list (Z + list Z))
  := match t, values return option (base.interp t * list (Z + list Z)) with
     | base.type.unit, _
       => Some (tt, values)
     | base.type.type_base base.type.Z, inl val :: values
       => Some (val, values)
     | base.type.prod A B, _
       => (vA <- build_base_runtime A values;
          let '(vA, values) := vA in
          vB <- build_base_runtime B values;
          let '(vB, values) := vB in
          Some ((vA, vB), values))
     | base.type.list (base.type.type_base base.type.Z), inr value :: values
       => Some (value, values)
     | base.type.type_base base.type.Z, inr _ :: _
     | base.type.list (base.type.type_base base.type.Z), inl _ :: _
     | base.type.type_base _, []
     | base.type.list _, []
     | base.type.type_base _, _
     | base.type.option _, _
     | base.type.list _, _ :: _
       => None
     end%option.
Definition build_runtime (t : API.type) (values : list (Z + list Z))
  : option (API.interp_type t * list (Z + list Z))
  := match t with
     | type.base t => build_base_runtime t values
     | type.arrow _ _ => None
     end.
Fixpoint build_input_runtime (t : API.type) (values : list (Z + list Z))
  : option (type.for_each_lhs_of_arrow API.interp_type t * list (Z + list Z))
  := match t with
     | type.base _ => Some (tt, values)
     | type.arrow A B
       => (vA <- build_runtime A values;
          let '(vA, values) := vA in
          vB <- build_input_runtime B values;
          let '(vB, values) := vB in
          Some ((vA, vB), values))
     end%option.

Fixpoint simplify_base_runtime {t : base.type} : base.interp t -> option (list (Z + list Z))
  := match t return base.interp t -> option (list (Z + list Z)) with
     | base.type.unit
       => fun 'tt => Some []
     | base.type.type_base base.type.Z => fun val => Some [inl val]
     | base.type.prod A B => fun ab => (a <- simplify_base_runtime (fst ab); b <- simplify_base_runtime (snd ab); Some (a ++ b))
     | base.type.list (base.type.type_base base.type.Z)
       => fun ls : list Z => Some (List.map inl ls)
     | base.type.list _
     | base.type.type_base _
     | base.type.option _
       => fun _ => None
     end%option.

Theorem symex_PHOAS_correct
        {t} (expr : API.Expr t)
        (inputs : list (idx + list idx))
        (d : dag)
        (rets : list (idx + list idx))
        (d' : dag)
        (Hwf : API.Wf expr)
        (H : symex_PHOAS expr inputs d = Success (rets, d'))
        (d_ok : dag_ok d)
        (t_ok : type_ok t)
  : (forall (runtime_inputs : list (Z + list Z)),
        List.Forall2 (eval_idx_or_list_idx d) inputs runtime_inputs
        -> exists (input_runtime_var : type.for_each_lhs_of_arrow API.interp_type t)
                  (runtime_rets : list (Z + list Z)),
          build_input_runtime t runtime_inputs = Some (input_runtime_var, [])
          /\ simplify_base_runtime (type.app_curried (API.Interp expr) input_runtime_var) = Some runtime_rets
          /\ List.Forall2 (eval_idx_or_list_idx d') rets runtime_rets)
    /\ dag_ok d'
    /\ (forall e n, eval d e n -> eval d' e n).
Proof.
  cbv [symex_PHOAS ErrorT.bind] in H.
  repeat first [ progress break_innermost_match_hyps
               | progress destruct_head'_and
               | progress subst
               | discriminate
               | assumption
               | apply (f_equal (@Some _))
               | apply (f_equal2 (@pair _ _))
               | reflexivity
               | progress reflect_hyps
               | match goal with
                 | [ H : Success _ = Success _ |- _ ] => inversion H; clear H
                 | [ H : symex_PHOAS_PHOAS _ _ _ = _ |- _ ] => apply symex_PHOAS_PHOAS_correct in H; [ | assumption.. ]
                 | [ |- exists a b, ?v = Some (a, _) /\ _ = Some b /\ _ ]
                   => let av := fresh in destruct v as [ [av ?] |] eqn:?; [ exists av | exfalso ]
                 | [ |- exists a, _ /\ ?v = Some a /\ _ ]
                   => let av := fresh in destruct v as [ av |] eqn:?; [ exists av | exfalso ]
                 | [ H : List.length ?l = 0%nat |- _ ] => is_var l; destruct l; cbn in H
                 end
               | apply conj
               | progress intros ].
  (** TODO: Jason can finish this proof, all that remains is matching up PHOAS types *)
Admitted.

Check symex_asm_func.
Theorem symex_asm_func_correct
        (d : dag) (gensym_st : gensym_state) (output_types : type_spec) (stack_size : nat)
        (inputs : list (idx + list idx)) (reg_available : list REG) (asm : Lines)
        (rets : list (idx + list idx))
        (s : symbolic_state)
        (H : symex_asm_func d gensym_st output_types stack_size inputs reg_available asm = Success (rets, s))
        (d' := s.(dag_state))
  : (forall (st : machine_state)
            (runtime_inputs : list (Z + list Z)),
        List.Forall2 (eval_idx_or_list_idx d) inputs runtime_inputs
        -> exists st'
                  (* ??? *) (*(input_runtime_var : type.for_each_lhs_of_arrow API.interp_type t)*)
                  (runtime_rets : list (Z + list Z)),
          DenoteLines st asm = Some st'
          (*/\ build_input_runtime t runtime_inputs = Some (input_runtime_var, [])*)
          (*/\ simplify_base_runtime (type.app_curried (API.Interp expr) input_runtime_var) = Some runtime_rets*)
          /\ List.Forall2 (eval_idx_or_list_idx d') rets runtime_rets)
    /\ dag_ok d'
    /\ (forall e n, eval d e n -> eval d' e n).
Proof.
Admitted.

Lemma build_inputs_ok d gensym_st v inputs d' gensym_st'
      (d_ok : dag_ok d)
      (H : build_inputs (d, gensym_st) v = (inputs, (d', gensym_st')))
  : True (* Something about inputs *)
    /\ dag_ok d'
    /\ True (* something about gensym_st' *).
Proof.
Admitted.

Axiom empty_dag_ok : dag_ok empty_dag.

Check @check_equivalence.
Theorem check_equivalence_correct
        {assembly_calling_registers' : assembly_calling_registers_opt}
        {assembly_stack_size' : assembly_stack_size_opt}
        {assembly_output_first : assembly_output_first_opt}
        {assembly_argument_registers_left_to_right : assembly_argument_registers_left_to_right_opt}
        {t}
        (asm : Lines)
        (expr : API.Expr t)
        (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (out_bounds : ZRange.type.base.option.interp (type.final_codomain t))
        (Hwf : API.Wf expr)
        (H : check_equivalence asm expr arg_bounds out_bounds = Success tt)
        (st : machine_state)
        (PHOAS_args : type.for_each_lhs_of_arrow API.interp_type t)
        (args : list (Z + list Z))
        (Hargs : build_input_runtime t args = Some (PHOAS_args, []))
        (HPHOAS_args : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds PHOAS_args = true)
  (* TODO(Andres): write down something that relates [st] to args *)
  : exists st'
           (retvals : list (Z + list Z)),
    DenoteLines st asm = Some st'
    /\ simplify_base_runtime (type.app_curried (API.Interp expr) PHOAS_args) = Some retvals
    /\ True (* TODO(andres): write down something that relates st' to retvals *).
Proof.
  cbv beta delta [check_equivalence ErrorT.bind] in H.
  repeat match type of H with
         | (let n := ?v in _) = _
           => set v as n in H;
                lazymatch type of H with
                | (let n := ?v in ?rest) = ?rhs
                  => change (match v with n => rest end = rhs) in H
                end
         | match ?v with Success n => @?S n | Error e => @?E e end = ?rhs
           => let n := fresh n in
              let e := fresh e in
              destruct v as [n|e] eqn:?; [ change (S n = rhs) in H | change (E e = rhs) in H ];
                cbv beta in H
         | match ?v with pair a b => @?P a b end = ?rhs
           => let a := fresh a in
              let b := fresh b in
              destruct v as [a b] eqn:?; change (P a b = rhs) in H;
                cbv beta in H
         end; try discriminate; [].
  subst.
  pose proof empty_dag_ok.
  repeat match goal with
         | [ H : build_inputs _ _ = _ |- _ ] => move H at bottom; apply build_inputs_ok in H; [ | assumption.. ]
         | [ H : symex_PHOAS _ _ _ = Success _ |- _ ] => move H at bottom; apply symex_PHOAS_correct in H; [ | assumption.. ]
         | [ H : _ /\ _ |- _ ] => move H at bottom; destruct H
         end.
  epose (DenoteLines st asm).

   lazymatch goal with
   | [ H : symex_PHOAS _ _ _ = Success _ |- _ ] => apply symex_PHOAS_correct in H; [ | try assumption.. ]
   end.
  2: { move d0 at bottom.
       Search empty_dag dag_ok.
Admitted.

Check @generate_assembly_of_hinted_expr.
Theorem generate_assembly_of_hinted_expr_correct
        {assembly_calling_registers' : assembly_calling_registers_opt}
        {assembly_stack_size' : assembly_stack_size_opt}
        {assembly_output_first : assembly_output_first_opt}
        {assembly_argument_registers_left_to_right : assembly_argument_registers_left_to_right_opt}
        {t}
        (asm : Lines)
        (expr : API.Expr t)
        (f : type.interp _ t)
        (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (out_bounds : ZRange.type.base.option.interp (type.final_codomain t))
        (asm_out : Lines)
        (* Phrased this way to line up with the bounds pipeline exactly *)
        (Hbounded
         : (forall arg1 arg2
                   (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                   (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds arg1 = true),
               ZRange.type.base.option.is_bounded_by out_bounds (type.app_curried (API.Interp expr) arg1) = true
               /\ type.app_curried (API.Interp expr) arg1 = type.app_curried f arg2)
           /\ API.Wf expr)
        (H : generate_assembly_of_hinted_expr asm expr arg_bounds out_bounds = Success asm_out)
  : asm = asm_out
    /\ True (* ??? Something about equivalence of [API.Interp expr] and [asm] *).
Proof.
  cbv [generate_assembly_of_hinted_expr] in H.
  break_innermost_match_hyps; inversion H; subst; repeat apply conj; try reflexivity.
Qed.

(* Some theorems about the result of calling generate_assembly_of_hinted_expr_correct on various Pipeline functions *)
