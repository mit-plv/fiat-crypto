Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Alloc.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Group.Point.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Local Open Scope Z_scope.


Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representaton : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.
  Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.
  
  Section Gallina.
    Local Open Scope F_scope.

    Definition ladderstep_gallina
               (X1 X2 Z2 X3 Z3: F M_pos) : F M_pos * F M_pos * F M_pos * F M_pos :=
      let/n A := alloc (X2+Z2) in
      let/n AA := alloc (A^2) in
      let/n B := alloc (X2-Z2) in
      let/n BB := alloc (B^2) in
      let/n E := alloc (AA-BB) in
      let/n C := alloc (X3+Z3) in
      let/n D := alloc (X3-Z3) in
      let/n DA := alloc (D*A) in
      let/n CB := alloc (C*B) in
      (* store X5 under X3 pointer *)
      let/n X3 := (DA+CB) in
      let/n X3 := X3^2 in
      (* store Z5 under Z3 pointer *)
      let/n Z3 := (DA-CB) in
      let/n Z3 := Z3^2 in
      let/n Z3 := X1*Z3 in
      (* store X4 under X2 pointer *)
      let/n X2 := AA*BB in
      (* store Z4 under Z2 pointer *)
      let/n Z2 := a24*E in
      let/n Z2:= (AA+Z2) in
      let/n Z2 := E*Z2 in
      (X2, Z2, X3, Z3).
  End Gallina.

  Instance spec_of_ladderstep : spec_of "ladderstep" :=
    fnspec! "ladderstep"
          (pX1 pX2 pZ2 pX3 pZ3 : Semantics.word)
          / (X1 X2 Z2 X3 Z3 : F M_pos) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) pX1 X1
            * FElem (Some tight_bounds) pX2 X2
            * FElem (Some tight_bounds) pZ2 Z2
            * FElem (Some tight_bounds) pX3 X3
            * FElem (Some tight_bounds) pZ3 Z3 * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists X4 Z4 X5 Z5 (* output values *)
                  : F M_pos,
          (ladderstep_gallina X1 X2 Z2 X3 Z3
           = (X4, Z4, X5, Z5))
          /\ (FElem (Some tight_bounds) pX1 X1
              * FElem (Some tight_bounds) pX2 X4
              * FElem (Some tight_bounds) pZ2 Z4
              * FElem (Some tight_bounds) pX3 X5
              * FElem (Some tight_bounds) pZ3 Z5 * R)%sep mem'}.

  (*TODO
  Lemma compile_ladderstep {tr mem locals functions}
        (x1 x2 z2 x3 z3 : F M_pos) :
    let v := ladderstep_gallina x1 x2 z2 x3 z3 in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
           Rout
           X1 X1_ptr X1_var X2 X2_ptr X2_var Z2 Z2_ptr Z2_var
           X3 X3_ptr X3_var Z3 Z3_ptr Z3_var,

      spec_of_ladderstep functions ->

      feval X1 = x1 ->
      feval X2 = x2 ->
      feval Z2 = z2 ->
      feval X3 = x3 ->
      feval Z3 = z3 ->
      bounded_by tight_bounds X1 ->
      bounded_by tight_bounds X2 ->
      bounded_by tight_bounds Z2 ->
      bounded_by tight_bounds X3 ->
      bounded_by tight_bounds Z3 ->
      (FElem X1_ptr X1
       * FElem X2_ptr X2 * FElem Z2_ptr Z2
       * FElem X3_ptr X3 * FElem Z3_ptr Z3 * Rout)%sep mem ->

        map.get locals X1_var = Some X1_ptr ->
        map.get locals X2_var = Some X2_ptr ->
        map.get locals Z2_var = Some Z2_ptr ->
        map.get locals X3_var = Some X3_ptr ->
        map.get locals Z3_var = Some Z3_ptr ->

        (let v := v in
         forall (X4 Z4 X5 Z5 (* output values *)
                 : felem) m
                (Heq : ladderstep_gallina
                         (feval X1) (feval X2) (feval Z2)
                         (feval X3) (feval Z3)
                       = (feval X4, feval Z4, feval X5, feval Z5)),
          bounded_by tight_bounds X4 ->
          bounded_by tight_bounds Z4 ->
          bounded_by tight_bounds X5 ->
          bounded_by tight_bounds Z5 ->
          (FElem X1_ptr X1 * FElem X2_ptr X4 * FElem Z2_ptr Z4
           * FElem X3_ptr X5 * FElem Z3_ptr Z5 * Rout)%sep m ->
           (<{ Trace := tr;
               Memory := m;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->

        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.call [] "ladderstep"
                    [ expr.var X1_var; expr.var X2_var;
                        expr.var Z2_var; expr.var X3_var;
                          expr.var Z3_var])
          k_impl
        <{ pred (nlet_eq
                   [X2_var; Z2_var; X3_var; Z3_var]
                   v k) }>.
  Proof.
      repeat straightline'.
      handle_call;
        lazymatch goal with
        | |- sep _ _ _ => ecancel_assumption
        | _ => solve [eauto]
        end.
    Qed.
*)
  
  Ltac ladderstep_compile_custom :=
    (*TODO: move some of this into core rupicola?*)
    lazymatch goal with
    | [v := alloc _ |-_] =>
      unfold alloc in v;
      subst v
      | _ =>
        simple apply compile_nlet_as_nlet_eq
    end;
    field_compile_step; [ repeat compile_step .. | intros ];
    eauto with compiler;
    (* rewrite results in terms of feval to match lemmas *)
    repeat lazymatch goal with
           | H : feval _ = ?x |- context [?x] =>
             is_var x; rewrite <-H
           end.

  Ltac compile_custom ::= ladderstep_compile_custom.

  
  Lemma relax_bounds_FElem x_ptr x
    : Lift1Prop.impl1 (FElem (Some tight_bounds) x_ptr x)
                      (FElem (Some loose_bounds) x_ptr x).
  Proof.
    unfold FElem.
    intros m H.
    sepsimpl.
    exists x0.
    sepsimpl; simpl in *; eauto using relax_bounds.
  Qed.
  
  Lemma drop_bounds_FElem x_ptr x bounds
    : Lift1Prop.impl1 (FElem bounds x_ptr x)
                      (FElem None x_ptr x).
  Proof.
    unfold FElem.
    intros m H.
    sepsimpl.
    exists x0.
    sepsimpl; simpl in *; eauto using relax_bounds.
  Qed.

  (*TODO: move to pred_sep if deemed useful*)
    Lemma merge_pred_sep A (a : A) R1 R2 pred tr m locals
    : pred_sep (R1*R2)%sep pred a tr m locals ->
      pred_sep R1 (pred_sep R2 pred) a tr m locals.
    Proof.
    unfold pred_sep; simpl.
    unfold Basics.flip; simpl.
    repeat change (fun x => ?h x) with h.
    intros; ecancel_assumption.
    Qed.


(*TODO: move to separate file; copy source and re-edit?*)
  Require Import coqutil.Tactics.syntactic_unify coqutil.Tactics.rdelta.
 

Require Import Coq.Classes.Morphisms.
Require Import coqutil.sanity coqutil.Decidable coqutil.Tactics.destr.
Section SepProperties.
  Context {key value} {map : map.map key value} {ok : map.ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
  Local Open Scope sep_scope.
  
  Definition hd {T} := Eval cbv delta in @List.hd T.
  Definition tl {T} := Eval cbv delta in @List.tl T.
  Definition firstn {T} := Eval cbv delta in @List.firstn T.
  Definition skipn {T} := Eval cbv delta in @List.skipn T.
  Definition app {T} := Eval cbv delta in @List.app T.

  Local Infix "++" := app. Local Infix "++" := app : list_scope.
  Let nth n xs := hd (emp(map:=map) True) (skipn n xs).
  Let remove_nth n (xs : list (map -> Prop)) :=
    (firstn n xs ++ tl (skipn n xs)).

  
  Lemma seps_nth_to_head n xs : Lift1Prop.iff1 (sep (nth n xs) (seps (remove_nth n xs))) (seps xs).
  Proof.
    cbv [nth remove_nth].
    pose proof (List.firstn_skipn n xs : (firstn n xs ++ skipn n xs) = xs).
    set (xsr := skipn n xs) in *; clearbody xsr.
    set (xsl := firstn n xs) in *; clearbody xsl.
    subst xs.
    setoid_rewrite <-seps'_iff1_seps.
    destruct xsr.
    { cbn [seps']; rewrite sep_emp_True_l, 2List.app_nil_r; exact (reflexivity _). }
    cbn [hd tl].
    induction xsl; cbn; [exact (reflexivity _)|].
    rewrite <-IHxsl; clear IHxsl.
    rewrite (sep_comm _ (seps' _)), <-(sep_assoc _ (seps' _)), <-(sep_comm _ (_ * seps' _)).
    exact (reflexivity _).
  Qed.
  
    (* iff1 instead of eq as a hyp would be a more general lemma, but eq is more convenient to use *)
  Lemma cancel_seps_at_indices i j xs ys
        (Hij : Lift1Prop.impl1 (nth i xs) (nth j ys))
        (Hrest : Lift1Prop.impl1 (seps (remove_nth i xs)) (seps (remove_nth j ys)))
    : Lift1Prop.impl1 (seps xs) (seps ys).
  Proof.
    rewrite <-(seps_nth_to_head i xs), <-(seps_nth_to_head j ys).
    rewrite Hij, Hrest.
    exact (reflexivity _).
  Qed.

  
End SepProperties.
  
  (* leaves two open goals:
   1) equality between left sep clause #i and right sep clause #j
   2) updated main goal *)
Ltac cancel_seps_at_indices i j :=
  lazymatch goal with
  | |- Lift1Prop.impl1 (seps ?LHS) (seps ?RHS) =>
    simple refine (cancel_seps_at_indices i j LHS RHS _ _);
    cbn [firstn skipn app hd tl]
  end.

Create HintDb ecancel_impl discriminated.
Hint Extern 1 => exact (fun m x => x) : ecancel_impl.

Ltac prop_at_index_is_evar j ys :=
  let p := eval cbn [firstn skipn app hd tl nth] in (nth j ys) in
      match p with
      | (fun _ => ?pb) => is_evar pb
      | _ => fail "malformed input"
      end.

(*TODO: performance*)
Ltac find_implication xs y :=
  multimatch xs with
  | cons ?x _ =>
    let H := fresh in
    constr:(O)
  | cons _ ?xs => let i := find_implication xs y in constr:(S i)
  end.


(*TODO: performance. I've replaced the deltavar stuff with heavier operations  *)
Ltac ecancel_step :=
      let RHS := lazymatch goal with |- Lift1Prop.impl1 _ (seps ?RHS) => RHS end in
      let jy := index_and_element_of RHS in (* <-- multi-success! *)
      let j := lazymatch jy with (?i, _) => i end in
      let y := lazymatch jy with (_, ?y) => y end in
      (* For implication, we don't want to touch RHS evars 
         until everything else is solved.
         Makes sure j doesn't point to an evar
       *)
      assert_fails (idtac; prop_at_index_is_evar 0%nat RHS);      
      let LHS := lazymatch goal with |- Lift1Prop.impl1 (seps ?LHS) _ => LHS end in
      let i := find_implication LHS y in (* <-- multi-success! *)
      cancel_seps_at_indices i j; [solve [auto 1 with ecancel_impl]|].
(*TODO: should I use deltavar here too?*)
Ltac ecancel :=
  cancel; repeat ecancel_step; (solve [ exact (fun m x => x) ]).


 Ltac ecancel_assumption_impl :=
    multimatch goal with
    | |- ?PG ?m1 =>
      multimatch goal with
      | H: ?PH ?m2
        |- _ =>
        syntactic_unify_deltavar m1 m2;
        refine (Morphisms.subrelation_refl Lift1Prop.impl1 PH PG _ m1 H); clear H;
        cbn[seps];(*TODO: why is this needed?*)
        solve[ecancel]
      end
    end.

 
    (*TODO: speed up by combining pred_seps first and using 1 proper/ecancel_assumption?*)
    Ltac clear_pred_seps :=   
    unfold pred_sep;
    repeat change (fun x => ?h x) with h;
    repeat match goal with
           | [ H : _ ?m |- _ ?m] =>
             eapply Proper_sep_impl1;
               [ eapply P_to_bytes | clear H m; intros H m | ecancel_assumption]
           end.
    Ltac compile_solve_side_conditions ::=
  match goal with
  | |- (_ ⋆ _) _ => cbn[fst snd] in *; ecancel_assumption
  | |- map.get _ _ = _ => solve [ subst_lets_in_goal; solve_map_get_goal ]
  | |- map.getmany_of_list _ _ = _ => apply map.getmany_of_list_cons
  | |- map.remove_many _ _ = _ => solve_map_remove_many
  | |- _ = _ => solve_map_eq
  | |- _ <> _ => congruence
  | |- _ /\ _ => split
  | |- exists _,_ => eexists (*TODO: is this worth adding?*)
  | |- pred_sep _ _ _ _ _ _ => clear_pred_seps
  | _ => first
  [ compile_cleanup
  | compile_autocleanup
  | reflexivity
  | compile_use_default_value
  | solve
  [ typeclasses eauto | eauto with compiler_cleanup ] ]
  end.

    
    Ltac ecancel_assumption ::=  ecancel_assumption_impl.

 
Hint Immediate relax_bounds_FElem : ecancel_impl.

Derive ladderstep_body SuchThat
       (let args := ["X1"; "X2"; "Z2"; "X3"; "Z3"] in
        ltac:(
          let proc := constr:(("ladderstep",
                               (args, [], ladderstep_body))
                              : Syntax.func) in
          let goal := Rupicola.Lib.Tactics.program_logic_goal_for_function
                        proc [mul;add;sub;square;scmula24] in
          exact (__rupicola_program_marker ladderstep_gallina -> goal)))
       As ladderstep_correct.
Proof. compile. Qed.
  
  
End __.

Existing Instance spec_of_ladderstep.

Import Syntax.
Local Unset Printing Coercions.
Redirect "Crypto.Bedrock.Group.ScalarMult.LadderStep.ladderstep_body" Print ladderstep_body.
