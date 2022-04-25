Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Local Open Scope Z_scope.

Section Gallina.
  Local Open Scope F_scope.

  Let F := F.F.

  Definition ladderstep_gallina (m : positive) (a24 : F m)
             (X1 X2 Z2 X3 Z3: F m) : \<< F m, F m, F m, F m \>> :=
    let/n A := stack (X2+Z2) in
    let/n X2 := (X2-Z2) in
    let/n Z2 := (X3+Z3) in
    let/n Z3 := (X3-Z3) in
    let/n Z3 := (Z3*A) in
    let/n Z2 := (Z2*X2) in
    let/n A := (A^2) in
    let/n X2 := (X2^2) in
    let/n E := stack (A-X2) in
    let/n X3 := (Z3+Z2) in
    let/n X3 := X3^2 in
    let/n Z3 := (Z3-Z2) in
    let/n Z3 := Z3^2 in
    let/n Z3 := X1*Z3 in
    let/n X2 := A*X2 in
    let/n Z2 := a24*E in
    let/n Z2:= (A+Z2) in
    let/n Z2 := E*Z2 in
    \<X2, Z2, X3, Z3\>.
End Gallina.

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {prime_field_parameters : PrimeFieldParameters}.

  Instance my_field_parameters : FieldParameters := PrimeField.prime_field_parameters.
  
  Context {field_representaton : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.

  Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Let F := F.F.

  Instance spec_of_ladderstep : spec_of "ladderstep" :=
    fnspec! "ladderstep"
          (pX1 pX2 pZ2 pX3 pZ3 : word)
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
                  (ladderstep_gallina M_pos a24 X1 X2 Z2 X3 Z3
           = \<X4, Z4, X5, Z5\>)
          /\ (FElem (Some tight_bounds) pX1 X1
              * FElem (Some tight_bounds) pX2 X4
              * FElem (Some tight_bounds) pZ2 Z4
              * FElem (Some tight_bounds) pX3 X5
              * FElem (Some tight_bounds) pZ3 Z5 * R)%sep mem'}.

  Lemma compile_ladderstep {tr m l functions}
        (x1 x2 z2 x3 z3 : F M_pos) :
    let v := ladderstep_gallina M_pos a24 x1 x2 z2 x3 z3 in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
           Rout
           X1_ptr X1_var X2_ptr X2_var Z2_ptr Z2_var
           X3_ptr X3_var Z3_ptr Z3_var,

      spec_of_ladderstep functions ->

      (FElem (Some tight_bounds) X1_ptr x1
       * FElem (Some tight_bounds) X2_ptr x2 * FElem (Some tight_bounds) Z2_ptr z2
       * FElem (Some tight_bounds) X3_ptr x3 * FElem (Some tight_bounds) Z3_ptr z3 * Rout)%sep m ->

      map.get l X1_var = Some X1_ptr ->
      map.get l X2_var = Some X2_ptr ->
      map.get l Z2_var = Some Z2_ptr ->
      map.get l X3_var = Some X3_ptr ->
      map.get l Z3_var = Some Z3_ptr ->

      (let v := v in
       forall (* output values *) m',
       let '\<X4, Z4, X5, Z5\> := ladderstep_gallina M_pos a24 x1 x2 z2 x3 z3 in
         (FElem (Some tight_bounds) X1_ptr x1
          * FElem (Some tight_bounds) X2_ptr X4
          * FElem (Some tight_bounds) Z2_ptr Z4
          * FElem (Some tight_bounds) X3_ptr X5
          * FElem (Some tight_bounds) Z3_ptr Z5 * Rout)%sep m' ->
         (<{ Trace := tr;
             Memory := m';
             Locals := l;
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->

      <{ Trace := tr;
         Memory := m;
         Locals := l;
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
    handle_call.
    apply H6.
    rewrite H9.
    ecancel_assumption.
  Qed.

  Local Ltac ecancel_assumption ::=  ecancel_assumption_impl.

  (*Why must these instances be included?*)

  Instance spec_of_mul : spec_of (@mul prime_field_parameters).
  Proof.
    pose proof (binop_spec bin_mul). cbv [spec_of]. eapply X.
  Defined.

  Instance spec_of_square : spec_of (@square prime_field_parameters).
  Proof.
    pose proof (unop_spec un_square). cbv [spec_of]. eapply X.
  Defined.

  Instance spec_of_add : spec_of (@add prime_field_parameters).
  Proof.
    pose proof (binop_spec bin_add). cbv [spec_of]. eapply X.
  Defined.

  Instance spec_of_sub : spec_of (@sub prime_field_parameters).
  Proof.
    pose proof (binop_spec bin_sub). cbv [spec_of]. eapply X.
  Defined.

  Instance spec_of_scmula24 : spec_of (@scmula24 prime_field_parameters).
  Proof.
    pose proof (unop_spec un_scmula24). cbv [spec_of]. eapply X.
  Defined.

  Lemma relax_bounds_FElem_R : forall R x x_ptr, Lift1Prop.impl1 ((FElem (Some tight_bounds) x_ptr x * R)%sep) ((FElem (Some loose_bounds) x_ptr x * R)%sep).
  Proof.
    intros. cbv [Lift1Prop.impl1]. intros.
    destruct H, H, H, H0.
    eexists; eexists; split; [eapply H | ]. split; eauto. eapply relax_bounds_FElem. auto.
  Qed.

  Lemma relax_bounds_binop : forall R x x_ptr y y_ptr, Lift1Prop.impl1 ((FElem (Some tight_bounds) x_ptr x * FElem (Some tight_bounds) y_ptr y * R)%sep) ((FElem (Some loose_bounds) x_ptr x * FElem (Some loose_bounds) y_ptr y * R)%sep).
  Proof.
    intros. cbv [Lift1Prop.impl1]. intros. eapply sep_assoc. eapply relax_bounds_FElem_R.
    eapply sep_comm, sep_assoc. eapply relax_bounds_FElem_R. ecancel_assumption.
  Qed.

  (*tactics for applying field operations*)

  Ltac find_in_map :=
    repeat first [ erewrite map.get_put_diff; [| intros contra; discriminate] |
      eapply map.get_put_same].

  Ltac apply_square :=
      try simple apply compile_nlet_as_nlet_eq;
      epose proof compile_square as Hsquare;
      cbv [AbstractField.F] in Hsquare; cbv [Compilation2.field_parameters PrimeField.prime_field_parameters] in *;
      cbv [AbstractField.square AbstractField.Fsquare Fmul Compilation2.field_parameters] in *;
      rewrite F.pow_2_r;
      eapply Hsquare; clear Hsquare; try repeat compile_step; [ eapply relax_bounds_FElem_R; ecancel_assumption | ..]; repeat compile_step.

      
  Ltac apply_mul :=
    try simple apply compile_nlet_as_nlet_eq;
    epose proof compile_mul as Hmul;
    cbv [AbstractField.F] in Hmul; cbv [Compilation2.field_parameters PrimeField.prime_field_parameters] in *;
    cbv [AbstractField.mul AbstractField.Fmul Fmul Compilation2.field_parameters] in *;
    eapply Hmul; clear Hmul; try repeat compile_step; [ eapply sep_assoc, relax_bounds_FElem_R, sep_comm, sep_assoc, relax_bounds_FElem_R; ecancel_assumption | compile_step| compile_step| ..]. 
  
  Ltac apply_add :=
    try simple apply compile_nlet_as_nlet_eq;
    epose proof compile_add as Hadd;
    cbv [AbstractField.F] in Hadd; cbv [Compilation2.field_parameters PrimeField.prime_field_parameters] in *;
    cbv [AbstractField.add AbstractField.Fadd Fadd Compilation2.field_parameters] in *;
    eapply Hadd; clear Hadd; [| find_in_map | eapply relax_bounds_FElem_R; ecancel_assumption| ecancel_assumption| ..]; try compile_step.

  Ltac apply_sub :=
    try simple apply compile_nlet_as_nlet_eq;
    epose proof compile_sub as Hsub;
    cbv [AbstractField.F] in Hsub; cbv [Compilation2.field_parameters PrimeField.prime_field_parameters] in *;
    cbv [AbstractField.sub AbstractField.Fsub Fsub Compilation2.field_parameters] in *;
    eapply Hsub; clear Hsub; [| find_in_map | eapply relax_bounds_FElem_R; ecancel_assumption| ecancel_assumption| ..]; try compile_step.
    

  Local Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (_ ^ 2)%F _))) =>
    let Hsquare := (fresh "Hsquare") in pose proof compile_square as Hsquare;
    rewrite F.pow_2_r; cbv [Compilation2.field_parameters PrimeField.prime_field_parameters] in Hsquare;
    eapply Hsquare; clear Hsquare; shelve : compiler.

    Local Hint Extern 6 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (a24 * _)%F _))) =>
    let Hscmul := (fresh "Hscmul") in epose proof compile_scmula24 as Hscmul;
    cbv [Compilation2.field_parameters PrimeField.prime_field_parameters] in *;
    eapply Hscmul; clear Hscmul; shelve : compiler.

  Local Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (_ * _)%F _))) =>
    let Hmul := (fresh "Hmul") in pose proof compile_mul as Hmul;
    cbv [Compilation2.field_parameters PrimeField.prime_field_parameters] in Hmul;
    eapply Hmul; [| | | try (eapply relax_bounds_binop; ecancel_assumption) | | |]; clear Hmul; shelve : compiler.

    Local Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (_ - _)%F _))) =>
    let Hsub := (fresh "Hsub") in epose proof compile_sub as Hsub;
    cbv [Compilation2.field_parameters PrimeField.prime_field_parameters] in *;
    eapply Hsub; clear Hsub; shelve : compiler.

  Local Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (_ + _)%F _))) =>
    let Hadd := (fresh "Hadd") in epose proof compile_add as Hadd;
    cbv [Compilation2.field_parameters PrimeField.prime_field_parameters] in *;
    eapply Hadd; clear Hadd; shelve : compiler.

  Local Hint Extern 9 ((FElem (Some loose_bounds) _ _ ⋆ FElem (Some loose_bounds) _ _ ⋆ _)%sep _) =>
    eapply relax_bounds_binop; ecancel_assumption : compiler.

  Local Hint Extern 9 =>
  simple eapply (@compile_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((@FElem width BW word mem prime_field_parameters field_representaton
    (@None (@bounds field_parameters width BW word mem field_representaton)))));
    [ecancel_assumption | shelve] : compiler.


  Lemma FElem_bounds_None : forall x x_ptr R, Lift1Prop.impl1 (FElem (Some loose_bounds) x_ptr x * R)%sep (FElem None x_ptr x * R)%sep.
  Proof.
    intros. cbv [Lift1Prop.impl1]; intros m Hsep.
    destruct Hsep as [m1 [m2 [Hsep1 [Hsep2 Hsep3]]]].
    do 2 eexists. split; eauto. split; eauto.
    cbv [FElem Lift1Prop.ex1] in *. sepsimpl. simpl.
    exists x0. sepsimpl; auto.
  Qed.

  Local Hint Extern 9 ((FElem None _ _ ⋆ _ )%sep _) =>
  eapply FElem_bounds_None; ecancel_assumption : compiler_cleanup_post.

  Ltac clear_pred_seps' :=   
  unfold pred_sep;
  repeat change (fun x => ?h x) with h;
  repeat match goal with
         | [ H : _ ?m |- _ ?m] =>
           eapply Proper_sep_impl1;
           [ eapply P_to_bytes | clear H m; intros H m |
            try (eapply FElem_bounds_None; ecancel_assumption);
            try (eapply FElem_bounds_None; eapply relax_bounds_FElem_R; ecancel_assumption)]
         end.

  Hint Extern 1 (pred_sep _ _ _ _ _ _) =>
         clear_pred_seps'; shelve : compiler_cleanup_post.


  Derive ladderstep_body SuchThat
         (defn! "ladderstep" ("X1", "X2", "Z2", "X3", "Z3")
              { ladderstep_body },
           implements ladderstep_gallina
                      using [@mul prime_field_parameters;@add prime_field_parameters;@sub prime_field_parameters;@square prime_field_parameters;@scmula24 prime_field_parameters])
         As ladderstep_correct.
  Proof. 
    compile.
  Qed.

End __.

Existing Instance spec_of_ladderstep.

Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (ladderstep_gallina _ _ _ _ _ _ _) _))) =>
       simple eapply compile_ladderstep; shelve : compiler.

Import Syntax.
Local Unset Printing Coercions.
Local Set Printing Depth 70.
(* Set the printing width so that arguments are printed on 1 line.
   Otherwise the build breaks.
*)
Local Set Printing Width 140.
Redirect "Crypto.Bedrock.Group.ScalarMult.LadderStep.ladderstep_body" Print ladderstep_body.
