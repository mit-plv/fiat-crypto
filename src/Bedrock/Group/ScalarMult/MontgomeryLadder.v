(* NOTE: the plan is to completely redo montladder after ladderstep is updated to use stackalloc *)

Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Alloc.
Require Import Rupicola.Lib.SepLocals.
Require Import Rupicola.Lib.ControlFlow.CondSwap.
Require Import Rupicola.Lib.ControlFlow.DownTo.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.ScalarField.Interface.Compilation.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Specs.ScalarField.
Require Import Crypto.Util.NumTheoryUtil.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Local Open Scope Z_scope.

(* TODO: migrate these to rupicola *)
(* TODO: which tuple to use? *)
Notation "'let/n' ( w , x , y , z ) := val 'in' body" :=
  (nlet [IdentParsing.TC.ident_to_string w;
        IdentParsing.TC.ident_to_string x;
        IdentParsing.TC.ident_to_string y;
        IdentParsing.TC.ident_to_string z]
        val  (fun '(w, x, y, z) => body))
   (at level 200, w ident, x  ident, y ident, z ident, body at level 200,
    only parsing).


Notation "'let/n' ( v , w , x , y , z ) := val 'in' body" :=
  (nlet [IdentParsing.TC.ident_to_string v;
        IdentParsing.TC.ident_to_string w;
        IdentParsing.TC.ident_to_string x;
        IdentParsing.TC.ident_to_string y;
        IdentParsing.TC.ident_to_string z]
        val (fun vwxyz => let '\< v, w, x, y, z \> := vwxyz in body))
    (at level 200, v ident, w ident, x ident, y ident, z ident, body at level 200,
     only parsing).

(*

Notation "'let/n' ( v , w , x , y , z ) := val 'in' body" :=
  (nlet [IdentParsing.TC.ident_to_string v;
        IdentParsing.TC.ident_to_string w;
        IdentParsing.TC.ident_to_string x;
        IdentParsing.TC.ident_to_string y;
        IdentParsing.TC.ident_to_string z]
        val  (fun '(v, w, x, y, z) => body))
   (at level 200, v ident,  w ident, x  ident, y ident, z ident, body at level 200,
     only parsing).
*)


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
          {scalar_field_parameters : ScalarFieldParameters}.
  Context {scalar_field_parameters_ok : ScalarFieldParameters_ok}.
  Context {field_representaton : FieldRepresentation}
  {scalar_representation : ScalarRepresentation}.
  Context {field_representation_ok : FieldRepresentation_ok}.
  Hint Resolve @relax_bounds : compiler.

  Section Gallina.
    Local Open Scope F_scope.

    Locate "let/n".
    Definition montladder_gallina
               (scalarbits : Z) (testbit:nat ->bool) (u:F M_pos)
      : F M_pos :=
      let/n X1 := stack 1 in
      let/n Z1 := stack 0 in
      let/n X2 := stack u in
      let/n Z2 := stack 1 in
     (* let/d P1 := (1, 0) in
        let/d P2 := (X2, Z2) in
      *)
      let/n swap := false in
      let/n count := scalarbits in
      let/n (X1, Z1, X2, Z2, swap) :=
         downto
           \<X1, Z1, X2, Z2, swap\> (* initial state *)
           (Z.to_nat count)
           (fun state i =>
              (*TODO: should this be a /n?*)
              let '\<X1, Z1, X2, Z2, swap\> := state in
              let/n s_i := testbit i in
              let/n swap := xorb swap s_i in
              let/n (X1, X2) := cswap swap X1 X2 in
              let/n (Z1, Z2) := cswap swap Z1 Z2 in
              let/n (X1, Z1, X2, Z2) := ladderstep_gallina u X1 Z1 X2 Z2 in
              let/n swap := s_i in
              \<X1, Z1, X2, Z2, swap\>
           ) in
      let/n (X1, X2) := cswap swap X1 X2 in
      let/n (Z1, Z2) := cswap swap Z1 Z2 in
      let/n r := stack (F.inv Z1) in
      let/n r := (X1 * r) in
      r.
  End Gallina.

  Section MontLadder.
    Context (scalarbits_small : word.wrap scalarbits = scalarbits).

    Instance spec_of_montladder : spec_of "montladder" :=
      fnspec! "montladder"
            (pOUT pK pU (*pX1 pZ1 pX2 pZ2*) : word)
            / (K : scalar) (U : F M_pos) (* inputs *)
            out_bound OUT (*X1 Z1 X2 Z2 *) (* intermediates *)
            R,
      { requires tr mem :=
          (FElem out_bound pOUT OUT * Scalar pK K * FElem (Some tight_bounds) pU U
              (** FElem pX1 X1 * FElem pZ1 Z1
               * FElem pX2 X2 * FElem pZ2 Z2*)
               *  R)%sep mem;
        ensures tr' mem' :=
          tr' = tr
          /\ (let OUT :=  montladder_gallina
                            scalarbits
                            (fun i =>
                               Z.testbit (F.to_Z (sceval K))
                                         (Z.of_nat i))
                            U in
              (FElem (Some tight_bounds) pOUT OUT * Scalar pK K
               * FElem (Some tight_bounds) pU U
                (** FElem pX1 X1 * FElem pZ1 Z1
                * FElem pX2 X2 * FElem pZ2 Z2 *)
                * R)%sep mem') }.


    Ltac apply_compile_cswap_nocopy :=
      simple eapply compile_cswap_nocopy with
        (Data :=
           fun p (X : F _) =>
             (Lift1Prop.ex1
                (fun x =>
                   (emp (feval x = X) * FElem p x)%sep)))
        (tmp:="tmp");
      [ lazymatch goal with
        | |- sep _ _ _ =>
          repeat lazymatch goal with
                 | |- Lift1Prop.ex1 _ _ => eexists
                 | |- feval _ = _ => eassumption
                 | _ => progress sepsimpl
                 end; ecancel_assumption
        | _ => idtac
        end .. | ];
      [ repeat compile_step .. | ];
      [ try congruence .. | ].

    Ltac compile_custom ::=
      simple apply compile_nlet_as_nlet_eq;
      first [ simple eapply compile_downto
            | simple eapply compile_sctestbit
            | simple eapply compile_felem_small_literal
            | simple eapply compile_felem_copy
            | simple eapply compile_cswap_pair
            | apply_compile_cswap_nocopy ].

    (* TODO: make a new loop invariant, drop the sep-local stuff *)
    (*nat -> bool -> F M_pos * F M_pos * F M_pos * F M_pos * bool -> predicate*)
    Definition downto_inv
               (swap_var OUT_var U_var X1_var Z1_var X2_var Z2_var K_var : string)
               K (pOUT K_ptr U_ptr X1_ptr Z1_ptr X2_ptr Z2_ptr : word) R
               (_ : nat)
               (gst : bool)
               (st : F M_pos * F M_pos * F M_pos * F M_pos * bool)
      : predicate :=
      fun (_ : Semantics.trace)
          (mem : mem)
          (locals : locals) =>
        let '(x1, z1, x2, z2, swap) := st in
        locals = (map.put
             (map.put
                (map.put
                   (map.put
                      (map.put
                         (map.put
                            (*TODO: where did outvar come from?*)
                            (map.put (map.put map.empty OUT_var pOUT) K_var K_ptr)
                            U_var U_ptr) X1_var X1_ptr) Z1_var Z1_ptr) X2_var
                   X2_ptr) Z2_var Z2_ptr) swap_var (word.b2w swap))
            /\ ((Scalar K_ptr K * FElem (Some tight_bounds) X1_ptr x1
            * FElem (Some tight_bounds) Z1_ptr z1
            * FElem (Some tight_bounds) X2_ptr x2
            * FElem (Some tight_bounds) Z2_ptr z2) * R)%sep mem.
    
    Definition downto_ghost_step
               (K : scalar) (st : F M_pos * F M_pos * F M_pos * F M_pos * bool)
               (gst : bool) (i : nat) :=
      let '(x1, z1, x2, z2, swap) := st in
      let swap := xorb swap (Z.testbit (F.to_Z (sceval K)) (Z.of_nat i)) in
      xorb gst swap.

    Ltac setup_downto_inv_init :=
      lift_eexists; sepsimpl;
      (* first fill in any map.get goals where we know the variable names *)
      lazymatch goal with
      | |- map.get _ ?x = Some _ =>
        tryif is_evar x then idtac
        else (autorewrite with mapsimpl; reflexivity)
      | _ => idtac
      end;
      lazymatch goal with
      | |- (_ * _)%sep _ => ecancel_assumption
      | _ => idtac
      end.

    Ltac solve_downto_inv_subgoals :=
      lazymatch goal with
      | |- map.get _ _ = _ => subst_lets_in_goal; solve_map_get_goal
      | |- bounded_by _ _ => solve [ auto ]
      | |- feval _ = _ =>
        subst_lets_in_goal; first [ reflexivity | assumption ]
      | |- ?x = ?x => reflexivity
      | |- ?x => fail "unrecognized side condition" x
      end.

    Lemma feval_fst_cswap s a b A B :
      feval a = A -> feval b = B ->
      feval (fst (cswap s a b)) = fst (cswap s A B).
    Proof. destruct s; cbn; auto. Qed.

    Lemma feval_snd_cswap s a b A B :
      feval a = A -> feval b = B ->
      feval (snd (cswap s a b)) = snd (cswap s A B).
    Proof. destruct s; cbn; auto. Qed.

    (* Adding word.unsigned_of_Z_1 and word.unsigned_of_Z_0 as hints to
       compiler doesn't work, presumably because of the typeclass
       preconditions. This is a hacky workaround. *)
    (* TODO: figure out a cleaner way to do this *)
    Lemma unsigned_of_Z_1 : word.unsigned (@word.of_Z _ word 1) = 1.
    Proof. exact word.unsigned_of_Z_1. Qed.
    Lemma unsigned_of_Z_0 : word.unsigned (@word.of_Z _ word 0) = 0.
    Proof. exact word.unsigned_of_Z_0. Qed.
    Hint Resolve unsigned_of_Z_0 unsigned_of_Z_1 : compiler.

    Ltac safe_compile_step :=
      compile_step;
      (* first pass fills in some evars *)
      [ repeat compile_step .. | idtac ];
      (* second pass must solve *)
      [ first [ solve [repeat compile_step]
              | solve [straightline_map_solver_locals] ] .. | idtac ].

    Ltac solve_field_subgoals_with_cswap :=
      lazymatch goal with
      | |- map.get _ _ = Some _ =>
        solve [subst_lets_in_goal; solve_map_get_goal]
      | |- feval _ = _ =>
        solve [eauto using feval_fst_cswap, feval_snd_cswap]
      | |- bounded_by _ (fst (cswap _ _ _)) =>
        apply cswap_cases_fst; solve [auto]
      | |- bounded_by _ (snd (cswap _ _ _)) =>
        apply cswap_cases_snd; solve [auto]
      | _ => idtac
      end; solve [eauto].

    (* create a new evar to take on the second swap clause *)
    Ltac rewrite_cswap_iff1_with_evar_frame :=
      match goal with
        |- (?P * ?R)%sep _ =>
        match P with context [cswap] => idtac end;
        is_evar R;
        let R1 := fresh "R" in
        let R2 := fresh "R" in
        evar (R1 : mem -> Prop);
        evar (R2 : mem -> Prop);
        unify R (sep R1 R2);
        seprewrite (cswap_iff1 FElem)
      end.
    
    Existing Instance spec_of_sctestbit.


  (*TODO: get compiling
  Require Import Rupicola.Examples.CMove.
   *)
  
 Definition felem_cswap := "felem_cswap".
  (*TODO: move to the right place;
    TODO: instantiate
   *)  
  Instance spec_of_felem_cswap : spec_of felem_cswap :=
    fnspec! felem_cswap mask ptr1 ptr2 / b1 b2 b c1 c2 R,
    { requires tr mem :=
        mask = word.of_Z (Z.b2z b) /\
        (FElem b1 ptr1 c1 * FElem b2 ptr2 c2 * R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        let (c1,c2) := cswap b c1 c2 in
        let (b1,b2) := cswap b b1 b2 in
        (FElem b1 ptr1 c1 * FElem b2 ptr2 c2 * R)%sep mem' }.
  
   Lemma compile_felem_cswap {tr m l functions} swap (lhs rhs : F M_pos) :
    let v := cswap swap lhs rhs in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      R mask_var lhs_ptr lhs_var b_lhs rhs_ptr rhs_var b_rhs,

      spec_of_felem_cswap functions ->

      map.get l mask_var = Some (word.of_Z (Z.b2z swap)) ->
      
      map.get l lhs_var = Some lhs_ptr ->
      map.get l rhs_var = Some rhs_ptr ->

      (FElem b_lhs lhs_ptr lhs * FElem b_rhs rhs_ptr rhs * R)%sep m ->

      (let v := v in
       let (b1,b2) := cswap swap b_lhs b_rhs in
       forall m',
         (FElem b1 lhs_ptr (fst v) * FElem b2 rhs_ptr (snd v) * R)%sep m' ->
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
        (cmd.call [] felem_cswap [expr.var mask_var; expr.var lhs_var; expr.var rhs_var])
        k_impl
      <{ pred (nlet_eq [lhs_var; rhs_var] v k) }>.
   Proof.     
     Local Ltac prove_field_compilation locals :=
       repeat straightline' locals;
       handle_call;
       lazymatch goal with
       | |- sep _ _ _ => ecancel_assumption
       | _ => idtac
       end; eauto;
       sepsimpl; repeat straightline' locals; subst; eauto.
     prove_field_compilation l.
     destruct swap; eapply H4; unfold v; unfold cswap; simpl; eauto.
   Qed.
   Hint Resolve compile_felem_cswap : compiler.

  (*
  Lemma compile_cswap_pair {tr mem locals functions} (swap: bool) {A} (x y: A * A) x1 x2 :
    let v := cswap swap x y in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl},
      (let __ := 0 in (* placeholder FIXME why? *)
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       k_impl
       <{ pred (nlet_eq [x1] (cswap swap (fst x) (fst y))
                     (fun xy1 eq1 =>
                        nlet_eq [x2] (cswap swap (snd x) (snd y))
                             (fun xy2 eq2 =>
                                let x := (fst xy1, fst xy2) in
                                let y := (snd xy1, snd xy2) in
                                k (x, y) ltac:(eauto)))) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      k_impl
      <{ pred (nlet_eq [x1; x2] v k) }>.
  Proof.
    repeat straightline'.
    subst_lets_in_goal. destruct_products.
    destruct swap; cbv [cswap dlet] in *; cbn [fst snd] in *.
    all:eauto.
  Qed.
   *)

  
  Lemma destruct_cswap {A} b (lhs rhs : A)
    : cswap b lhs rhs = (if b then rhs else lhs, if b then lhs else rhs).
  Proof.
    destruct b;
      reflexivity.
  Qed.

  Existing Instance felem_alloc.


  Lemma cswap_same {A} b (a : A): cswap b a a = (a,a).
  Proof.
    destruct b; reflexivity.
  Qed.
  
  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.
  
  Hint Extern 1 (spec_of _) => (simple refine (@spec_of_felem_copy _ _ _ _ _ _ _ _)) : typeclass_instances.
  Hint Extern 1 (spec_of _) => (simple refine (@spec_of_felem_small_literal _ _ _ _ _ _ _ _)) : typeclass_instances.

  Axiom TODO: forall {A}, A.
  Ltac todo := solve[refine (TODO)].
  
  Derive montladder_body SuchThat
           (let args := ["OUT"; "K"; "U" (*;"X1"; "Z1"; "X2"; "Z2" *)] in
            let montladder : Syntax.func :=
                ("montladder", (args, [], montladder_body)) in
          ltac:(
            let goal := Rupicola.Lib.Tactics.program_logic_goal_for_function
                          montladder [felem_cswap; felem_small_literal; felem_copy;
                                        sctestbit; "ladderstep"; inv; mul] in
            exact (__rupicola_program_marker montladder_gallina -> goal)))
         As montladder_correct.
    Proof.
      pose proof scalarbits_pos.
      pose proof unsigned_of_Z_1.
      pose proof unsigned_of_Z_0.
      compile_setup.
      unfold F.one.
      unfold F.zero.
      
      simple apply compile_nlet_as_nlet_eq.
      simple eapply compile_stack; eauto.
      (*TODO: is this doing allocation?*)
      compile_step.
      compile_step.
      simple eapply compile_felem_small_literal; eauto.
      compile_step.
      compile_step.
      simple apply compile_nlet_as_nlet_eq.
      simple eapply compile_stack; eauto.
      compile_step.
      simple eapply compile_felem_small_literal; eauto.
      compile_step.
      compile_step.
      simple apply compile_nlet_as_nlet_eq.
      simple eapply compile_stack; eauto.
      compile_step.
      simple eapply compile_felem_copy; eauto.
      todo (*TODO: hint not working*).
      compile_step.
      compile_step.
      compile_step.
      compile_step.
      simple apply compile_nlet_as_nlet_eq.
      simple eapply compile_stack; eauto.
      compile_step.
      simple eapply compile_felem_small_literal; eauto.
      compile_step.
      compile_step.
      compile_step.
      compile_step.
      compile_step.
      compile_step.
      Import DownToCompiler.
      (*TODO: why not handled by compile step*)
      simple apply compile_nlet_as_nlet_eq.
      lazymatch goal with
      | [ |- WeakestPrecondition.cmd _ _ _ _ ?locals _ ] =>
        let i_v := gensym locals "i" in
        let lp := infer_downto_predicate i_v in
        eapply compile_downto with (i_var := i_v) (loop_pred := lp)
      end.
      todo (*easy*).
      solve[repeat compile_step].
      solve[repeat compile_step].
      solve[repeat compile_step].
      repeat compile_step.
      todo (*spec_of should be in context*).
      2:{
        instantiate (1:=word.of_Z (Z.of_nat i)).
        todo (* easy*).
      }
      solve[repeat compile_step].
      repeat compile_step.
      simple apply compile_nlet_as_nlet_eq.
      eapply compile_bool_xorb. (*TODO: why not already a hint?*)
      solve[repeat compile_step].
      solve[repeat compile_step].
      repeat compile_step.
      (*TODO: why not handled by compile_step?*)
      (*TODO: need free vars from downto_inv?*)
      eapply compile_nlet_as_nlet_eq.
      eapply compile_felem_cswap; eauto;
        try ecancel_assumption.
      solve[repeat compile_step].
      solve[repeat compile_step].
      solve[repeat compile_step].
      repeat compile_step.
      
      (*TODO: automate w/ compile cswap*)
      rewrite cswap_same.

      compile_step.
      (*make sure not to unfold st*)
      remember st as st'.
      destruct st'.
      destruct v8.
      (*TODO: why not handled by compile_step?*)
      (*TODO: need free vars from downto_inv?*)
      eapply compile_nlet_as_nlet_eq.
      eapply compile_felem_cswap; eauto;
        try ecancel_assumption.
      solve[repeat compile_step].
      solve[repeat compile_step].
      solve[repeat compile_step].
      repeat compile_step.
      
      (*TODO: automate w/ compile cswap*)
      rewrite cswap_same.
      
      compile_step.
      destruct v8.
      eapply compile_nlet_as_nlet_eq.
      eapply compile_ladderstep; eauto;
        try ecancel_assumption.
      todo (*TODO: spec of*).
      assert ((FElem (Some tight_bounds) out_ptr0 (fst (f1, f2))
         ⋆ FElem (Some tight_bounds) out_ptr2 (snd (f1, f2))
         ⋆ seps
             [FElem (Some tight_bounds) out_ptr (fst (f, f0));
             FElem (Some tight_bounds) out_ptr1 (snd (f, f0)); Scalar pK K; 
             FElem (Some tight_bounds) pU U; FElem out_bound pOUT OUT; R]) m'8) by
          todo (* TODO: bounds*).
      clear H13.
      solve[repeat compile_step].
      solve[repeat compile_step].
      solve[repeat compile_step].
      solve[repeat compile_step].
      solve[repeat compile_step].
      solve[repeat compile_step].

      compile_step.
      (*TODO: why is this needed?*)
      remember v8 as v9.
      destruct v9 as [[[? ?] ?] ?].
      eapply compile_nlet_as_nlet_eq.
      eapply compile_sctestbit; eauto.
      todo (*TODO: spec of*).
      ecancel_assumption.
      solve[repeat compile_step].
      2:{
        instantiate (1:=word.of_Z (Z.of_nat i)).
        todo (* easy*).
      }
      solve[repeat compile_step].
      {
        compile_step.
        compile_step.
        compile_step.
        cbn [P2.car P2.cdr seps].
        cbn [seps] in H16.
        unfold v8 in *.
        rewrite Heq in Heqv9.
        inversion Heqv9; subst.
        ecancel_assumption.
      }
      {
        repeat compile_step.
      (*TODO: why not handled by compile_step?*)
      (*TODO: need free vars from downto_inv?*)
      eapply compile_nlet_as_nlet_eq.
      eapply compile_felem_cswap; eauto;
        try ecancel_assumption.
      solve[repeat compile_step].
      solve[repeat compile_step].
      solve[repeat compile_step].
      repeat compile_step.
      
      (*TODO: automate w/ compile cswap*)
      rewrite cswap_same.
      
      compile_step.
      destruct v6.

      (*TODO: why not handled by compile_step?*)
      (*TODO: need free vars from downto_inv?*)
      eapply compile_nlet_as_nlet_eq.
      eapply compile_felem_cswap; eauto;
        try ecancel_assumption.
      solve[repeat compile_step].
      solve[repeat compile_step].
      solve[repeat compile_step].
      repeat compile_step.
      
      (*TODO: automate w/ compile cswap*)
      rewrite cswap_same.
      
      compile_step.
      destruct v6.

      (*TODO: tries to apply felem_copy*)
      eapply compile_nlet_as_nlet_eq.
      simple eapply compile_alloc.
      eassumption.
      compile_step.
      compile_step.
      todo (*spec_of*).
      solve[repeat compile_step].
      solve[repeat compile_step].
      assert ((FElem (Some tight_bounds) out_ptr3 uninit3
         ⋆ (FElem (Some tight_bounds) out_ptr0 (fst (f1, f2))
            ⋆ FElem (Some tight_bounds) out_ptr2 (snd (f1, f2))
            ⋆ seps
                [FElem (Some tight_bounds) out_ptr (fst (f, f0));
                FElem (Some tight_bounds) out_ptr1 (snd (f, f0)); 
                FElem (Some tight_bounds) pU U; FElem out_bound pOUT OUT; 
                Scalar pK K; R])) m'9) by
          todo (* TODO: bounds*).
      clear H12.
      ecancel_assumption.
      solve[repeat compile_step].

      compile_step.
      (*TODO: tries to apply felem_copy*)
      eapply compile_nlet_as_nlet_eq.
      simple eapply compile_mul;
      repeat compile_step.
      todo (*spec_of*).
      assert ((FElem (Some loose_bounds) out_ptr3 v6
         ⋆ seps
             [FElem (Some loose_bounds) out_ptr0 f1; FElem (Some loose_bounds) out_ptr2 f2;
             FElem (Some loose_bounds) out_ptr f; FElem (Some loose_bounds) out_ptr1 f0; 
             FElem (Some loose_bounds) pU U; FElem out_bound pOUT OUT; 
             Scalar pK K; R]) m'10) by
          todo (* TODO: bounds*).
      clear H10.
      ecancel_assumption.
      solve[repeat compile_step].
      solve[repeat compile_step].
      assert (seps [FElem (Some tight_bounds) pU U; FElem (Some tight_bounds) pOUT OUT; Scalar pK K; R] H11)
        by todo.
      clear m'11.
      shelve (*TODO: why OUT in hyp?*).
      }

      Unshelve.
      all: todo.
    Qed.
    Eval 
      cbv[ fold_right ExprReflection.compile word.b2w montladder_body gs
                      cmd_downto cmd_downto_fresh]
      in montladder_body.
  End MontLadder.
End __.

Global Hint Extern 1 (spec_of _) => (simple refine (@spec_of_montladder _ _ _ _ _ _ _ _ _ _)) : typeclass_instances.

Import bedrock2.Syntax.Coercions.
Local Unset Printing Coercions.
(*
Redirect "Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.montladder_body" Print montladder_body.
*)
