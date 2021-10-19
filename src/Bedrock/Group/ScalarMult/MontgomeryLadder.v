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

Import DownToCompiler.
Locate "let/n".
(* TODO: migrate these to rupicola.
   Currently break when put in Notations.v
 *)
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
      let/n OUT := (F.inv Z1) in
      let/n OUT := (X1 * OUT) in
      OUT.
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

    (* Adding word.unsigned_of_Z_1 and word.unsigned_of_Z_0 as hints to
       compiler doesn't work, presumably because of the typeclass
       preconditions. This is a hacky workaround. *)
    (* TODO: figure out a cleaner way to do this *)
    Lemma unsigned_of_Z_1 : word.unsigned (@word.of_Z _ word 1) = 1.
    Proof. exact word.unsigned_of_Z_1. Qed.
    Lemma unsigned_of_Z_0 : word.unsigned (@word.of_Z _ word 0) = 0.
    Proof. exact word.unsigned_of_Z_0. Qed.
    Hint Resolve unsigned_of_Z_0 unsigned_of_Z_1 : compiler.

    
    Existing Instance spec_of_sctestbit.
    
    Hint Extern 8
         (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (Z.testbit (F.to_Z (sceval _)) _) _))) =>
    simple eapply compile_sctestbit; shelve : compiler.


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

  Existing Instance felem_alloc.


  Lemma cswap_same {A} b (a : A): cswap b a a = (a,a).
  Proof.
    destruct b; reflexivity.
  Qed.
  
  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

  Lemma scalarbits_bound : scalarbits < 2 ^ width.
  Proof.
    rewrite <- scalarbits_small.
    unfold word.wrap.
    apply Z_mod_lt.
    pose proof word.width_pos.
    pose proof (Z.pow_pos_nonneg 2 width ltac:(lia)).
    lia.
  Qed.

  (*TODO: tactics not working; specs not properly generated *)
(*
  Derive montladder_body SuchThat
 (let args := ["OUT"; "K"; "U"] in
  let montladder := ("montladder", (args, [], montladder_body)) in
  __rupicola_program_marker montladder_gallina ->
  forall functions : list bedrock_func,
  spec_of_felem_cswap functions ->
  spec_of_felem_small_literal functions ->
  spec_of_felem_small_literal functions ->
  spec_of_felem_copy functions ->
  spec_of_sctestbit functions ->
  spec_of_ladderstep functions ->
  spec_of_UnOp un_inv functions ->
  spec_of_BinOp bin_mul functions ->
  spec_of_montladder (montladder :: functions))
  As montladder_correct.*)

  (* TODO: why doesn't `Existing Instance` work?
    Existing Instance spec_of_sctestbit.*)
  Hint Extern 1 (spec_of sctestbit) =>
  (simple refine (@spec_of_sctestbit _ _ _ _ _ _ _ _)) : typeclass_instances.
  Hint Extern 1 (spec_of "ladderstep") =>
  (simple refine (@spec_of_ladderstep _ _ _ _ _ _ _ _)) : typeclass_instances.


  
(* TODO: this one is dangerous to have as a hint.
   How should we automate this? check for an identifier? marker like `stack`? seems fragile
#[export] Hint Extern 10 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ _ _))) =>
simple eapply compile_felem_copy; shelve : compiler.
 *)
  
  Derive montladder_body SuchThat
           (let args := ["OUT"; "K"; "U" (*;"X1"; "Z1"; "X2"; "Z2" *)] in
            let montladder : Syntax.func :=
                ("montladder", (args, [], montladder_body)) in
          ltac:(
            let goal := Rupicola.Lib.Tactics.program_logic_goal_for_function
                          montladder [felem_cswap; felem_copy; felem_small_literal;
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

      repeat compile_step.
      simple eapply compile_felem_copy; repeat compile_step.
      
      { pose proof scalarbits_bound; lia. }
      2:{
        instantiate (1:=word.of_Z (Z.of_nat i)).
        rewrite word.unsigned_of_Z.
        rewrite word.wrap_small; auto.
        pose proof scalarbits_bound.
        lia.
      }
      solve[repeat compile_step].
      {
      repeat compile_step.
      eapply compile_nlet_as_nlet_eq.
      eapply compile_bool_xorb. (*TODO: why not already a hint?*)
      solve[repeat compile_step].
      solve[repeat compile_step].
      repeat compile_step.
      (*TODO: why not handled by compile_step?*)
      (*TODO: need free vars from downto_inv?*)
      eapply compile_nlet_as_nlet_eq.
      eapply compile_felem_cswap;
        [solve[repeat compile_step] .. | ].
      
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
      eapply compile_felem_cswap;
        [solve[repeat compile_step] .. | ].
      
      repeat compile_step.
      
      (*TODO: automate w/ compile cswap*)
      rewrite cswap_same.
      
      compile_step.
      destruct v8.
      eapply compile_nlet_as_nlet_eq.
      eapply compile_ladderstep; [ solve[repeat compile_step] .. |].

      compile_step.
      (*TODO: why is this needed?*)
      remember v8 as v9.
      destruct v9 as [[[? ?] ?] ?].
      eapply compile_nlet_as_nlet_eq.
      eapply compile_sctestbit; eauto.
      solve[repeat compile_step].
      solve[repeat compile_step].
      2:{
        instantiate (1:=word.of_Z (Z.of_nat i)).
        rewrite word.unsigned_of_Z.
        rewrite word.wrap_small; auto.
        pose proof scalarbits_bound.
        lia.
      }
      solve[repeat compile_step].
      {
          compile_step.
          compile_step.
          compile_step.
          cbn [P2.car P2.cdr seps].
          unfold v8 in *.
          rewrite Heq in Heqv9.
          inversion Heqv9; subst.
          ecancel_assumption.
      }
      }
      {
        repeat compile_step.
        (*TODO: why not handled by compile_step?*)
        (*TODO: need free vars from downto_inv?*)
        eapply compile_nlet_as_nlet_eq.
        eapply compile_felem_cswap;
          [solve[repeat compile_step] .. | ].
        
        repeat compile_step.
        
        (*TODO: automate w/ compile cswap*)
        rewrite cswap_same.
        
        compile_step.
        destruct v6.

         (*TODO: why not handled by compile_step?*)
        (*TODO: need free vars from downto_inv?*)
        eapply compile_nlet_as_nlet_eq.
        eapply compile_felem_cswap;
          [solve[repeat compile_step] .. | ].
        
        repeat compile_step.
        
        (*TODO: automate w/ compile cswap*)
        rewrite cswap_same.
        
        compile_step.
        destruct v6.

        repeat compile_step.
      }
    Qed.
  End MontLadder.
End __.

Global Hint Extern 1 (spec_of "montladder") => (simple refine (@spec_of_montladder _ _ _ _ _ _ _ _ _ _)) : typeclass_instances.

Import bedrock2.Syntax.Coercions.
Local Unset Printing Coercions.
(* Set the printing width so that arguments are printed on 1 line.
   Otherwise the build breaks.
*)
Local Set Printing Width 160.
Redirect "Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.montladder_body" Print montladder_body.
