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

Require Import bedrock2.ZnWords.

Local Open Scope Z_scope.

Import NoExprReflectionCompiler.
Import DownToCompiler.
(* TODO: migrate these to rupicola.
   Currently break when put in Notations.v
 *)
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
      let/n swap := false in
      let/n count := scalarbits in
      let/n (X1, Z1, X2, Z2, swap) :=
         downto
           \<X1, Z1, X2, Z2, swap\> (* initial state *)
           (Z.to_nat count)
           (fun state i =>
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
            (pOUT pK pU : word)
            / (K : scalar) (U : F M_pos) (* inputs *)
            out_bound OUT
            R,
      { requires tr mem :=
          (FElem out_bound pOUT OUT * Scalar pK K * FElem (Some tight_bounds) pU U
           *  R)%sep mem;
        ensures tr' mem' :=
          tr' = tr
          /\ (let OUT := montladder_gallina
                           scalarbits
                           (fun i =>
                              Z.testbit (F.to_Z (sceval K))
                                        (Z.of_nat i))
                           U in
              (FElem (Some tight_bounds) pOUT OUT * Scalar pK K
               * FElem (Some tight_bounds) pU U
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


    (*TODO: determine the best place for felem_cswap. Should it get its own file?*)
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

    (* TODO: why doesn't `Existing Instance` work?
    Existing Instance spec_of_sctestbit.*)
    Hint Extern 1 (spec_of sctestbit) =>
    (simple refine (@spec_of_sctestbit _ _ _ _ _ _ _ _)) : typeclass_instances.
    Hint Extern 1 (spec_of "ladderstep") =>
    (simple refine (@spec_of_ladderstep _ _ _ _ _ _ _ _)) : typeclass_instances.

    (* TODO: this seems a bit delicate*)
    Ltac compile_cswap :=
      eapply compile_felem_cswap;
      [solve[repeat compile_step] ..
      | repeat compile_step;
        rewrite cswap_same;
        compile_step;      
        match goal with
        | [|- (WeakestPrecondition.cmd _ _ _ _ _ (_ (let (_,_) := ?v in _)))] =>
          destruct v
        end].
    
    Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (cswap _ _ _) _))) =>
    compile_cswap; shelve : compiler.
    
    Ltac compile_ladderstep :=
      eapply compile_ladderstep;
      [ | | | | | |
        | compile_step;
          match goal with
          | [|- (WeakestPrecondition.cmd _ _ _ _ _ (_ (match ?e with _ => _ end)))] =>
            let v := fresh "v" in
            remember e as v;
            destruct v as [[[? ?] ?] ?]
          end].
    Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (ladderstep_gallina _ _ _ _ _) _))) =>
    compile_ladderstep; shelve : compiler.

    
    Lemma word_unsigned_of_Z_eq z
      : 0 <= z < 2 ^ width -> word.unsigned (word.of_Z z : word) = z.
    Proof.
      intros.
      rewrite word.unsigned_of_Z.
      rewrite word.wrap_small; auto.
    Qed.

    Hint Extern 8 (word.unsigned (word.of_Z _) = _) =>
    simple eapply word_unsigned_of_Z_eq; [ ZnWords |] : compiler.

    (*TODO: should this go in core rupicola?*)
    (* FIXME find a way to automate the application of these copy lemmas *)
    (* N.B. should only be added to compilation tactics that solve their subgoals,
     since this applies to any shape of goal *)
    Lemma compile_copy_bool {tr m l functions} (x: bool) :
      let v := x in
      forall {P} {pred: P v -> predicate}
             {k: nlet_eq_k P v} {k_impl}
             x_expr var,

        WeakestPrecondition.dexpr m l x_expr (word.of_Z (Z.b2z v)) ->

        (let v := v in
         <{ Trace := tr;
            Memory := m;
            Locals := map.put l var (word.of_Z (Z.b2z v));
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := m;
           Locals := l;
           Functions := functions }>
        cmd.seq (cmd.set var x_expr) k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros.
      repeat straightline.
      eauto.
    Qed.
    Hint Extern 10 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ ?v _))) =>
    is_var v; simple eapply compile_copy_bool; shelve : compiler.
    
    Derive montladder_body SuchThat
           (let args := ["OUT"; "K"; "U"] in
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
      pose proof scalarbits_bound.
      compile_setup.
      unfold F.one.
      unfold F.zero.     
      
      repeat compile_step;
        [ lia | | apply word_unsigned_of_Z_eq; lia | ];
        repeat compile_step.
      (*TODO: the final compile step takes ~30s to fail *)
      {
        cbn [P2.car P2.cdr seps].
        unfold v8 in *.
        rewrite Heq in Heqv9.
        inversion Heqv9; subst.
        ecancel_assumption.
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

