(* NOTE: the plan is to completely redo montladder after ladderstep is updated to use stackalloc *)

Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.SepLocals.
Require Import Rupicola.Lib.ControlFlow.CondSwap.
Require Import Rupicola.Lib.ControlFlow.DownTo.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Compilation.
Require Import Crypto.Bedrock.Group.Point.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.ScalarField.Interface.Compilation.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Specs.ScalarField.
Require Import Crypto.Util.NumTheoryUtil.
Local Open Scope Z_scope.


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
        val  (fun '(v, w, x, y, z) => body))
   (at level 200, v ident,  w ident, x  ident, y ident, z ident, body at level 200,
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
      let/n X1 := felem_alloc 1 in
      let/n Z1 := felem_alloc 0 in
      let/n X2 := felem_alloc u in
      let/n Z2 := felem_alloc 1 in
     (* let/d P1 := (1, 0) in
        let/d P2 := (X2, Z2) in
      *)
      let/n swap := false in
      let/n count := scalarbits in
      let/n (X1, Z1, X2, Z2, swap) :=
         downto
           (X1, Z1, X2, Z2, swap) (* initial state *)
           (Z.to_nat count)
           (fun state i =>
              (*TODO: should this be a /n?*)
              let '(X1, Z1, X2, Z2, swap) := state in
              let/n s_i := testbit i in
              let/n swap := xorb swap s_i in
              let/n (X1, X2) := cswap swap X1 X2 in
              let/n (Z1, Z2) := cswap swap Z1 Z2 in
              let/n (X1, Z1, X2, Z2) := ladderstep_gallina u X1 Z1 X2 Z2 in
              let/n swap := s_i in
              (X1, Z1, X2, Z2, swap)
           ) in
      let/n (X1, X2) := cswap swap X1 X2 in
      let/n (Z1, Z2) := cswap swap Z1 Z2 in
      let/n r := felem_alloc (F.inv Z1) in
      let/n r := (X1 * r) in
      r.
  End Gallina.

  Section MontLadder.
    Context (scalarbits_small : word.wrap scalarbits = scalarbits).

    Instance spec_of_montladder : spec_of "montladder" :=
      fnspec! "montladder"
            (pOUT pK pU (*pX1 pZ1 pX2 pZ2*) : Semantics.word)
            / (K : scalar) (U : felem) (* inputs *)
            OUT (*X1 Z1 X2 Z2 *) (* intermediates *)
            R,
      { requires tr mem :=
           bounded_by tight_bounds U
           /\ (FElem pOUT OUT * Scalar pK K * FElem pU U
              (** FElem pX1 X1 * FElem pZ1 Z1
               * FElem pX2 X2 * FElem pZ2 Z2*)
               *  R)%sep mem;
        ensures tr' mem' :=
          tr' = tr
          /\ (exists OUT (*X1 Z1 X2 Z2*)  : felem,
                 feval OUT = montladder_gallina
                               scalarbits
                               (fun i =>
                                  Z.testbit (F.to_Z (sceval K))
                                            (Z.of_nat i))
                               (feval U)
            /\ bounded_by tight_bounds OUT
            /\ (FElem pOUT OUT * Scalar pK K * FElem pU U
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
            | simple eapply compile_point_assign
            | simple eapply compile_felem_small_literal
            | simple eapply compile_felem_copy
            | simple eapply compile_cswap_pair
            | apply_compile_cswap_nocopy ].

    (* TODO: make a new loop invariant, drop the sep-local stuff *)
    (*nat -> bool -> F M_pos * F M_pos * F M_pos * F M_pos * bool -> predicate*)
    Definition downto_inv
               (swap_var  X1_var Z1_var X2_var Z2_var K_var : string)
               K (K_ptr X1_ptr Z1_ptr X2_ptr Z2_ptr : word) R
               (_ : nat)
               (gst : bool)
               (st : F M_pos * F M_pos * F M_pos * F M_pos * bool)
      : predicate :=
      fun (_ : Semantics.trace)
          (mem : Semantics.mem)
          (locals : Semantics.locals) =>
      let '(x1, z1, x2, z2, swap) := st in
      let swapped := gst in
      (liftexists
                 X1 Z1 X2 Z2,
        (emp (bounded_by tight_bounds X1
              /\ bounded_by tight_bounds Z1
              /\ bounded_by tight_bounds X2
              /\ bounded_by tight_bounds Z2
              /\ feval X1 = x1
                     /\ feval Z1 = z1
                     /\ feval X2 = x2
                     /\ feval Z2 = z2
            /\ map.get locals swap_var = Some (word.of_Z (Z.b2z swap))
            /\ map.get locals K_var = Some K_ptr
            /\ map.get locals X1_var = Some X1_ptr
            /\ map.get locals X2_var = Some X2_ptr
            /\ map.get locals Z1_var = Some Z1_ptr
            /\ map.get locals Z2_var = Some Z2_ptr
             (*
              /\ (Var swap_var (word.of_Z (Z.b2z swap)) * Var K_var K_ptr
                  * Var X1_var X1_ptr' * Var Z1_var Z1_ptr'
                  * Var X2_var X2_ptr' * Var Z2_var Z2_ptr'
                  * Rl)%sep locals *) )
         * (Scalar K_ptr K * FElem X1_ptr X1
            * FElem Z1_ptr Z1
            * FElem X2_ptr X2
            * FElem Z2_ptr Z2) * R)%sep) mem.
    
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

    Ltac safe_field_compile_step :=
      field_compile_step;
      lazymatch goal with
      | |- sep _ ?R _ =>
        tryif is_evar R
        then (repeat rewrite_cswap_iff1_with_evar_frame)
        else (repeat seprewrite (cswap_iff1 FElem));
        ecancel_assumption
      | _ => idtac
      end;
      lazymatch goal with
      | |- context [WeakestPrecondition.cmd] => idtac
      | _ => solve_field_subgoals_with_cswap
      end.

    Existing Instance spec_of_sctestbit.


      Lemma compile_felem_small_literal_alloc {tr mem locals functions} x:
    let v := felem_alloc (F.of_Z _ x) in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      (R : _ -> Prop) (wx : word) out_var,

      spec_of_felem_small_literal functions ->
      R mem ->

      word.unsigned wx = x ->

      (let v := v in
       forall X m out_ptr,
         (FElem out_ptr X * R)%sep m ->
         feval X = v ->
         bounded_by tight_bounds X ->
         (<{ Trace := tr;
             Memory := m;
             Locals := map.put locals out_var out_ptr;
             Functions := functions }>
          k_impl
          <{ pred_sep (Placeholder out_ptr) pred (k v eq_refl) }>)) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.stackalloc out_var (@felem_size_in_bytes field_parameters _ field_representaton)
                     (cmd.seq
                        (cmd.call [] felem_small_literal
                                  [expr.var out_var; expr.literal x])
                        k_impl)
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof.
     repeat straightline'.
     split; eauto using felem_size_in_bytes_mod.
     intros out_ptr mStack mCombined Hplace%FElem_from_bytes.
     destruct Hplace as [out Hout].
     repeat straightline'.
     straightline_call.
     intuition eauto.
     {
       exists mStack.
       exists mem.
       intuition eauto.
       apply map.split_comm; eauto.
     }
     repeat straightline'.
     eapply WeakestPrecondition_weaken
       with (p1 := pred_sep (Memory.anybytes out_ptr felem_size_in_bytes)
                            pred (let/n x as out_var eq:Heq := v in
                                  k x Heq)).
     {
       unfold pred_sep.
       repeat straightline'.
       destruct H4 as [mStack' [m' [Hmem [HmStack Hm]]]].
       unfold Basics.flip in Hm.
       exists m'.
       exists mStack'.
       intuition.
       apply map.split_comm; auto.
     }
     eapply H2; repeat straightline'.
     {
       unfold v.
       unfold felem_alloc.
       eauto.
     }
     eauto.
     {
       rewrite H6.
       rewrite <- H1.
       rewrite word.of_Z_unsigned.
       rewrite H1.
       reflexivity.
     }
     eauto.
  Qed.

  
  Lemma compile_felem_copy_alloc {tr mem locals functions} x :
    let v := feval x in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      R x_ptr x_var out_var,

      spec_of_felem_copy functions ->

      (FElem x_ptr x  * R)%sep mem ->
      map.get locals x_var = Some x_ptr ->

      out_var<> x_var ->
      
      (let v := v in
       forall X m out_ptr,
         (FElem out_ptr X * (FElem x_ptr x  * R))%sep m ->
         feval X = v ->
         (<{ Trace := tr;
             Memory := m;
             Locals := map.put locals out_var out_ptr;
             Functions := functions }>
          k_impl
          <{ pred_sep (Placeholder out_ptr) pred (k v eq_refl) }>)) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.stackalloc out_var (@felem_size_in_bytes field_parameters _ field_representaton)
      (cmd.seq
        (cmd.call [] felem_copy [expr.var out_var; expr.var x_var])
        k_impl)
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof.
     repeat straightline'.
     split; eauto using felem_size_in_bytes_mod.
     intros out_ptr mStack mCombined Hplace%FElem_from_bytes.
     destruct Hplace as [out Hout].
     repeat straightline'.
     straightline_call.
     intuition eauto.
     {
       apply sep_assoc.
       apply sep_comm.
       apply sep_assoc.
       exists mStack.
       exists mem.
       intuition eauto.
       eauto.
       apply map.split_comm; eauto.
       apply sep_comm; eauto.
     }
     repeat straightline'.
     eapply WeakestPrecondition_weaken
       with (p1 := pred_sep (Memory.anybytes out_ptr felem_size_in_bytes)
                            pred (let/n x as out_var eq:Heq := v in
                                  k x Heq)).
     {
       unfold pred_sep.
       repeat straightline'.
       destruct H5 as [mStack' [m' [Hmem [HmStack Hm]]]].
       unfold Basics.flip in Hm.
       exists m'.
       exists mStack'.
       intuition.
       apply map.split_comm; auto.
     }
     eapply H3; repeat straightline'.
     {
       unfold v.
       unfold felem_alloc.
       ecancel_assumption.
     }
     eauto.
  Qed.

  (*TODO: get compiling
  Require Import Rupicola.Examples.CMove.
   *)
  
 Definition felem_cswap := "felem_cswap".
  (*TODO: move to the right place;
    TODO: instantiate
   *)  
  Instance spec_of_felem_cswap : spec_of felem_cswap :=
    fnspec! felem_cswap mask ptr1 ptr2 / b c1 c2 R,
    { requires tr mem :=
        mask = word.of_Z (Z.b2z b) /\
        (FElem ptr1 c1 * FElem ptr2 c2 * R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        let (c1,c2) := cswap b c1 c2 in
        (FElem ptr1 c1 * FElem ptr2 c2 * R)%sep mem' }.
  
   Lemma compile_felem_cswap {tr mem locals functions} swap (lhs rhs : F M_pos) :
    let v := cswap swap lhs rhs in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      R mask_var lhs_ptr lhs_var lhs' rhs_ptr rhs_var rhs',

      spec_of_felem_cswap functions ->

      map.get locals mask_var = Some (word.of_Z (Z.b2z swap)) ->
      
      map.get locals lhs_var = Some lhs_ptr ->
      map.get locals rhs_var = Some rhs_ptr ->

      
      feval lhs' = lhs ->
      feval rhs' = rhs ->

      (FElem lhs_ptr lhs' * FElem rhs_ptr rhs' * R)%sep mem ->

      (let v := v in
       forall m lhs' rhs',
         feval lhs' = fst v ->
         feval rhs' = snd v ->
         (FElem lhs_ptr lhs' * FElem rhs_ptr rhs' * R)%sep m ->
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
        (cmd.call [] felem_cswap [expr.var mask_var; expr.var lhs_var; expr.var rhs_var])
        k_impl
      <{ pred (nlet_eq [lhs_var; rhs_var] v k) }>.
   Proof.     
     Local Ltac prove_field_compilation :=
       repeat straightline';
       handle_call;
       lazymatch goal with
       | |- sep _ _ _ => ecancel_assumption
       | _ => idtac
       end; eauto;
       sepsimpl; repeat straightline'; subst; eauto.
     prove_field_compilation.
     destruct swap; eapply H6; unfold v; unfold cswap; simpl; eauto.
   Qed.
   Hint Resolve compile_felem_cswap : compiler.
    

  (*TODO: why doesn't simple eapply work? *)
Ltac field_compile_step ::=
  first [ simple eapply compile_scmula24 (* must precede compile_mul *)
        | simple eapply compile_mul
        | simple eapply compile_add
        | simple eapply compile_sub
        | simple eapply compile_square
        | simple eapply compile_inv
        (*must come second due to eapply *)
        | eapply compile_scmula24_alloc (* must precede compile_mul_alloc *)
        | eapply compile_mul_alloc
        | eapply compile_add_alloc
        | eapply compile_sub_alloc
        | eapply compile_square_alloc
        | eapply compile_inv_alloc 
        | eapply compile_felem_small_literal_alloc
        | eapply compile_felem_copy_alloc ];
  lazymatch goal with
  | |- feval _ = _ => try eassumption; try reflexivity
  | |- _ => idtac
  end.


  
  Ltac ladderstep_compile_custom :=
    simple apply compile_nlet_as_nlet_eq;
    field_compile_step; [ repeat compile_step .. | intros ];
    eauto with compiler;
    (* rewrite results in terms of feval to match lemmas *)
    repeat lazymatch goal with
           | H : feval _ = ?x |- context [?x] =>
             is_var x; rewrite <-H
           end.
  
  Ltac compile_custom ::= ladderstep_compile_custom.


  
  (*TODO: move to right place*)
  (* There are two ways cswap could be compiled; you can either swap the local
     variables (the pointers), or you can leave the pointers and copy over the
     data. This version does the copying. *)
  Lemma compile_cswap_nocopy {tr mem locals functions} (swap: bool) {A} (x y: A) :
    let v := cswap swap x y in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      R (Data : word -> A -> Semantics.mem -> Prop)
      swap_var x_var x_ptr y_var y_ptr tmp,

      map.get locals swap_var = Some (word.of_Z (Z.b2z swap)) ->
      map.get locals x_var = Some x_ptr ->
      map.get locals y_var = Some y_ptr ->

      (* tmp is a strictly temporary variable, confined to one part of the
         if-clause; it gets unset after use *)
      map.get locals tmp = None ->
      (Data x_ptr x * Data y_ptr y * R)%sep mem ->

      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put (map.put locals x_var (fst (cswap swap x_ptr y_ptr))) y_var
                      (snd (cswap swap x_ptr y_ptr));
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.cond
           (expr.var swap_var)
           (cmd.seq
              (cmd.seq
                 (cmd.seq
                    (cmd.set tmp (expr.var x_var))
                    (cmd.set x_var (expr.var y_var)))
                 (cmd.set y_var (expr.var tmp)))
              (cmd.unset tmp))
           (cmd.skip))
        k_impl
      <{ pred (nlet_eq [x_var; y_var] v k) }>.
  Proof.
    intros; subst v; unfold cswap.
    simple eapply compile_if with
        (val_pred := fun _ tr' mem' locals' =>
                      tr' = tr /\
                      mem' = mem /\
                      locals' =
                      let locals := map.put locals x_var (if swap then y_ptr else x_ptr) in
                      let locals := map.put locals y_var (if swap then x_ptr else y_ptr) in
                      locals);
      repeat compile_step;
      repeat straightline'; subst_lets_in_goal; cbn; ssplit; eauto.
    - rewrite !map.remove_put_diff, !map.remove_put_same, map.remove_not_in by congruence.
      reflexivity.
    - rewrite (map.put_noop x_var x_ptr), map.put_noop by assumption.
      reflexivity.
    - cbv beta in *; repeat compile_step; cbn.
      destruct swap; eassumption.
  Qed.

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
      compile_step. 
      compile_step.
      compile_step.
      compile_step.
      compile_step.
      compile_step.
      compile_step.
      compile_step.
      compile_step.
      compile_step.
      simple apply compile_nlet_as_nlet_eq.
      let tmp_var := constr:("tmp") in
      let x1_var := constr:("X1") in
      let z1_var := constr:("Z1") in
      let x2_var := constr:("X2") in
      let z2_var := constr:("Z2") in
      let counter_var := constr:("count") in
      eapply compile_downto with (i_var := counter_var)
      (wcount := word.of_Z scalarbits)
      (ginit := false)
      (ghost_step := downto_ghost_step K)
      (Inv :=
         downto_inv
           _ x1_var z1_var x2_var z2_var _
           _ pK out_ptr out_ptr0 out_ptr1 out_ptr2
           _).
      {
        unfold downto_inv.
        repeat compile_step.
        exists X.
        exists X0.
        exists X1.
        exists X2.
        progress sepsimpl; eauto.
        admit(*TODO: X1 related to U; how to find/preserve bounds?*).
        instantiate (1:="swap").
        rewrite map.get_remove_diff.
        compile_step.
        compile_step.
        instantiate (1:="K").
        rewrite map.get_remove_diff.
        compile_step.
        compile_step.
        all: try rewrite map.get_remove_diff.
        all: repeat compile_step.
      }
      compile_step.
      admit (*z/word math*).
      lia.
      {
        compile_step.
        unfold downto_inv in H12.
        do 4 destruct st as [st ?].
        do 4 destruct H12 as [? H12].
        sepsimpl.
        clear gst'.
        eapply compile_nlet_as_nlet_eq.
        eapply compile_sctestbit; eauto.
        ecancel_assumption.
        all: 
          repeat
            match goal with
            | [H : map.get (map.remove _ _)_ = _|-_] =>
              rewrite map.get_remove_diff in H; [| compile_step];[]
            end.
        {
          rewrite map.get_put_diff; eauto;
            compile_step.
        }
        compile_step.
        repeat compile_step.
        {
          repeat rewrite map.get_put_diff;
            repeat compile_step.
        }
        repeat compile_step.
        (*TODO: why not handled by compile_step?*)
        (*TODO: need free vars from downto_inv?*)
        eapply compile_nlet_as_nlet_eq.
        eapply compile_felem_cswap; eauto;
          try ecancel_assumption.
        compile_step.
        {
          repeat rewrite map.get_put_diff; compile_step.
        }
        {
          repeat rewrite map.get_put_diff; compile_step.
        }
        {
          compile_step.
          remember v8 as v9.
          unfold v8 in *.
          clear v8.
          rewrite destruct_cswap in Heqv9.
          destruct v9 as [v91 v92].
          inversion Heqv9; clear Heqv9; subst v91 v92.

          
          eapply compile_nlet_as_nlet_eq.
          eapply compile_felem_cswap; eauto;
            try ecancel_assumption.
          compile_step.
          {
            repeat rewrite map.get_put_diff; compile_step.
          }
          {
            repeat rewrite map.get_put_diff; compile_step.
          }
          compile_step.
          remember v8 as v9.
          unfold v8 in *.
          clear v8.
          rewrite destruct_cswap in Heqv9.
          destruct v9 as [v91 v92].
          inversion Heqv9; clear Heqv9; subst v91 v92.
          
          eapply compile_nlet_as_nlet_eq.
          cbn [fst snd] in *.
          eapply compile_ladderstep; eauto;
            try ecancel_assumption.
          admit (*TODO: bounds*).
          admit (*TODO: bounds*).
          admit (*TODO: bounds*).
          admit (*TODO: bounds*).
          admit (*TODO: bounds*).
          assert (X1 = U) by admit (*TODO: want X1 to be U*).
          subst X1.
          ecancel_assumption.
          {
            repeat rewrite map.get_put_diff.
            admit (*TODO: U ptr*).
            admit.
            admit.
            admit.
          }
          all: try solve [repeat rewrite map.get_put_diff; compile_step].
          repeat compile_step.
          admit (*easy*).
          {
            unfold downto_inv.
            admit(*TODO: is this unnecessarily complex? ghost state is showing up*).
          }
        }
      }
      {
        compile_step.
        remember v5 as v6.
        destruct v6 as [[[[? ?] ?] ?] ?].
        unfold downto_inv in H12.
        sepsimpl.
        all: 
          repeat
            match goal with
            | [H : map.get (map.remove _ _)_ = _|-_] =>
              rewrite map.get_remove_diff in H; [| compile_step];[]
            end.

        
        eapply compile_nlet_as_nlet_eq.
        eapply compile_felem_cswap; eauto.
        ecancel_assumption.

        compile_step.
        remember v6 as v9.
        unfold v6 in *.
        clear v6.
        rewrite destruct_cswap in Heqv9.
        destruct v9 as [v91 v92].
        inversion Heqv9; clear Heqv9; subst v91 v92.
        cbn [fst snd] in *.

        
        eapply compile_nlet_as_nlet_eq.
        eapply compile_felem_cswap; eauto.
        ecancel_assumption.
        
        compile_step.
        remember v6 as v9.
        unfold v6 in *.
        clear v6.
        rewrite destruct_cswap in Heqv9.
        destruct v9 as [v91 v92].
        inversion Heqv9; clear Heqv9; subst v91 v92.
        cbn [fst snd] in *.

        rewrite <- H38.
        compile_step.
        admit (*TOD: bounds*).
        rewrite <- H35.
        rewrite <- Heq.
        compile_step.
        admit (*TOD: bounds*).
        {
          rewrite map.get_put_same; auto.
        }
        {
          rewrite map.get_put_diff; eauto.
          compile_step.
        }
        repeat compile_step.
        {
    unfold pred_sep; simpl.
    unfold Basics.flip; simpl.
    repeat change (fun x => ?h x) with h.
    unfold map.getmany_of_list.
    simpl.
    {      
      repeat match goal with
      | [ H : _ ?m |- _ ?m] =>
      eapply Proper_sep_impl1;
        [ eapply FElem_to_bytes | clear H m; intros H m | ecancel_assumption]
      end.
      exists [].
      repeat compile_step.
      admit (*TODO: not lined up right*).

      eexists; intuition.
      (*TODO: out and out0 not limed up; want FElem'?*)
      admit (*ecancel_assumption.*).
    }
      Unshelve.
      constructor.

(* NOTE: the plan is to completely redo montladder after ladderstep is updated to use stackalloc *)
    Abort.
(*
      pose proof scalarbits_pos.
      compile_setup.
      repeat compile_step.
      (* need to update point compilation lemmas! Point.v *)

      (* compile constants *)

      cbv [program_logic_goal_for spec_of_montladder].
      setup. cbv [F.one F.zero]. (* expose F.of_Z *)

      (* prevent things from getting stored in pOUT *)
      hide pOUT.

      repeat safe_compile_step.

      let i_var := gen_sym_fetch "v" in (* last used variable name *)
      let locals := lazymatch goal with
                    | |- WeakestPrecondition.cmd _ _ _ _ ?l _ => l end in
      remember locals as L;
      evar (l : map.rep (map:=locals));
        let Hl := fresh in
        assert (map.remove L i_var = l) as Hl by
              (subst L; push_map_remove; subst_lets_in_goal; reflexivity);
          subst l;
          match type of Hl with
          | _ = ?l =>
            sep_from_literal_locals l;
              match goal with H : sep _ _ l |- _ =>
                              rewrite <-Hl in H; clear Hl
              end
          end.

      let tmp_var := constr:("tmp") in
      let x1_var := constr:("X1") in
      let z1_var := constr:("Z1") in
      let x2_var := constr:("X2") in
      let z2_var := constr:("Z2") in
      let counter_var := gen_sym_fetch "v" in
      let locals := lazymatch goal with
                    | |- WeakestPrecondition.cmd _ _ _ _ ?l _ => l end in
        simple eapply compile_downto with
            (wcount := word.of_Z scalarbits)
            (ginit := false)
            (i_var := counter_var)
            (ghost_step := downto_ghost_step K)
            (Inv :=
               downto_inv
                 _ x1_var z1_var x2_var z2_var _
                 _ pK pX1 pZ1 pX2 pZ2
                 _ pA pAA pB pBB pE pC pD pDA pCB);
          [ .. | subst L | subst L ].
      { cbv [downto_inv].
        setup_downto_inv_init.
        all:solve_downto_inv_subgoals. }
      { subst. autorewrite with mapsimpl.
        reflexivity. }
      { rewrite word.unsigned_of_Z, Z2Nat.id by lia;
          solve [eauto using scalarbits_small]. }
      { subst_lets_in_goal. lia. }
      { (* loop body *)
        intros. clear_old_seps.
        match goal with gst' := downto_ghost_step _ _ _ _ |- _ =>
                                subst gst' end.
        destruct_products.
        cbv [downto_inv] in * |-. sepsimpl_hyps.
        eexists; intros.

        (* convert locals back to literal map using the separation-logic
           condition; an alternative would be to have all lemmas play nice with
           locals in separation logic *)
        match goal with H : sep _ _ (map.remove _ ?i_var)
                        |- context [map.get _ ?i_var = Some ?wi] =>
                        eapply Var_put_remove with (v:=wi) in H;
                          eapply sep_assoc in H
        end.
        literal_locals_from_sep.

        repeat safe_compile_step.

        simple eapply compile_ladderstep.
        (* first, resolve evars *)
        all:lazymatch goal with
            | |- feval _ = _ =>
              solve [eauto using feval_fst_cswap, feval_snd_cswap]
            | _ => idtac
            end.
        (* *after* evar resolution *)
        all:lazymatch goal with
            | |- sep _ _ _ =>
              repeat seprewrite (cswap_iff1 FElem);
                ecancel_assumption
            | |- context [WeakestPrecondition.cmd] => idtac
            | _ => solve_field_subgoals_with_cswap
            end.

        repeat safe_compile_step.

        (* TODO: use nlet to do this rename automatically *)
        let locals := lazymatch goal with
                      | |- WeakestPrecondition.cmd _ _ _ _ ?l _ => l end in
        let b := lazymatch goal with x := xorb ?b _ |- _ => b end in
        let swap_var := lazymatch locals with
                          context [map.put _ ?x (word.of_Z (Z.b2z b))] => x end in
        eapply compile_rename_bool with (var := swap_var);
          [ solve [repeat compile_step] .. | ].
        intro.

        (* unset loop-local variables *)
        repeat remove_unused_var.

        compile_done.
        { (* prove locals postcondition *)
          autorewrite with mapsimpl.
          ssplit; [ | reflexivity ].
          subst_lets_in_goal. reflexivity. }
        { (* prove loop invariant held *)
          cbv [downto_inv downto_ghost_step].
          cbv [LadderStepResult] in *.
          cleanup; sepsimpl_hyps.
          repeat match goal with
                 | H : ?x = (_, _) |- context [fst ?x] =>
                   rewrite H; progress cbn [fst snd]
                 end.
          clear_old_seps.
          lift_eexists. sepsimpl.
          (* first, resolve evars *)
          all:lazymatch goal with
              | |- @sep _ _ mem _ _ _ =>
                repeat seprewrite FElem_from_bytes;
                repeat (sepsimpl; lift_eexists);
                ecancel_assumption
              | |- @sep _ _ locals _ _ ?locals =>
                subst_lets_in_goal; push_map_remove;
                  let locals := match goal with |- ?P ?l => l end in
                  sep_from_literal_locals locals;
                    ecancel_assumption
              | _ => idtac
              end.
          (* now solve other subgoals *)
          all:subst_lets_in_goal; eauto.
          match goal with
          | H : if ?gst then _ else _ |-
            if xorb ?gst ?x then _ else _ =>
            destr gst; cleanup; subst;
              cbn [xorb]; destr x
          end.
          all:cbn [cswap fst snd]; ssplit; reflexivity. } }
      { (* loop done; rest of function *)
        intros. destruct_products.
        cbv [downto_inv downto_inv] in *.
        sepsimpl_hyps.

        (* convert locals back to literal map using the separation-logic
           condition; an alternative would be to have all lemmas play nice with
           locals in separation logic *)
        match goal with H : sep _ _ (map.remove _ ?i_var),
                            Hget : map.get _ ?i_var = Some ?wi |- _ =>
                        eapply Var_put_remove with (v:=wi) in H;
                          eapply sep_assoc in H;
                          rewrite map.put_noop in H by assumption
        end.
        literal_locals_from_sep.

        repeat safe_compile_step. (cbv match zeta beta).

        subst_lets_in_goal. erewrite <-!feval_fst_cswap by eauto.
        safe_field_compile_step. safe_compile_step.

        (* the output of this last operation needs to be stored in the pointer
           for the output, so we guide the automation to the right pointer *)
        clear_old_seps.
        repeat lazymatch goal with
               | H : sep _ _ _ |- _ =>
                 seprewrite_in FElem_from_bytes H
               end.
        sepsimpl.
        unhide pOUT.

        safe_field_compile_step.
        repeat safe_compile_step.
        compile_done. cbv [MontLadderResult].
        (* destruct the hypothesis identifying the new pointers as some swapping
           of the original ones *)
        destruct_one_match_hyp_of_type bool.
        all:cleanup; subst.
        all:lift_eexists.
        all:sepsimpl; [ solve [eauto] .. | ].
        all:repeat seprewrite FElem_from_bytes.
        all:repeat (sepsimpl; lift_eexists).
        all:ecancel_assumption. }
    Qed.
 *)

  End MontLadder.
End __.

Global Hint Extern 1 (spec_of _) => (simple refine (@spec_of_montladder _ _ _ _ _ _ _ _ _ _)) : typeclass_instances.

Import bedrock2.Syntax.Coercions.
Local Unset Printing Coercions.
(*
Redirect "Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.montladder_body" Print montladder_body.
*)
