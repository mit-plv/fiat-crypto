Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Array.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Operation.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.Tactics.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.X25519_64.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import bedrock2.Semantics.

Require Import Crypto.Bedrock.Field.Interface.Representation.

Import ListNotations.
Import Syntax.Coercions.
Local Open Scope Z_scope.

Existing Instances
         Defaults64.default_parameters names
         curve25519_bedrock2_funcs curve25519_bedrock2_specs
         curve25519_bedrock2_correctness.
Local Open Scope string_scope.

(* Notations to make spec more readable *)
Local Notation n := X25519_64.n.
Local Notation s := X25519_64.s.
Local Notation c := X25519_64.c.
Local Notation machine_wordsize := X25519_64.machine_wordsize.
Local Notation M := (UnsaturatedSolinas.m s c).
Local Notation weight :=
  (ModOps.weight (QArith_base.Qnum
                    (UnsaturatedSolinasHeuristics.limbwidth n s c))
                 (Z.pos (QArith_base.Qden
                           (UnsaturatedSolinasHeuristics.limbwidth n s c)))).
Local Notation eval := (Positional.eval weight n).
Local Notation loose_bounds := (UnsaturatedSolinasHeuristics.loose_bounds n s c).
Local Notation tight_bounds := (UnsaturatedSolinasHeuristics.tight_bounds n s c).
Local Infix "*" := sep : sep_scope.
Delimit Scope sep_scope with sep.

Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Util.ZRange.

Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.

Section FImpl.
  Context {field_parameters : FieldParameters}.
  Context (sz : nat) (weight : nat -> Z)
          (loose_bounds tight_bounds : list (option zrange))
          (relax_bounds :
             forall X : list Z,
               list_Z_bounded_by tight_bounds X ->
               list_Z_bounded_by loose_bounds X).

  Local Definition frep := (frep sz weight loose_bounds tight_bounds).
  
  Existing Instance field_parameters.
  Existing Instance semantics.
  Existing Instance frep.
  Existing Instance frep_ok.

  Definition copy_spec :=
    (@spec_of_felem_copy semantics field_parameters frep).
  Existing Instance copy_spec.

   Fixpoint rep (n : nat) (cmdf : nat -> cmd) : cmd :=
    match n with
    | O => cmd.skip
    | S n' => cmd.seq (cmdf n') (rep n' cmdf)
    end. 

  Local Definition incr_nat x n :=
    expr.op bopname.add x ((Memory.bytes_per_word Semantics.width) * Z.of_nat n).

  Lemma copy_satisfies_spec :
    (let args := ["out"; "x"] in
     let rets := [] in
     let copy_body :=  (rep sz
                          (fun n =>
                             cmd.store access_size.word
                                     (incr_nat "out" (sz - 1 - n))
                                     (expr.load access_size.word (incr_nat "x" (sz - 1 - n))))) in
     let felem_copy := (felem_copy, (args, rets, copy_body)) in
     program_logic_goal_for
       felem_copy
       (forall functions : list (string * (list string * list string * cmd)),
           copy_spec (felem_copy :: functions))).
  Proof.
    
    Require Import Rupicola.Lib.Api.
    unfold copy_spec.
    unfold spec_of_felem_copy.

    cbv[program_logic_goal_for].
    intros; WeakestPrecondition.unfold1_call_goal; cbv beta match delta [WeakestPrecondition.call_body].
    
   
    lazymatch goal with
     | |- if ?test then ?T else _ => rewrite String.eqb_refl; change_no_check T
    end; cbv beta match delta [WeakestPrecondition.func].
    repeat straightline; subst_lets_in_goal.
    cbn[Datatypes.length].
    (first
   [ apply postcondition_func_norets_postcondition_cmd | apply postcondition_func_postcondition_cmd ]).

    cbv[FElem frep Representation.frep felem_size_in_bytes Placeholder Bignum] in *.
    revert mem H.
    (*TODO: want to do induction on rep sz but not fn szs *)
    induction sz;
      destruct x; cbn[Datatypes.length].
    {
      intro.
      simpl.
      cbv[postcondition_cmd]; repeat split; auto.
      exists [].
      split; cbn; auto.
      clear sz functions tr.
      eapply Util.iff1_sep_cancel_both;[| reflexivity | eassumption].
      clear H.
      repeat eapply Util.iff1_sep_cancel_both; try reflexivity.
      split.
      {
        simpl.
        cbv[anybytes ftprint sep emp].
        intro H.
        do 2 destruct H.
        destruct H.
        do 2 destruct H0.
        destruct H1.
        subst.
        destruct H.
        simpl in H; subst.
        exists []; reflexivity.
      }
      {          
        intros H.
        destruct H.
        cbv[anybytes ftprint sep emp] in H.
        simpl in H.
        destruct x0; simpl in *; inversion H; subst.
        cbv[sep].
        exists map.empty.
        exists map.empty.
        simpl.
        repeat split; eauto.
        intros k v1 v2 H1 H2.
        inversion H1.
      }
    }
    {
      simpl.
      intros mem H.
      exfalso.
      do 3 destruct H.
      do 5 destruct H0.
      do 5 destruct H2.
      destruct H5.
      inversion H5.
      inversion H9.
    }
    {
      simpl.
      intros mem H.
      exfalso.
      do 3 destruct H.
      do 5 destruct H0.
      do 5 destruct H2.
      destruct H5.
      inversion H5.
      inversion H9.
    }
    {
      intros mem H.
      cbn[FImpl.rep array].
      assert (S (Datatypes.length x) = S n).
      {
        repeat match goal with
               | H : ?G |- ?G => exact H
               | H : context[?G] |- ?G =>
                 destruct H
               end.
      }
      rewrite H0.
      inversion H0.
      repeat straightline.
      exists r.
      split.
      {
        simpl.
        rewrite Nat.sub_0_r.
        rewrite Nat.sub_diag.
        unfold incr_nat.
        rewrite Z.mul_0_r.
        cbv[WeakestPrecondition.dexpr
              WeakestPrecondition.expr
              WeakestPrecondition.expr_body
              WeakestPrecondition.get
              WeakestPrecondition.literal ].
        exists px.
        split; simpl; auto.
        cbv[dlet].
        cbn[Naive.unsigned Naive.wrap].
        rewrite Z.mod_0_l.
        {
          rewrite Z.add_0_r.
          exists r; split; auto.
          rewrite Naive.of_Z_unsigned.
          cbn [array] in H.
          Search _ sep.
          apply sep_assoc in H.
          apply sep_comm in H.
          apply sep_assoc in H.
          apply sep_comm in H.
          apply sep_assoc in H.
          apply sep_comm in H.
          apply sep_emp_l in H; destruct H.
          apply sep_comm in H1.
          apply sep_assoc in H1.
          apply sep_comm in H1.
          apply sep_assoc in H1.
          apply sep_comm in H1.
          eapply load_word_of_sep; eauto.
        }
        {
          apply Z.pow_nonzero.
          { intro zeq; inversion zeq. }
          { intro zle; inversion zle. }
        }
      }
      {
        simpl.
        cbv[WeakestPrecondition.store].
        
        assert (S (Datatypes.length x) - 1 - Datatypes.length x = (0:nat)).
        {
          simpl.
          rewrite Nat.sub_0_r.
          rewrite Nat.sub_diag.
          reflexivity.
        }
        assert (a =word.add pout
                            (word.of_Z (bytes_per_word width * Z.of_nat 0))).
        {        
          unfold a.
          f_equal.
          f_equal.
          f_equal.
          f_equal.
          exact H1.
        }
        cbn[Z.of_nat] in H3.
        rewrite Z.mul_0_r in H3.
        assert (a = pout).
        {
          rewrite <- word.of_Z_unsigned in H3.
          rewrite H3.
(*          cbv[word word.of_Z semantics Defaults64.default_parameters BasicC64Semantics.parameters
                   Naive.word].*)
          rewrite word.unsigned_add.
          rewrite word.unsigned_of_Z.
          rewrite (word.wrap_small 0).
          {
            rewrite Z.add_0_r.
            rewrite <- word.unsigned_of_Z.
            repeat rewrite word.of_Z_unsigned.
            reflexivity.
          }
          {
            split.
            { intro eq; inversion eq. }
            { apply Z.pow_pos_nonneg.
              { constructor. }
              { intro eq; inversion eq. }
            }
          }
        }
        rewrite H4.
        eexists.
        split.
        {
          cbv[store store_Z store_bytes].
          assert (
              exists v,  @load_bytes (@width BasicC64Semantics.parameters) word
                                     (@Semantics.mem BasicC64Semantics.parameters)
                                     (@bytes_per (@width BasicC64Semantics.parameters) access_size.word)
                                     mem pout
                         = Some v).
          { admit. }
          destruct H5.
          rewrite H5.
          f_equal.
        }
        {
          rewrite H2.
          clear a H3 H4.
          TODO: need to make 0s into 1s by removing +8s
          Fail.
              Search _ (_< _^_)%Z.
            Unset Printing Notations.
            simpl.
        Search _ (word.of_Z).
        Print 
        rewrite H3.
        eexists.
        rewrite H1.
        Fail.
          Search _ (_^_<>0)%Z.

      s
      simpl.
        repeat destruct H.
        repeat destruct H0.
        repeat destruct H.
        repeat destruct H2.
        repeat destruct H.
        repeat destruct H2.
        cbv[emp] in H.

  
(*
  Local Fixpoint felem_copy_loads (x out : string) (incr : Z) (loads_left : nat) : cmd :=
    match loads_left with
    | O => cmd.skip
    | S ll =>
      cmd.seq
        (cmd.store access_size.word (expr.op bopname.add out incr)
                   (expr.load access_size.word (expr.op bopname.add x incr)))
        (felem_copy_loads x out (incr + word_size_in_bytes) ll)
    end.

  Local Definition load_count : nat := Z.to_nat (felem_size_in_bytes/ word_size_in_bytes).
  Definition felem_copy_impl : func :=
    let x := "x" in
    let out := "out" in
    (felem_copy,
     ([out; x], [], felem_copy_loads x out 0 load_count)).
 *)
  
  (*Instance spec_of_felem_copy_generic : spec_of felem_copy := spec_of_felem_copy.*)

  Lemma zero_size_placeholder px : felem_size_in_bytes = 0 -> Placeholder px Interface.map.empty.
  Proof.
    intro szeq.
    unfold Placeholder.
    rewrite szeq.
    unfold anybytes.
    exists [].
    reflexivity.
  Qed.

  Lemma placeholder_empty_mem px m
    : felem_size_in_bytes = 0 ->
      Placeholder px m ->
      m = Interface.map.empty.
  Proof.
    intro szeq.
    unfold Placeholder.
    rewrite szeq.
    unfold anybytes.
    intro H; destruct H.
    cbn in *.
    destruct x.
    { inversion H; reflexivity. }
    { inversion H. }
  Qed.

  (*
  Lemma felem_function x y px m
    : FElem px x m ->
      FElem px y m ->
      x = y.
  Proof.
    intros Fx Fy.
    apply FElem_to_bytes in Fx.
    apply FElem_to_bytes in Fy.
  
  Lemma zero_size_unit (x y : felem) px py mx my
    : felem_size_in_bytes = 0 ->
      FElem px x mx ->
      FElem py y my ->
      x = y.
  Proof.
    intros szeq elx ely.
    eapply FElem_to_bytes in elx.
    eapply FElem_to_bytes in ely.
    assert (mx = Interface.map.empty); eauto using placeholder_empty_mem.
    assert (my = Interface.map.empty); eauto using placeholder_empty_mem.
    rewrite H in elx.
    rewrite H0 in ely.
    Search _ Placeholder.
    inversion elx.
    inversion ely.


 
    
    Search FElem.
    
 Fail Admitted.
   *)
  (*Duplicate px pout x = FElem px x * FElem pout (frombytes(tobytes x)).*)
  (*Axiom 
    FElem_from_bytes' :
      forall px m, exists x, (Placeholder px m) <-> (FElem px x m).*)
(*  Axiom 
    FElem_unique :
      forall px x1 x2 m, FElem px x1 m -> FElem px x2 m -> x1 = x2.*)
  Require Import Rupicola.Lib.Api.

  
  Definition Duplicate px pout x
    : list word -> Semantics.mem -> Prop :=
    fun _ => (FElem px x * FElem pout x)%sep.

  Definition copy_gallina {A} (x : A) := (x,x).

  Definition TwoElems a_ptr b_ptr ab
    : list word -> Semantics.mem -> Prop :=
    fun _ =>
      sep (FElem a_ptr (fst ab)) (FElem b_ptr (snd ab)).
  Hint Unfold TwoElems : compiler.

  Local Lemma BinIntDef_to_nat_of_nat_to_nat z
    : BinIntDef.Z.to_nat (Z.of_nat (Z.to_nat z))
      = BinIntDef.Z.to_nat z.
  Proof using .
    elim z; simpl; auto.
    intro p.
    rewrite positive_nat_Z.
    simpl.
    auto.
  Qed.

  Lemma placeholder_to_bytes :
      forall px,
        Lift1Prop.iff1 (Placeholder px) (Lift1Prop.ex1 (FElemBytes px)).
  Proof.
    intros px m; unfold Lift1Prop.ex1.
    split.
    {
      cbv [Placeholder FElemBytes].
      intro ph.
      apply anybytes_to_array_1 in ph.
      destruct ph.
      destruct H.
      exists x.
      apply sep_emp_l; auto.
    }
    {
      cbv [Placeholder FElemBytes].
      intro feb; destruct feb.
      apply sep_emp_l in H.
      destruct H.
      apply array_1_to_anybytes in H0.
      rewrite H in H0.
      Search _ (Z.of_nat (Z.to_nat _)).
      unfold anybytes.
      unfold ftprint.
      rewrite  <-BinIntDef_to_nat_of_nat_to_nat.
      exact H0.
    }
  Qed.

  Lemma felem_to_bytes :
      forall px,
        Lift1Prop.iff1 (Lift1Prop.ex1 (FElem px)) (Lift1Prop.ex1 (FElemBytes px)).
  Proof.
    intro.
    rewrite <-placeholder_to_bytes.
    symmetry.
    apply FElem_from_bytes.
  Qed.

  
  Definition TwoElemBytes a_ptr b_ptr ab
    : list word -> Semantics.mem -> Prop :=
    fun _ =>
      sep (FElemBytes a_ptr (fst ab)) (FElemBytes b_ptr (snd ab)).
  Hint Unfold TwoElemBytes : compiler.

  
  (*Require Import Rupicola.Lib.ControlFlow.DownTo.*)
  Fixpoint rep (n : nat) (cmdf : nat -> cmd) : cmd :=
    match n with
    | O => cmd.skip
    | S n' => cmd.seq (cmdf n') (rep n' cmdf)
    end.

  Local Definition felem_size :=
    Z.to_nat(felem_size_in_bytes / Memory.bytes_per_word Semantics.width).

  Local Definition incr_nat x n :=
    expr.op bopname.add x (Z.of_nat n).  

  
  Lemma rewrite_nat_in_div a b
    : Z.to_nat (a / b) = Z.to_nat (Z.of_nat (Z.to_nat a) / b).
  Proof.
    case a; case b; intros; simpl in *; auto.
    {
      generalize (Pos.to_nat p); intro n; clear p; case n; simpl; auto.
    }
    {
      cbn.
  Admitted.


  Lemma compile_copy :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr retvars R R' functions
           T (pred: T -> list word -> Semantics.mem -> Prop)
           bs bs_ptr bs_var out_ptr out_var k k_impl,
      sep (FElemBytes bs_ptr bs) R' mem ->
      map.get locals bs_var = Some bs_ptr ->
      map.get locals out_var = Some out_ptr ->
      let v := copy_gallina bs in
      (let head := v in
       find k_impl
       implementing (pred (k (fst head) (snd head)))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (rep (Z.to_nat felem_size_in_bytes)
                          (fun n =>
                             cmd.store access_size.one
                                     (incr_nat out_var ((Z.to_nat felem_size_in_bytes) - 1 - n))
                                     (expr.load access_size.one (incr_nat bs_var n))))
                     k_impl)
       implementing (pred (dlet (snd head) (dlet (fst head) k)))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    unfold FElemBytes in *.
    unfold felem_size.
    repeat straightline.
    apply sep_assoc in H.
    apply sep_emp_l in H.
    destruct H.
    rewrite <- H.
    clear H.
    revert H3 v H2.
    induction bs.
    {
      repeat straightline; auto.
    }
    {
      repeat straightline.

      eexists ?[out_var_loc].
      simpl.
      split.
      {
        replace (Datatypes.length bs - 0 - Datatypes.length bs) with 0.
        {
          cbv [incr_nat];simpl.
          unfold WeakestPrecondition.dexpr.
          unfold WeakestPrecondition.expr.
          simpl.
          cbv[WeakestPrecondition.literal dlet WeakestPrecondition.get].
          exists ?out_var_loc.
          split.
          2:{
            
           Search _ word.add.
            Search _ (word.add _ (word.of_Z 0)).
          simpl.
        simpl.
        rewrite minus_n_O.
      eexists.
      split.
      2:eexists;split.
      3:{
        repeat straightline.
    rewrite rewrite_nat_in_div.
    rewrite <- H.
    
    Search _ (Z.to_nat (_/_)).
    Lemma rewrite_nat_in_div a b c
      : c = Z.to_nat a -> Z.to_nat (a / b) = Z.to_nat (Z.from_nat c / b).
    eexists.
  
  Definition copy_bytes (bs bs': list Init.Byte.byte) :=
    let/d ret := downto (bs,bs') n
                        (fun st n => (fst st, List.listUpdate (fst st) n (nth_default Byte.xff (fst st) n))) in
    ret.


  Instance spec_of_copy_bytes : spec_of "copy_bytes" :=
    fun functions =>
      forall c_ptr c_out (c garbage : list Init.Byte.byte) tr R mem,
        (FElemBytes c_ptr c * FElemBytes c_out garbage * R)%sep mem ->
        WeakestPrecondition.call
          functions "copy_bytes" tr mem [c_out; c_ptr]
          (postcondition_func_norets
          (*(fun tr' mem' rets =>
             tr = tr' /\ rets = nil
             /\ *)
             (TwoElemBytes c_ptr c_out (copy_bytes c garbage)) R tr).
  Transparent spec_of_copy_bytes.

  Derive copy_body SuchThat
         (let args := ["c_out";"c"] in
          let rets := [] in
          let copy := ("copy_bytes", (args, rets, copy_body)) in
          program_logic_goal_for
            copy
            (ltac:(let x := program_logic_goal_for_function
                              copy (@nil string) in
                   exact x)))
         As copy_body_correct.
  Proof.
    unfold spec_of_copy_bytes.
    setup.
    simple eapply compile_downto.
    Check compile_downto.
    Print compile_custom.
    Print compile_step.
    try clear_old_seps.
    apply compile_downto.
    setup.
    Print while.
    compile.
    unfold TwoElemBytes; simpl.
  Qed.

  
   Lemma compile_copy :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr retvars R R' functions
           T (pred: T -> list word -> Semantics.mem -> Prop)
           bs bs_ptr bs_var k k_impl,
    forall var,
      sep (FElemBytes bs_ptr bs) R' mem ->
      map.get locals bs_var = Some bs_ptr ->
      let v := bs in
      (let head := copy_gallina bs in
       find k_impl
       implementing (pred (k head))
       and-returning retvars
       and-locals-post locals_ok
       with-locals (map.put locals var head)
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.load access_size.word (expr.var c_var)))
                     k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof using semantics_ok.

  Lemma felem_from_bytes_fn
  : exists f,
  forall px m,
  exists bs, (FElem px (f bs) m) <-> FElemBytes px bs m.
  Proof.
    eexists.
    intros.
    eexists.
    split.
    Search _ array.
        Lift1Prop.iff1 (Lift1Prop.ex1 (FElem px)) (Lift1Prop.ex1 (FElemBytes px)).
    
  
  Definition spec_of_felem_copy' : spec_of felem_copy :=
    fun functions =>
      forall x_ptr x x'_ptr tr R mem,
        (FElem x_ptr x * Placeholder x'_ptr * R)%sep mem ->
        WeakestPrecondition.call
          functions felem_copy tr mem [x'_ptr; x_ptr]
          (postcondition_func_norets
          (*(fun tr' mem' rets =>
             tr = tr' /\ rets = nil
             /\ *)
             (TwoElems x_ptr x'_ptr (felem_copy_gallina x)) R tr).
  Transparent spec_of_felem_copy'.

  Lemma spec_of_felem_copy_copy' fns
    : spec_of_felem_copy' fns <-> spec_of_felem_copy fns.
  Proof.
  Admitted.
    
  
  Derive copy_body SuchThat
         (let args := ["out"; "x"] in
          let rets := [] in
          let felem_copy := (felem_copy, (args, rets, copy_body)) in
          program_logic_goal_for
            felem_copy
            (forall functions : list (string * (list string * list string * cmd)),
     spec_of_felem_copy' (felem_copy :: functions)))
         As felem_copy_body_correct.
  Proof.
    unfold spec_of_felem_copy'.

    cbv[program_logic_goal_for].
    intros; WeakestPrecondition.unfold1_call_goal;
    cbv beta match delta [WeakestPrecondition.call_body].
                   rewrite String.eqb_refl.
   cbv beta match delta [WeakestPrecondition.func]. 
   repeat straightline; subst_lets_in_goal; cbn[Datatypes.length]; (first
   [ apply postcondition_func_norets_postcondition_cmd
   | apply postcondition_func_postcondition_cmd ]).

   unfold TwoElems.
   simpl.
   
   unfold Duplicate.
   cbn.


    
    setup.
    
  Hint Unfold Duplicate : compiler.
  change (fun _: list word.rep =>(FElem ?px ?x * FElem ?pout ?x)%sep)
    with (Duplicate px pout x).

  cbv[program_logic_goal_for].
  intros; WeakestPrecondition.unfold1_call_goal;
    cbv beta match delta [WeakestPrecondition.call_body].
                   rewrite String.eqb_refl.
   cbv beta match delta [WeakestPrecondition.func]. 
   repeat straightline; subst_lets_in_goal; cbn[Datatypes.length]; (first
   [ apply postcondition_func_norets_postcondition_cmd
   | apply postcondition_func_postcondition_cmd ]).
   
   unfold Duplicate.
   cbn.


   
   change (FElem pout x) with (let/d xb := from_bytes let/d x' := x in (FElem pout x')).
   Check from_bytes.
   Check to_bytes.
   autounfold with compiler in *; cbn[fst snd] in *.
   ecancel_assumption.
   Print compile_step.
   
  
  Print
    setup.
    compile.
  
  Lemma felem_copy_correct :
  (*program_logic_goal_for_function! felem_copy_impl*)
  program_logic_goal_for felem_copy_impl
    (forall functions : list (string * (list string * list string * cmd)),
     spec_of_felem_copy_generic (felem_copy_impl :: functions)).
  Proof.
    unfold spec_of_felem_copy_generic.
    unfold spec_of_felem_copy.
    unfold felem_copy_impl.
    remember load_count as lc.
    induction lc.

    {
      intros functions.
      intros.
      WeakestPrecondition.unfold1_call_goal.
      cbv beta match delta [WeakestPrecondition.call_body].
      unfold felem_copy_impl.
      lazymatch goal with
      | |- if ?test then ?T else _ => change_no_check test with true; change T
      end.
      unfold load_count.
      cbv beta match delta [WeakestPrecondition.func].
      repeat straightline.
      split; auto.
      revert H.
      generalize mem; clear mem.
      apply Util.iff1_sep_cancel_both.
      {
        intro.
        rewrite sep_emp_l.
        assert (forall {A B : Prop}, A -> (A/\B <-> B)).
        { tauto. }
        rewrite H; auto.
        generalize x0; clear x0.
        apply Util.iff1_sep_cancel_both.
        { intro; reflexivity. }
        {
          intro.
          split.
          {
            eapply FElem_to_bytes.
          }
          {
            unfold Placeholder.
            unfold anybytes.
            assert (felem_size_in_bytes = 0).
            1:give_up.
            rewrite H0.
            
            intro H1; destruct H1.
            cbn in H1.
            destruct x1.
            {
              inversion H1.
              admit.
            }
            {
              inversion H1.
            }
          }
        }
      }
      {
        reflexivity.
      }
    }
    {
      intros functions.
      intros.
      WeakestPrecondition.unfold1_call_goal.
      cbv beta match delta [WeakestPrecondition.call_body].
      lazymatch goal with
      | |- if ?test then ?T else _ => change_no_check test with true; change T
      end.
      cbv beta match delta [WeakestPrecondition.func].
      repeat straightline.
      
      repeat esplit.
      {
        unfold l.
        rewrite Interface.map.get_put_diff.
        { rewrite Interface.map.get_put_same.
          reflexivity.
        }
        
        intro.
        inversion H0.
      }
      {
        unfold l.
        rewrite Interface.map.get_put_same.
        reflexivity.
      }
      {
        cbn.
        
        Search _ load.

      {tauto.
        absurd.
              Search _ Interface.map.get.


      try ecancel_assumption.
      






      Search _ FElem.
              pose (p :=FElem_from_bytes
            
            inversion x1.
            unfold ftprint in *.
            simpl in *.
            unfold Interface.map.of_disjoint_list_zip in *.
            unfold             
            intro
            unfold load_count in *
        
      gener
      rewrite sep_emp_l.
      
      esplit.
      eexists.
      split.
      2:{
        split.
        Search _ (_*_)%sep.
      unfold Notations.postcondition_func_norets.
      unfold Notations.postcondition_func.
      
                     
    intros functions.
    intros.
    WeakestPrecondition.unfold1_call_goal.
    cbv beta match delta [WeakestPrecondition.call_body].
    unfold felem_copy_impl.
    lazymatch goal with
         | |- if ?test then ?T else _ => change_no_check test with true; change T
    end.
    unfold load_count.
    cbv beta match delta [WeakestPrecondition.func].
    repeat straightline.


    remember 
    
    
    Print FElem.
    
    eexists; split.
    {
      repeat straightline.
      eexists;split; repeat straightline.
      {
        cbv delta [l].
        rewrite Interface.map.get_put_same.
        reflexivity.
      }
      {
        eexists; split; eauto.
        Search load.
        Print width.
        Locate width.
        Check word.
        Check felem_size_in_bytes.
        Scalars.load_one_of_sep.
        destruct H.
        


        
      Print spec_of_felem_copy.
    
    Search _ (?a =? ?a).
                   
    ; cbv zeta; intros; WeakestPrecondition.unfold1_call_goal;
         cbv beta match delta [WeakestPrecondition.call_body];
         lazymatch goal with
         | |- if ?test then ?T else _ => change_no_check test with true; change T
         end; cbv beta match delta [WeakestPrecondition.func]
    Print straightline_init_with_change.
  intro.
    unfold spec_of_felem_copy.
    intros.
    
    
    cbn [seps] in *.
    eexists; split; [ solve [repeat straightline] | ].
    repeat straightline.
    repeat split; ecancel_assumption.

    
    _compile.

Lemma mul_twice_correct :
  program_logic_goal_for_function! mul_twice.
Proof.
  straightline_init_with_change.

  repeat straightline.
  handle_call; [ prove_preconditions .. | ].
  repeat straightline.
  handle_call; [ prove_preconditions .. | ].

  repeat split; try reflexivity.
  sepsimpl_hyps.
  eexists; sepsimpl;
    lazymatch goal with
    | |- sep _ _ _ => ecancel_assumption
    | _ => idtac
    end.
  all: try prove_bounds.
  repeat match goal with
         | H : eval _ mod _ = (eval _ * eval _) mod _ |- _ =>
           rewrite H
         | _ => progress Modulo.push_Zmod
         end.
  reflexivity.
Qed.
