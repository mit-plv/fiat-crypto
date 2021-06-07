Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Compilation.
Require Import Crypto.Bedrock.Group.Point.
Require Import Crypto.Bedrock.Specs.Field.
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

  (*
  (*Modified from stack_alloc*)
  Definition felem_alloc : Comp (felem) := fun _ => True.
   *)

  Definition felem_alloc (v : F M_pos) := v.
  Arguments felem_alloc : simpl never.
  
  Lemma compile_felem_alloc
        (tr : Semantics.trace)
        (mem locals : map.rep)
        (functions : list (string * (list string * list string * cmd)))
        (e : felem) :
    let v := (feval e)%F in
    forall (P : F M_pos -> Type)
           (pred : P v -> predicate)
           (k : nlet_eq_k P v) (v_impl k_impl : cmd)
           (Rin Rout : map.rep -> Prop)
           (out : felem)
           (out_var : string),
      (*
      (FElem out_ptr out ⋆ Rout) mem ->
      (FElem e_ptr e ⋆ Rin) mem ->
       *)
      Rout mem ->
      Rin mem ->
      bounded_by loose_bounds e ->
      (let v0 := v in
       forall (out0 : felem) (out_ptr : word.rep) (m : map.rep),
         feval out0 = v0 ->
         bounded_by loose_bounds out0 ->
         (Placeholder out_ptr ⋆ Rout) m ->
         <{ Trace := tr;
            Memory := m;
            Locals := map.put locals out_var out_ptr;
            Functions := functions }>
         v_impl
         <{ fun tr' mem l => tr' = tr /\ (FElem out_ptr out0 ⋆ Rout) mem /\ l = map.put locals out_var out_ptr }>) ->
      (let v0 := v in
       forall (out0 : felem) (out_ptr : word.rep) (m : map.rep),
         feval out0 = v0 ->
         bounded_by loose_bounds out0 ->
         (FElem out_ptr out0 ⋆ Rout) m ->
         <{ Trace := tr;
            Memory := m;
            Locals := map.put locals out_var out_ptr;
            Functions := functions }>
         k_impl
         <{fun tr' mem' locals' =>
             exists m' mStack' : map.rep, Placeholder out_ptr mStack' /\
                                          map.split mem' m' mStack' /\
                                          pred (k v0 eq_refl) tr' m' locals' }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.stackalloc out_var (@felem_size_in_bytes field_parameters _ field_representaton)
                     (cmd.seq v_impl k_impl)
      <{ pred (let/n x as out_var eq:Heq := felem_alloc v in
               k x Heq) }>.
  Proof.
    red.
    red.
    cbn.
    intros.
    split; eauto using felem_size_in_bytes_mod.
    change (Memory.anybytes ?p felem_size_in_bytes ?m) with (Placeholder p m).
    intros ptr mStack mCombined Hany Hsplit.
    eapply WeakestPrecondition_weaken; cycle 1.
    - eapply H2; eauto.
      exists mStack.
      exists mem.
      intuition.
      apply map.split_comm; eauto.
    - intros tr' mem' locals' [Htr [Hmem Hloc]]; subst.
      unfold felem_alloc.
      unfold nlet_eq.
      eapply H3; eauto.
  Qed.

  (*
   Local Ltac prove_field_compilation :=
    repeat straightline';
    handle_call;
    lazymatch goal with
    | |- sep _ _ _ => ecancel_assumption
    | _ => idtac
    end; eauto;
    sepsimpl; repeat straightline'; subst; eauto.
*)

  Lemma compile_binop_alloc {name} {op: BinOp name}
        {tr mem locals functions} x y:
    let v := felem_alloc (bin_model (feval x) (feval y)) in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      Rin x_ptr x_var y_ptr y_var out_var,

      (_: spec_of name) functions ->
      bounded_by bin_xbounds x ->
      bounded_by bin_ybounds y ->

      (*
      map.get locals out_var = Some out_ptr ->
       
      (FElem out_ptr out * Rout)%sep mem ->
       *)
      (*Rout mem -> TODO: is this okay?*)
      let Rout := (FElem x_ptr x * FElem y_ptr y * Rin)%sep in
      (FElem x_ptr x * FElem y_ptr y * Rin)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals y_var = Some y_ptr ->

      out_var <> x_var ->
      out_var <> y_var ->

      (let v := v in
       forall out out_ptr m (Heq: feval out = v),
         bounded_by bin_outbounds out ->
         sep (FElem out_ptr out) Rout m ->
         (<{ Trace := tr;
             Memory := m;
             Locals := map.put locals out_var out_ptr;
             Functions := functions }>
          k_impl
          <{ fun tr' mem' locals' =>
             exists m' mStack' : map.rep, Placeholder out_ptr mStack' /\
                                          map.split mem' m' mStack' /\
                                          pred (k v eq_refl) tr' m' locals' }>)) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      
      cmd.stackalloc out_var (@felem_size_in_bytes field_parameters _ field_representaton)
                     (cmd.seq
                        (cmd.call [] name [expr.var out_var; expr.var x_var; expr.var y_var ])
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
      exists (FElem out_ptr out * Rin)%sep.
      assert (((FElem x_ptr x ⋆ FElem y_ptr y ⋆ Rin) * FElem out_ptr out)%sep mCombined).
      exists mem.
      exists mStack.
      intuition.
      ecancel_assumption.
    }
    {
      exists mStack.
      exists mem.
      intuition eauto.
      apply map.split_comm; eauto.
    }
    repeat straightline'.
    eapply H7; repeat straightline'.
    {
      unfold v.
      unfold felem_alloc.
      eauto.
    }
    eauto.
    {
      unfold Rout.
      ecancel_assumption.
    }
  Qed.

   Ltac cleanup_op_lemma lem := (* This makes [simple apply] work *)
    let lm := fresh in
    let op := match lem with _ _ ?op => op end in
    let op_hd := term_head op in
    let simp proj :=
        (let hd := term_head proj in
         let reduced := (eval cbv [op_hd hd] in proj) in
         change proj with reduced in (type of lm)) in
    pose lem as lm;
    first [ simp (bin_model (BinOp := op));
            simp (bin_xbounds (BinOp := op));
            simp (bin_ybounds (BinOp := op));
            simp (bin_outbounds (BinOp := op))
          | simp (un_model (UnOp := op));
            simp (un_xbounds (UnOp := op));
            simp (un_outbounds (UnOp := op)) ];
    let t := type of lm in
    let t := (eval cbv beta in t) in
    exact (lm: t).
  
  Notation make_bin_alloc_lemma op :=
    ltac:(cleanup_op_lemma (@compile_binop_alloc _ op)) (only parsing).

  Definition compile_mul := make_bin_alloc_lemma bin_mul.
  Definition compile_add := make_bin_alloc_lemma bin_add.
  Definition compile_sub := make_bin_alloc_lemma bin_sub.

   Lemma compile_unop_alloc {name} (op: UnOp name) {tr mem locals functions} x:
    let v := felem_alloc (un_model (feval x)) in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      Rin x_ptr x_var out_var,

      (_: spec_of name) functions ->
      bounded_by un_xbounds x ->

      
      let Rout := (FElem x_ptr x * Rin)%sep in
      (*
        map.get locals out_var = Some out_ptr ->
        (FElem out_ptr out * Rout)%sep mem ->
       *)

      (FElem x_ptr x * Rin)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      out_var <> x_var ->

      (let v := v in
       forall out out_ptr m (Heq : feval out = v),
         bounded_by un_outbounds out ->
         sep (FElem out_ptr out) Rout m ->
         (<{ Trace := tr;
             Memory := m;
             Locals := map.put locals out_var out_ptr;
             Functions := functions }>
          k_impl
          <{ fun tr' mem' locals' =>
             exists m' mStack' : map.rep, Placeholder out_ptr mStack' /\
                                          map.split mem' m' mStack' /\
                                          pred (k v eq_refl) tr' m' locals' }>)) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.stackalloc out_var (@felem_size_in_bytes field_parameters _ field_representaton)
                     (cmd.seq
                        (cmd.call [] name [expr.var out_var; expr.var x_var])
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
      exists (FElem out_ptr out * Rin)%sep.
      assert (((FElem x_ptr x ⋆ Rin) * FElem out_ptr out)%sep mCombined).
      exists mem.
      exists mStack.
      intuition.
      ecancel_assumption.
    }
    {
      exists mStack.
      exists mem.
      intuition eauto.
      apply map.split_comm; eauto.
    }
    repeat straightline'.
    eapply H4; repeat straightline'.
    {
      unfold v.
      unfold felem_alloc.
      eauto.
    }
    eauto.
    {
      unfold Rout.
      ecancel_assumption.
    }
  Qed.

   Notation make_un_lemma op :=
     ltac:(cleanup_op_lemma (@compile_unop _ _ _ _ _ op)) (only parsing).

   Definition compile_square := make_un_lemma un_square.
   Definition compile_scmula24 := make_un_lemma un_scmula24.
   Definition compile_inv := make_un_lemma un_inv.

  Section Gallina.
    Local Open Scope F_scope.

    Definition ladderstep_gallina
               (X1: F M_pos) (P1 P2: point) : (point * point) :=
      let '(X2, Z2) := P1 in
      let '(X3, Z3) := P2 in
      (*TODO: set things up so eq isn't needed *)
      let/n A := felem_alloc (X2+Z2) in
      let/n AA := felem_alloc (A^2) in
      let/n B := felem_alloc (X2-Z2) in
      let/n BB := felem_alloc (B^2) in
      let/n E := felem_alloc (AA-BB) in
      let/n C := felem_alloc (X3+Z3) in
      let/n D := felem_alloc (X3-Z3) in
      let/n DA := felem_alloc (D*A) in
      let/n CB := felem_alloc (C*B) in
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
      (* ((X4, Z4), (X5, Z5)) *)
      ((X2, Z2), (X3, Z3)).
  End Gallina.

  Instance spec_of_ladderstep : spec_of "ladderstep" :=
    fnspec! "ladderstep"
          (pX1 pX2 pZ2 pX3 pZ3
               (*pA pAA pB pBB pE pC pD pDA pCB*) : Semantics.word)
          / (X1 X2 Z2 X3 Z3 (*A AA B BB E C D DA CB*) : felem) R,
    { requires tr mem :=
        bounded_by tight_bounds X1
        /\ bounded_by tight_bounds X2
        /\ bounded_by tight_bounds Z2
        /\ bounded_by tight_bounds X3
        /\ bounded_by tight_bounds Z3
        /\ (FElem pX1 X1
            * FElem pX2 X2 * FElem pZ2 Z2
            * FElem pX3 X3 * FElem pZ3 Z3
            (** FElem pA A * FElem pAA AA
             * FElem pB B * FElem pBB BB
             * FElem pE E * FElem pC C
             * FElem pD D * FElem pDA DA
             * FElem pCB CB*) * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists X4 Z4 X5 Z5 (* output values *)
                  (*A' AA' B' BB' E' C' D' DA' CB' (* new intermediates *)*)
                  : felem,
          (ladderstep_gallina
             (feval X1) (feval X2, feval Z2)
             (feval X3, feval Z3)
           = ((feval X4, feval Z4), (feval X5, feval Z5)))
          /\ bounded_by tight_bounds X4
          /\ bounded_by tight_bounds Z4
          /\ bounded_by tight_bounds X5
          /\ bounded_by tight_bounds Z5
          /\ (FElem pX1 X1 * FElem pX2 X4 * FElem pZ2 Z4
              * FElem pX3 X5 * FElem pZ3 Z5
              (** FElem pA A' * FElem pAA AA'
               * FElem pB B' * FElem pBB BB'
               * FElem pE E' * FElem pC C' * FElem pD D'
               * FElem pDA DA' * FElem pCB CB'*) * R)%sep mem'}.

  Lemma compile_ladderstep : forall {tr mem locals functions}
        (x1 x2 z2 x3 z3 : F M_pos),
    let v := ladderstep_gallina x1 (x2, z2) (x3, z3) in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
           Rout
           X1 X1_ptr X1_var X2 X2_ptr X2_var Z2 Z2_ptr Z2_var
           X3 X3_ptr X3_var Z3 Z3_ptr Z3_var
    (* A A_ptr A_var AA AA_ptr AA_var
           B B_ptr B_var BB BB_ptr BB_var
           E E_ptr E_var C C_ptr C_var
           D D_ptr D_var DA DA_ptr DA_var
           CB CB_ptr CB_var*),

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
       * FElem X3_ptr X3 * FElem Z3_ptr Z3
      (* * FElem A_ptr A * FElem AA_ptr AA
       * FElem B_ptr B * FElem BB_ptr BB
       * FElem E_ptr E * FElem C_ptr C
       * FElem D_ptr D * FElem DA_ptr DA
       * FElem CB_ptr CB *) * Rout)%sep mem ->

        map.get locals X1_var = Some X1_ptr ->
        map.get locals X2_var = Some X2_ptr ->
        map.get locals Z2_var = Some Z2_ptr ->
        map.get locals X3_var = Some X3_ptr ->
        map.get locals Z3_var = Some Z3_ptr ->
        (*map.get locals A_var = Some A_ptr ->
        map.get locals AA_var = Some AA_ptr ->
        map.get locals B_var = Some B_ptr ->
        map.get locals BB_var = Some BB_ptr ->
        map.get locals E_var = Some E_ptr ->
        map.get locals C_var = Some C_ptr ->
        map.get locals D_var = Some D_ptr ->
        map.get locals DA_var = Some DA_ptr ->
        map.get locals CB_var = Some CB_ptr ->*)

        (let v := v in
         forall (X4 Z4 X5 Z5 (* output values *)
                    (*A' AA' B' BB' E' C' D' DA' CB' (* new intermediates *)*)
                 : felem) m
                (Heq : ladderstep_gallina
                         (feval X1) (feval X2, feval Z2)
                         (feval X3, feval Z3)
                       = ((feval X4, feval Z4), (feval X5, feval Z5))),
          bounded_by tight_bounds X4 ->
          bounded_by tight_bounds Z4 ->
          bounded_by tight_bounds X5 ->
          bounded_by tight_bounds Z5 ->
          (FElem X1_ptr X1 * FElem X2_ptr X4 * FElem Z2_ptr Z4
           * FElem X3_ptr X5 * FElem Z3_ptr Z5
           (* * FElem A_ptr A' * FElem AA_ptr AA'
           * FElem B_ptr B' * FElem BB_ptr BB'
           * FElem E_ptr E' * FElem C_ptr C' * FElem D_ptr D'
           * FElem DA_ptr DA' * FElem CB_ptr CB' *) * Rout)%sep m ->
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
                          expr.var Z3_var (*; expr.var A_var;
                            expr.var AA_var; expr.var B_var;
                              expr.var BB_var; expr.var E_var;
                                expr.var C_var; expr.var D_var;
                                  expr.var DA_var; expr.var CB_var *)])
          k_impl
        <{ pred (nlet_eq
                   [X1_var; X2_var; Z2_var; X3_var; Z3_var]
                   v k) }>.
  Proof.
      repeat straightline'.
      handle_call;
        lazymatch goal with
        | |- sep _ _ _ => ecancel_assumption
        | _ => solve [eauto]
        end.
    Qed.

  (*TODO: move, along with allocating lemma *)
  Ltac field_compile_step :=
  (first
   [ simple eapply compile_scmula24
   | simple eapply compile_mul
   | simple eapply compile_add
   | simple eapply compile_sub
   | simple eapply compile_square
   | simple eapply compile_inv
   | simple eapply Compilation.compile_scmula24
   | simple eapply Compilation.compile_mul
   | simple eapply Compilation.compile_add
   | simple eapply Compilation.compile_sub
   | simple eapply Compilation.compile_square
   | simple eapply Compilation.compile_inv ]); lazymatch goal with
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
  
Definition
  ladderstep_body' :=
  noskips
  (cmd.seq (cmd.call [] add [expr.var "X2"; expr.var "Z2"; expr.var "A"])
     (cmd.seq (cmd.call [] square [expr.var "A"; expr.var "AA"])
        (cmd.seq (cmd.call [] sub [expr.var "X2"; expr.var "Z2"; expr.var "B"])
           (cmd.seq (cmd.call [] square [expr.var "B"; expr.var "BB"])
              (cmd.seq (cmd.call [] sub [expr.var "AA"; expr.var "BB"; expr.var "E"])
                 (cmd.seq (cmd.call [] add [expr.var "X3"; expr.var "Z3"; expr.var "C"])
                    (cmd.seq (cmd.call [] sub [expr.var "X3"; expr.var "Z3"; expr.var "D"])
                       (cmd.seq (cmd.call [] mul [expr.var "D"; expr.var "A"; expr.var "DA"])
                          (cmd.seq (cmd.call [] mul [expr.var "C"; expr.var "B"; expr.var "CB"])
                             (cmd.seq (cmd.call [] add [expr.var "DA"; expr.var "CB"; expr.var "X3"])
                                (cmd.seq (cmd.call [] square [expr.var "X3"; expr.var "X3"])
                                   (cmd.seq (cmd.call [] sub [expr.var "DA"; expr.var "CB"; expr.var "Z3"])
                                      (cmd.seq (cmd.call [] square [expr.var "Z3"; expr.var "Z3"])
                                         (cmd.seq (cmd.call [] mul [expr.var "X1"; expr.var "Z3"; expr.var "Z3"])
                                            (cmd.seq
                                               (cmd.call [] mul [expr.var "AA"; expr.var "BB"; expr.var "X2"])
                                               (cmd.seq (cmd.call [] scmula24 [expr.var "E"; expr.var "Z2"])
                                                  (cmd.seq
                                                     (cmd.call [] add
                                                        [expr.var "AA"; expr.var "Z2"; expr.var "Z2"])
                                                     (cmd.seq
                                                        (cmd.call [] mul
                                                           [expr.var "E"; expr.var "Z2"; expr.var "Z2"])
                                                        (fold_right
                                                           (fun (v : string) (c : cmd) => cmd.seq (cmd.unset v) c)
                                                           cmd.skip []))))))))))))))))))).

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
Proof.
  compile_setup.
  repeat compile_step.
  simpl.
  simple eapply compile_nlet_as_nlet_eq.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  simple eapply compile_add.
  compile_step.
    compile.
  Qed.

  
End __.

Existing Instance spec_of_ladderstep.

Import Syntax.
Local Unset Printing Coercions.
Redirect "Crypto.Bedrock.Group.ScalarMult.LadderStep.ladderstep_body" Print ladderstep_body.
