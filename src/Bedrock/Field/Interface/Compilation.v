Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Local Open Scope Z_scope.

Section Compile.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}
          {field_representaton : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.
  Existing Instances spec_of_mul spec_of_add spec_of_sub spec_of_square
           spec_of_scmula24 spec_of_inv spec_of_felem_copy
           spec_of_felem_small_literal.

  (* "Hidden" alias protects a Placeholder (e.g. the pointer reserved for the
     final output value) from having intermediate values stored in it *)
  Definition Hidden := Placeholder.

  Local Ltac prove_field_compilation :=
    repeat straightline';
    handle_call;
    lazymatch goal with
    | |- sep _ _ _ => ecancel_assumption
    | _ => idtac
    end; eauto;
    sepsimpl; repeat straightline'; subst; eauto.

  Lemma compile_mul :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr retvars R Rin Rout functions T (pred: T -> list word -> Semantics.mem -> Prop)
      (x y : felem) x_ptr x_var y_ptr y_var out_ptr out_var
      (X Y : F M_pos) k k_impl,
      spec_of_mul functions ->
      bounded_by loose_bounds x ->
      bounded_by loose_bounds y ->
      feval x = X ->
      feval y = Y ->
      (FElem x_ptr x * FElem y_ptr y * Rin)%sep mem ->
      (Placeholder out_ptr * Rout)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals y_var = Some y_ptr ->
      map.get locals out_var = Some out_ptr ->
      let v := (X * Y)%F in
      (let head := v in
       forall out m,
         feval out = head ->
         bounded_by tight_bounds out ->
         sep (FElem out_ptr out) Rout m ->
         (find k_impl
          implementing (pred (k head))
          and-returning retvars
          and-locals-post locals_ok
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [] mul [expr.var out_var; expr.var x_var;
                                   expr.var y_var])
               k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof. prove_field_compilation. Qed.

  Lemma compile_add :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr retvars R Rin Rout functions T (pred: T -> list word -> Semantics.mem -> Prop)
      (x y : felem) x_ptr x_var y_ptr y_var out_ptr out_var
      (X Y : F M_pos) k k_impl,
      spec_of_add functions ->
      bounded_by tight_bounds x ->
      bounded_by tight_bounds y ->
      feval x = X ->
      feval y = Y ->
      (FElem x_ptr x * FElem y_ptr y * Rin)%sep mem ->
      (Placeholder out_ptr * Rout)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals y_var = Some y_ptr ->
      map.get locals out_var = Some out_ptr ->
      let v := (X + Y)%F in
      (let head := v in
       forall out m,
         feval out = head ->
         bounded_by loose_bounds out ->
         sep (FElem out_ptr out) Rout m ->
         (find k_impl
          implementing (pred (k head))
          and-returning retvars
          and-locals-post locals_ok
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [] add [expr.var out_var; expr.var x_var;
                                   expr.var y_var])
               k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof. prove_field_compilation. Qed.

  Lemma compile_sub :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr retvars R Rin Rout functions T (pred: T -> list word -> Semantics.mem -> Prop)
      (x y : felem) x_ptr x_var y_ptr y_var out_ptr out_var
      (X Y : F M_pos) k k_impl,
      spec_of_sub functions ->
      bounded_by tight_bounds x ->
      bounded_by tight_bounds y ->
      feval x = X ->
      feval y = Y ->
      (FElem x_ptr x * FElem y_ptr y * Rin)%sep mem ->
      (Placeholder out_ptr * Rout)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals y_var = Some y_ptr ->
      map.get locals out_var = Some out_ptr ->
      let v := (X - Y)%F in
      (let head := v in
       forall out m,
         feval out = head ->
         bounded_by loose_bounds out ->
         sep (FElem out_ptr out) Rout m ->
         (find k_impl
          implementing (pred (k head))
          and-returning retvars
          and-locals-post locals_ok
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [] sub [expr.var out_var; expr.var x_var;
                                   expr.var y_var])
               k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof. prove_field_compilation. Qed.

  Lemma compile_square :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr retvars R Rin Rout functions T (pred: T -> list word -> Semantics.mem -> Prop)
      (x : felem) x_ptr x_var out_ptr out_var (X : F M_pos) k k_impl,
      spec_of_square functions ->
      bounded_by loose_bounds x ->
      feval x = X ->
      (FElem x_ptr x * Rin)%sep mem ->
      (Placeholder out_ptr * Rout)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals out_var = Some out_ptr ->
      let v := (X ^ 2)%F in
      (let head := v in
       forall out m,
         feval out = head ->
         bounded_by tight_bounds out ->
         sep (FElem out_ptr out) Rout m ->
         (find k_impl
          implementing (pred (k head))
          and-returning retvars
          and-locals-post locals_ok
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [] square [expr.var out_var; expr.var x_var])
               k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros. subst_lets_in_goal.
    rewrite F.pow_2_r in *.
    prove_field_compilation.
  Qed.

  Lemma compile_scmula24 :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr retvars R Rin Rout functions T (pred: T -> list word -> Semantics.mem -> Prop)
      (x : felem) x_ptr x_var out_ptr out_var (X : F M_pos) k k_impl,
      spec_of_scmula24 functions ->
      bounded_by loose_bounds x ->
      feval x = X ->
      (FElem x_ptr x * Rin)%sep mem ->
      (Placeholder out_ptr * Rout)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals out_var = Some out_ptr ->
      let v := (a24 * X)%F in
      (let head := v in
       forall out m,
         feval out = head ->
         bounded_by tight_bounds out ->
         sep (FElem out_ptr out) Rout m ->
         (find k_impl
          implementing (pred (k head))
          and-returning retvars
          and-locals-post locals_ok
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [] scmula24 [expr.var out_var; expr.var x_var])
               k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof. prove_field_compilation. Qed.

  Lemma compile_inv :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr retvars R Rin Rout functions T (pred: T -> list word -> Semantics.mem -> Prop)
      (x : felem) x_ptr x_var out_ptr out_var (X : F M_pos) k k_impl,
      spec_of_inv functions ->
      bounded_by tight_bounds x ->
      feval x = X ->
      (FElem x_ptr x * Rin)%sep mem ->
      (Placeholder out_ptr * Rout)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals out_var = Some out_ptr ->
      let v := F.inv X in
      (let head := v in
       forall out m,
         feval out = head ->
         bounded_by loose_bounds out ->
         sep (FElem out_ptr out) Rout m ->
         (find k_impl
          implementing (pred (k head))
          and-returning retvars
          and-locals-post locals_ok
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [] inv [expr.var out_var; expr.var x_var])
               k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof. prove_field_compilation. Qed.

  Lemma compile_felem_copy :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr retvars R R' functions T (pred: T -> list word -> Semantics.mem -> Prop)
      (x : felem) x_ptr x_var out_ptr out_var
      (X : F M_pos) k k_impl,
      spec_of_felem_copy functions ->
      feval x = X ->
      (FElem x_ptr x * Placeholder out_ptr * R')%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals out_var = Some out_ptr ->
      let v := X in
      (let head := v in
       forall m,
         (FElem x_ptr x * FElem out_ptr x * R')%sep m ->
         (find k_impl
          implementing (pred (k head))
          and-returning retvars
          and-locals-post locals_ok
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [] felem_copy [expr.var out_var; expr.var x_var])
               k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof. prove_field_compilation. Qed.

  Lemma compile_felem_small_literal :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr retvars R R' functions T (pred: T -> list word -> Semantics.mem -> Prop)
      (wx : word) (x : Z) out_ptr out_var k k_impl,
      spec_of_felem_small_literal functions ->
      (Placeholder out_ptr * R')%sep mem ->
      map.get locals out_var = Some out_ptr ->
      word.unsigned wx = x ->
      let v := F.of_Z M_pos x in
      (let head := v in
       forall X m,
         (FElem out_ptr X * R')%sep m ->
         feval X = head ->
         bounded_by tight_bounds X ->
         (find k_impl
          implementing (pred (k head))
          and-returning retvars
          and-locals-post locals_ok
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [] felem_small_literal
                         [expr.var out_var; expr.literal x])
               k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    prove_field_compilation.
    match goal with H : _ |- _ =>
                    rewrite word.of_Z_unsigned in H end.
    use_hyp_with_matching_cmd; eauto; [ ].
    subst_lets_in_goal.
    match goal with H : F.to_Z _ = _ |- _ => rewrite <-H end.
    rewrite F.of_Z_to_Z. eauto.
  Qed.

  (* noop indicating that the last argument should store output *)
  Definition overwrite1 {A B} := @id (A -> B).
  (* noop indicating that the 2nd-to-last argument should store output *)
  Definition overwrite2 {A B C} := @id (A -> B -> C).

  Lemma compile_compose_l :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr retvars R Rout functions T (pred: T -> list word -> Semantics.mem -> Prop)
           {A1 A2 : Type} (* second arg is N for F.pow, so allow that *)
           (op1 : F M_pos -> A1 -> F M_pos)
           (op2 : F M_pos -> A2 -> F M_pos)
           x y z out_ptr out_var k k_impl,
      (Placeholder out_ptr * Rout)%sep mem ->
      map.get locals out_var = Some out_ptr ->
      let v := ((op2 (op1 x y) z)) in
      (let head := v in
       (find k_impl
        implementing
             (pred (dlet (op1 x y)
                         (fun xy => dlet ((overwrite2 op2) xy z) k)))
        and-returning retvars
        and-locals-post locals_ok
        with-locals locals and-memory mem and-trace tr and-rest R
        and-functions functions)) ->
      (let head := v in
       find k_impl
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    cbv [Placeholder overwrite1 overwrite2] in *.
    repeat straightline'. auto.
  Qed.

  Lemma compile_compose_r :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr retvars R Rout functions T (pred: T -> list word -> Semantics.mem -> Prop)
           {A1 : Type} (* second arg is N for F.pow, so allow that *)
           (op1 : F M_pos -> A1 -> F M_pos)
           (op2 : F M_pos -> F M_pos -> F M_pos)
           x y z out_ptr out_var k k_impl,
      (Placeholder out_ptr * Rout)%sep mem ->
      map.get locals out_var = Some out_ptr ->
      let v := (op2 z (op1 x y)) in
      (let head := v in
       (find k_impl
        implementing
             (pred (dlet (op1 x y)
                         (fun xy => dlet ((overwrite1 op2) z xy) k)))
        and-returning retvars
        and-locals-post locals_ok
        with-locals locals and-memory mem and-trace tr and-rest R
        and-functions functions)) ->
      (let head := v in
       find k_impl
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    cbv [Placeholder overwrite1 overwrite2] in *.
    repeat straightline'. auto.
  Qed.

  Lemma compile_overwrite1 :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr retvars R Rin functions T (pred: T -> list word -> Semantics.mem -> Prop)
      (x : F M_pos) (op : F M_pos -> F M_pos -> F M_pos)
      (y : felem) y_ptr y_var (Y : F M_pos) k k_impl,
      (FElem y_ptr y * Rin)%sep mem ->
      feval y = Y ->
      map.get locals y_var = Some y_ptr ->
      let v := (overwrite1 op) x Y in
      let v' := op x Y in
      (let __ := 0 in (* placeholder *)
       forall m,
         sep (FElem y_ptr y) Rin m ->
         sep (Placeholder y_ptr) Rin m ->
         (find k_impl
          implementing (pred (dlet v' k))
          and-returning retvars
          and-locals-post locals_ok
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find k_impl
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'. auto.
    match goal with H : _ |- _ => apply H end.
    { ecancel_assumption. }
    { seprewrite FElem_from_bytes.
      sepsimpl; eexists; ecancel_assumption. }
  Qed.

  Lemma compile_overwrite2 :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr retvars R Rin functions T (pred: T -> list word -> Semantics.mem -> Prop)
      {A} (y : A)
      (op : F M_pos -> A -> F M_pos)
      (x : felem) x_ptr x_var (X : F M_pos) k k_impl,
      feval x = X ->
      (FElem x_ptr x * Rin)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      let v := (overwrite2 op) X y in
      let v' := op X y in
      (let __ := 0 in (* placeholder *)
       forall m,
         sep (FElem x_ptr x) Rin m ->
         sep (Placeholder x_ptr) Rin m ->
         (find k_impl
          implementing (pred (dlet v' k))
          and-returning retvars
          and-locals-post locals_ok
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find k_impl
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'. auto.
    match goal with H : _ |- _ => apply H end.
    { ecancel_assumption. }
    { seprewrite FElem_from_bytes.
      sepsimpl; eexists; ecancel_assumption. }
  Qed.
End Compile.

Ltac field_compile_step :=
  first [ simple eapply compile_scmula24 (* must precede compile_mul *)
        | simple eapply compile_mul
        | simple eapply compile_add
        | simple eapply compile_sub
        | simple eapply compile_square
        | simple eapply compile_inv ];
  lazymatch goal with
  | |- feval _ = _ => try eassumption; try reflexivity
  | |- _ => idtac
  end.

Ltac compile_compose_step :=
  first [ simple eapply compile_compose_l
        | simple eapply compile_compose_r
        | simple eapply compile_overwrite1
        | simple eapply compile_overwrite2 ];
  [ solve [repeat compile_step] .. | intros ].

(* Change an FElem into a Placeholder to indicate that it is overwritable *)
Ltac free p :=
  match goal with
  | H : sep ?P ?Q ?m |- context [?m] =>
    let x :=
        match type of H with
        | context [FElem p ?x] => x
        end in
    let F :=
        match (eval pattern (FElem p x) in (sep P Q m)) with
        | ?F _ => F end in
    let H' := fresh in
    assert (F (Placeholder p)) as H'
        by (seprewrite FElem_from_bytes; sepsimpl; eexists;
            ecancel_assumption);
    cbv beta in H'; clear H
  end.

(* Protect a pointer (e.g. the pointer reserved for final output) by "hiding"
   the fact that it is available under the "Hidden" alias *)
Ltac hide p :=
  change (Placeholder p) with (Hidden p) in *.
Ltac unhide p :=
  change (Hidden p) with (Placeholder p) in *.
