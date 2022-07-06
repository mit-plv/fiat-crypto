Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Alloc.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Local Open Scope Z_scope.

Section Compile.
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

  Definition maybe_bounded mbounds v :=
    match mbounds with
    | Some bounds => bounded_by bounds v
    | None => True
    end.

  (* TODO: Replace uses of the old FElem with this? *)
  Definition FElem mbounds ptr v :=
    (Lift1Prop.ex1 (fun v' => (emp (feval v' = v /\ maybe_bounded mbounds v') * FElem ptr v')%sep)).

  Lemma drop_bounds_FElem x_ptr x bounds
    : Lift1Prop.impl1 (FElem bounds x_ptr x)
                      (FElem None x_ptr x).
  Proof using mem_ok word_ok.
    unfold FElem.
    intros m H.
    sepsimpl.
    exists x0.
    sepsimpl; simpl in *; eauto using relax_bounds.
  Qed.

  Lemma relax_bounds_FElem x_ptr x
    : Lift1Prop.impl1 (FElem (Some tight_bounds) x_ptr x)
                      (FElem (Some loose_bounds) x_ptr x).
  Proof using field_representation_ok mem_ok word_ok.
    unfold FElem.
    intros m H.
    sepsimpl.
    exists x0.
    sepsimpl; simpl in *; eauto using relax_bounds.
  Qed.

  Lemma FElem'_from_bytes
    : forall px : word.rep,
      Lift1Prop.iff1 (Placeholder px) (Lift1Prop.ex1 (FElem None px)).
  Proof using mem_ok word_ok.
    unfold FElem.
    intros.
    split; intros.
    {
      apply FElem_from_bytes in H.
      destruct H.
      do 2 eexists.
      sepsimpl; simpl; eauto.
    }
    {
      destruct H as [? [? ?]].
      sepsimpl.

      eapply FElem_to_bytes; eauto.
    }
  Qed.

  #[refine]
   Instance felem_alloc : Allocable (FElem None) :=
    {|
    size_in_bytes := felem_size_in_bytes;
    size_in_bytes_mod := felem_size_in_bytes_mod;
    |}.
  Proof.
    {
      intros; intros m H.
      apply FElem'_from_bytes.
      eexists.
      eapply drop_bounds_FElem; eauto.
    }
    {
      intros; intros m H.
      apply FElem'_from_bytes.
      eauto.
    }
  Defined.

  Local Ltac prove_field_compilation :=
    repeat straightline';
    handle_call;
    lazymatch goal with
    | |- sep _ _ _ => ecancel_assumption
    | _ => idtac
    end; eauto;
    sepsimpl; repeat straightline'; subst; eauto.


  Local Hint Extern 1 (spec_of _) => (simple refine (@spec_of_BinOp _ _ _ _ _ _ _ _ _ _)) : typeclass_instances.
  Local Hint Extern 1 (spec_of _) => (simple refine (@spec_of_UnOp _ _ _ _ _ _ _ _ _ _)) : typeclass_instances.

  Lemma compile_binop {name} {op: BinOp name}
        {tr m l functions} x y:
    let v := bin_model x y in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
           Rin Rout out x_ptr x_var y_ptr y_var out_ptr out_var
           bound_out,

      (_: spec_of name) functions ->

      map.get l out_var = Some out_ptr ->
      (FElem bound_out out_ptr out * Rout)%sep m ->

      (FElem (Some bin_xbounds) x_ptr x
       * FElem (Some bin_ybounds) y_ptr y
       * Rin)%sep m ->
      map.get l x_var = Some x_ptr ->
      map.get l y_var = Some y_ptr ->

      (let v := v in
       forall m',
         sep (FElem (Some bin_outbounds) out_ptr v) Rout m' ->
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
        (cmd.call [] name [expr.var out_var; expr.var x_var; expr.var y_var])
        k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof using env_ok ext_spec_ok locals_ok mem_ok word_ok.
    repeat straightline'.
    unfold FElem in *.
    sepsimpl.
    prove_field_compilation.
    apply H5.

    eapply Proper_sep_impl1; eauto.
    2:exact(fun a b => b).
    intros m' H'.
    eexists.
    sepsimpl;
      eauto.
  Qed.

  Lemma compile_unop {name} (op: UnOp name) {tr m l functions} x:
    let v := un_model x in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
           Rin Rout out x_ptr x_var out_ptr out_var out_bounds,

      (_: spec_of name) functions ->

      map.get l out_var = Some out_ptr ->
      (FElem out_bounds out_ptr out * Rout)%sep m ->

      (FElem (Some un_xbounds) x_ptr x * Rin)%sep m ->
      map.get l x_var = Some x_ptr ->

      (let v := v in
       forall m',
         sep (FElem (Some un_outbounds) out_ptr v) Rout m' ->
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
        (cmd.call [] name [expr.var out_var; expr.var x_var])
        k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof using env_ok ext_spec_ok locals_ok mem_ok word_ok.
    repeat straightline'.
    unfold FElem in *.
    sepsimpl.
    prove_field_compilation.
    apply H4.

    eapply Proper_sep_impl1; eauto.
    2:exact(fun a b => b).
    intros m' H'.
    eexists.
    sepsimpl;
      eauto.
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

  Notation make_bin_lemma op :=
    ltac:(cleanup_op_lemma (@compile_binop _ op)) (only parsing).

  Definition compile_mul := make_bin_lemma bin_mul.
  Definition compile_add := make_bin_lemma bin_add.
  Definition compile_sub := make_bin_lemma bin_sub.

  Notation make_un_lemma op :=
    ltac:(cleanup_op_lemma (@compile_unop _ op)) (only parsing).

  Definition compile_square := make_un_lemma un_square.
  Definition compile_scmula24 := make_un_lemma un_scmula24.

  Local Hint Extern 1 (spec_of _) => (simple refine (@spec_of_felem_copy _ _ _ _ _ _ _ _)) : typeclass_instances.

  Lemma compile_felem_copy {tr m l functions} x :
    let v := x in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
           R x_ptr x_var out out_ptr out_var x_bound out_bound,

      spec_of_felem_copy functions ->

      map.get l out_var = Some out_ptr ->

      (FElem x_bound x_ptr x * FElem out_bound out_ptr out * R)%sep m ->
      map.get l x_var = Some x_ptr ->

      (let v := v in
       forall m',
         (FElem x_bound x_ptr x * FElem x_bound out_ptr x * R)%sep m' ->
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
        (cmd.call [] felem_copy [expr.var out_var; expr.var x_var])
        k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof using env_ok ext_spec_ok locals_ok mem_ok word_ok.
    repeat straightline'.
    unfold FElem in *.
    sepsimpl.
    prove_field_compilation.
    apply H3.

    eapply Proper_sep_impl1; eauto.
    2:exact(fun a b => b).
    intros m' H'.
    sepsimpl;
      eauto.
    do 2 (eexists;
          sepsimpl;
          simpl;
          eauto).
    ecancel_assumption.
  Qed.

  Local Hint Extern 1 (spec_of _) => (simple refine (@spec_of_from_word _ _ _ _ _ _ _ _)) : typeclass_instances.

  Lemma compile_from_word {tr m l functions} x:
    let v := F.of_Z _ x in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
           R (wx : word) out out_ptr out_var out_bounds,

      spec_of_from_word functions ->

      map.get l out_var = Some out_ptr ->
      (FElem out_bounds out_ptr out * R)%sep m ->

      word.unsigned wx = x ->

      (let v := v in
       forall m',
         (FElem (Some tight_bounds) out_ptr v * R)%sep m' ->
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
        (cmd.call [] from_word
                  [expr.var out_var; expr.literal x])
        k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof using env_ok ext_spec_ok locals_ok mem_ok word_ok.
    repeat straightline'.
    unfold FElem in *.
    sepsimpl.
    prove_field_compilation.
    apply H3.

    eapply Proper_sep_impl1; eauto.
    2:exact(fun a b => b).
    intros m' H'.
    match goal with H : _ |- _ =>
                    rewrite word.of_Z_unsigned in H end.
    SpecializeBy.specialize_by_assumption.
    eexists;
      sepsimpl;
      eauto.
  Qed.

  Local Hint Extern 1 (spec_of _) => (simple refine (@spec_of_from_bytes _ _ _ _ _ _ _ _)) : typeclass_instances.

  Lemma compile_from_bytes {tr m l functions} x :
    let v : F _ := feval_bytes x in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
           Rx R x_ptr x_var out out_ptr out_var out_bound,

      spec_of_from_bytes functions ->

      map.get l out_var = Some out_ptr ->

      (FElemBytes x_ptr x * Rx)%sep m ->
      (FElem out_bound out_ptr out * R)%sep m ->
      map.get l x_var = Some x_ptr ->

      (let v := v in
       forall m',
         (FElem (Some tight_bounds) out_ptr v * R)%sep m' ->
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
        (cmd.call [] from_bytes [expr.var out_var; expr.var x_var])
        k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof using env_ok ext_spec_ok locals_ok mem_ok word_ok.
    repeat straightline'.
    unfold FElem in *.
    sepsimpl.
    prove_field_compilation.
    apply H4.

    eapply Proper_sep_impl1; eauto; try reflexivity.
    eapply Lift1Prop.impl1_ex1_r.
    intros m' H'; ssplit; eapply sep_emp_l; ssplit; eauto.
  Qed.

  Lemma compile_to_bytes {tr m l functions} x :
    let v : list _ := Z_to_bytes (F.to_Z x) encoded_felem_size_in_bytes in
    forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
           Rx R x_ptr x_var out out_ptr out_var,

      spec_of_to_bytes functions ->

      map.get l out_var = Some out_ptr ->

      (FElem (Some tight_bounds) x_ptr x * Rx)%sep m ->
      (FElemBytes out_ptr out * R)%sep m ->
      map.get l x_var = Some x_ptr ->

      (let v := v in
       forall m',
         (FElemBytes out_ptr v * R)%sep m' ->
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
        (cmd.call [] to_bytes [expr.var out_var; expr.var x_var])
        k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof using env_ok ext_spec_ok locals_ok mem_ok word_ok.
    repeat straightline'.
    subst v.
    unfold FElem in *.
    sepsimpl;
    eapply Proper_call; [ |eapply H]; cycle 1;
     [ ssplit;
        lazymatch goal with
        | |- (_ ⋆ _) _ => ecancel_assumption
        | |- exists R, (_ ⋆ R) _ => eexists; ecancel_assumption
        | _ => idtac
        end
     | cbv[postcondition_func postcondition_func_norets] in *;
        repeat straightline; destruct_lists_of_known_length;
        repeat straightline ].
    { unfold maybe_bounded in *; eauto. }
    intros ? ? ? ?; repeat straightline'.
    subst; eauto.
  Qed.
End Compile.


(*must be higher priority than compile_mul*)
#[export] Hint Extern 6 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (a24 * _)%F _))) =>
simple eapply compile_scmula24; shelve : compiler.

#[export] Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (_ * _)%F _))) =>
simple eapply compile_mul; shelve : compiler.
#[export] Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (_ + _)%F _))) =>
simple eapply compile_add; shelve : compiler.
#[export] Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (_ - _)%F _))) =>
simple eapply compile_sub; shelve : compiler.
#[export] Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (_ ^ 2)%F _))) =>
simple eapply compile_square; shelve : compiler.
#[export] Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (F.of_Z M_pos _) _))) =>
simple eapply compile_from_word; shelve : compiler.
#[export] Hint Extern 10 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ ?v _))) =>
is_var v; simple eapply compile_felem_copy; shelve : compiler.


#[export] Hint Immediate relax_bounds_FElem : ecancel_impl.
#[export] Hint Immediate drop_bounds_FElem : ecancel_impl.


#[export] Hint Extern 1 (spec_of _) => (simple refine (@spec_of_BinOp _ _ _ _ _ _ _ _ _ _)) : typeclass_instances.
#[export] Hint Extern 1 (spec_of _) => (simple refine (@spec_of_UnOp _ _ _ _ _ _ _ _ _ _)) : typeclass_instances.
#[export] Hint Extern 1 (spec_of felem_copy) => (simple refine (@spec_of_felem_copy _ _ _ _ _ _ _ _)) : typeclass_instances.
#[export] Hint Extern 1 (spec_of from_word) => (simple refine (@spec_of_from_word _ _ _ _ _ _ _ _)) : typeclass_instances.
