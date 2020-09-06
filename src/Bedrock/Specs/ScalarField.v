Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Local Open Scope Z_scope.

Class ScalarFieldParameters :=
  { (** mathematical parameters **)
    L_pos : positive; (* modulus *)
    L : Z := Z.pos L_pos;
    scalarbits : Z;

    (** function names for bedrock2 **)
    sctestbit : string;
  }.

Class ScalarFieldParameters_ok
      {scalar_field_parameters : ScalarFieldParameters} :=
  { L_prime : Znumtheory.prime L;
    scalarbits_eq : scalarbits = Z.log2_up L;
  }.

Class ScalarRepresentation
      {scalar_field_parameters : ScalarFieldParameters}
      {semantics : Semantics.parameters} :=
  { scalar : Type;
    sceval : scalar -> F L_pos;
    Scalar : word -> scalar -> Semantics.mem -> Prop;
  }.

Section Specs.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {scalar_field_parameters : ScalarFieldParameters}.
  Context {scalar_representaton : ScalarRepresentation}.

  Definition spec_of_sctestbit : spec_of sctestbit :=
    (forall! (x : scalar) (px wi : word)
           (b:=Z.testbit (F.to_Z (sceval x)) (word.unsigned wi)),
        (fun Rr mem =>
           (exists Ra, (Scalar px x * Ra)%sep mem)
           /\ Rr mem)
          ===>
          sctestbit @ [px; wi] returns rets
          ===>
          (liftexists r,
           emp (rets = [r]
                /\ r = word.of_Z (Z.b2z b)))).
End Specs.

Section Proofs.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {scalar_field_parameters : ScalarFieldParameters}
          {scalar_field_parameters_ok : ScalarFieldParameters_ok}
          {scalar_representation : ScalarRepresentation}.

  Lemma sceval_range k :
    0 <= F.to_Z (sceval k) < 2 ^ scalarbits.
  Proof.
    pose proof (Znumtheory.prime_ge_2 (Z.pos L_pos) L_prime).
    pose proof (@F.to_Z_range L_pos (sceval k) ltac:(lia)).
    pose proof (Z.log2_log2_up_spec (Z.pos L_pos) ltac:(lia)).
    rewrite scalarbits_eq. change L with (Z.pos L_pos). lia.
  Qed.
End Proofs.

Section Compile.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {scalar_field_parameters : ScalarFieldParameters}.
  Context {scalar_representaton : ScalarRepresentation}.
  Existing Instance spec_of_sctestbit.

  Lemma compile_sctestbit :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr retvars R R' functions
           T (pred: T -> list word -> Semantics.mem -> Prop)
      x x_ptr x_var i wi i_var k k_impl var,
      spec_of_sctestbit functions ->
      (Scalar x_ptr x * R')%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals i_var = Some wi ->
      word.unsigned wi = Z.of_nat i ->
      let v := Z.testbit (F.to_Z (sceval x)) (Z.of_nat i) in
      (let head := v in
       forall m,
         (Scalar x_ptr x * R')%sep m ->
         (find k_impl
          implementing (pred (k head))
          and-returning retvars
          and-locals-post locals_ok
          with-locals (map.put locals var (word.of_Z (Z.b2z head)))
          and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [var] sctestbit [expr.var x_var; expr.var i_var])
               k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'.
    handle_call; [ solve [eauto] ..
                 | cbv [dlet.dlet] in *|-; sepsimpl ].
    cbn [length] in *. destruct_lists_of_known_length.
    subst_lets_in_goal. subst.
    match goal with H : word.unsigned _ = Z.of_nat _ |- _ =>
                    rewrite H in *
    end.
    repeat straightline'; eauto.
  Qed.
End Compile.

Ltac scfield_compile_step := simple eapply compile_sctestbit.
