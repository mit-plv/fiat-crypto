Require Import Rupicola.Lib.Api.
Local Open Scope Z_scope.

Class ScalarFieldParameters :=
  { (** mathematical parameters **)
    L_pos : positive; (* modulus *)
    L : Z := Z.pos L_pos;
    (** function names **)
    sctestbit : string;
  }.

(* In practice, these would be instantiated with:
   bignum := list word
   eval := fun ws => Positional.eval weight n (map word.unsigned ws)
   Bignum := (fun addr xs =>
               (emp (length xs = n) * array scalar addr xs)%sep)
   bounds := list (option zrange)
   bounded_by := (fun bs ws =>
                   list_Z_bounded_by bs (map word.unsigned ws)) *)
Class ScalarRepresentation :=
  { scalar : Type;
    sceval : scalar -> Z;
    Scalar :
      forall {semantics : Semantics.parameters},
        word -> scalar -> Semantics.mem -> Prop;
  }.

Section Specs.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {scalar_field_parameters : ScalarFieldParameters}.
  Context {scalar_representaton : ScalarRepresentation}.

  Instance spec_of_sctestbit : spec_of sctestbit :=
    (forall! (x : scalar) (px wi : word)
           (b:=Z.testbit (sceval x) (word.unsigned wi)),
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
Existing Instances spec_of_sctestbit.

Section Compile.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {scalar_field_parameters : ScalarFieldParameters}.
  Context {scalar_representaton : ScalarRepresentation}.

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
      let v := Z.testbit (sceval x) (Z.of_nat i) in
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
