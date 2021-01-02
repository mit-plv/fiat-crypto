Require Import coqutil.Byte.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Local Open Scope Z_scope.

Class FieldParameters :=
  { (** mathematical parameters **)
    M_pos : positive; (* modulus *)
    M : Z := Z.pos M_pos;
    a24 : F M_pos; (* (a+2) / 4 or (a-2) / 4, depending on the implementation *)

    (** function names **)
    mul : string; add : string; sub : string; opp : string;
    square : string; scmula24 : string; inv : string;
    from_bytes : string; to_bytes : string;

    (* felem_small_literal p x :=
         store p (expr.literal x);
         store (p+4) (expr.literal 0);
         ...

       felem_copy pX pY :=
         store pX (load pY);
         store (pX+4) (load (pY+4));
         ... *)
    felem_copy : string;
    felem_small_literal : string;
  }.

Class FieldParameters_ok {field_parameters : FieldParameters} :=
  { M_prime : Znumtheory.prime M;
    (* TODO: a24_ok *)
  }.

Class FieldRepresentation
      {field_parameters : FieldParameters}
      {semantics : Semantics.parameters} :=
  { felem : Type;
    feval : felem -> F M_pos;
    feval_bytes : list byte -> F M_pos;
    felem_size_in_bytes : Z; (* for stack allocation *)
    FElem : word -> felem -> Semantics.mem -> Prop;
    FElemBytes : word -> list byte -> Semantics.mem -> Prop :=
      fun addr bs =>
        (emp (length bs = Z.to_nat felem_size_in_bytes)
         * array ptsto (word.of_Z 1) addr bs)%sep;
    bounds : Type;
    bounded_by : bounds -> felem -> Prop;

    (* for saturated implementations, loose/tight bounds are the same *)
    loose_bounds : bounds;
    tight_bounds : bounds;
  }.

Definition Placeholder
           {field_parameters : FieldParameters}
           {semantics : Semantics.parameters}
           {field_representation : FieldRepresentation}
           (p : Semantics.word) : Semantics.mem -> Prop :=
  Memory.anybytes p felem_size_in_bytes.

Class FieldRepresentation_ok
      {field_parameters : FieldParameters}
      {semantics : Semantics.parameters}
      {field_representation : FieldRepresentation} :=
  { felem_size_in_bytes_mod :
      (felem_size_in_bytes mod Memory.bytes_per_word Semantics.width)%Z = 0%Z;
    FElem_from_bytes :
      forall px,
        Lift1Prop.iff1 (Placeholder px) (Lift1Prop.ex1 (FElem px));
    relax_bounds :
      forall X : felem, bounded_by tight_bounds X
                        -> bounded_by loose_bounds X;
  }.

Notation unop_spec name op xbounds outbounds :=
  (forall! (x : felem) (px pout : word),
      (fun Rr mem =>
         bounded_by xbounds x
         /\ (exists Ra, (FElem px x * Ra)%sep mem)
         /\ (Placeholder pout * Rr)%sep mem)
        ===> name @ [pout; px] ===>
        (fun _ =>
           liftexists out,
           (emp (feval out = op (feval x)
                 /\ bounded_by outbounds out)
            * FElem pout out)%sep))
    (only parsing).

Notation binop_spec name op xbounds ybounds outbounds :=
  (forall! (x y : felem) (px py pout : word),
      (fun Rr mem =>
         bounded_by xbounds x
         /\ bounded_by ybounds y
         /\ (exists Ra, (FElem px x * Ra)%sep mem)
         /\ (exists Ra, (FElem py y * Ra)%sep mem)
         /\ (Placeholder pout * Rr)%sep mem)
        ===> name @ [pout; px; py] ===>
        (fun _ =>
           liftexists out,
           (emp ((feval out = op (feval x) (feval y))
                 /\ bounded_by outbounds out)
            * FElem pout out)%sep)) (only parsing).

Section FunctionSpecs.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.

  Instance spec_of_mul : spec_of mul :=
    binop_spec mul F.mul loose_bounds loose_bounds tight_bounds.
  Instance spec_of_square : spec_of square :=
    unop_spec square (fun x => F.mul x x) loose_bounds tight_bounds.
  Instance spec_of_add : spec_of add :=
    binop_spec add F.add tight_bounds tight_bounds loose_bounds.
  Instance spec_of_sub : spec_of sub :=
    binop_spec sub F.sub tight_bounds tight_bounds loose_bounds.
  Instance spec_of_opp : spec_of opp :=
    unop_spec opp F.opp tight_bounds loose_bounds.
  Instance spec_of_scmula24 : spec_of scmula24 :=
    unop_spec scmula24 (F.mul a24) loose_bounds tight_bounds.
  (* TODO: what are the bounds for inv? *)
  Instance spec_of_inv : spec_of inv :=
    unop_spec inv F.inv tight_bounds loose_bounds.

  Definition spec_of_from_bytes : spec_of from_bytes :=
    forall! (bs : list byte) (px pout : word),
      (fun Rr mem =>
         (exists Ra, (FElemBytes px bs * Ra)%sep mem)
         /\ (Placeholder pout * Rr)%sep mem)
        ===> from_bytes @ [pout; px] ===>
        (fun _ =>
           liftexists X,
           (emp (feval X = feval_bytes bs /\ bounded_by tight_bounds X)
            * FElem pout X)%sep).

  Definition spec_of_to_bytes : spec_of to_bytes :=
    forall! (x : felem) (px pout : word) (old_out : list byte),
      (fun Rr mem =>
         bounded_by tight_bounds x
         /\ (exists Ra, (FElem px x * Ra)%sep mem)
         /\ (FElemBytes pout old_out * Rr)%sep mem)
        ===> to_bytes @ [pout; px] ===>
        (fun _ =>
           liftexists bs,
           (emp (feval_bytes bs = feval x) * FElemBytes pout bs)%sep).

  Definition spec_of_felem_copy : spec_of felem_copy :=
    forall! (x : felem) (px pout : word),
      (sep (FElem px x * Placeholder pout)%sep)
        ===> felem_copy @ [pout; px] ===>
        (fun _ => FElem px x * FElem pout x)%sep.

  Definition spec_of_felem_small_literal : spec_of felem_small_literal :=
    forall! (x pout : word),
      (sep (Placeholder pout))
        ===> felem_small_literal @ [pout; x] ===>
        (fun _ =>
           liftexists X,
           (emp (F.to_Z (feval X) = word.unsigned x
                 /\ bounded_by tight_bounds X)
            * FElem pout X)%sep).
End FunctionSpecs.

Section SpecProperties.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.

  Lemma FElem_to_bytes px x :
    Lift1Prop.impl1 (FElem px x) (Placeholder px).
  Proof.
    rewrite FElem_from_bytes.
    repeat intro; eexists; eauto.
  Qed.

  Lemma M_nonzero : M <> 0.
  Proof. cbv [M]. congruence. Qed.
End SpecProperties.
