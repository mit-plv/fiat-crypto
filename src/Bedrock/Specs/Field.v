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
    mul : string; add : string; sub : string;
    square : string; scmula24 : string; inv : string;

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

Lemma M_nonzero {fp : FieldParameters} : M <> 0.
Proof. cbv [M]. congruence. Qed.

Class FieldParameters_ok {field_parameters : FieldParameters} :=
  { M_prime : Znumtheory.prime M;
    (* TODO: a24_ok *)
  }.

Class FieldRepresentation
      {field_parameters : FieldParameters}
      {semantics : Semantics.parameters} :=
  { felem : Type;
    feval : felem -> F M_pos;
    felem_size_in_bytes : Z; (* for stack allocation *)
    FElem : word -> felem -> Semantics.mem -> Prop;
    bounds : Type;
    bounded_by : bounds -> felem -> Prop;

    (* for saturated implementations, loose/tight bounds are the same *)
    loose_bounds : bounds;
    tight_bounds : bounds;
  }.

Class FieldRepresentation_ok
      {field_parameters : FieldParameters}
      {semantics : Semantics.parameters}
      {field_representation : FieldRepresentation} :=
  { felem_size_in_bytes_mod :
      (felem_size_in_bytes mod Memory.bytes_per_word Semantics.width)%Z = 0%Z;
    relax_bounds :
      forall X : felem, bounded_by tight_bounds X
                        -> bounded_by loose_bounds X;
    }.

Section Specs.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}
          {field_representaton : FieldRepresentation}.

  Local Notation unop_spec name op xbounds outbounds :=
    (forall! (x : felem) (px pout : word) (old_out : felem),
        (fun Rr mem =>
           bounded_by xbounds x
           /\ (exists Ra, (FElem px x * Ra)%sep mem)
           /\ (FElem pout old_out * Rr)%sep mem)
          ===> name @ [px; pout] ===>
          (fun _ =>
           liftexists out,
           (emp (feval out = op (feval x)
                 /\ bounded_by outbounds out)
            * FElem pout out)%sep))
      (only parsing).

  Local Notation binop_spec name op xbounds ybounds outbounds :=
    (forall! (x y : felem) (px py pout : word) (old_out : felem),
        (fun Rr mem =>
           bounded_by xbounds x
           /\ bounded_by ybounds y
           /\ (exists Ra, (FElem px x * FElem py y * Ra)%sep mem)
           /\ (FElem pout old_out * Rr)%sep mem)
          ===> name @ [px; py; pout] ===>
          (fun _ =>
           liftexists out,
           (emp ((feval out = op (feval x) (feval y))
                 /\ bounded_by outbounds out)
            * FElem pout out)%sep)) (only parsing).

  Instance spec_of_mul : spec_of mul :=
    binop_spec mul F.mul loose_bounds loose_bounds tight_bounds.
  Instance spec_of_square : spec_of square :=
    unop_spec square (fun x => F.mul x x) loose_bounds tight_bounds.
  Instance spec_of_add : spec_of add :=
    binop_spec add F.add tight_bounds tight_bounds loose_bounds.
  Instance spec_of_sub : spec_of sub :=
    binop_spec sub F.sub tight_bounds tight_bounds loose_bounds.
  Instance spec_of_scmula24 : spec_of scmula24 :=
    unop_spec scmula24 (F.mul a24) loose_bounds tight_bounds.
  (* TODO: what are the bounds for inv? *)
  Instance spec_of_inv : spec_of inv :=
    unop_spec inv F.inv tight_bounds loose_bounds.

  Definition spec_of_felem_copy : spec_of felem_copy :=
    forall! (x : felem) (px pout : word) (old_out : felem),
      (sep (FElem px x * FElem pout old_out)%sep)
        ===> felem_copy @ [px; pout] ===>
        (fun _ => FElem px x * FElem pout x)%sep.

  Definition spec_of_felem_small_literal : spec_of felem_small_literal :=
    forall! (x pout : word) (old_out : felem),
      (sep (FElem pout old_out))
        ===> felem_small_literal @ [x; pout] ===>
        (fun _ =>
           liftexists X,
           (emp (F.to_Z (feval X) = word.unsigned x
                 /\ bounded_by tight_bounds X)
            * FElem pout X)%sep).
End Specs.
