Require Import Rupicola.Lib.Api.
Local Open Scope Z_scope.

Class FieldParameters :=
  { (** mathematical parameters **)
    M_pos : positive; (* modulus *)
    M : Z := Z.pos M_pos;
    a24 : Z; (* (a+2) / 4 or (a-2) / 4, depending on the implementation *)
    Finv : Z -> Z; (* modular inverse in Z/M *)
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

Class FieldRepresentation {semantics : Semantics.parameters} :=
  { felem : Type;
    feval : felem -> Z;
    FElem : word -> felem -> Semantics.mem -> Prop;
    bounds : Type;
    bounded_by : bounds -> felem -> Prop;

    (* for saturated implementations, loose/tight bounds are the same *)
    loose_bounds : bounds;
    tight_bounds : bounds;
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
           (emp ((feval out mod M = (op (feval x)) mod M)%Z
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
           (emp ((feval out mod M = (op (feval x) (feval y)) mod M)%Z
                 /\ bounded_by outbounds out)
            * FElem pout out)%sep)) (only parsing).

  Definition spec_of_mul : spec_of mul :=
    binop_spec mul Z.mul loose_bounds loose_bounds tight_bounds.
  Definition spec_of_square : spec_of square :=
    unop_spec square (fun x => Z.mul x x) loose_bounds tight_bounds.
  Definition spec_of_add : spec_of add :=
    binop_spec add Z.add tight_bounds tight_bounds loose_bounds.
  Definition spec_of_sub : spec_of sub :=
    binop_spec sub Z.sub tight_bounds tight_bounds loose_bounds.
  Definition spec_of_scmula24 : spec_of scmula24 :=
    unop_spec scmula24 (Z.mul a24) loose_bounds tight_bounds.

  (* TODO: what are the bounds for inv? *)
  Definition spec_of_inv : spec_of inv :=
    (forall! (x : felem) (px pout : word) (old_out : felem),
        (fun Rr mem =>
           bounded_by tight_bounds x
           /\ (exists Ra, (FElem px x * Ra)%sep mem)
           /\ (FElem pout old_out * Rr)%sep mem)
          ===> inv @ [px; pout] ===>
          (fun _ =>
           liftexists out,
           (emp ((feval out mod M = (Finv (feval x mod M)) mod M)%Z
                 /\ bounded_by loose_bounds out)
            * FElem pout out)%sep)).

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
           (emp (feval X mod M = word.unsigned x mod M
                 /\ bounded_by tight_bounds X)
            * FElem pout X)%sep).
End Specs.
