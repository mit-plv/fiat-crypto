Require Import bedrock2.Semantics.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.ScalarField.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Group.
Require Import Crypto.Algebra.ScalarMult.

Class GroupParameters :=
  { G : Type;
    eq : G -> G -> Prop;
    add : G -> G -> G;
    zero : G;
    opp : G -> G;
    scalarmult : Z -> G -> G;

    (* function names *)
    scmul : string;
  }.

Class GroupParameters_ok {group_parameters : GroupParameters} :=
  { group_ok : @group G eq add zero opp;
    scalarmult_ok : @is_scalarmult G eq add zero opp scalarmult;
  }.

Class GroupRepresentation {G : Type} {semantics : Semantics.parameters} :=
  { gelem : Type;
    geval : gelem -> G;
    GElem : word -> gelem -> Semantics.mem -> Prop;
  }.

Section Specs.
  Context {semantics : Semantics.parameters}
          {scalar_representaton : ScalarRepresentation}.
  Context {group_parameters : GroupParameters}
          {group_representaton : @GroupRepresentation G}.

  Instance spec_of_scmul : spec_of scmul :=
    (forall! (x old_out : gelem) (k : scalar) (pout px pk : word),
        (fun Rr mem =>
           (exists Ra, (GElem px x * Scalar pk k * Ra)%sep mem)
           /\ (GElem pout old_out * Rr)%sep mem)
          ===>
          scmul @ [pout; px; pk]
          ===>
          (fun _ =>
             liftexists (xk : gelem),
             (emp (geval xk = scalarmult (sceval k) (geval x))
              * GElem pout xk)%sep)).
End Specs.
Existing Instance spec_of_scmul.


