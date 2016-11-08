Require Import Coq.Classes.RelationClasses.
Notation iffT A B := (((A -> B) * (B -> A)))%type.
Notation iffTp := (fun A B => inhabited (iffT A B)).

Global Instance iffTp_Reflexive : Reflexive iffTp | 1.
Proof. repeat constructor; intro; assumption. Defined.
Global Instance iffTp_Symmetric : Symmetric iffTp | 1.
Proof. repeat (intros [?] || intro); constructor; tauto. Defined.
Global Instance iffTp_Transitive : Transitive iffTp | 1.
Proof. repeat (intros [?] || intro); constructor; tauto. Defined.
