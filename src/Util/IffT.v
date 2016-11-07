Require Import Coq.Classes.RelationClasses.
Notation iffT := (fun A B => inhabited ((A -> B) * (B -> A)))%type.

Global Instance iffT_Reflexive : Reflexive iffT | 1.
Proof. repeat constructor; intro; assumption. Defined.
Global Instance iffT_Symmetric : Symmetric iffT | 1.
Proof. repeat (intros [?] || intro); constructor; tauto. Defined.
Global Instance iffT_Transitive : Transitive iffT | 1.
Proof. repeat (intros [?] || intro); constructor; tauto. Defined.
