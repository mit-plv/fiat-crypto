Class Encoding (T B:Type) := {
  enc : T -> B ;
  dec : B -> option T ;
  encoding_valid : forall x, dec (enc x) = Some x
}.

Notation "'encoding' 'of' T 'as' B" := (Encoding T B) (at level 50).