Class CanonicalEncoding (T B:Type) := {
  enc : T -> B ;
  dec : B -> option T ;
  encoding_valid : forall x, dec (enc x) = Some x ;
  encoding_canonical : forall x_enc x, dec x_enc = Some x -> enc x = x_enc
}.

Notation "'canonical' 'encoding' 'of' T 'as' B" := (CanonicalEncoding T B) (at level 50).