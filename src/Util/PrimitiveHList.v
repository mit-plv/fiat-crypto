Require Import Coq.Lists.List.
Require Import Crypto.Util.PrimitiveProd.

Import Primitive.Notations.

Fixpoint hlist {A} (P : A -> Type) (ls : list A) : Type
  := match ls return Type with
     | nil => unit
     | cons x xs => P x * @hlist A P xs
     end%type.
Fixpoint split_list {A P} (ls : list (@sigT A P)) : { ls : list A & hlist P ls }
  := match ls with
     | nil => existT _ nil tt
     | cons x xs => let 'existT ls' hls' := @split_list A P xs in existT _ (cons (projT1 x) ls') (projT2 x, hls')
     end.
Fixpoint combine_hlist {A P} (ls : list A) : hlist P ls -> list (@sigT A P)
  := match ls return hlist P ls -> _ with
     | nil => fun _ => nil
     | cons x xs => fun '(Px, Pxs) => existT P x Px :: @combine_hlist A P xs Pxs
     end.
