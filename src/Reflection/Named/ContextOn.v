(** * Transfer [Context] across an injection *)
Require Import Crypto.Reflection.Named.Syntax.

Section language.
  Context {base_type_code Name1 Name2 : Type}
          (f : Name2 -> Name1)
          (f_inj : forall x y, f x = f y -> x = y)
          {var : base_type_code -> Type}.

  Definition ContextOn (Ctx : Context Name1 var) : Context Name2 var
    := {| ContextT := Ctx;
          lookupb ctx n t := lookupb ctx (f n) t;
          extendb ctx n t v := extendb ctx (f n) v;
          removeb ctx n t := removeb ctx (f n) t;
          empty := empty |}.
End language.
