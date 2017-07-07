(** * Transfer [Context] across an injection *)
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.ContextDefinitions.

Section language.
  Context {base_type_code Name1 Name2 : Type}
          (f : Name2 -> Name1)
          (f_inj : forall x y, f x = f y -> x = y)
          {var : base_type_code -> Type}.

  Definition ContextOn (Ctx : Context Name1 var) : Context Name2 var
    := {| ContextT := Ctx;
          lookupb t ctx n := lookupb t ctx (f n);
          extendb t ctx n v := extendb ctx (f n) v;
          removeb t ctx n := removeb t ctx (f n);
          empty := empty |}.

  Lemma ContextOnOk {Ctx} (COk : ContextOk Ctx) : ContextOk (ContextOn Ctx).
  Proof.
    unfold ContextOn in *; split; intros; try eapply COk; eauto.
  Qed.
End language.

Arguments ContextOnOk {_ _ _ f} f_inj {_ _} COk.
