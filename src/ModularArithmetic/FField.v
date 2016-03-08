Require Export Crypto.Spec.ModularArithmetic.
Require Export Field.

Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.

Local Open Scope F_scope.

Definition OpaqueF := F.
Definition OpaqueZmodulo := BinInt.Z.modulo.
Definition Opaqueadd {p} : OpaqueF p -> OpaqueF p -> OpaqueF p := @add p.
Definition Opaquemul {p} : OpaqueF p -> OpaqueF p -> OpaqueF p := @mul p.
Definition Opaquesub {p} : OpaqueF p -> OpaqueF p -> OpaqueF p := @sub p.
Definition Opaquediv {p} : OpaqueF p -> OpaqueF p -> OpaqueF p := @div p.
Definition Opaqueopp {p} : OpaqueF p -> OpaqueF p := @opp p.
Definition Opaqueinv {p} : OpaqueF p -> OpaqueF p := @inv p.
Definition OpaqueZToField {p} : BinInt.Z -> OpaqueF p := @ZToField p.
Definition Opaqueadd_correct {p} : @Opaqueadd p = @add p := eq_refl.
Definition Opaquesub_correct {p} : @Opaquesub p = @sub p := eq_refl.
Definition Opaquemul_correct {p} : @Opaquemul p = @mul p := eq_refl.
Definition Opaquediv_correct {p} : @Opaquediv p = @div p := eq_refl.
Global Opaque F OpaqueZmodulo Opaqueadd Opaquemul Opaquesub Opaquediv Opaqueopp Opaqueinv OpaqueZToField.

Definition OpaqueFieldTheory p {prime_p} : @field_theory (OpaqueF p) (OpaqueZToField 0%Z) (OpaqueZToField 1%Z) Opaqueadd Opaquemul Opaquesub Opaqueopp Opaquediv Opaqueinv eq := Eval hnf in @Ffield_theory p prime_p.

Ltac FIELD_SIMPL_idtac FLD lH rl :=
  let Simpl := idtac (* (protect_fv "field") *) in
  let lemma := get_SimplifyEqLemma FLD in
  get_FldPre FLD ();
  Field_Scheme Simpl Ring_tac.ring_subst_niter lemma FLD lH;
  get_FldPost FLD ().
Ltac field_simplify_eq_idtac := let G := Get_goal in field_lookup (PackField FIELD_SIMPL_idtac) [] G.

Ltac F_to_Opaque :=
  change F with OpaqueF in *;
  change BinInt.Z.modulo with OpaqueZmodulo in *;
  change @add with @Opaqueadd in *;
  change @mul with @Opaquemul in *;
  change @sub with @Opaquesub in *;
  change @div with @Opaquediv in *;
  change @opp with @Opaqueopp in *;
  change @inv with @Opaqueinv in *;
  change @ZToField with @OpaqueZToField in *.

Ltac F_from_Opaque p :=
  change OpaqueF with F in *;
  change (@sig BinNums.Z (fun z : BinNums.Z => @eq BinNums.Z z (BinInt.Z.modulo z p))) with (F p) in *;
  change OpaqueZmodulo with BinInt.Z.modulo in *;
  change @Opaqueopp with @opp in *;
  change @Opaqueinv with @inv in *;
  change @OpaqueZToField with @ZToField in *;
  rewrite ?@Opaqueadd_correct, ?@Opaquesub_correct, ?@Opaquemul_correct, ?@Opaquediv_correct in *.

Ltac F_field_simplify_eq :=
  lazymatch goal with |- @eq (F ?p) _ _ =>
    F_to_Opaque;
    field_simplify_eq_idtac;
    compute;
    F_from_Opaque p
  end.

Ltac F_field := F_field_simplify_eq; [ring|..].

Ltac notConstant t := constr:NotConstant.
