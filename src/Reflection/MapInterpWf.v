(** * Well-foundedness of changing the interp function on PHOAS Representation of Gallina *)
Require Import Coq.Strings.String Coq.Classes.RelationClasses.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.MapInterp.
Require Import Crypto.Reflection.WfRel.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

Local Open Scope ctype_scope.
Local Open Scope expr_scope.
Section language.
  Context {base_type_code : Type}
          {interp_base_type interp_base_type1 interp_base_type2 : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (f1 : forall t, interp_base_type t -> interp_base_type1 t)
          (f2 : forall t, interp_base_type t -> interp_base_type2 t)
          (R : forall t, interp_base_type1 t -> interp_base_type2 t -> Prop)
          (Rf12 : forall t v, R t (f1 t v) (f2 t v)).

  Section with_var.
    Context {var1 var2 : base_type_code -> Type}.

    Lemma flat_rel_pointwise2_mapf {t} (v : interp_flat_type_gen interp_base_type t)
      : interp_flat_type_gen_rel_pointwise2
          R
          (mapf_interp_flat_type_gen f1 v)
          (mapf_interp_flat_type_gen f2 v).
    Proof. induction t; simpl; auto. Qed.

    Lemma wff_mapf_interp {t e1 e2} G
          (Hwf : @wff base_type_code interp_base_type op var1 var2 G t e1 e2)
      : rel_wff R G (mapf_interp f1 e1) (mapf_interp f2 e2).
    Proof. induction Hwf; constructor; auto using flat_rel_pointwise2_mapf. Qed.

    Lemma wf_map_interp {t e1 e2} G
          (Hwf : @wf base_type_code interp_base_type op var1 var2 G t e1 e2)
      : rel_wf R G (map_interp f1 e1) (map_interp f2 e2).
    Proof. induction Hwf; constructor; auto using wff_mapf_interp. Qed.
  End with_var.

  Lemma WfMapInterp {t e} (Hwf : @Wf base_type_code interp_base_type op t e)
    : RelWf R (MapInterp f1 e) (MapInterp f2 e).
  Proof. repeat intro; apply wf_map_interp, Hwf. Qed.
End language.
