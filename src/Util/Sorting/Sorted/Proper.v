Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Lists.SetoidPermutation.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Sorting.Sorted.
Require Import Crypto.Util.Tactics.SplitInContext.

Local Set Implicit Arguments.

Local Ltac t' :=
  repeat first [ progress cbv [Proper respectful impl flip] in *
               | progress intros
               | progress invlist HdRel
               | progress invlist Sorted
               | progress invlist StronglySorted
               | progress split_iff
               | solve [ eauto ] ].
Local Ltac t :=
  first [ induction 1; progress repeat constructor; t'
        | intro; t ].

Global Instance HdRel_Proper_impl A R
  : Proper ((R ==> R ==> impl) ==> R ==> eqlistA R ==> impl) (@HdRel A).
Proof. t. Qed.
Global Instance HdRel_Proper_flip_impl A R
  : Proper ((R ==> R ==> flip impl) ==> R ==> eqlistA R ==> flip impl) (@HdRel A).
Proof. t. Qed.
Global Instance HdRel_Proper_iff A R
  : Proper ((R ==> R ==> iff) ==> R ==> eqlistA R ==> iff) (@HdRel A).
Proof. t. Qed.
Global Instance HdRel_Proper_impl_sym A R {_: Symmetric R}
  : Proper ((R ==> R ==> impl) ==> R ==> flip (eqlistA R) ==> impl) (@HdRel A).
Proof. t. Qed.
Global Instance HdRel_Proper_flip_impl_sym A R {_: Symmetric R}
  : Proper ((R ==> R ==> flip impl) ==> R ==> flip (eqlistA R) ==> flip impl) (@HdRel A).
Proof. t. Qed.
Global Instance HdRel_Proper_iff_sym A R {_: Symmetric R}
  : Proper ((R ==> R ==> iff) ==> R ==> flip (eqlistA R) ==> iff) (@HdRel A).
Proof. t. Qed.
Global Instance Sorted_Proper_impl A R
  : Proper ((R ==> R ==> impl) ==> eqlistA R ==> impl) (@Sorted A).
Proof. t. eapply HdRel_Proper_impl; eassumption. Qed.
Global Instance Sorted_Proper_flip_impl A R
  : Proper ((R ==> R ==> flip impl) ==> eqlistA R ==> flip impl) (@Sorted A).
Proof. t. eapply HdRel_Proper_flip_impl; eassumption. Qed.
Global Instance Sorted_Proper_iff A R
  : Proper ((R ==> R ==> iff) ==> eqlistA R ==> iff) (@Sorted A).
Proof.
  repeat intro; split; [ eapply Sorted_Proper_impl | eapply Sorted_Proper_flip_impl ]; try eassumption; t'.
Qed.
Global Instance Sorted_Proper_impl_sym A R {_: Symmetric R}
  : Proper ((R ==> R ==> impl) ==> flip (eqlistA R) ==> impl) (@Sorted A).
Proof. t. eapply HdRel_Proper_impl_sym; (idtac + symmetry); eassumption. Qed.
Global Instance Sorted_Proper_flip_impl_sym A R {_: Symmetric R}
  : Proper ((R ==> R ==> flip impl) ==> flip (eqlistA R) ==> flip impl) (@Sorted A).
Proof. t. eapply HdRel_Proper_flip_impl_sym; (idtac + symmetry); eassumption. Qed.
Global Instance Sorted_Proper_iff_sym A R {_: Symmetric R}
  : Proper ((R ==> R ==> iff) ==> flip (eqlistA R) ==> iff) (@Sorted A).
Proof.
  repeat intro; split; [ eapply Sorted_Proper_impl_sym | eapply Sorted_Proper_flip_impl_sym ]; try eassumption; t'.
Qed.
