Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.MSets.MSetFacts.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.ListUtil.SetoidList.
Require Import Crypto.Util.Logic.ExistsEqAnd.

Local Set Implicit Arguments.

Set Implicit Arguments.
Unset Strict Implicit.

Module PositiveSetFacts.
  Module F := Facts PositiveSet.
  Include F.
  Import PositiveSet.

  Global Instance elements_Proper_Equal
    : Proper (Equal ==> Logic.eq) elements | 10.
  Proof.
    intros p1 p2 Hp.
    apply eqlistA_eq_iff.
    eapply SortA_equivlistA_eqlistA; try apply elements_spec2; try exact _.
    cbv [equivlistA]; intro.
    rewrite !elements_spec1.
    apply Hp.
  Qed.
End PositiveSetFacts.
