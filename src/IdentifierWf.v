Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import Crypto.Identifier.
Require Import Crypto.LanguageInversion.
Require Export Crypto.LanguageWf.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.Forall.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Logic.ProdForall.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Notations.
Import Coq.Lists.List ListNotations. Local Open Scope list_scope.

Import EqNotations.
Module Compilers.
  Import LanguageInversion.Compilers.
  Import Identifier.Compilers.
  Import expr.Notations.
  Export LanguageWf.Compilers.

  Module ident.
    Export Identifier.Compilers.ident.

    Local Open Scope etype_scope.
    Global Instance eqv_Reflexive {t} : Reflexive (fun idc1 idc2 : ident t => type.eqv (ident.interp idc1) (ident.interp idc2)) | 20.
    Proof. intro; apply eqv_Reflexive_Proper. Qed.

    Global Instance eqv_Transitive {t} : Transitive (fun idc1 idc2 : ident t => type.eqv (ident.interp idc1) (ident.interp idc2)) | 20.
    Proof. repeat intro; etransitivity; eassumption. Qed.

    Global Instance eqv_Symmetric {t} : Symmetric (fun idc1 idc2 : ident t => type.eqv (ident.interp idc1) (ident.interp idc2)) | 20.
    Proof. repeat intro; symmetry; eassumption. Qed.
  End ident.

  (*
  Module expr.
    Export LanguageWf.Compilers.expr.
    Section with_cast.
      Context {cast_outside_of_range : ZRange.zrange -> BinInt.Z -> BinInt.Z}.
      Local Notation ident_interp := (@ident.gen_interp cast_outside_of_range).
      Local Notation interp := (@expr.interp _ _ _ (@ident_interp)).
      Local Notation Interp := (@expr.Interp _ _ _ (@ident_interp)).
      Local Open Scope etype_scope.
      Lemma wf_interp_Proper G {t} e1 e2
            (Hwf : @wf _ _ _ _ G t e1 e2)
            (HG : forall t v1 v2, In (existT _ t (v1, v2)) G -> v1 == v2)
        : interp e1 == interp e2.
      Proof. eapply wf_interp_Proper_gen1; eassumption. Qed.

      Lemma Wf_Interp_Proper {t} (e : expr.Expr t) : Wf e -> Proper type.eqv (Interp e).
      Proof. eapply Wf_Interp_Proper_gen; eassumption. Qed.
    End with_cast.
   End expr.
   *)

  (*
  Module GeneralizeVar.
    Import Language.Compilers.GeneralizeVar.
    Export LanguageWf.Compilers.GeneralizeVar.
    Local Open Scope etype_scope.

    Section with_cast.
      Context {cast_outside_of_range : zrange -> Z -> Z}.

      Local Notation Interp := (expr.Interp (@ident.gen_interp cast_outside_of_range)).

      Lemma Interp_FromFlat_ToFlat {t} (e : Expr t) (Hwf : expr.Wf e) : Interp (FromFlat (ToFlat e)) == Interp e.
      Proof. apply Interp_gen1_FromFlat_ToFlat; assumption. Qed.

      Lemma Interp_GeneralizeVar {t} (e : Expr t) (Hwf : expr.Wf e) : Interp (GeneralizeVar (e _)) == Interp e.
      Proof. apply Interp_gen1_GeneralizeVar; assumption. Qed.
    End with_cast.
  End GeneralizeVar.
*)
End Compilers.
