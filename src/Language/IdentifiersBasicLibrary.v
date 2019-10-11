Require Import Crypto.Language.Pre.
Require Import Crypto.Language.Language.
Require Import Crypto.Language.Inversion.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Sigma.

Module Compilers.
  Import Language.Compilers.
  Import Inversion.Compilers.
  Module Basic.
    Module GoalType.
      Local Set Primitive Projections.

      Class ExprReifyInfoT {exprInfo : Classes.ExprInfoT} :=
        {
          all_base_and_interp : list (Classes.base * Type)
          ; all_ident_and_interp : GallinaAndReifiedIdentList.t
        }.

      Record package :=
        {
          exprInfo : Classes.ExprInfoT
          ; exprExtraInfo : @Classes.ExprExtraInfoT exprInfo
          ; exprReifyInfo : @ExprReifyInfoT exprInfo
          ; ident_is_var_like : forall t (idc : Classes.ident t), Datatypes.bool
        }.

      Definition package_with_args (scraped_data : ScrapedData.t) (var_like_idents : GallinaIdentList.t) (base : Type) (ident : type.type (base.type base) -> Type)
        := package.

      Definition base_elim_with_args (scraped_data : ScrapedData.t) := Type.
      Definition ident_elim_with_args (scraped_data : ScrapedData.t) (base : Type) := Type.
    End GoalType.

    Module HelperLemmas.
      Section build_BuildInvertIdentCorrectT_opt.
        Context {base base_interp ident invertIdent buildIdent}
                (resT0 := @invert_expr.BuildInvertIdentCorrectT base base_interp ident invertIdent buildIdent).

        Definition build_BuildInvertIdentCorrectT_opt_bigT t (idc : ident t)
          := match invert_expr.invert_ident_Literal idc, invert_expr.is_nil idc, invert_expr.is_cons idc, invert_expr.is_Some idc, invert_expr.is_None idc, invert_expr.is_pair idc, invert_expr.is_tt idc return Prop with
             | Some v, false, false, false, false, false, false
               => match t return ident t -> type.interp (base.interp base_interp) t -> Prop with
                  | type.base (base.type.type_base t)
                    => fun idc v => idc = ident.ident_Literal (t:=t) v
                  | _ => fun _ _ => False
                  end idc v
             | None, true, false, false, false, false, false
               => match t return ident t -> Prop with
                  | type.base (base.type.list t)
                    => fun idc => idc = ident.ident_nil (t:=t)
                  | _ => fun _ => False
                  end idc
             | None, false, true, false, false, false, false
               => match t return ident t -> Prop with
                  | type.base t -> type.base (base.type.list _) -> type.base (base.type.list _)
                    => fun idc => existT _ _ idc = existT _ _ (ident.ident_cons (t:=t)) :> sigT ident
                  | _ => fun _ => False
                  end%etype idc
             | None, false, false, true, false, false, false
               => match t return ident t -> Prop with
                  | type.base t -> type.base (base.type.option _)
                    => fun idc => existT _ _ idc = existT _ _ (ident.ident_Some (t:=t)) :> sigT ident
                  | _ => fun _ => False
                  end%etype idc
             | None, false, false, false, true, false, false
               => match t return ident t -> Prop with
                  | type.base (base.type.option t)
                    => fun idc => idc = ident.ident_None (t:=t)
                  | _ => fun _ => False
                  end idc
             | None, false, false, false, false, true, false
               => match t return ident t -> Prop with
                  | type.base A -> type.base B -> type.base (base.type.prod _ _)
                    => fun idc => existT _ _ idc = existT _ _ (ident.ident_pair (A:=A) (B:=B)) :> sigT ident
                  | _ => fun _ => False
                  end%etype idc
             | None, false, false, false, false, false, true
               => match t return ident t -> Prop with
                  | type.base base.type.unit
                    => fun idc => idc = ident.ident_tt
                  | _ => fun _ => False
                  end%etype idc
             | None, false, false, false, false, false, false => True
             | _, _, _, _, _, _, _ => False
             end.

        Lemma build_BuildInvertIdentCorrectT_opt
              {base_beq} {reflect_base_beq : reflect_rel (@eq base) base_beq}
              (resT := @invert_expr.BuildInvertIdentCorrectT base base_interp ident invertIdent buildIdent)
          : (forall t v, invert_expr.invert_ident_Literal (ident.ident_Literal (t:=t) v) = Some v)
            -> (forall t, invert_expr.is_nil (ident.ident_nil (t:=t)) = true)
            -> (forall t, invert_expr.is_cons (ident.ident_cons (t:=t)) = true)
            -> (forall t, invert_expr.is_Some (ident.ident_Some (t:=t)) = true)
            -> (forall t, invert_expr.is_None (ident.ident_None (t:=t)) = true)
            -> (forall A B, invert_expr.is_pair (ident.ident_pair (A:=A) (B:=B)) = true)
            -> (invert_expr.is_tt ident.ident_tt = true)
            -> (forall t (idc : ident t), build_BuildInvertIdentCorrectT_opt_bigT t idc)
            -> resT.
        Proof using Type.
          cbv [build_BuildInvertIdentCorrectT_opt_bigT].
          intros ? ? ? ? ? ? ? H'; subst resT.
          constructor; intros ? idc; specialize (H' _ idc);
            repeat first [ solve [ eauto using eq_refl with nocore ]
                         | exfalso; assumption
                         | progress intros
                         | progress break_innermost_match
                         | apply conj
                         | progress subst
                         | progress inversion_sigma
                         | progress inversion_type
                         | match goal with
                           | [ H : ?x = _, H' : context[match ?x with _ => _ end] |- _ ]
                             => rewrite H in H'
                           end
                         | progress break_innermost_match_hyps ].
        Qed.
      End build_BuildInvertIdentCorrectT_opt.
    End HelperLemmas.
  End Basic.
End Compilers.
