Require Import Rewriter.Language.Language.
Require Import Rewriter.Language.Inversion.
Require Import Crypto.Language.API.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.HProp.

Module Compilers.
  Import Language.Compilers.
  Import Inversion.Compilers.
  Import Language.API.Compilers.
  Import Compilers.API.

  Module expr.
    Import Language.API.Compilers.invert_expr.

    Local Notation tZ := (base.type.type_base base.type.Z).
    Local Notation tzrange := (base.type.type_base base.type.zrange).

    Local Lemma diff_None_Some {T v P} : @None T = Some v -> P.
    Proof. discriminate. Qed.

    Lemma invert_Z_cast_Z_cast {var} (r : ZRange.zrange)
      : invert_Z_cast (var:=var) (#ident.Z_cast @ ##r) = Some r.
    Proof. destruct_head'_prod; reflexivity. Qed.

    Lemma invert_Z_cast_Some_match_type {var t} (e : @expr var t) r
      : invert_Z_cast e = Some r
        -> match t return expr t -> Prop with
           | (type.base tZ -> type.base tZ)
             => fun e => e = (#ident.Z_cast @ ##r)%expr
           | _ => fun _ => False
           end%etype e.
    Proof.
      cbv [invert_Z_cast Option.bind].
      edestruct invert_AppIdent eqn:?; expr.invert_subst; try exact diff_None_Some; [].
      destruct_head'_sigT; destruct_head'_prod; cbn [fst snd projT1 projT2] in *.
      repeat (break_innermost_match_step; try exact diff_None_Some; []).
      edestruct reflect_smart_Literal eqn:?; expr.invert_subst; try exact diff_None_Some; [].
      ident.invert_for ident; subst; inversion_type; cbn [f_equal2 eq_rect] in *; try exact diff_None_Some; [].
      now intro; inversion_option; subst; inversion_prod; subst.
    Qed.

    Lemma invert_Z_cast_Some {var t} (e : @expr var t) r
      : invert_Z_cast e = Some r -> existT (@expr var) t e = existT (@expr var) _ (#ident.Z_cast @ ##r)%expr.
    Proof.
      intro H; apply invert_Z_cast_Some_match_type in H;
        now break_innermost_match_hyps; subst.
    Qed.

    Lemma invert_Z_cast_Some_Z {var} (e : @expr var (tZ -> tZ)) r
      : invert_Z_cast e = Some r -> e = (#ident.Z_cast @ ##r)%expr.
    Proof. apply (@invert_Z_cast_Some_match_type var _ e). Qed.

    Lemma invert_Z_cast2_Z_cast2 {var} (r : ZRange.zrange * ZRange.zrange)
      : invert_Z_cast2 (var:=var) (#ident.Z_cast2 @ ##r) = Some r.
    Proof. destruct_head'_prod; reflexivity. Qed.

    Lemma invert_Z_cast2_Some_match_type {var t} (e : @expr var t) r
      : invert_Z_cast2 e = Some r
        -> match t return expr t -> Prop with
           | (type.base (tZ * tZ) -> type.base (tZ * tZ))
             => fun e => e = (#ident.Z_cast2 @ ##r)%expr
           | _ => fun _ => False
           end%etype e.
    Proof.
      cbv [invert_Z_cast2 Option.bind].
      edestruct invert_AppIdent eqn:?; expr.invert_subst; try exact diff_None_Some; [].
      destruct_head'_sigT; destruct_head'_prod; cbn [fst snd projT1 projT2] in *.
      repeat (break_innermost_match_step; try exact diff_None_Some; []).
      edestruct reflect_smart_Literal eqn:?; expr.invert_subst; try exact diff_None_Some; [].
      ident.invert_for ident; subst; inversion_type; cbn [f_equal2 eq_rect] in *; try exact diff_None_Some; [].
      now intro; inversion_option; subst; inversion_prod; subst.
    Qed.

    Lemma invert_Z_cast2_Some {var t} (e : @expr var t) r
      : invert_Z_cast2 e = Some r -> existT (@expr var) t e = existT (@expr var) _ (#ident.Z_cast2 @ ##r)%expr.
    Proof.
      intro H; apply invert_Z_cast2_Some_match_type in H;
        now break_innermost_match_hyps; subst.
    Qed.

    Lemma invert_Z_cast2_Some_ZZ {var} (e : @expr var (tZ * tZ -> tZ * tZ)) r
      : invert_Z_cast2 e = Some r -> e = (#ident.Z_cast2 @ ##r)%expr.
    Proof. apply (@invert_Z_cast2_Some_match_type var _ e). Qed.
  End expr.
End Compilers.
