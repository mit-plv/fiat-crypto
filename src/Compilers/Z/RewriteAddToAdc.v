Require Import Coq.ZArith.ZArith.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.InterpretToPHOAS.
Require Import Crypto.Compilers.Named.Compile.
Require Import Crypto.Compilers.Named.Wf.
Require Import Crypto.Compilers.Named.CountLets.
Require Import Crypto.Compilers.Named.PositiveContext.
Require Import Crypto.Compilers.Named.PositiveContext.Defaults.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Named.DeadCodeElimination.
Require Import Crypto.Compilers.Z.Named.RewriteAddToAdc.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Decidable.

(** N.B. This procedure only works when there are no nested lets,
    i.e., nothing like [let x := let y := z in w] in the PHOAS syntax
    tree.  This is a limitation of [compile]. *)

Local Open Scope bool_scope.

Section language.
  Local Notation PContext var := (PositiveContext _ var _ internal_base_type_dec_bl).

  Definition RewriteAdc {t} (e : Expr base_type op t)
    : Expr base_type op t
    := let is_good e' := match option_map (wf_unit (Context:=PContext _) empty) e' with
                         | Some (Some trivial) => true
                         | _ => false
                         end in
       let interp_to_phoas := InterpToPHOAS (Context:=fun var => PContext var)
                                            (fun _ t => Op (OpConst 0%Z) TT) in
       let e' := compile (e _) (DefaultNamesFor e) in
       let e' := option_map (rewrite_expr Pos.eqb) e' in
       let good := is_good e' in
       let e' := match e' with
                 | Some e'
                   => let ls := Named.default_names_for e' in
                      match EliminateDeadCode (Context:=PContext _) e' ls with
                      | Some e'' => Some e''
                      | None => Some e'
                      end
                 | None => None
                 end in
       let good := good && is_good e' in
       if good
       then let e' := option_map interp_to_phoas e' in
            match e' with
            | Some e'
              => match t return Expr _ _ (Arrow (domain t) (codomain t)) -> Expr _ _ t with
                 | Arrow _ _ => fun x => x
                 end e'
            | None => e
            end
       else e.
End language.
