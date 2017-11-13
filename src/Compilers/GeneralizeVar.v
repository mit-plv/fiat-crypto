(** * Generalize [var] in [exprf] *)
Require Import Coq.PArith.BinPos.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.InterpretToPHOAS.
Require Import Crypto.Compilers.Named.Compile.
Require Import Crypto.Compilers.Named.PositiveContext.
Require Import Crypto.Compilers.Named.PositiveContext.Defaults.
Require Import Crypto.Compilers.Named.Wf.
Require Import Crypto.Compilers.Syntax.

(** N.B. This procedure only works when there are no nested lets,
    i.e., nothing like [let x := let y := z in w] in the PHOAS syntax
    tree.  This is a limitation of [compile]. *)

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (base_type_code_beq : base_type_code -> base_type_code -> bool)
          (base_type_code_bl_transparent : forall x y, base_type_code_beq x y = true -> x = y)
          (failb : forall var t, @Syntax.exprf base_type_code op var (Tbase t)).

  Local Notation PContext var := (PositiveContext _ var _ base_type_code_bl_transparent).

  Definition GeneralizeVar {t} (e : @Syntax.expr base_type_code op (fun _ => FMapPositive.PositiveMap.key) t)
    : option (@Syntax.Expr base_type_code op (domain t -> codomain t))
    := let e := compile e (default_names_for (fun _ => 1%positive) e) in
       let e := match e with
                | Some e
                  => match wf_unit (Context:=PContext _) empty e with
                     | Some PointedProp.trivial => Some e
                     | Some (PointedProp.inject _) => None
                     | None => None
                     end
                | None => None
                end in
       let e := option_map (InterpToPHOAS (Context:=fun var => PContext var) failb) e in
       e.
End language.
