Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
  Local Notation Expr := (@Expr base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation exprf := (@exprf base_type_code op).

  Section with_var.
    Context {var : base_type_code -> Type}.

    Fixpoint strip_exprf {T} (e : @exprf (fun t => @exprf var (Tbase t)) T)
      : @exprf var T
      := match e with
         | TT => TT
         | Var t v
           => v
         | Op src dst opv args
           => Op opv (strip_exprf args)
         | LetIn tx ex tC eC
           => LetIn (strip_exprf ex)
                    (fun v => strip_exprf (eC (SmartVarVarf v)))
         | Pair tx ex ty ey
           => Pair (strip_exprf ex) (strip_exprf ey)
         end.

    Definition strip_expr {T} (e : @expr (fun t => @exprf var (Tbase t)) T)
      : @expr var T
      := match e with
         | Abs src dst f => Abs (fun x => strip_exprf (f (SmartVarVarf x)))
         end.
  End with_var.
End language.
