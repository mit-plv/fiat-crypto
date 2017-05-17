Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.Wf.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Util.PointedProp.

Local Notation eta_and x := (conj (let (a, b) := x in a) (let (a, b) := x in b)).

Module Export Named.
  Section language.
    Context {base_type_code : Type}
            {op : flat_type base_type_code -> flat_type base_type_code -> Type}
            {Name : Type}.
    Section with_var.
      Context {var : base_type_code -> Type}
              {Context : Context Name var}
              (failb : forall t, @Syntax.exprf base_type_code op var (Tbase t)).

      Local Notation failf t (* : @Syntax.exprf base_type_code op var t*)
        := (SmartPairf (SmartValf _ failb t)).

      Fixpoint interpf_to_phoas
               (ctx : Context)
               {t} (e : @Named.exprf base_type_code op Name t)
               {struct e}
        : @Syntax.exprf base_type_code op var t
        := match e in Named.exprf _ _ _ t return @Syntax.exprf base_type_code op var t with
           | Named.Var t' x
             => match lookupb t' ctx x with
                | Some v => Var v
                | None => failf _
                end
           | Named.TT => TT
           | Named.Pair tx ex ty ey
             => Pair (@interpf_to_phoas ctx tx ex) (@interpf_to_phoas ctx ty ey)
           | Named.Op _ _ opc args
             => Op opc (@interpf_to_phoas ctx _ args)
           | Named.LetIn _ n ex _ eC
             => LetIn (@interpf_to_phoas ctx _ ex)
                      (fun v
                       => @interpf_to_phoas (extend ctx n v) _ eC)
           end.

      Definition interp_to_phoas
                 (ctx : Context)
                 {t} (e : @Named.expr base_type_code op Name t)
        : @Syntax.expr base_type_code op var (domain t -> codomain t)
        := Abs (fun v => interpf_to_phoas (extend ctx (Abs_name e) v) (invert_Abs e)).
    End with_var.

    Section all.
      Context {Context : forall var, @Context base_type_code Name var}
              (failb : forall var t, @Syntax.exprf base_type_code op var (Tbase t)).
      Definition InterpToPHOAS_gen
                 (ctx : forall var, Context var)
                 {t} (e : @Named.expr base_type_code op Name t)
        : @Syntax.Expr base_type_code op (domain t -> codomain t)
        := fun var => interp_to_phoas (failb var) (ctx var) e.

      Definition InterpToPHOAS {t} e
        := @InterpToPHOAS_gen (fun var => empty) t e.
    End all.
  End language.
End Named.
