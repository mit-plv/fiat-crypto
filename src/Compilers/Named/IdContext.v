Require Import Coq.Lists.List.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.

Section language.
  Context {base_type_code Name}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (Context : @Context base_type_code Name (fun _ => Name)).

  Fixpoint collect_binders {t} (e : Named.exprf base_type_code op Name t)
    : list { t : flat_type base_type_code & interp_flat_type (fun _ => Name) t }
    := match e with
       | TT => nil
       | Var t n => (existT _ (Tbase t) n) :: nil
       | Op t1 tR opc args => @collect_binders _ args
       | LetIn tx n ex tC eC
         => (existT _ tx n) :: @collect_binders tx ex ++ @collect_binders tC eC
       | Pair tx ex ty ey
         => @collect_binders tx ex ++ @collect_binders ty ey
       end%list.
  Definition idcontext {t} (e : Named.exprf base_type_code op Name t) : Context
    := List.fold_right
         (fun v ctx => extend ctx (projT2 v) (projT2 v))
         empty
         (collect_binders e).
End language.
