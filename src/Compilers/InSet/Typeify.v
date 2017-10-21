Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.InSet.Syntax.

Section language.
  Context {base_type_code : Set}
          {op : flat_type base_type_code -> flat_type base_type_code -> Set}
          {var : base_type_code -> Set}.

  Fixpoint typeify_interp_flat_type {t}
    : InSet.Syntax.interp_flat_type var t -> Compilers.Syntax.interp_flat_type var t
    := match t with
       | Tbase T => fun v => v
       | Unit => fun v => v
       | Prod A B => fun ab : InSet.Syntax.interp_flat_type _ A * InSet.Syntax.interp_flat_type _ B
                     => (@typeify_interp_flat_type _ (fst ab),
                         @typeify_interp_flat_type _ (snd ab))
       end.
  Fixpoint untypeify_interp_flat_type {t}
    : Compilers.Syntax.interp_flat_type var t -> InSet.Syntax.interp_flat_type var t
    := match t with
       | Tbase T => fun v => v
       | Unit => fun v => v
       | Prod A B => fun ab : Compilers.Syntax.interp_flat_type _ A * Compilers.Syntax.interp_flat_type _ B
                     => (@untypeify_interp_flat_type _ (fst ab),
                         @untypeify_interp_flat_type _ (snd ab))
       end.

  Fixpoint typeify {t} (e : @InSet.Syntax.exprf base_type_code op var t)
    : @Compilers.Syntax.exprf base_type_code op var t
    := match e with
       | TT => Compilers.Syntax.TT
       | Var t v => Compilers.Syntax.Var v
       | Op t1 tR opc args => Compilers.Syntax.Op opc (@typeify _ args)
       | LetIn tx ex tC eC
         => Compilers.Syntax.LetIn
              (@typeify _ ex)
              (fun x => @typeify _ (eC (untypeify_interp_flat_type x)))
       | Pair tx ex ty ey => Compilers.Syntax.Pair
                               (@typeify _ ex)
                               (@typeify _ ey)
       end.

  Fixpoint untypeify {t} (e : @Compilers.Syntax.exprf base_type_code op var t)
    : @InSet.Syntax.exprf base_type_code op var t
    := match e with
       | Compilers.Syntax.TT => TT
       | Compilers.Syntax.Var t v => Var v
       | Compilers.Syntax.Op t1 tR opc args => Op opc (@untypeify _ args)
       | Compilers.Syntax.LetIn tx ex tC eC
         => LetIn
              (@untypeify _ ex)
              (fun x => @untypeify _ (eC (typeify_interp_flat_type x)))
       | Compilers.Syntax.Pair tx ex ty ey
         => Pair
              (@untypeify _ ex)
              (@untypeify _ ey)
       end.
End language.
