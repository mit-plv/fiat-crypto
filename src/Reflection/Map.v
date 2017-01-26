Require Import Crypto.Reflection.Syntax.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {var1 var2 : base_type_code -> Type}
          (fvar12 : forall t, var1 t -> var2 t)
          (fvar21 : forall t, var2 t -> var1 t).
  Local Notation exprf := (@exprf base_type_code op).
  Fixpoint mapf_interp_flat_type {t} (e : interp_flat_type var2 t) {struct t}
    : interp_flat_type var1 t
    := match t return interp_flat_type _ t -> interp_flat_type _ t with
       | Tbase _ => fvar21 _
       | Unit => fun v : unit => v
       | Prod x y => fun xy => (@mapf_interp_flat_type _ (fst xy),
                                @mapf_interp_flat_type _ (snd xy))
       end e.

  Fixpoint mapf {t} (e : @exprf var1 t) : @exprf var2 t
    := match e in Syntax.exprf _ _ t return exprf t with
       | TT => TT
       | Var _ x => Var (fvar12 _ x)
       | Op _ _ op args => Op op (@mapf _ args)
       | LetIn _ ex _ eC => LetIn (@mapf _ ex) (fun x => @mapf _ (eC (mapf_interp_flat_type x)))
       | Pair _ ex _ ey => Pair (@mapf _ ex) (@mapf _ ey)
       end.
End language.

Global Arguments mapf_interp_flat_type {_ _ _} _ {t} _.
Global Arguments mapf {_ _ _ _} _ _ {t} _.
