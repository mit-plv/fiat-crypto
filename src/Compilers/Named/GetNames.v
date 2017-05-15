Require Import Coq.Lists.List.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Syntax.

Local Open Scope list_scope.

Section language.
  Context {base_type_code}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {Name : Type}.

  Local Notation exprf := (@exprf base_type_code op Name).
  Local Notation expr := (@expr base_type_code op Name).

  Fixpoint get_names_of_type {t} : interp_flat_type (fun _ : base_type_code => Name) t -> list Name
    := match t with
       | Tbase T => fun n => n::nil
       | Unit => fun _ => nil
       | Prod A B => fun ab : interp_flat_type _ A * interp_flat_type _ B
                     => @get_names_of_type _ (fst ab) ++ @get_names_of_type _ (snd ab)
       end.

  Fixpoint get_namesf {t} (e : exprf t) : list Name
    := match e with
       | TT => nil
       | Var _ x => x::nil
       | Op _ _ opc args => @get_namesf _ args
       | LetIn tx nx ex tC eC
         => get_names_of_type nx ++ (* @get_namesf _ ex ++ *) @get_namesf _ eC
       | Pair _ ex _ ey
         => @get_namesf _ ex ++ @get_namesf _ ey
       end.

  Fixpoint get_names {t} (e : expr t) : list Name
    := match e with
       | Abs _ _ n f => get_names_of_type n ++ get_namesf f
       end.
End language.
