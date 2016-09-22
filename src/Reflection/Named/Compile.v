(** * PHOAS → Named Representation of Gallina *)
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.NameUtil.
Require Import Crypto.Reflection.Syntax.

Local Notation eta x := (fst x, snd x).

Local Open Scope ctype_scope.
Local Open Scope nexpr_scope.
Local Open Scope expr_scope.
Section language.
  Context (base_type_code : Type)
          (interp_base_type : base_type_code -> Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (Name : Type).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type := (interp_flat_type_gen interp_base_type).
  Local Notation exprf := (@exprf base_type_code interp_base_type op (fun _ => Name)).
  Local Notation expr := (@expr base_type_code interp_base_type op (fun _ => Name)).
  Local Notation nexprf := (@Named.exprf base_type_code interp_base_type op Name).
  Local Notation nexpr := (@Named.expr base_type_code interp_base_type op Name).

  Fixpoint compilef {t} (e : exprf t) (ls : list Name) {struct e}
    : option (nexprf t)
    := match e in @Syntax.exprf _ _ _ _ t return option (nexprf t) with
       | Const _ x => Some (Named.Const x)
       | Var _ x => Some (Named.Var x)
       | Op _ _ op args => option_map (Named.Op op) (@compilef _ args ls)
       | LetIn tx ex _ eC
         => match @compilef _ ex nil, split_names tx ls with
            | Some x, (Some n, ls')%core
              => option_map (fun C => Named.LetIn tx n x C) (@compilef _ (eC n) ls')
            | _, _ => None
            end
       | Pair _ ex _ ey => match @compilef _ ex nil, @compilef _ ey nil with
                           | Some x, Some y => Some (Named.Pair x y)
                           | _, _ => None
                           end
       end.

  Fixpoint compile {t} (e : expr t) (ls : list Name) {struct e}
    : option (nexpr t)
    := match e in @Syntax.expr _ _ _ _ t return option (nexpr t) with
       | Return _ x => option_map Named.Return (compilef x ls)
       | Abs _ _ f
         => match ls with
            | cons n ls'
              => option_map (Named.Abs n) (@compile _ (f n) ls')
            | _ => None
            end
       end.
End language.

Global Arguments compilef {_ _ _ _ _} e ls.
Global Arguments compile {_ _ _ _ _} e ls.
