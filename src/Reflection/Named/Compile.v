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
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (Name : Type).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op (fun _ => Name)).
  Local Notation expr := (@expr base_type_code op (fun _ => Name)).
  Local Notation nexprf := (@Named.exprf base_type_code op Name).
  Local Notation nexpr := (@Named.expr base_type_code op Name).

  Fixpoint ocompilef {t} (e : exprf t) (ls : list (option Name)) {struct e}
    : option (nexprf t)
    := match e in @Syntax.exprf _ _ _ t return option (nexprf t) with
       | TT => Some Named.TT
       | Var _ x => Some (Named.Var x)
       | Op _ _ op args => option_map (Named.Op op) (@ocompilef _ args ls)
       | LetIn tx ex _ eC
         => match @ocompilef _ ex nil, split_onames tx ls with
            | Some x, (Some n, ls')%core
              => option_map (fun C => Named.LetIn tx n x C) (@ocompilef _ (eC n) ls')
            | _, _ => None
            end
       | Pair _ ex _ ey => match @ocompilef _ ex nil, @ocompilef _ ey nil with
                           | Some x, Some y => Some (Named.Pair x y)
                           | _, _ => None
                           end
       end.

  Definition ocompile {t} (e : expr t) (ls : list (option Name))
    : option (nexpr t)
    := match e in @Syntax.expr _ _ _ t return option (nexpr t) with
       | Abs src _ f
         => match split_onames src ls with
            | (Some n, ls')%core
              => option_map (Named.Abs n) (@ocompilef _ (f n) ls')
            | _ => None
            end
       end.

  Definition compilef {t} (e : exprf t) (ls : list Name) := @ocompilef t e (List.map (@Some _) ls).
  Definition compile {t} (e : expr t) (ls : list Name) := @ocompile t e (List.map (@Some _) ls).
End language.

Global Arguments ocompilef {_ _ _ _} e ls.
Global Arguments ocompile {_ _ _ _} e ls.
Global Arguments compilef {_ _ _ _} e ls.
Global Arguments compile {_ _ _ _} e ls.
