(** * Counts how many binders there are *)
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.CountLets.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.SmartMap.

Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {Name : Type}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).

  Local Notation count_pairs := (@count_pairs base_type_code).

  Local Notation exprf := (@Named.exprf base_type_code op Name).
  Local Notation expr := (@Named.expr base_type_code op Name).

  Section gen.
    Context (count_type_let : flat_type -> nat).
    Context (count_type_abs : flat_type -> nat).

    Fixpoint count_lets_genf {t} (e : exprf t) : nat
      := match e with
         | LetIn tx _ _ _ eC
           => count_type_let tx + @count_lets_genf _ eC
         | Op _ _ _ e => @count_lets_genf _ e
         | Pair _ ex _ ey => @count_lets_genf _ ex + @count_lets_genf _ ey
         | _ => 0
         end.
    Definition count_lets_gen {t} (e : expr t) : nat
      := match e with
         | Abs tx _ _ f => count_type_abs tx + @count_lets_genf _ f
         end.
  End gen.

  Definition count_let_bindersf {t} (e : exprf t) : nat
    := count_lets_genf count_pairs e.
  Definition count_letsf {t} (e : exprf t) : nat
    := count_lets_genf (fun _ => 1) e.
  Definition count_let_binders {t} (e : expr t) : nat
    := count_lets_gen count_pairs (fun _ => 0) e.
  Definition count_lets {t} (e : expr t) : nat
    := count_lets_gen (fun _ => 1) (fun _ => 0) e.
  Definition count_binders {t} (e : expr t) : nat
    := count_lets_gen count_pairs count_pairs e.
End language.
