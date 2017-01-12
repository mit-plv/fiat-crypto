(** * Computes a list of live variables *)
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Named.NameUtil.
Require Import Crypto.Reflection.CountLets.
Require Import Crypto.Util.ListUtil.

Local Notation eta x := (fst x, snd x).

Local Open Scope ctype_scope.
Section language.
  Context (base_type_code : Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (Name : Type)
          (dead_name : Name)
          (merge_names : Name -> Name -> Name)
          (* equations:
             - [merge_names x dead_name = merge_names dead_name x = x]
             - [merge_names x x = x] *).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation var := (fun t : base_type_code => list Name).
  Local Notation exprf := (@exprf base_type_code op var).
  Local Notation expr := (@expr base_type_code op var).
  Local Notation Expr := (@Expr base_type_code op var).

  Fixpoint merge_name_lists (ls1 ls2 : list Name) : list Name :=
    match ls1, ls2 with
    | cons x xs, cons y ys => cons (merge_names x y) (merge_name_lists xs ys)
    | ls1, nil => ls1
    | nil, ls2 => ls2
    end.

  Definition names_to_list {t} : interp_flat_type (fun _ : base_type_code => Name) t -> list Name
    := smart_interp_flat_map (g:=fun _ => list Name) (fun _ x => x :: nil)%list nil (fun _ _ x y => x ++ y)%list.

  Fixpoint filter_live_namesf (prefix remaining : list Name) {t} (e : exprf t) : list Name
    := match e with
       | TT => prefix
       | Var _ x => x
       | Op _ _ op args => @filter_live_namesf prefix remaining _ args
       | LetIn tx ex _ eC
         => let namesx := @filter_live_namesf prefix nil _ ex in
            let '(ns, remaining') := eta (split_names tx remaining) in
            match ns with
            | Some n =>
              @filter_live_namesf
                (prefix ++ repeat dead_name (count_pairs tx))%list remaining' _
                (eC (SmartValf (fun _ => list Name) (fun _ => namesx ++ names_to_list n)%list _))
            | None => nil
            end
       | Pair _ ex _ ey => merge_name_lists (@filter_live_namesf prefix remaining _ ex)
                                            (@filter_live_namesf prefix remaining _ ey)
       end.

  Definition filter_live_names (prefix remaining : list Name) {t} (e : expr t) : list Name
    := match e with
       | Abs src _ ef
         => let '(ns, remaining') := eta (split_names src remaining) in
            match ns with
            | Some n =>
              let prefix' := (prefix ++ names_to_list n)%list in
              filter_live_namesf
                prefix' remaining'
                (ef (SmartValf _ (fun _ => prefix') src))
            | None => nil
            end
       end.
End language.
