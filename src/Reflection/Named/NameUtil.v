Require Import Coq.Lists.List.
Require Import Crypto.Reflection.Syntax.

Local Open Scope core_scope.
Local Notation eta x := (fst x, snd x).

Section language.
  Context {base_type_code : Type}
          {Name : Type}.

  Section monad.
    Context (MName : Type) (force : MName -> option Name).
    Fixpoint split_mnames
             (t : flat_type base_type_code) (ls : list MName)
      : option (interp_flat_type (fun _ => Name) t) * list MName
      := match t return option (@interp_flat_type base_type_code (fun _ => Name) t) * _ with
         | Tbase _
           => match ls with
              | cons n ls'
                => match force n with
                   | Some n => (Some n, ls')
                   | None => (None, ls')
                   end
              | nil => (None, nil)
              end
         | Unit => (Some tt, ls)
         | Prod A B
           => let '(a, ls) := eta (@split_mnames A ls) in
              let '(b, ls) := eta (@split_mnames B ls) in
              (match a, b with
               | Some a', Some b' => Some (a', b')
               | _, _ => None
               end,
               ls)
         end.
    Definition mname_list_unique (ls : list MName) : Prop
      := forall k n,
        List.In (Some n) (firstn k (List.map force ls))
        -> List.In (Some n) (skipn k (List.map force ls))
        -> False.
  End monad.
  Definition split_onames := @split_mnames (option Name) (fun x => x).
  Definition split_names := @split_mnames Name (@Some _).

  Definition oname_list_unique (ls : list (option Name)) : Prop
    := mname_list_unique (option Name) (fun x => x) ls.
  Definition name_list_unique (ls : list Name) : Prop
    := mname_list_unique Name (@Some _) ls.
End language.

Global Arguments split_mnames {_ _ MName} force _ _, {_ _} MName force _ _.
Global Arguments split_onames {_ _} _ _.
Global Arguments split_names {_ _} _ _.
Global Arguments mname_list_unique {_ MName} force ls, {_} MName force ls.
Global Arguments oname_list_unique {_} ls.
Global Arguments name_list_unique {_} ls.
