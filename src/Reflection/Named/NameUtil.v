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
      : option (interp_flat_type_gen (fun _ => Name) t) * list MName
      := match t return option (@interp_flat_type_gen base_type_code (fun _ => Name) t) * _ with
         | Syntax.Tbase _
           => match ls with
              | cons n ls'
                => match force n with
                   | Some n => (Some n, ls')
                   | None => (None, ls')
                   end
              | nil => (None, nil)
              end
         | Prod A B
           => let '(a, ls) := eta (@split_mnames A ls) in
              let '(b, ls) := eta (@split_mnames B ls) in
              (match a, b with
               | Some a', Some b' => Some (a', b')
               | _, _ => None
               end,
               ls)
         end.
  End monad.
  Definition split_onames := @split_mnames (option Name) (fun x => x).
  Definition split_names := @split_mnames Name (@Some _).
End language.

Global Arguments split_mnames {_ _ MName} force _ _, {_ _} MName force _ _.
Global Arguments split_onames {_ _} _ _.
Global Arguments split_names {_ _} _ _.
