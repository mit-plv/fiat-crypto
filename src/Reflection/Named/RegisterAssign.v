(** * Reassign registers *)
Require Import Coq.FSets.FMapPositive Coq.PArith.BinPos.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.NameUtil.
Require Import Crypto.Util.Decidable.

Local Notation eta x := (fst x, snd x).

Local Open Scope ctype_scope.
Delimit Scope nexpr_scope with nexpr.
Section language.
  Context (base_type_code : Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).

  Section internal.
    Context (InName OutName : Type)
            {InContext : Context InName (fun _ : base_type_code => OutName)}
            {ReverseContext : Context OutName (fun _ : base_type_code => InName)}
            (InName_beq : InName -> InName -> bool).

    Definition register_reassignf_step
               (register_reassignf : forall (ctxi : InContext) (ctxr : ReverseContext)
                                            {t} (e : exprf InName t) (new_names : list (option OutName)),
                   option (exprf OutName t))
               (ctxi : InContext) (ctxr : ReverseContext)
               {t} (e : exprf InName t) (new_names : list (option OutName))
      : option (exprf OutName t)
      := match e in Named.exprf _ _ _ t return option (exprf _ t) with
         | TT => Some TT
         | Var t' name => match lookupb ctxi name t' with
                          | Some new_name
                            => match lookupb ctxr new_name t' with
                               | Some name'
                                 => if InName_beq name name'
                                    then Some (Var new_name)
                                    else None
                               | None => None
                               end
                          | None => None
                          end
         | Op _ _ op args
           => option_map (Op op) (@register_reassignf ctxi ctxr _ args new_names)
         | LetIn tx n ex _ eC
           => let '(n', new_names') := eta (split_onames tx new_names) in
              match n', @register_reassignf ctxi ctxr _ ex nil with
              | Some n', Some x
                => let ctxi := extend ctxi n n' in
                   let ctxr := extend ctxr n' n in
                   option_map (LetIn tx n' x) (@register_reassignf ctxi ctxr _ eC new_names')
              | _, _
                => let ctxi := remove ctxi n in
                   @register_reassignf ctxi ctxr _ eC new_names'
              end
         | Pair _ ex _ ey
           => match @register_reassignf ctxi ctxr _ ex nil, @register_reassignf ctxi ctxr _ ey nil with
              | Some x, Some y
                => Some (Pair x y)
              | _, _ => None
              end
         end.
    Fixpoint register_reassignf ctxi ctxr {t} e new_names
      := @register_reassignf_step (@register_reassignf) ctxi ctxr t e new_names.

    Definition register_reassign (ctxi : InContext) (ctxr : ReverseContext)
             {t} (e : expr InName t) (new_names : list (option OutName))
      : option (expr OutName t)
      := match e in Named.expr _ _ _ t return option (expr _ t) with
         | Abs src _ n f
           => let '(n', new_names') := eta (split_onames src new_names) in
              match n' with
              | Some n'
                => let ctxi := extend (t:=src) ctxi n n' in
                   let ctxr := extend (t:=src) ctxr n' n in
                   option_map (Abs n') (register_reassignf ctxi ctxr f new_names')
              | None => None
              end
         end.
  End internal.

  Section context_pos.
    Global Instance pos_context {decR : DecidableRel (@eq base_type_code)}
           (var : base_type_code -> Type) : Context positive var
      := { ContextT := PositiveMap.t { t : _ & var t };
           lookupb ctx key t := match PositiveMap.find key ctx with
                                | Some v => match dec (projT1 v = t) with
                                            | left pf => Some match pf in (_ = t) return var t with
                                                              | eq_refl => projT2 v
                                                              end
                                            | right _ => None
                                            end
                                | None => None
                                end;
           extendb ctx key t v := PositiveMap.add key (existT _ t v) ctx;
           removeb ctx key t := if dec (option_map (@projT1 _ _) (PositiveMap.find key ctx) = Some t)
                                then PositiveMap.remove key ctx
                                else ctx;
           empty := PositiveMap.empty _ }.
    Global Instance pos_context_nd
           (var : Type)
      : Context positive (fun _ : base_type_code => var)
      := { ContextT := PositiveMap.t var;
           lookupb ctx key t := PositiveMap.find key ctx;
           extendb ctx key t v := PositiveMap.add key v ctx;
           removeb ctx key t := PositiveMap.remove key ctx;
           empty := PositiveMap.empty _ }.
  End context_pos.
End language.

Global Arguments pos_context {_ _} var.
Global Arguments pos_context_nd : clear implicits.
Global Arguments register_reassign {_ _ _ _ _ _} _ ctxi ctxr {t} e _.
Global Arguments register_reassignf {_ _ _ _ _ _} _ ctxi ctxr {t} e _.
