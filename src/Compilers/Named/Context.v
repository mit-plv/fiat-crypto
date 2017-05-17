(** * Contexts for Named Representation of Gallina *)
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Util.Notations.

Record Context {base_type_code} (Name : Type) (var : base_type_code -> Type) :=
  { ContextT : Type;
    lookupb : forall {t : base_type_code}, ContextT -> Name -> option (var t);
    extendb : forall {t : base_type_code}, ContextT -> Name -> var t -> ContextT;
    removeb : base_type_code -> ContextT -> Name -> ContextT;
    empty : ContextT }.
Coercion ContextT : Context >-> Sortclass.
Arguments ContextT {_ _ _ _}, {_ _ _} _.
Arguments lookupb {_ _ _ _ _} _ _, {_ _ _ _} _ _ _.
Arguments extendb {_ _ _ _} [_] _ _ _.
Arguments removeb {_ _ _ _} _ _ _.
Arguments empty {_ _ _ _}.

Section language.
  Context {base_type_code : Type}
          {Name : Type}
          {var : base_type_code -> Type}
          {Context : Context Name var}.

  Local Notation flat_type := (flat_type base_type_code).

  Fixpoint extend {t : flat_type} (ctx : Context)
           (n : interp_flat_type (fun _ => Name) t) (v : interp_flat_type var t)
    : Context
    := match t return interp_flat_type (fun _ => Name) t -> interp_flat_type var t -> Context with
       | Tbase t => fun n v => extendb ctx n v
       | Unit => fun _ _ => ctx
       | Prod A B => fun n v
                     => let ctx := @extend A ctx (fst n) (fst v) in
                        let ctx := @extend B ctx (snd n) (snd v) in
                        ctx
       end n v.

  Fixpoint remove {t : flat_type} (ctx : Context)
           (n : interp_flat_type (fun _ => Name) t)
    : Context
    := match t return interp_flat_type (fun _ => Name) t -> Context with
       | Tbase t => fun n => removeb t ctx n
       | Unit => fun _ => ctx
       | Prod A B => fun n
                     => let ctx := @remove A ctx (fst n) in
                        let ctx := @remove B ctx (snd n) in
                        ctx
       end n.

  Definition lookup {t} (ctx : Context)
    : interp_flat_type (fun _ => Name) t -> option (interp_flat_type var t)
    := smart_interp_flat_map
         (g := fun t => option (interp_flat_type var t))
         (fun t v => lookupb ctx v)
         (Some tt)
         (fun A B x y => match x, y with
                         | Some x', Some y' => Some (x', y')%core
                         | _, _ => None
                         end).
End language.

Global Arguments extend {_ _ _ _} {_} ctx _ _.
Global Arguments remove {_ _ _ _} {_} ctx _.
Global Arguments lookup {_ _ _ _} {_} ctx _, {_ _ _ _} _ ctx _.
