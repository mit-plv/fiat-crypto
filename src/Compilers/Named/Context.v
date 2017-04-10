(** * Contexts for Named Representation of Gallina *)
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Util.Notations.

Record Context {base_type_code} (Name : Type) (var : base_type_code -> Type) :=
  { ContextT : Type;
    lookupb : ContextT -> Name -> forall {t : base_type_code}, option (var t);
    extendb : ContextT -> Name -> forall {t : base_type_code}, var t -> ContextT;
    removeb : ContextT -> Name -> base_type_code -> ContextT;
    empty : ContextT }.
Coercion ContextT : Context >-> Sortclass.
Arguments ContextT {_ _ _ _}, {_ _ _} _.
Arguments lookupb {_ _ _ _} _ _ {_}, {_ _ _ _} _ _ _.
Arguments extendb {_ _ _ _} _ _ [_] _.
Arguments removeb {_ _ _ _} _ _ _.
Arguments empty {_ _ _ _}.

Section language.
  Context {base_type_code : Type}
          {Name : Type}
          {var : base_type_code -> Type}
          {Context : Context Name var}.

  Local Notation flat_type := (flat_type base_type_code).

  Fixpoint extend (ctx : Context) {t : flat_type}
           (n : interp_flat_type (fun _ => Name) t) (v : interp_flat_type var t)
    : Context
    := match t return interp_flat_type (fun _ => Name) t -> interp_flat_type var t -> Context with
       | Tbase t => fun n v => extendb ctx n v
       | Unit => fun _ _ => ctx
       | Prod A B => fun n v
                     => let ctx := @extend ctx A (fst n) (fst v) in
                        let ctx := @extend ctx B (snd n) (snd v) in
                        ctx
       end n v.

  Fixpoint remove (ctx : Context) {t : flat_type}
           (n : interp_flat_type (fun _ => Name) t)
    : Context
    := match t return interp_flat_type (fun _ => Name) t -> Context with
       | Tbase t => fun n => removeb ctx n t
       | Unit => fun _ => ctx
       | Prod A B => fun n
                     => let ctx := @remove ctx A (fst n) in
                        let ctx := @remove ctx B (snd n) in
                        ctx
       end n.

  Definition lookup (ctx : Context) {t}
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

Global Arguments extend {_ _ _ _} ctx {_} _ _.
Global Arguments remove {_ _ _ _} ctx {_} _.
Global Arguments lookup {_ _ _ _} ctx {_} _, {_ _ _ _} ctx _ _.
