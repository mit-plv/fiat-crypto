(** * Common Subexpression Elimination for PHOAS Syntax *)
Require Import Coq.Lists.List.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Util.Tactics Crypto.Util.Bool.

Local Open Scope list_scope.

Inductive symbolic_expr {base_type_code op_code} : Type :=
| STT
| SVar   (v : base_type_code) (n : nat)
| SOp    (op : op_code) (args : symbolic_expr)
| SPair  (x y : symbolic_expr)
| SInvalid.
Scheme Equality for symbolic_expr.

Arguments symbolic_expr : clear implicits.

Ltac inversion_symbolic_expr_step :=
  match goal with
  | [ H : SVar _ _ = SVar _ _ |- _ ] => inversion H; clear H
  | [ H : SOp _ _ = SOp _ _ |- _ ] => inversion H; clear H
  | [ H : SPair _ _ = SPair _ _ |- _ ] => inversion H; clear H
  end.
Ltac inversion_symbolic_expr := repeat inversion_symbolic_expr_step.

Local Open Scope ctype_scope.
Section symbolic.
  (** Holds decidably-equal versions of raw expressions, for lookup. *)
  Context (base_type_code : Type)
          (op_code : Type)
          (base_type_code_beq : base_type_code -> base_type_code -> bool)
          (op_code_beq : op_code -> op_code -> bool)
          (base_type_code_bl : forall x y, base_type_code_beq x y = true -> x = y)
          (base_type_code_lb : forall x y, x = y -> base_type_code_beq x y = true)
          (op_code_bl : forall x y, op_code_beq x y = true -> x = y)
          (op_code_lb : forall x y, x = y -> op_code_beq x y = true)
          (interp_base_type : base_type_code -> Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (symbolize_op : forall s d, op s d -> op_code).

  Local Notation symbolic_expr := (symbolic_expr base_type_code op_code).
  Local Notation symbolic_expr_beq := (@symbolic_expr_beq base_type_code op_code base_type_code_beq op_code_beq).
  Local Notation symbolic_expr_lb := (@internal_symbolic_expr_dec_lb base_type_code op_code base_type_code_beq op_code_beq base_type_code_lb op_code_lb).
  Local Notation symbolic_expr_bl := (@internal_symbolic_expr_dec_bl base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op_code_bl).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type_gen := interp_flat_type.
  Local Notation interp_flat_type := (interp_flat_type interp_base_type).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).


  Section with_var.
    Context {var : base_type_code -> Type}.

    Local Notation svar t := (var t * symbolic_expr)%type.
    Local Notation fsvar := (fun t => svar t).
    Local Notation mapping := (forall t : base_type_code, list (svar t))%type.

    Context (prefix : list (sigT (fun t : flat_type => @exprf fsvar t))).

    Definition empty_mapping : mapping := fun _ => nil.
    Definition type_lookup t (xs : mapping) : list (svar t) := xs t.
    Definition mapping_update_type t (xs : mapping) (upd : list (svar t) -> list (svar t))
      : mapping
      := fun t' => (if base_type_code_beq t t' as b return base_type_code_beq t t' = b -> _
                    then fun H => match base_type_code_bl _ _ H in (_ = t') return list (svar t') with
                                  | eq_refl => upd (type_lookup t xs)
                                  end
                    else fun _ => type_lookup t' xs)
                     eq_refl.

    Fixpoint lookup' {t} (sv : symbolic_expr) (xs : list (svar t)) {struct xs} : option (var t) :=
      match xs with
      | nil => None
      | (x, sv') :: xs' =>
        if symbolic_expr_beq sv' sv
        then Some x
        else lookup' sv xs'
      end.
    Definition lookup t (sv : symbolic_expr) (xs : mapping) : option (var t) :=
      lookup' sv (type_lookup t xs).
    Definition symbolicify_var {t : base_type_code} (v : var t) (xs : mapping) : symbolic_expr :=
      SVar t (length (type_lookup t xs)).
    Definition add_mapping {t} (v : var t) (sv : symbolic_expr) (xs : mapping) : mapping :=
      mapping_update_type t xs (fun ls => (v, sv) :: ls).

    Fixpoint symbolize_exprf
             {t} (v : @exprf fsvar t) {struct v}
      : option symbolic_expr
      := match v with
         | TT => Some STT
         | Var _ x => Some (snd x)
         | Op _ _ op args => option_map
                               (fun sargs => SOp (symbolize_op _ _ op) sargs)
                               (@symbolize_exprf _ args)
         | LetIn _ ex _ eC => None
         | Pair _ ex _ ey => match @symbolize_exprf _ ex, @symbolize_exprf _ ey with
                             | Some sx, Some sy => Some (SPair sx sy)
                             | _, _ => None
                             end
         end.

    Fixpoint smart_lookup_gen f (proj : forall t, svar t -> f t)
             (t : flat_type) (sv : symbolic_expr) (xs : mapping) {struct t}
      : option (interp_flat_type_gen f t)
      := match t return option (interp_flat_type_gen f t) with
         | Tbase t => option_map (fun v => proj t (v, sv)) (lookup t sv xs)
         | Unit => Some tt
         | Prod A B => match @smart_lookup_gen f proj A sv xs, @smart_lookup_gen f proj B sv xs with
                       | Some a, Some b => Some (a, b)
                       | _, _ => None
                       end
         end.
    Definition smart_lookup (t : flat_type) (sv : symbolic_expr) (xs : mapping) : option (interp_flat_type_gen fsvar t)
      := @smart_lookup_gen fsvar (fun _ x => x) t sv xs.
    Definition smart_lookupo (t : flat_type) (sv : option symbolic_expr) (xs : mapping) : option (interp_flat_type_gen fsvar t)
      := match sv with
         | Some sv => smart_lookup t sv xs
         | None => None
         end.
    Definition symbolicify_smart_var {t : flat_type} (xs : mapping) (replacement : option symbolic_expr)
      : interp_flat_type_gen var t -> interp_flat_type_gen fsvar t
      := smart_interp_flat_map
           (g:=interp_flat_type_gen fsvar)
           (fun t v => (v,
                        match replacement with
                        | Some sv => sv
                        | None => symbolicify_var v xs
                        end))
           tt
           (fun A B => @pair _ _).
    Fixpoint smart_add_mapping {t : flat_type} (xs : mapping) : interp_flat_type_gen fsvar t -> mapping
      := match t return interp_flat_type_gen fsvar t -> mapping with
         | Tbase t => fun v => add_mapping (fst v) (snd v) xs
         | Unit => fun _ => xs
         | Prod A B
           => fun v => let xs := @smart_add_mapping B xs (snd v) in
                       let xs := @smart_add_mapping A xs (fst v) in
                       xs
         end.

    Definition csef_step
               (csef : forall {t} (v : @exprf fsvar t) (xs : mapping), @exprf var t)
               {t} (v : @exprf fsvar t) (xs : mapping)
      : @exprf var t
      := match v in @Syntax.exprf _ _ _ t return exprf t with
         | LetIn tx ex _ eC => let sx := symbolize_exprf ex in
                             let ex' := @csef _ ex xs in
                             let sv := smart_lookupo tx sx xs in
                             match sv with
                             | Some v => @csef _ (eC v) xs
                             | None
                               => LetIn ex' (fun x => let x' := symbolicify_smart_var xs sx x in
                                                    @csef _ (eC x') (smart_add_mapping xs x'))
                             end
         | TT => TT
         | Var _ x => Var (fst x)
         | Op _ _ op args => Op op (@csef _ args xs)
         | Pair _ ex _ ey => Pair (@csef _ ex xs) (@csef _ ey xs)
         end.

    Fixpoint csef {t} (v : @exprf fsvar t) (xs : mapping)
      := @csef_step (@csef) t v xs.

    Fixpoint prepend_prefix {t} (e : @exprf fsvar t) (ls : list (sigT (fun t : flat_type => @exprf fsvar t)))
      : @exprf fsvar t
      := match ls with
         | nil => e
         | x :: xs => LetIn (projT2 x) (fun _ => @prepend_prefix _ e xs)
         end.

    Definition cse {t} (v : @expr fsvar t) (xs : mapping) : @expr var t
      := match v in @Syntax.expr _ _ _ t return expr t with
         | Abs _ _ f => Abs (fun x => let x' := symbolicify_smart_var xs None x in
                                      csef (prepend_prefix (f x') prefix) (smart_add_mapping xs x'))
         end.
  End with_var.

  Definition CSE {t} (e : Expr t) (prefix : forall var, list (sigT (fun t : flat_type => @exprf var t)))
    : Expr t
    := fun var => cse (prefix _) (e _) empty_mapping.
End symbolic.

Global Arguments csef {_} op_code base_type_code_beq op_code_beq base_type_code_bl {_} symbolize_op {var t} _ _.
Global Arguments cse {_} op_code base_type_code_beq op_code_beq base_type_code_bl {_} symbolize_op {var} prefix {t} _ _.
Global Arguments CSE {_} op_code base_type_code_beq op_code_beq base_type_code_bl {_} symbolize_op {t} e prefix var.
