(** * Common Subexpression Elimination for PHOAS Syntax *)
Require Import Coq.Lists.List.
Require Import Coq.FSets.FMapInterface.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Equality.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.AListContext.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Decidable.

Local Open Scope list_scope.

Inductive symbolic_expr {base_type_code op_code} : Type :=
| STT
| SVar  (n : nat)
| SOp   (argT : flat_type base_type_code) (op : op_code) (args : symbolic_expr)
| SPair (x y : symbolic_expr)
| SFst  (A B : flat_type base_type_code) (x : symbolic_expr)
| SSnd  (A B : flat_type base_type_code) (x : symbolic_expr)
| SInvalid.
Scheme Equality for symbolic_expr.

Arguments symbolic_expr : clear implicits.

Global Instance symbolic_expr_dec {base_type_code op_code}
       `{DecidableRel (@eq base_type_code), DecidableRel (@eq op_code)}
  : DecidableRel (@eq (symbolic_expr base_type_code op_code)).
Proof.
  unfold Decidable in *; intros; repeat decide equality.
Defined.

Ltac inversion_symbolic_expr_step :=
  match goal with
  | [ H : SVar _ = SVar _ |- _ ] => inversion H; clear H
  | [ H : SOp _ _ _ = SOp _ _ _ |- _ ] => inversion H; clear H
  | [ H : SPair _ _ = SPair _ _ |- _ ] => inversion H; clear H
  | [ H : SFst _ _ _ = SFst _ _ _ |- _ ] => inversion H; clear H
  | [ H : SSnd _ _ _ = SSnd _ _ _ |- _ ] => inversion H; clear H
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
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (symbolize_op : forall s d, op s d -> op_code)
          (op_code_leb : op_code -> op_code -> bool)
          (base_type_leb : base_type_code -> base_type_code -> bool).
  Local Notation symbolic_expr := (symbolic_expr base_type_code op_code).
  Context (normalize_symbolic_op_arguments : op_code -> symbolic_expr -> symbolic_expr)
          (inline_symbolic_expr_in_lookup : bool).

  Local Notation symbolic_expr_beq := (@symbolic_expr_beq base_type_code op_code base_type_code_beq op_code_beq).
  Local Notation symbolic_expr_lb := (@internal_symbolic_expr_dec_lb base_type_code op_code base_type_code_beq op_code_beq base_type_code_lb op_code_lb).
  Local Notation symbolic_expr_bl := (@internal_symbolic_expr_dec_bl base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op_code_bl).

  Local Notation flat_type_beq := (@flat_type_beq base_type_code base_type_code_beq).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Definition SymbolicExprContext {var : flat_type -> Type}
    : Context symbolic_expr var
    := @AListContext symbolic_expr symbolic_expr_beq _ var flat_type_beq (@flat_type_dec_bl _ _ base_type_code_bl).

  Local Instance SymbolicExprContextOk {var} : ContextOk (@SymbolicExprContext var)
    := @AListContextOk
         symbolic_expr symbolic_expr_beq symbolic_expr_bl symbolic_expr_lb
         _ _ _ _ (@flat_type_dec_lb _ _ base_type_code_lb).

  Fixpoint push_pair_symbolic_expr {t : flat_type} (s : symbolic_expr)
    : interp_flat_type (fun _ => symbolic_expr) t
    := match t with
       | Unit => tt
       | Tbase T => s
       | Prod A B
         => (@push_pair_symbolic_expr A (SFst A B s), @push_pair_symbolic_expr B (SSnd A B s))
       end.

  Section with_var0.
    Context {var : base_type_code -> Type}.

    Fixpoint prepend_prefix {t} (e : @exprf var t) (ls : list (sigT (fun t : flat_type => @exprf var t)))
      : @exprf var t
      := match ls with
         | nil => e
         | x :: xs => LetIn (projT2 x) (fun _ => @prepend_prefix _ e xs)
         end.
  End with_var0.

  Local Notation op_code_eqb argT1 argT2 op1 op2
    := (flat_type_beq _ base_type_code_beq argT1 argT2 && op_code_beq op1 op2).
  Local Notation ltb_of_leb leb eqb
    := (leb && negb eqb).
  Local Notation leb_pair leb1 eqb1 leb2
    := (ltb_of_leb leb1 eqb1 || (eqb1 && leb2)).
  Local Notation op_code_ltb op1 op2
    := (ltb_of_leb (op_code_leb op1 op2)
                   (op_code_beq op1 op2)).

  Fixpoint flat_type_leb (x y : flat_type) : bool
    := match x, y with
       | Unit, _ => true
       | _, Unit => false
       | Tbase x, Tbase y => base_type_leb x y
       | Tbase _, _ => true
       | _, Tbase _ => false
       | Prod A1 B1, Prod A2 B2
         => leb_pair (flat_type_leb A1 A2)
                     (flat_type_beq A1 A2)
                     (flat_type_leb B1 B2)
       end.

  Fixpoint symbolic_expr_leb (x y : symbolic_expr) : bool
    := match x, y with
       | STT, _ => true
       | _, STT => false
       | SVar n1, SVar n2 => Nat.leb n1 n2
       | SVar _, _ => true
       | _, SVar _ => false
       | SOp argT1 op1 args1, SOp argT2 op2 args2
         => leb_pair (leb_pair (op_code_leb op1 op2)
                               (op_code_beq op1 op2)
                               (flat_type_leb argT1 argT2))
                     (op_code_beq op1 op2 && flat_type_beq argT1 argT2)
                     (symbolic_expr_leb args1 args2)
       | SOp _ _ _, _ => true
       | _, SOp _ _ _ => false
       | SPair x1 y1, SPair x2 y2
         => leb_pair (symbolic_expr_leb x1 x2)
                     (symbolic_expr_beq x1 x2)
                     (symbolic_expr_leb y1 y2)
       | SPair _ _, _ => true
       | _, SPair _ _ => false
       | SFst A B x, SFst A' B' y
         => leb_pair (flat_type_leb (Prod A B) (Prod A' B'))
                     (flat_type_beq (Prod A B) (Prod A' B'))
                     (symbolic_expr_leb x y)
       | SFst _ _ _, _ => true
       | _, SFst _ _ _ => false
       | SSnd A B x, SSnd A' B' y
         => leb_pair (flat_type_leb (Prod A B) (Prod A' B'))
                     (flat_type_beq (Prod A B) (Prod A' B'))
                     (symbolic_expr_leb x y)
       | SSnd _ _ _, _ => true
       | _, SSnd _ _ _ => false
       | SInvalid, _ => true
       end.
  Definition symbolic_expr_ltb x y
    := ltb_of_leb (symbolic_expr_leb x y) (symbolic_expr_beq x y).

  Fixpoint symbolic_expr_normalize (x : symbolic_expr) : symbolic_expr
    := match x with
       | STT => STT
       | SVar n => SVar n
       | SOp argT op args
         => SOp argT op (normalize_symbolic_op_arguments op args)
       | SPair x y
         => SPair (symbolic_expr_normalize x) (symbolic_expr_normalize y)
       | SFst A B x => SFst A B (symbolic_expr_normalize x)
       | SSnd A B x => SFst A B (symbolic_expr_normalize x)
       | SInvalid => SInvalid
       end.

  Section with_var.
    Context {var : base_type_code -> Type}.

    Local Notation svar t := (var t * symbolic_expr)%type.
    Local Notation fsvar := (fun t => svar t).
    Local Notation mapping := (@SymbolicExprContext (interp_flat_type var)).

    Context (prefix : list (sigT (fun t : flat_type => @exprf fsvar t))).

    Definition symbolize_var (xs : mapping) (t : flat_type) : symbolic_expr :=
      SVar (length xs).

    Fixpoint symbolize_exprf
             {t} (v : @exprf fsvar t) {struct v}
      : option symbolic_expr
      := match v with
         | TT => Some STT
         | Var _ x => Some (snd x)
         | Op argsT _ op args => option_map
                                   (fun sargs => SOp argsT (symbolize_op _ _ op) sargs)
                                   (@symbolize_exprf _ args)
         | LetIn _ ex _ eC => None
         | Pair _ ex _ ey => match @symbolize_exprf _ ex, @symbolize_exprf _ ey with
                             | Some sx, Some sy => Some (SPair sx sy)
                             | _, _ => None
                             end
         end.

    Definition norm_symbolize_exprf {t} v : option symbolic_expr
      := option_map symbolic_expr_normalize (@symbolize_exprf t v).

    Definition symbolicify_smart_var {t : flat_type}
               (vs : interp_flat_type var t)
               (ss : symbolic_expr)
      : interp_flat_type fsvar t
      := SmartVarfMap2 (fun t v s => (v, s)) vs (push_pair_symbolic_expr ss).

    Definition csef_step
               (csef : forall {t} (v : @exprf fsvar t) (xs : mapping), @exprf var t)
               {t} (v : @exprf fsvar t) (xs : mapping)
      : @exprf var t
      := match v in @Syntax.exprf _ _ _ t return exprf t with
         | LetIn tx ex _ eC
           => let sx := norm_symbolize_exprf ex in
              let ex' := @csef _ ex xs in
              let '(sx, sv) := match sx with
                               | Some sx => (sx, lookupb xs sx)
                               | None => (symbolize_var xs tx, None)
                               end in
              let reduced_sx := if inline_symbolic_expr_in_lookup then sx else symbolize_var xs tx in
              match sv with
              | Some v => @csef _ (eC (symbolicify_smart_var v reduced_sx)) (extendb xs reduced_sx v)
              | None
                => LetIn ex' (fun x => let sx' := symbolicify_smart_var x reduced_sx in
                                       @csef _ (eC sx') (extendb (extendb xs sx x) reduced_sx x))
              end
         | TT => TT
         | Var _ x => Var (fst x)
         | Op _ _ op args => Op op (@csef _ args xs)
         | Pair _ ex _ ey => Pair (@csef _ ex xs) (@csef _ ey xs)
         end.

    Fixpoint csef {t} (v : @exprf fsvar t) (xs : mapping)
      := @csef_step (@csef) t v xs.

    Definition cse {t} (v : @expr fsvar t) (xs : mapping) : @expr var t
      := match v in @Syntax.expr _ _ _ t return expr t with
         | Abs src dst f
           => let sx := symbolize_var xs src in
              Abs (fun x => let x' := symbolicify_smart_var x sx in
                            csef (prepend_prefix (f x') prefix) (extendb xs sx x))
         end.
  End with_var.

  Definition CSE {t} (e : Expr t) (prefix : forall var, list (sigT (fun t : flat_type => @exprf var t)))
    : Expr t
    := fun var => cse (prefix _) (e _) empty.
End symbolic.

Global Arguments csef {_} op_code base_type_code_beq op_code_beq base_type_code_bl {_} symbolize_op normalize_symbolic_op_arguments inline_symbolic_expr_in_lookup {var t} _ _.
Global Arguments cse {_} op_code base_type_code_beq op_code_beq base_type_code_bl {_} symbolize_op normalize_symbolic_op_arguments inline_symbolic_expr_in_lookup {var} prefix {t} _ _.
Global Arguments CSE {_} op_code base_type_code_beq op_code_beq base_type_code_bl {_} symbolize_op normalize_symbolic_op_arguments inline_symbolic_expr_in_lookup {t} e prefix var.
