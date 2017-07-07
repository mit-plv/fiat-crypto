(** * Common Subexpression Elimination for PHOAS Syntax *)
Require Import Coq.Lists.List.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.AListContext.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Equality.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.CommonSubexpressionElimination.

Section symbolic.
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
          (denote_op : forall s d, op_code -> option (op s d))
          (denote_symbolize_op : forall s d opc, denote_op s d (symbolize_op s d opc) = Some opc).

  Local Notation symbolic_expr := (symbolic_expr base_type_code op_code).
  Local Notation symbolic_expr_beq := (@symbolic_expr_beq base_type_code op_code base_type_code_beq op_code_beq).
  Local Notation symbolic_expr_lb := (@internal_symbolic_expr_dec_lb base_type_code op_code base_type_code_beq op_code_beq base_type_code_lb op_code_lb).
  Local Notation symbolic_expr_bl := (@internal_symbolic_expr_dec_bl base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op_code_bl).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Local Notation flat_type_beq := (@flat_type_beq base_type_code base_type_code_beq).
  Local Notation flat_type_dec_bl := (@flat_type_dec_bl base_type_code base_type_code_beq base_type_code_bl).

  Local Notation symbolicify_smart_var := (@symbolicify_smart_var base_type_code op_code).
  Local Notation symbolize_exprf := (@symbolize_exprf base_type_code op_code op symbolize_op).
  Local Notation csef := (@csef base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op).
  Local Notation cse := (@cse base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op).
  Local Notation CSE := (@CSE base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op).
  Local Notation SymbolicExprContext := (@SymbolicExprContext base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl).
  Local Notation SymbolicExprContextOk := (@SymbolicExprContextOk base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl base_type_code_lb op_code_bl op_code_lb).
  Local Notation prepend_prefix := (@prepend_prefix base_type_code op).

  Section with_var.
    Context {interp_base_type : base_type_code -> Type}
            {interp_op : forall s d, op s d -> interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d}
            (m : @SymbolicExprContext (interp_flat_type interp_base_type)).

    Local Notation var_cast := (@var_cast _ (interp_flat_type interp_base_type) flat_type_beq flat_type_dec_bl).
    Fixpoint denote_symbolic_expr
             (t : flat_type)
             (se : symbolic_expr)
      : option (interp_flat_type interp_base_type t)
      := match se, t with
         | STT, Unit => Some tt
         | SVar n, t
           => match List.nth_error m (length m - S n) with
              | Some e => @var_cast _ t (projT2 (snd e))
              | None => None
              end
         | SOp argsT op args, _
           => match denote_op argsT t op, @denote_symbolic_expr argsT args with
              | Some opc, Some eargs => Some (interp_op _ _ opc eargs)
              | Some _, None | None, Some _ | None, None => None
              end
         | SPair x y, Prod A B
           => match @denote_symbolic_expr A x, @denote_symbolic_expr B y with
              | Some ex, Some ey => Some (ex, ey)
              | Some _, None | None, Some _ | None, None => None
              end
         | SFst A B x, A'
           => if flat_type_beq A A'
              then option_map (@fst _ _) (@denote_symbolic_expr (Prod A' B) x)
              else None
         | SSnd A B x, B'
           => if flat_type_beq B B'
              then option_map (@snd _ _) (@denote_symbolic_expr (Prod A B') x)
              else None
         | SInvalid, _
         | STT, _
         | SPair _ _, _
           => None
         end.

    Fail Lemma denote_symbolize_exprf
          (*(Hm : forall n v, List.nth_error m n = Some v -> denote_symbolic_expr *)
          t e se e'
      : @symbolize_exprf var t e = Some se
        -> denote_symbolic_expr t se = Some e'
        -> e' = e. (* The command has indeed failed with message:
In environment
base_type_code : Type
op_code : Type
base_type_code_beq : base_type_code -> base_type_code -> bool
op_code_beq : op_code -> op_code -> bool
base_type_code_bl : forall x y : base_type_code, base_type_code_beq x y = true -> x = y
base_type_code_lb : forall x y : base_type_code, x = y -> base_type_code_beq x y = true
op_code_bl : forall x y : op_code, op_code_beq x y = true -> x = y
op_code_lb : forall x y : op_code, x = y -> op_code_beq x y = true
op : flat_type -> flat_type -> Type
symbolize_op : forall s d : flat_type, op s d -> op_code
denote_op : forall s d : flat_type, op_code -> option (op s d)
denote_symbolize_op : forall (s d : flat_type) (opc : op s d), denote_op s d (symbolize_op s d opc) = Some opc
var : base_type_code -> Type
m : SymbolicExprContext
t : flat_type
e : exprf t
se : symbolic_expr
e' : exprf t
The term "e" has type
 "@Syntax.exprf base_type_code op
    (fun t : base_type_code => prod (var t) (CommonSubexpressionElimination.symbolic_expr base_type_code op_code)) t"
while it is expected to have type "@Syntax.exprf base_type_code op var t".
                    *)
  End with_var.
End symbolic.
