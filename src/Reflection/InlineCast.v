Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartCast.
Require Import Crypto.Reflection.TypeUtil.
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Util.Notations.

Local Open Scope expr_scope.
Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (base_type_beq : base_type_code -> base_type_code -> bool)
          (base_type_bl_transparent : forall x y, base_type_beq x y = true -> x = y)
          (base_type_leb : base_type_code -> base_type_code -> bool)
          (Cast : forall var A A', exprf base_type_code op (var:=var) (Tbase A) -> exprf base_type_code op (var:=var) (Tbase A'))
          (is_cast : forall src dst, op src dst -> bool)
          (is_const : forall src dst, op src dst -> bool).
  Local Infix "<=?" := base_type_leb : expr_scope.
  Local Infix "=?" := base_type_beq : expr_scope.

  Local Notation base_type_min := (base_type_min base_type_leb).
  Local Notation SmartCast_base := (@SmartCast_base _ op _ base_type_bl_transparent Cast).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  (** We can squash [a -> b -> c] into [a -> c] if [min a b c = min a
      c], i.e., if the narrowest type we pass through in the original
      case is the same as the narrowest type we pass through in the
      new case. *)
  Definition squash_cast {var} (a b c : base_type_code)
    : @exprf var (Tbase a) -> @exprf var (Tbase c)
    := if base_type_beq (base_type_min b (base_type_min a c)) (base_type_min a c)
       then SmartCast_base
       else fun x => Cast _ b c (Cast _ a b x).
  Fixpoint maybe_push_cast {var t} (v : @exprf var t) : option (@exprf var t)
    := match v in Syntax.exprf _ _ t return option (exprf t) with
       | Var _ _ as v'
         => Some v'
       | Op t1 tR opc args
         => match t1, tR return op t1 tR -> exprf t1 -> option (exprf tR) with
            | Tbase b, Tbase c
              => fun opc args
                 => if is_cast _ _ opc
                    then match @maybe_push_cast _ _ args with
                         | Some (Op t1 tR opc' args')
                           => match t1, tR return op t1 tR -> exprf t1 -> option (exprf (Tbase c)) with
                              | Tbase a, Tbase b
                                => fun opc' args'
                                   => if is_cast _ _ opc'
                                      then Some (squash_cast a b c args')
                                      else None
                              | Unit, Tbase _
                                => fun opc' args'
                                   => if is_const _ _ opc'
                                      then Some (SmartCast_base (Op opc' TT))
                                      else None
                              | _, _ => fun _ _ => None
                              end opc' args'
                         | Some (Var _ v as v') => Some (SmartCast_base v')
                         | Some _ => None
                         | None => None
                         end
                    else None
            | Unit, _
              => fun opc args
                 => if is_const _ _ opc
                    then Some (Op opc TT)
                    else None
            | _, _
              => fun _ _ => None
            end opc args
       | Pair _ _ _ _
       | LetIn _ _ _ _
       | TT
         => None
       end.
  Definition push_cast {var t} : @exprf var t -> inline_directive (op:=op) (var:=var) t
    := match t with
       | Tbase _ => fun v => match maybe_push_cast v with
                             | Some e => inline e
                             | None => default_inline v
                             end
       | _ => default_inline
       end.

  Definition InlineCast {t} (e : Expr t) : Expr t
    := InlineConstGen (@push_cast) e.
End language.
