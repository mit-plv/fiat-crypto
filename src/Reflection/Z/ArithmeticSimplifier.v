(** * SimplifyArith: Remove things like (_ * 1), (_ + 0), etc *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Rewriter.
Require Import Crypto.Reflection.Z.Syntax.

Section language.
  Local Notation exprf := (@exprf base_type op).
  Local Notation Expr := (@Expr base_type op).

  Section with_var.
    Context {var : base_type -> Type}.

    Fixpoint interp_as_expr_or_const {t} (x : exprf (var:=var) t)
      : option (interp_flat_type (fun t => Z + (exprf (var:=var) (Tbase t)))%type t)
      := match x in Syntax.exprf _ _ t return option (interp_flat_type _ t) with
         | Op t1 (Tbase _) opc args
           => Some (match opc with
                    | OpConst _ z => fun _ => inl z
                    | _ => fun x => x
                    end (inr (Op opc args)))
         | TT => Some tt
         | Var t v => Some (inr (Var v))
         | Op _ _ _ _
         | LetIn _ _ _ _
           => None
         | Pair tx ex ty ey
           => match @interp_as_expr_or_const tx ex, @interp_as_expr_or_const ty ey with
              | Some vx, Some vy => Some (vx, vy)
              | _, None | None, _ => None
              end
         end.

    Definition simplify_op_expr {src dst} (opc : op src dst)
      : exprf (var:=var) src -> exprf (var:=var) dst
      := match opc in op src dst return exprf src -> exprf dst with
         | Add TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (inl l, inl r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (inl v, inr e)
                 | Some (inr e, inl v)
                   => if (v =? 0)%Z
                      then e
                      else Op opc args
                 | _ => Op opc args
                 end
         | Sub TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (inl l, inl r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (inr e, inl v)
                   => if (v =? 0)%Z
                      then e
                      else Op opc args
                 | _ => Op opc args
                 end
         | Mul TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (inl l, inl r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (inl v, inr e)
                 | Some (inr e, inl v)
                   => if (v =? 0)%Z
                      then Op (OpConst 0%Z) TT
                      else if (v =? 1)%Z
                           then e
                           else Op opc args
                 | _ => Op opc args
                 end
         | Shl TZ TZ TZ as opc
         | Shr TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (inl l, inl r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (inr e, inl v)
                   => if (v =? 0)%Z
                      then e
                      else Op opc args
                 | _ => Op opc args
                 end
         | Land TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (inl l, inl r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (inl v, inr e)
                 | Some (inr e, inl v)
                   => if (v =? 0)%Z
                      then Op (OpConst 0%Z) TT
                      else Op opc args
                 | _ => Op opc args
                 end
         | Lor TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (inl l, inl r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (inl v, inr e)
                 | Some (inr e, inl v)
                   => if (v =? 0)%Z
                      then e
                      else Op opc args
                 | _ => Op opc args
                 end
         | Add _ _ _ as opc
         | Sub _ _ _ as opc
         | Mul _ _ _ as opc
         | Shl _ _ _ as opc
         | Shr _ _ _ as opc
         | Land _ _ _ as opc
         | Lor _ _ _ as opc
         | OpConst _ _ as opc
         | Neg _ _ _ as opc
         | Cmovne _ _ _ _ _ as opc
         | Cmovle _ _ _ _ _ as opc
           => Op opc
         end.
  End with_var.

  Definition SimplifyArith {t} (e : Expr t) : Expr t
    := @RewriteOp base_type op (@simplify_op_expr) t e.
End language.
