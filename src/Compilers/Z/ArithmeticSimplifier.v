(** * SimplifyArith: Remove things like (_ * 1), (_ + 0), etc *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Rewriter.
Require Import Crypto.Compilers.Z.Syntax.

Section language.
  Local Notation exprf := (@exprf base_type op).
  Local Notation Expr := (@Expr base_type op).

  Section with_var.
    Context {var : base_type -> Type}.

    Inductive inverted_expr t :=
    | const_of (v : Z)
    | gen_expr (e : exprf (var:=var) (Tbase t))
    | neg_expr (e : exprf (var:=var) (Tbase t)).

    Fixpoint interp_as_expr_or_const {t} (x : exprf (var:=var) t)
      : option (interp_flat_type inverted_expr t)
      := match x in Syntax.exprf _ _ t return option (interp_flat_type _ t) with
         | Op t1 (Tbase _) opc args
           => Some (match opc in op src dst
                          return exprf dst
                                 -> exprf src
                                 -> match dst with
                                    | Tbase t => inverted_expr t
                                    | Prod _ _ => True
                                    | _ => inverted_expr TZ
                                    end
                    with
                    | OpConst _ z => fun _ _ => const_of _ z
                    | Opp TZ TZ => fun _ args => neg_expr _ args
                    | AddWithGetCarry _ _ _ _ _ _ => fun _ _ => I
                    | _ => fun e _ => gen_expr _ e
                    end (Op opc args) args)
         | TT => Some tt
         | Var t v => Some (gen_expr _ (Var v))
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
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (const_of v, gen_expr e)
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then e
                      else Op opc args
                 | Some (const_of v, neg_expr e)
                 | Some (neg_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (Opp _ _) e
                      else Op opc args
                 | Some (gen_expr ep, neg_expr en)
                 | Some (neg_expr en, gen_expr ep)
                   => Op (Sub _ _ _) (Pair ep en)
                 | _ => Op opc args
                 end
         | Sub TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then e
                      else Op opc args
                 | Some (neg_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (Opp _ _) e
                      else Op opc args
                 | Some (gen_expr e1, neg_expr e2)
                   => Op (Add _ _ _) (Pair e1 e2)
                 | Some (neg_expr e1, neg_expr e2)
                   => Op (Sub _ _ _) (Pair e2 e1)
                 | _ => Op opc args
                 end
         | Mul TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (const_of v, gen_expr e)
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (OpConst 0%Z) TT
                      else if (v =? 1)%Z
                           then e
                           else if (v =? -1)%Z
                                then Op (Opp _ _) e
                                else Op opc args
                 | Some (const_of v, neg_expr e)
                 | Some (neg_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (OpConst 0%Z) TT
                      else if (v =? 1)%Z
                           then Op (Opp _ _) e
                           else if (v =? -1)%Z
                                then e
                                else Op opc args
                 | Some (gen_expr e1, neg_expr e2)
                 | Some (neg_expr e1, gen_expr e2)
                   => Op (Opp _ _) (Op (Mul _ _ TZ) (Pair e1 e2))
                 | Some (neg_expr e1, neg_expr e2)
                   => Op (Mul _ _ _) (Pair e1 e2)
                 | _ => Op opc args
                 end
         | Shl TZ TZ TZ as opc
         | Shr TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then e
                      else Op opc args
                 | Some (neg_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (Opp _ _) e
                      else Op opc args
                 | _ => Op opc args
                 end
         | Land TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (const_of v, gen_expr _)
                 | Some (gen_expr _, const_of v)
                 | Some (const_of v, neg_expr _)
                 | Some (neg_expr _, const_of v)
                   => if (v =? 0)%Z
                      then Op (OpConst 0%Z) TT
                      else Op opc args
                 | _ => Op opc args
                 end
         | Lor TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (const_of v, gen_expr e)
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then e
                      else Op opc args
                 | Some (const_of v, neg_expr e)
                 | Some (neg_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (Opp _ _) e
                      else Op opc args
                 | _ => Op opc args
                 end
         | Opp TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of v)
                   => Op (OpConst (interp_op _ _ opc v)) TT
                 | Some (neg_expr e)
                   => e
                 | _
                   => Op opc args
                 end
         | Add _ _ _ as opc
         | Sub _ _ _ as opc
         | Mul _ _ _ as opc
         | Shl _ _ _ as opc
         | Shr _ _ _ as opc
         | Land _ _ _ as opc
         | Lor _ _ _ as opc
         | OpConst _ _ as opc
         | Opp _ _ as opc
         | Zselect _ _ _ _ as opc
         | AddWithCarry _ _ _ _ as opc
         | AddWithGetCarry _ _ _ _ _ _ as opc
           => Op opc
         end.
  End with_var.

  Definition SimplifyArith {t} (e : Expr t) : Expr t
    := @RewriteOp base_type op (@simplify_op_expr) t e.
End language.
