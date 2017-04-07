Require Import Crypto.Compilers.Syntax.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Section with_var.
    Context {var : base_type_code -> Type}.
    Context (rewrite_op_expr : forall src dst (opc : op src dst),
                exprf (var:=var) src -> exprf (var:=var) dst).

    Fixpoint rewrite_opf {t} (e : @exprf var t) : @exprf var t
      := match e in Syntax.exprf _ _ t return @exprf var t with
         | LetIn tx ex tC eC
           => LetIn (@rewrite_opf tx ex) (fun x => @rewrite_opf tC (eC x))
         | Var _ x => Var x
         | TT => TT
         | Pair tx ex ty ey
           => Pair (@rewrite_opf tx ex) (@rewrite_opf ty ey)
         | Op t1 tR opc args => rewrite_op_expr _ _ opc (@rewrite_opf t1 args)
         end.

    Definition rewrite_op {t} (e : @expr var t) : @expr var t
      := match e in Syntax.expr _ _ t return @expr var t with
         | Abs _ _ f => Abs (fun x => rewrite_opf (f x))
         end.
  End with_var.

  Definition RewriteOp
             (rewrite_op_expr : forall var src dst, op src dst -> @exprf var src -> @exprf var dst)
             {t} (e : Expr t)
    : Expr t
    := fun var => rewrite_op (rewrite_op_expr _) (e _).
End language.
