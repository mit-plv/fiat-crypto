Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.TypeUtil.
Require Import Crypto.Compilers.SmartCast.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Util.Notations.

Local Open Scope expr_scope.
Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_base_type_bounds : base_type_code -> Type)
          (interp_op_bounds : forall src dst, op src dst -> interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst)
          (bound_base_type : forall t, interp_base_type_bounds t -> base_type_code)
          (base_type_beq : base_type_code -> base_type_code -> bool)
          (base_type_bl_transparent : forall x y, base_type_beq x y = true -> x = y)
          (base_type_leb : base_type_code -> base_type_code -> bool)
          (Cast : forall var A A', exprf base_type_code op (var:=var) (Tbase A) -> exprf base_type_code op (var:=var) (Tbase A'))
          (genericize_op : forall src dst (opc : op src dst) (new_bounded_type_in new_bounded_type_out : base_type_code),
              option { src'dst' : _ & op (fst src'dst') (snd src'dst') })
          (failf : forall var t, @exprf base_type_code op var (Tbase t)).
  Local Infix "<=?" := base_type_leb : expr_scope.
  Local Infix "=?" := base_type_beq : expr_scope.

  Local Notation flat_type_max := (flat_type_max base_type_leb).
  Local Notation SmartCast := (@SmartCast _ op _ base_type_bl_transparent Cast).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Definition bound_flat_type {t} : interp_flat_type interp_base_type_bounds t
                                   -> flat_type
    := @SmartFlatTypeMap _ interp_base_type_bounds (fun t v => bound_base_type t v) t.
  Definition bound_type {t}
             (e_bounds : interp_type interp_base_type_bounds t)
             (input_bounds : interp_flat_type interp_base_type_bounds (domain t))
    : type
    := Arrow (@bound_flat_type (domain t) input_bounds)
             (@bound_flat_type (codomain t) (e_bounds input_bounds)).
  Definition bound_op
             ovar src1 dst1 src2 dst2 (opc1 : op src1 dst1) (opc2 : op src2 dst2)
    : exprf (var:=ovar) src1
      -> interp_flat_type interp_base_type_bounds src2
      -> exprf (var:=ovar) dst1
    := fun args input_bounds
       => let output_bounds := interp_op_bounds _ _ opc2 input_bounds in
          let input_ts := SmartVarfMap bound_base_type input_bounds in
          let output_ts := SmartVarfMap bound_base_type output_bounds in
          let new_type_in := flat_type_max input_ts in
          let new_type_out := flat_type_max output_ts in
          let new_opc := match new_type_in, new_type_out with
                         | Some new_type_in, Some new_type_out
                           => genericize_op _ _ opc1 new_type_in new_type_out
                         | None, _ | _, None => None
                         end in
          match new_opc with
          | Some (existT _ new_opc)
            => match SmartCast _ _, SmartCast _ _ with
               | Some SmartCast_args, Some SmartCast_result
                 => LetIn args
                          (fun args
                           => LetIn (Op new_opc (SmartCast_args args))
                                    (fun opv => SmartCast_result opv))
               | None, _
               | _, None
                 => Op opc1 args
               end
          | None
            => Op opc1 args
          end.

  Section smart_bound.
    Definition interpf_smart_bound_exprf {var t}
               (e : interp_flat_type var t) (bounds : interp_flat_type interp_base_type_bounds t)
    : interp_flat_type (fun t => exprf (var:=var) (Tbase t)) (bound_flat_type bounds)
      := SmartFlatTypeMap2Interp2
           (f:=fun t v => Tbase _)
           (fun t bs v => Cast _ t (bound_base_type t bs) (Var v))
           bounds e.
    Definition interpf_smart_unbound_exprf {var t}
               (bounds : interp_flat_type interp_base_type_bounds t)
               (e : interp_flat_type (fun t => exprf (var:=var) (Tbase t)) (bound_flat_type bounds))
      : interp_flat_type (fun t => @exprf var (Tbase t)) t
      := SmartFlatTypeMapUnInterp2
           (f:=fun t v => Tbase (bound_base_type t _))
           (fun t bs v => Cast _ (bound_base_type t bs) t v)
           e.

    Definition interpf_smart_bound
               {interp_base_type}
               (cast_val : forall A A', interp_base_type A -> interp_base_type A')
               {t}
               (e : interp_flat_type interp_base_type t)
               (bounds : interp_flat_type interp_base_type_bounds t)
    : interp_flat_type interp_base_type (bound_flat_type bounds)
      := SmartFlatTypeMap2Interp2
           (f:=fun t v => Tbase _)
           (fun t bs v => cast_val t (bound_base_type t bs) v)
           bounds e.
    Definition interpf_smart_unbound
               {interp_base_type}
               (cast_val : forall A A', interp_base_type A -> interp_base_type A')
               {t}
               (bounds : interp_flat_type interp_base_type_bounds t)
               (e : interp_flat_type interp_base_type (bound_flat_type bounds))
      : interp_flat_type interp_base_type t
    := SmartFlatTypeMapUnInterp2 (f:=fun _ _ => Tbase _) (fun t b v => cast_val _ _ v) e.

    Definition smart_boundf {var t1} (e1 : exprf (var:=var) t1) (bounds : interp_flat_type interp_base_type_bounds t1)
      : exprf (var:=var) (bound_flat_type bounds)
      := LetIn e1 (fun e1' => SmartPairf (var:=var) (interpf_smart_bound_exprf e1' bounds)).
    Definition smart_bound {var t1} (e1 : expr (var:=var) t1)
               (e_bounds : interp_type interp_base_type_bounds t1)
               (input_bounds : interp_flat_type interp_base_type_bounds (domain t1))
      : expr (var:=var) (bound_type e_bounds input_bounds)
      := Abs
           (fun args
            => LetIn
                 (SmartPairf (interpf_smart_unbound_exprf input_bounds (SmartVarfMap (fun _ => Var) args)))
                 (fun v => smart_boundf
                             (invert_Abs e1 v)
                             (e_bounds input_bounds))).
    Definition SmartBound {t1} (e : Expr t1)
               (input_bounds : interp_flat_type interp_base_type_bounds (domain t1))
      : Expr (bound_type _ input_bounds)
      := fun var => smart_bound (e var) (interp (@interp_op_bounds) (e _)) input_bounds.
  End smart_bound.
End language.

Global Arguments bound_flat_type _ _ _ !_ _ / .
Global Arguments bound_type _ _ _ !_ _ _ / .
