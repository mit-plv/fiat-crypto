Require Import Coq.Bool.Sumbool.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Reflection.MapCast.
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
          (is_cast : forall src dst, op src dst -> bool)
          (is_const : forall src dst, op src dst -> bool)
          (genericize_op : forall src dst (opc : op src dst) (new_bounded_type : base_type_code),
              option { src'dst' : _ & op (fst src'dst') (snd src'dst') })
          (failf : forall var t, @exprf base_type_code op var (Tbase t)).
  Local Infix "<=?" := base_type_leb : expr_scope.
  Local Infix "=?" := base_type_beq : expr_scope.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Definition base_type_min (a b : base_type_code) : base_type_code
    := if a <=? b then a else b.
  Definition base_type_max (a b : base_type_code) : base_type_code
    := if a <=? b then b else a.
  Section gen.
    Context (join : base_type_code -> base_type_code -> base_type_code).
    Fixpoint flat_type_join {t : flat_type}
      : interp_flat_type (fun _ => base_type_code) t -> option base_type_code
      := match t with
         | Tbase _ => fun v => Some v
         | Unit => fun _ => None
         | Prod A B
           => fun v => match @flat_type_join A (fst v), @flat_type_join B (snd v) with
                       | Some a, Some b => Some (join a b)
                       | Some a, None => Some a
                       | None, Some b => Some b
                       | None, None => None
                       end
         end.
  End gen.
  Definition flat_type_min {t} := @flat_type_join base_type_min t.
  Definition flat_type_max {t} := @flat_type_join base_type_max t.

  Definition SmartCast_base {var A A'} (x : exprf (var:=var) (Tbase A))
    : exprf (var:=var) (Tbase A')
    := match sumbool_of_bool (base_type_beq A A') with
       | left pf => match base_type_bl_transparent _ _ pf with
                    | eq_refl => x
                    end
       | right _ => Cast _ _ A' x
       end.

  Fixpoint SmartCast {var} A B
    : option (interp_flat_type var A -> exprf (var:=var) B)
    := match A, B return option (interp_flat_type var A -> exprf (var:=var) B) with
       | Tbase A, Tbase B => Some (fun v => SmartCast_base (Var (var:=var) v))
       | Prod A0 A1, Prod B0 B1
         => match @SmartCast _ A0 B0, @SmartCast _ A1 B1 with
            | Some f, Some g => Some (fun xy => Pair (f (fst xy)) (g (snd xy)))
            | _, _ => None
            end
       | Unit, Unit => Some (fun _ => TT)
       | Tbase _, _
       | Prod _ _, _
       | Unit, _
         => None
       end.

  Section inline_cast.
    (** We can squash [a -> b -> c] into [a -> c] if [min a b c = min
        a c], i.e., if the narrowest type we pass through in the
        original case is the same as the narrowest type we pass
        through in the new case. *)
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
  End inline_cast.

  Definition bound_flat_type {t} : interp_flat_type interp_base_type_bounds t
                                   -> flat_type
    := @SmartFlatTypeMap2 _ _ interp_base_type_bounds (fun t v => Tbase (bound_base_type t v)) t.
  Fixpoint bound_type {t} : forall (e_bounds : interp_type interp_base_type_bounds t)
                                   (input_bounds : interp_all_binders_for' t interp_base_type_bounds),
      type
    := match t return interp_type _ t -> interp_all_binders_for' t _ -> type with
       | Tflat T => fun e_bounds _ => @bound_flat_type T e_bounds
       | Arrow A B
         => fun e_bounds input_bounds
            => Arrow (@bound_base_type A (fst input_bounds))
                     (@bound_type B (e_bounds (fst input_bounds)) (snd input_bounds))
       end.
  Definition bound_op
             ovar src1 dst1 src2 dst2 (opc1 : op src1 dst1) (opc2 : op src2 dst2)
    : exprf (var:=ovar) src1
      -> interp_flat_type interp_base_type_bounds src2
      -> exprf (var:=ovar) dst1
    := fun args input_bounds
       => let output_bounds := interp_op_bounds _ _ opc2 input_bounds in
          let input_ts := SmartVarfMap bound_base_type input_bounds in
          let output_ts := SmartVarfMap bound_base_type output_bounds in
          let new_type := flat_type_max (t:=Prod _ _) (input_ts, output_ts)%core in
          let new_opc := option_map (genericize_op _ _ opc1) new_type in
          match new_opc with
          | Some (Some (existT _ new_opc))
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
          | Some None
          | None
            => Op opc1 args
          end.

  Section smart_bound.
    Definition interpf_smart_bound {var t}
               (e : interp_flat_type var t) (bounds : interp_flat_type interp_base_type_bounds t)
    : interp_flat_type (fun t => exprf (var:=var) (Tbase t)) (bound_flat_type bounds)
      := SmartFlatTypeMap2Interp2
           (f:=fun t v => Tbase _)
           (fun t bs v => Cast _ t (bound_base_type t bs) (Var v))
           bounds e.
    Definition interpf_smart_unbound {var t}
               (bounds : interp_flat_type interp_base_type_bounds t)
               (e : interp_flat_type (fun t => exprf (var:=var) (Tbase t)) (bound_flat_type bounds))
      : interp_flat_type (fun t => @exprf var (Tbase t)) t
      := SmartFlatTypeMapUnInterp2
           (f:=fun t v => Tbase (bound_base_type t _))
           (fun t bs v => Cast _ (bound_base_type t bs) t v)
           e.

    Definition smart_boundf {var t1} (e1 : exprf (var:=var) t1) (bounds : interp_flat_type interp_base_type_bounds t1)
      : exprf (var:=var) (bound_flat_type bounds)
      := LetIn e1 (fun e1' => SmartPairf (var:=var) (interpf_smart_bound e1' bounds)).
    Fixpoint UnSmartArrow {P t}
      : forall (e_bounds : interp_type interp_base_type_bounds t)
               (input_bounds : interp_all_binders_for' t interp_base_type_bounds)
               (e : P (SmartArrow (bound_flat_type input_bounds)
                                  (bound_flat_type (ApplyInterpedAll' e_bounds input_bounds)))),
        P (bound_type e_bounds input_bounds)
      := match t
               return (forall (e_bounds : interp_type interp_base_type_bounds t)
                              (input_bounds : interp_all_binders_for' t interp_base_type_bounds)
                              (e : P (SmartArrow (bound_flat_type input_bounds)
                                                 (bound_flat_type (ApplyInterpedAll' e_bounds input_bounds)))),
                          P (bound_type e_bounds input_bounds))
         with
         | Tflat T => fun _ _ x => x
         | Arrow A B => fun e_bounds input_bounds
                        => @UnSmartArrow
                             (fun t => P (Arrow (bound_base_type A (fst input_bounds)) t))
                             B
                             (e_bounds (fst input_bounds))
                             (snd input_bounds)
         end.
    Definition smart_bound {var t1} (e1 : expr (var:=var) t1)
               (e_bounds : interp_type interp_base_type_bounds t1)
               (input_bounds : interp_all_binders_for' t1 interp_base_type_bounds)
      : expr (var:=var) (bound_type e_bounds input_bounds)
      := UnSmartArrow
           e_bounds
           input_bounds
           (SmartAbs
              (fun args
               => LetIn
                    args
                    (fun args
                     => LetIn
                          (SmartPairf (interpf_smart_unbound input_bounds (SmartVarfMap (fun _ => Var) args)))
                          (fun v => smart_boundf
                                      (ApplyAll e1 (interp_all_binders_for_of' v))
                                      (ApplyInterpedAll' e_bounds input_bounds))))).
    Definition SmartBound {t1} (e : Expr t1)
               (input_bounds : interp_all_binders_for' t1 interp_base_type_bounds)
      : Expr (bound_type _ input_bounds)
      := fun var => smart_bound (e var) (interp (@interp_op_bounds) (e _)) input_bounds.
  End smart_bound.

  Definition Boundify {t1} (e1 : Expr t1) args2
    : Expr _
    := InlineConstGen
         (@push_cast)
         (Linearize
            (SmartBound
               (@MapInterpCast
                  base_type_code interp_base_type_bounds
                  op (@interp_op_bounds)
                  (@failf)
                  (@bound_op)
                  t1 e1 (interp_all_binders_for_to' args2))
               (interp_all_binders_for_to' args2))).
End language.
