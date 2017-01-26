Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.

Local Open Scope ctype_scope.
Local Open Scope expr_scope.
Section language.
  Context {base_type_code1 base_type_code2 : Type}
          {interp_base_type2 : base_type_code2 -> Type}
          {op1 : flat_type base_type_code1 -> flat_type base_type_code1 -> Type}
          {op2 : flat_type base_type_code2 -> flat_type base_type_code2 -> Type}
          (interp_op2 : forall src dst, op2 src dst -> interp_flat_type interp_base_type2 src -> interp_flat_type interp_base_type2 dst)
          (failv : forall {var t}, @exprf base_type_code1 op1 var (Tbase t))
          (new_base_type : forall t, interp_base_type2 t -> base_type_code1).
  Local Notation new_flat_type (*: forall t, interp_flat_type interp_base_type2 t -> flat_type base_type_code1*)
    := (@SmartFlatTypeMap2 _ _ interp_base_type2 (fun t v => Tbase (new_base_type t v))).
  Fixpoint new_type t
    : forall (ve : interp_all_binders_for' t interp_base_type2) (v : interp_type interp_base_type2 t),
      type base_type_code1
    := match t return interp_all_binders_for' t _ -> interp_type _ t -> type base_type_code1 with
       | Tflat T => fun _ => new_flat_type
       | Arrow A B => fun ve v => Arrow (@new_base_type A (fst ve)) (@new_type B (snd ve) (v (fst ve)))
       end.
  Context (transfer_op : forall ovar src1 dst1 src2 dst2
                                (opc1 : op1 src1 dst1)
                                (opc2 : op2 src2 dst2)
                                args2
                                (args' : @exprf base_type_code1 op1 ovar (@new_flat_type _ (interpf interp_op2 args2))),
              @exprf base_type_code1 op1 ovar (@new_flat_type _ (interpf interp_op2 (Op opc2 args2)))).


  Section with_var.
    Context {ovar : base_type_code1 -> Type}.
    Local Notation ivar t := (@exprf base_type_code1 op1 ovar (Tbase t)) (only parsing).
    Local Notation ivarf := (fun t => ivar t).
    Context (transfer_var : forall tx1 tx2 tC1
                                   (f : interp_flat_type ivarf tx1 -> exprf base_type_code1 op1 (var:=ovar) tC1)
                                   (v : interp_flat_type ivarf tx2),
                exprf base_type_code1 op1 (var:=ovar) tC1).
    Local Notation SmartFail
      := (SmartValf _ (@failv _)).
    Local Notation failf t (* {t} : @exprf base_type_code1 op1 ovar t*)
      := (SmartPairf (SmartFail t)).
    Fixpoint fail t : @expr base_type_code1 op1 ovar t
      := match t with
         | Tflat T => @failf _
         | Arrow A B => Abs (fun _ => @fail B)
         end.

    Fixpoint mapf_interp_cast
             {t1} (e1 : @exprf base_type_code1 op1 ivarf t1)
             {t2} (e2 : @exprf base_type_code2 op2 interp_base_type2 t2)
             {struct e1}
      : @exprf base_type_code1 op1 ovar (@new_flat_type _ (interpf interp_op2 e2))
      := match e1 in exprf _ _ t1, e2 as e2 in exprf _ _ t2
               return exprf _ _ (var:=ovar) (@new_flat_type _ (interpf interp_op2 e2)) with
         | TT, TT => TT
         | Var tx1 x1, Var tx2 x2 as e2'
           => transfer_var (Tbase _) (Tbase _) (Tbase _) (fun x => x) x1
         | Op _ tR1 op1 args1, Op _ tR2 op2 args2
           => let args' := @mapf_interp_cast _ args1 _ args2 in
              transfer_op _ _ _ _ _ op1 op2 args2 args'
         | LetIn tx1 ex1 tC1 eC1, LetIn tx2 ex2 tC2 eC2
           => let ex' := @mapf_interp_cast _ ex1 _ ex2 in
              let eC' := fun v' => @mapf_interp_cast _ (eC1 v') _ (eC2 (interpf interp_op2 ex2)) in
              LetIn ex'
                    (fun v => transfer_var _ _ _ eC' (SmartVarfMap (fun t => Var) v))
         | Pair tx1 ex1 ty1 ey1, Pair tx2 ex2 ty2 ey2
           => Pair
                (@mapf_interp_cast _ ex1 _ ex2)
                (@mapf_interp_cast _ ey1 _ ey2)
         | TT, _
         | Var _ _, _
         | Op _ _ _ _, _
         | LetIn _ _ _ _, _
         | Pair _ _ _ _, _
           => @failf _
         end.
    Arguments mapf_interp_cast {_} _ {_} _. (* 8.4 workaround for bad arguments *)

    Fixpoint map_interp_cast
             {t1} (e1 : @expr base_type_code1 op1 ivarf t1)
             {t2} (e2 : @expr base_type_code2 op2 interp_base_type2 t2)
             {struct e2}
      : forall (args2 : interp_all_binders_for' t2 interp_base_type2),
        @expr base_type_code1 op1 ovar (@new_type _ args2 (interp interp_op2 e2))
      := match e1 in expr _ _ t1, e2 in expr _ _ t2
               return forall (args2 : interp_all_binders_for' t2 _), expr _ _ (new_type _ args2 (interp _ e2)) with
         | Return t1 ex1, Return t2 ex2
           => fun _ => mapf_interp_cast ex1 ex2
         | Abs src1 dst1 f1, Abs src2 dst2 f2
           => fun args2
              => Abs (fun x
                      => let x' := @transfer_var (Tbase _) (Tbase _) (Tbase _) (fun x => x) (Var x) in
                         @map_interp_cast _ (f1 x') _ (f2 (fst args2)) (snd args2))
         | Return _ _, _
         | Abs _ _ _, _
           => fun _ => @fail _
         end.
  End with_var.
End language.

Global Arguments mapf_interp_cast {_ _ _ _ _ _} failv {_} transfer_op {ovar} transfer_var {t1} e1 {t2} e2.
Global Arguments map_interp_cast {_ _ _ _ _ _} failv {_} transfer_op {ovar} transfer_var {t1} e1 {t2} e2 args2.
Global Arguments new_type {_ _ _} new_base_type {t} _ _.

Section homogenous.
  Context {base_type_code : Type}
          {interp_base_type2 : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_op2 : forall src dst, op src dst -> interp_flat_type interp_base_type2 src -> interp_flat_type interp_base_type2 dst)
          (failv : forall {var t}, @exprf base_type_code op var (Tbase t))
          (new_base_type : forall t, interp_base_type2 t -> base_type_code).

  Definition MapInterpCast
          transfer_op
          (transfer_var : forall ovar tx1 tx2 tC1
                                 (ivarf := fun t => @exprf base_type_code op ovar (Tbase t))
                                 (f : interp_flat_type ivarf tx1 -> exprf base_type_code op (var:=ovar) tC1)
                                 (v : interp_flat_type ivarf tx2),
              exprf base_type_code op (var:=ovar) tC1)
          {t} (e : Expr base_type_code op t) args
    : Expr base_type_code op (new_type (@new_base_type) args (Interp interp_op2 e))
    := fun var => map_interp_cast (@failv) transfer_op (transfer_var _) (e _) (e _) args.
End homogenous.
