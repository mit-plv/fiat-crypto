Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.ExprInversion.
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
          (failv : forall {var t}, @exprf base_type_code1 op1 var (Tbase t)).
  Context (transfer_op : forall ovar src1 dst1 src2 dst2
                                (opc1 : op1 src1 dst1)
                                (opc2 : op2 src2 dst2)
                                (args1' : @exprf base_type_code1 op1 ovar src1)
                                (args2 : interp_flat_type interp_base_type2 src2),
              @exprf base_type_code1 op1 ovar dst1).


  Section with_var.
    Context {ovar : base_type_code1 -> Type}.
    Local Notation SmartFail
      := (SmartValf _ (@failv _)).
    Local Notation failf t (* {t} : @exprf base_type_code1 op1 ovar t*)
      := (SmartPairf (SmartFail t)).

    (** We only ever make use of this when [e1] and [e2] are the same
        type, and, in fact, the same syntax tree instantiated to
        different [var] arguments.  However, if we make
        [mapf_interp_cast] homogenous (force [t1] and [t2] to be
        judgmentally equal), then we run into trouble in the recursive
        calls in the [LetIn] and [Op] cases; we'd need to have
        evidence that they are the same (such as a (transparent!)
        well-foundedness proof), or a decider of type equality with
        transparent proofs that we can cast across.

        Rather than asking for either of these, we take the simpler
        route of allowing expression trees of different types, and
        failing ([failf]) or falling back to default behavior (as in
        the [TT] and [Var] cases) when things don't match.

        Allowing two different [base_type_code]s and [op] types is
        unnecessary, and they could be collapsed.  The extra
        generalization costs little in lines-of-code, though, so I've
        left it in. *)
    Fixpoint mapf_interp_cast
             {t1} (e1 : @exprf base_type_code1 op1 ovar t1)
             {t2} (e2 : @exprf base_type_code2 op2 interp_base_type2 t2)
             {struct e1}
      : @exprf base_type_code1 op1 ovar t1
      := match e1 in exprf _ _ t1, e2 as e2 in exprf _ _ t2
               return exprf _ _ (var:=ovar) t1 with
         | TT as e1', _
         | Var _ _ as e1', _
           => e1'
         | Pair tx1 ex1 ty1 ey1, Pair tx2 ex2 ty2 ey2
           => Pair
                (@mapf_interp_cast _ ex1 _ ex2)
                (@mapf_interp_cast _ ey1 _ ey2)
         | Op _ tR1 op1 args1, Op _ tR2 op2 args2
           => let args' := @mapf_interp_cast _ args1 _ args2 in
              transfer_op _ _ _ _ _ op1 op2 args' (interpf interp_op2 args2)
         | LetIn tx1 ex1 tC1 eC1, LetIn tx2 ex2 tC2 eC2
           => let ex' := @mapf_interp_cast _ ex1 _ ex2 in
              let eC' := fun v' => @mapf_interp_cast _ (eC1 v') _ (eC2 (interpf interp_op2 ex2)) in
              LetIn ex' eC'
         | Op _ _ _ _, _
         | LetIn _ _ _ _, _
         | Pair _ _ _ _, _
           => @failf _
         end.
    Arguments mapf_interp_cast {_} _ {_} _. (* 8.4 workaround for bad arguments *)

    Definition map_interp_cast
             {t1} (e1 : @expr base_type_code1 op1 ovar t1)
             {t2} (e2 : @expr base_type_code2 op2 interp_base_type2 t2)
             (args2 : interp_flat_type interp_base_type2 (domain t2))
      : @expr base_type_code1 op1 ovar (Arrow (domain t1) (codomain t1))
      := let f1 := invert_Abs e1 in
         let f2 := invert_Abs e2 in
         Abs (fun x => @mapf_interp_cast _ (f1 x) _ (f2 args2)).
  End with_var.
End language.

Global Arguments mapf_interp_cast {_ _ _ _ _} interp_op2 failv transfer_op {ovar} {t1} e1 {t2} e2.
Global Arguments map_interp_cast {_ _ _ _ _} interp_op2 failv transfer_op {ovar} {t1} e1 {t2} e2 args2.

Section homogenous.
  Context {base_type_code : Type}
          {interp_base_type2 : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_op2 : forall src dst, op src dst -> interp_flat_type interp_base_type2 src -> interp_flat_type interp_base_type2 dst)
          (failv : forall {var t}, @exprf base_type_code op var (Tbase t)).

  Definition MapInterpCast
             transfer_op
             {t} (e : Expr base_type_code op t) (args : interp_flat_type interp_base_type2 (domain t))
    : Expr base_type_code op (Arrow (domain t) (codomain t))
    := fun var => map_interp_cast interp_op2 (@failv) transfer_op (e _) (e _) args.
End homogenous.
