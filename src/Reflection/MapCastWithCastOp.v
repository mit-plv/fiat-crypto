Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Equality.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.MapCast.
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
          (base_type_code1_beq : base_type_code1 -> base_type_code1 -> bool)
          (base_type_code1_bl : forall x y, base_type_code1_beq x y = true -> x = y)
          (base_type_code1_lb : forall x y, x = y -> base_type_code1_beq x y = true)
          (failv : forall {var t}, @exprf base_type_code1 op1 var (Tbase t))
          (new_base_type : forall t, interp_base_type2 t -> base_type_code1)
          (Cast : forall var t1 t2, @exprf base_type_code1 op1 var (Tbase t1)
                                    -> @exprf base_type_code1 op1 var (Tbase t2))
          (is_cast : forall t1 t2, op1 t1 t2 -> bool).
  Local Notation new_flat_type (*: forall t, interp_flat_type interp_base_type2 t -> flat_type base_type_code1*)
    := (@SmartFlatTypeMap2 _ _ interp_base_type2 (fun t v => Tbase (new_base_type t v))).
  Local Notation new_type := (@new_type base_type_code1 base_type_code2 interp_base_type2 new_base_type).
  Context (new_op : forall ovar src1 dst1 src2 dst2 (opc1 : op1 src1 dst1) (opc2 : op2 src2 dst2)
                           args2,
              option { new_src : _ & (@exprf base_type_code1 op1 ovar new_src
                                      -> @exprf base_type_code1 op1 ovar (new_flat_type (interpf interp_op2 (Op opc2 args2))))%type }).
  Local Notation SmartFail
    := (SmartValf _ (@failv _)).
  Local Notation failf t (* {t} : @exprf base_type_code1 op1 ovar t*)
    := (SmartPairf (SmartFail t)).

  Fixpoint VarBound {var} T1 T2 : interp_flat_type var T1 -> exprf _ op1 (var:=var) T2
    := match T1, T2 return interp_flat_type var T1 -> exprf _ _ T2 with
       | Tbase T1', Tbase T2' => fun v : var T1' => Cast _ _ _ (Var v)
       | _, Unit => fun _ => TT
       | Prod A1 B1, Prod A2 B2
         => fun xy
            => Pair (@VarBound _ _ _ (fst xy)) (@VarBound _ _ _ (snd xy))
       | Tbase _, _
       | Prod _ _, _
       | Unit, _
         => fun _ => failf _
       end.
  Fixpoint SmartBound {var t1 t2} (v : @exprf _ op1 var t1) : @exprf _ op1 var t2.
  Proof.
    refine match Sumbool.sumbool_of_bool (flat_type_beq _ base_type_code1_beq t1 t2) with
           | left pf => match flat_type_dec_bl _ _ base_type_code1_bl _ _ pf in (_ = y) return exprf _ _ y with
                        | eq_refl => v
                        end
           | right _ => _
           end.
    refine (match v in exprf _ _ t1, t2 return (exprf _ _ _ -> exprf _ _ t2) -> exprf _ _ t2 with
            | Op t1 tR opc args, _
              => if is_cast _ _ opc
                 then fun _ => @SmartBound _ _ _ args
                 else fun default => default v
            | Pair _ ex _ ey, Prod _ _ => fun _ => Pair (@SmartBound _ _ _ ex) (@SmartBound _ _ _ ey)
            | v', _ => fun default => default v'
            end _).
    refine (match t1, t2 return exprf _ _ t1 -> exprf _ _ t2 with
            | Tbase t1', Tbase t2' => Cast _ _ _
            | _, Unit => fun _ => TT
            | Prod A1 B1, Prod A2 B2 => fun x => LetIn x (VarBound _ _)
            | Tbase _, _
            | Prod _ _, _
            | Unit, _
              => fun _ => failf _
            end).
  Defined.
  Definition bound_op ovar
             {src1 dst1 src2 dst2}
             (opc1 : op1 src1 dst1)
             (opc2 : op2 src2 dst2)
    : forall args2
             (args' : @exprf base_type_code1 op1 ovar (@new_flat_type _ (interpf interp_op2 args2))),
      @exprf base_type_code1 op1 ovar (@new_flat_type _ (interpf interp_op2 (Op opc2 args2)))
    := if is_cast _ _ opc1
       then fun _ x => SmartBound x
       else fun args2 args'
            => match new_op _ _ _ _ _ opc1 opc2 args2 with
               | Some f => projT2 f (SmartBound args')
               | None => failf _
               end.

  Section with_var.
    Context {ovar : base_type_code1 -> Type}.
    Local Notation ivar t := (@exprf base_type_code1 op1 ovar (Tbase t)) (only parsing).
    Local Notation ivarf := (fun t => ivar t).

    Fixpoint bound_var tx1 tx2 tC1
             {struct tx2}
      : forall (f : interp_flat_type ivarf tx1 -> exprf _ op1 (var:=ovar) tC1)
               (v : interp_flat_type ivarf tx2),
        exprf _ op1 (var:=ovar) tC1
      := match tx1, tx2 return (interp_flat_type _ tx1 -> _) -> interp_flat_type _ tx2 -> _ with
         | Tbase T1, Tbase T2 => fun f v => f (SmartBound v)
         | Unit, _ => fun f _ => f tt
         | Prod A1 B1, Prod A2 B2
           => fun f v
              => @bound_var
                   _ _ _
                   (fun v1 => @bound_var _ _ _ (fun v2 => f (v1, v2)%core) (snd v))
                   (fst v)
         | Tbase _, _
         | Prod _ _, _
           => fun f _ => f (SmartValf _ (fun t => failf _) _)
         end.

    Definition mapf_interp_cast_with_cast_op
               {t1} (e1 : @exprf base_type_code1 op1 ivarf t1)
               {t2} (e2 : @exprf base_type_code2 op2 interp_base_type2 t2)
      : @exprf base_type_code1 op1 ovar (@new_flat_type _ (interpf interp_op2 e2))
      := @mapf_interp_cast
           base_type_code1 base_type_code2 interp_base_type2 op1 op2
           interp_op2 (@failv) new_base_type bound_op
           ovar bound_var
           t1 e1 t2 e2.
    Definition map_interp_cast_with_cast_op
             {t1} (e1 : @expr base_type_code1 op1 ivarf t1)
             {t2} (e2 : @expr base_type_code2 op2 interp_base_type2 t2)
      : forall (args2 : interp_all_binders_for' t2 interp_base_type2),
        @expr base_type_code1 op1 ovar (@new_type _ args2 (interp interp_op2 e2))
      := @map_interp_cast
           base_type_code1 base_type_code2 interp_base_type2 op1 op2
           interp_op2 (@failv) new_base_type bound_op
           ovar bound_var
           t1 e1 t2 e2.
  End with_var.
End language.

Global Arguments mapf_interp_cast_with_cast_op {_ _ _ _ _ _} base_type_code1_beq base_type_code1_bl failv {_} Cast is_cast new_op {ovar} {t1} e1 {t2} e2.
Global Arguments map_interp_cast_with_cast_op {_ _ _ _ _ _} base_type_code1_beq base_type_code1_bl failv {_} Cast is_cast new_op {ovar} {t1} e1 {t2} e2 args2.

Section homogenous.
  Context {base_type_code : Type}
          {interp_base_type2 : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_op2 : forall src dst, op src dst -> interp_flat_type interp_base_type2 src -> interp_flat_type interp_base_type2 dst)
          (base_type_code_beq : base_type_code -> base_type_code -> bool)
          (base_type_code_bl : forall x y, base_type_code_beq x y = true -> x = y)
          (base_type_code_lb : forall x y, x = y -> base_type_code_beq x y = true)
          (failv : forall {var t}, @exprf base_type_code op var (Tbase t))
          {new_base_type : forall t, interp_base_type2 t -> base_type_code}
          (Cast : forall var t1 t2, @exprf base_type_code op var (Tbase t1)
                                    -> @exprf base_type_code op var (Tbase t2))
          (is_cast : forall t1 t2, op t1 t2 -> bool).
  Definition MapInterpCastWithCastOp
             new_op
             {t} (e : Expr base_type_code op t) args
    : Expr base_type_code op (new_type (@new_base_type) args (Interp interp_op2 e))
    := fun var => map_interp_cast_with_cast_op base_type_code_beq base_type_code_bl (@failv) Cast is_cast new_op (e _) (e _) args.
End homogenous.
