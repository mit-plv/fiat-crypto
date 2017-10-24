Require Import Coq.Bool.Sumbool.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.ExprInversion.

Section language.
  Context {base_type_code1 base_type_code2 : Type}
          {op1 : flat_type base_type_code1 -> flat_type base_type_code1 -> Type}
          {op2 : flat_type base_type_code2 -> flat_type base_type_code2 -> Type}
          (f_base : base_type_code1 -> base_type_code2)
          (f_op : forall s d,
              op1 s d
              -> option (op2 (lift_flat_type f_base s) (lift_flat_type f_base d))).

  Section with_var.
    Context {var1 : base_type_code1 -> Type}
            {var2 : base_type_code2 -> Type}
            (f_var12 : forall t, var1 t -> var2 (f_base t))
            (f_var21 : forall t, var2 (f_base t) -> var1 t)
            (failb : forall t, exprf _ op2 (var:=var2) (Tbase t)).

    Local Notation failf t
      := (SmartPairf (SmartValf _ failb t)).

    Fixpoint mapf_base_type
             {t} (e : exprf base_type_code1 op1 (var:=var1) t)
      : exprf base_type_code2 op2 (var:=var2) (lift_flat_type f_base t)
      := match e in exprf _ _ t return exprf _ _ (lift_flat_type f_base t) with
         | TT => TT
         | Var t x => Var (f_var12 _ x)
         | Op t1 tR opc args
           => let opc := f_op _ _ opc in
              let args := @mapf_base_type _ args in
              match opc with
              | Some opc => Op opc args
              | None => failf _
              end
         | LetIn tx ex tC eC
           => let ex := @mapf_base_type _ ex in
              let eC := fun x => @mapf_base_type _ (eC x) in
              LetIn ex (fun x => eC (untransfer_interp_flat_type (t:=tx) f_base f_var21 x))
         | Pair tx ex ty ey
           => let ex := @mapf_base_type _ ex in
              let ey := @mapf_base_type _ ey in
              Pair ex ey
         end.

    Definition map_base_type
               {t} (e : expr base_type_code1 op1 t)
      : expr base_type_code2 op2 (Arrow (lift_flat_type f_base (domain t)) (lift_flat_type f_base (codomain t)))
      := let f := invert_Abs e in
         let f := fun x => mapf_base_type (f x) in
         Abs (src:=lift_flat_type f_base (domain t))
             (fun x => f (untransfer_interp_flat_type _ f_var21 x)).
  End with_var.

  Section bool_gen.
    Context {var : base_type_code1 -> Type}
            (val : forall t, var t).

    Fixpoint check_mapf_base_type_gen
             {t} (e : exprf base_type_code1 op1 (var:=var) t)
    : bool
      := match e with
         | TT => true
         | Var t x => true
         | Op t1 tR opc args
           => let opc := f_op _ _ opc in
              let check_args := @check_mapf_base_type_gen _ args in
              match opc with
              | Some opc => check_args
              | None => false
              end
         | LetIn tx ex tC eC
           => let check_ex := @check_mapf_base_type_gen _ ex in
              let check_eC := fun x => @check_mapf_base_type_gen _ (eC x) in
              andb check_ex (check_eC (SmartValf _ val _))
         | Pair tx ex ty ey
           => let check_ex := @check_mapf_base_type_gen _ ex in
              let check_ey := @check_mapf_base_type_gen _ ey in
              andb check_ex check_ey
         end.

    Definition check_map_base_type_gen
               {t} (e : expr base_type_code1 op1 (var:=var) t)
      : bool
      := let f := invert_Abs e in
         let f := fun x => check_mapf_base_type_gen (f x) in
         f (SmartValf _ val _).
  End bool_gen.

  Section bool.
    Definition check_mapf_base_type {t} e
      := @check_mapf_base_type_gen (fun _ => unit) (fun _ => tt) t e.
    Definition check_map_base_type {t} e
      := @check_map_base_type_gen (fun _ => unit) (fun _ => tt) t e.
  End bool.

  Definition MapBaseType
             (failb : forall var t, exprf _ op2 (var:=var) (Tbase t))
             {t} (e : Expr base_type_code1 op1 t)
    : Expr base_type_code2 op2 (Arrow (lift_flat_type f_base (domain t)) (lift_flat_type f_base (codomain t)))
    := fun var => map_base_type
                    (var1:=fun t => var (f_base t)) (var2:=var)
                    (fun _ x => x) (fun _ x => x) (failb _) (e _).
End language.
