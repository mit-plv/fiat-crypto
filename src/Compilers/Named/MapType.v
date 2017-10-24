Require Import Coq.Bool.Sumbool.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Syntax.

Local Open Scope nexpr_scope.
Section language.
  Context {base_type_code1 base_type_code2 : Type}
          {op1 : flat_type base_type_code1 -> flat_type base_type_code1 -> Type}
          {op2 : flat_type base_type_code2 -> flat_type base_type_code2 -> Type}
          {Name : Type}
          (f_base : base_type_code1 -> base_type_code2)
          (f_op : forall s d,
              op1 s d
              -> option (op2 (lift_flat_type f_base s) (lift_flat_type f_base d))).

  Fixpoint mapf_type
           {t} (e : exprf base_type_code1 op1 Name t)
    : option (exprf base_type_code2 op2 Name (lift_flat_type f_base t))
    := match e in exprf _ _ _ t return option (exprf _ _ _ (lift_flat_type f_base t)) with
       | TT => Some TT
       | Var t x => Some (Var x)
       | Op t1 tR opc args
         => let opc := f_op _ _ opc in
            let args := @mapf_type _ args in
            match opc, args with
            | Some opc, Some args => Some (Op opc args)
            | _, _ => None
            end
       | LetIn tx n ex tC eC
         => let n := transfer_interp_flat_type f_base (fun _ (n : Name) => n) n in
            let ex := @mapf_type _ ex in
            let eC := @mapf_type _ eC in
            match ex, eC with
            | Some ex, Some eC
              => Some (LetIn _ n ex eC)
            | _, _ => None
            end
       | Pair tx ex ty ey
         => let ex := @mapf_type _ ex in
            let ey := @mapf_type _ ey in
            match ex, ey with
            | Some ex, Some ey
              => Some (Pair ex ey)
            | _, _ => None
            end
       end.

  Definition map_type
             {t} (e : expr base_type_code1 op1 Name t)
    : option (expr base_type_code2 op2 Name (Arrow (lift_flat_type f_base (domain t)) (lift_flat_type f_base (codomain t))))
    := let f := invert_Abs e in
       let f := mapf_type f in
       let n := Abs_name e in
       let n := transfer_interp_flat_type f_base (fun _ (n : Name) => n) n in
       option_map
         (fun f => Abs n f)
         f.
End language.
