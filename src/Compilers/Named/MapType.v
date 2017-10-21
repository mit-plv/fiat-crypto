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
          (f_base_type_code : base_type_code1 -> base_type_code2).
  Fixpoint lift_flat_type (t : flat_type base_type_code1) : flat_type base_type_code2
    := match t with
       | Tbase T => Tbase (f_base_type_code T)
       | Unit => Unit
       | Prod A B => Prod (lift_flat_type A) (lift_flat_type B)
       end.
  Context (f_op : forall s d,
              op1 s d
              -> option (op2 (lift_flat_type s) (lift_flat_type d))).

  Fixpoint transfer_interp_flat_type {t}
    : interp_flat_type (fun _ => Name) t
      -> interp_flat_type (fun _ => Name) (lift_flat_type t)
    := match t with
       | Tbase T => fun v => v
       | Unit => fun v => v
       | Prod A B => fun ab : interp_flat_type _ A * interp_flat_type _ B
                     => (@transfer_interp_flat_type _ (fst ab),
                         @transfer_interp_flat_type _ (snd ab))%core
       end.

  Fixpoint mapf_type
           {t} (e : exprf base_type_code1 op1 Name t)
    : option (exprf base_type_code2 op2 Name (lift_flat_type t))
    := match e in exprf _ _ _ t return option (exprf _ _ _ (lift_flat_type t)) with
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
         => let n := transfer_interp_flat_type n in
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
    : option (expr base_type_code2 op2 Name (Arrow (lift_flat_type (domain t)) (lift_flat_type (codomain t))))
    := let f := invert_Abs e in
       let f := mapf_type f in
       let n := Abs_name e in
       let n := transfer_interp_flat_type n in
       option_map
         (fun f => Abs n f)
         f.
End language.
