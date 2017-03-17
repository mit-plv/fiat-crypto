Require Import Coq.Bool.Sumbool.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Named.Syntax.

Local Open Scope nexpr_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {Name : Type}
          {interp_base_type_bounds : base_type_code -> Type}
          (interp_op_bounds : forall src dst, op src dst -> interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst)
          (pick_typeb : forall t, interp_base_type_bounds t -> base_type_code).
  Local Notation pick_type v := (SmartFlatTypeMap pick_typeb v).
  Context (cast_op
           : forall t tR (opc : op t tR) args_bs
                    (args : Named.exprf base_type_code op Name (pick_type args_bs)),
              option (Named.exprf base_type_code op Name (pick_type (interp_op_bounds t tR opc args_bs))))
          {BoundsContext : Context Name interp_base_type_bounds}.

  Fixpoint mapf_cast
           (ctx : BoundsContext)
           {t} (e : exprf base_type_code op Name t)
           {struct e}
    : option { bounds : interp_flat_type interp_base_type_bounds t
                        & exprf base_type_code op Name (pick_type bounds) }
    := match e in exprf _ _ _ t return option { bounds : interp_flat_type interp_base_type_bounds t
                                                         & exprf base_type_code op Name (pick_type bounds) } with
       | TT => Some (existT _ tt TT)
       | Pair tx ex ty ey
         => match @mapf_cast ctx _ ex, @mapf_cast ctx _ ey with
            | Some (existT x_bs xv), Some (existT y_bs yv)
              => Some (existT _ (x_bs, y_bs)%core (Pair xv yv))
            | None, _ | _, None => None
            end
       | Var t x
         => option_map
              (fun bounds => existT _ bounds (Var x))
              (lookupb (t:=t) ctx x)
       | LetIn tx n ex tC eC
         => match @mapf_cast ctx _ ex with
            | Some (existT x_bounds ex')
              => option_map
                   (fun eC' => let 'existT Cx_bounds C_expr := eC' in
                               existT _ Cx_bounds (LetIn (pick_type x_bounds)
                                                         (SmartFlatTypeMapInterp2 (t:=tx) (fun _ _ (n : Name) => n) x_bounds n) ex' C_expr))
                   (@mapf_cast (extend (t:=tx) ctx n x_bounds) _ eC)
            | None => None
            end
       | Op t tR opc args
         => match @mapf_cast ctx _ args with
            | Some (existT args_bounds argsv)
              => option_map
                   (existT _
                           (interp_op_bounds _ _ _ args_bounds))
                   (cast_op t tR opc args_bounds argsv)
            | None => None
            end
       end.

  Definition map_cast
             (ctx : BoundsContext)
             {t} (e : expr base_type_code op Name t)
             (input_bounds : interp_flat_type interp_base_type_bounds (domain t))
    : option { output_bounds : interp_flat_type interp_base_type_bounds (codomain t)
                               & expr base_type_code op Name (Arrow (pick_type input_bounds) (pick_type output_bounds)) }
    := option_map
         (fun v => existT
                     _
                     (projT1 v)
                     (Abs (SmartFlatTypeMapInterp2 (fun _ _ (n' : Name) => n') input_bounds (Abs_name e))
                          (projT2 v)))
         (mapf_cast (extend ctx (Abs_name e) input_bounds) (invert_Abs e)).
End language.
