Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.MapCast.
Require Import Crypto.Reflection.Named.InterpretToPHOAS.
Require Import Crypto.Reflection.Named.Compile.
Require Import Crypto.Reflection.Named.PositiveContext.
Require Import Crypto.Reflection.Named.PositiveContext.Defaults.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Reflection.Syntax.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (base_type_code_beq : base_type_code -> base_type_code -> bool)
          (base_type_code_bl_transparent : forall x y, base_type_code_beq x y = true -> x = y)
          (failb : forall var t, @Syntax.exprf base_type_code op var (Tbase t))
          {interp_base_type_bounds : base_type_code -> Type}
          (interp_op_bounds : forall src dst, op src dst -> interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst)
          (pick_typeb : forall t, interp_base_type_bounds t -> base_type_code).
  Local Notation pick_type v := (SmartFlatTypeMap pick_typeb v).
  Context (cast_op : forall t tR (opc : op t tR) args_bs,
              op (pick_type args_bs) (pick_type (interp_op_bounds t tR opc args_bs))).

  Definition MapCast {t} (e : Expr base_type_code op t)
             (input_bounds : interp_flat_type interp_base_type_bounds (domain t))
    : option { output_bounds : interp_flat_type interp_base_type_bounds (codomain t)
                               & Expr base_type_code op (Arrow (pick_type input_bounds) (pick_type output_bounds)) }
    := let Context var := PositiveContext _ _ _ base_type_code_bl_transparent in
       match option_map
               (fun e' => map_cast
                            interp_op_bounds pick_typeb cast_op
                            (BoundsContext:=Context _)
                            empty
                            e'
                            input_bounds)
               (compile (Linearize e _) (DefaultNamesFor e))
       with
       | Some (Some (existT output_bounds e'))
         => Some (existT _ output_bounds (InterpToPHOAS (Context:=Context) failb e'))
       | Some None | None => None
       end.
End language.
