Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.MapCast.
Require Import Crypto.Reflection.Named.InterpretToPHOAS.
Require Import Crypto.Reflection.Named.Compile.
Require Import Crypto.Reflection.Named.PositiveContext.
Require Import Crypto.Reflection.Named.PositiveContext.Defaults.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Reflection.Eta.
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

  Local Notation PContext var := (PositiveContext _ var _ base_type_code_bl_transparent).

  Section MapCast.
    Context {t} (e : Expr base_type_code op t)
            (input_bounds : interp_flat_type interp_base_type_bounds (domain t)).

    Definition MapCastPreProcess
      := ExprEta (Linearize e).
    Definition MapCastCompile (e' : Expr base_type_code op (domain t -> codomain t))
      := compile (e' _) (DefaultNamesFor e').
    Definition MapCastDoCast (e' : option (Named.expr base_type_code op BinNums.positive (domain t -> codomain t)))
      := option_map
           (fun e'' => map_cast
                         (t:=Arrow (domain t) (codomain t))
                         interp_op_bounds pick_typeb cast_op
                         (BoundsContext:=PContext _)
                         empty
                         e''
                         input_bounds)
           e'.
    Definition MapCastDoInterp
               (e' : option
                       (option
                          { output_bounds : interp_flat_type interp_base_type_bounds (codomain t) &
                                           Named.expr _ _ _ (Arrow (pick_type input_bounds) (pick_type output_bounds)) }))
      : option { output_bounds : interp_flat_type interp_base_type_bounds (codomain t)
                                 & Expr base_type_code op (Arrow (pick_type input_bounds) (pick_type output_bounds)) }
      := match e' with
         | Some (Some (existT output_bounds e''))
           => Some (existT _ output_bounds (Eta.ExprEta (InterpToPHOAS (Context:=fun var => PContext var) failb e'')))
         | Some None | None => None
         end.
    Definition MapCast
      : option { output_bounds : interp_flat_type interp_base_type_bounds (codomain t)
                                 & Expr base_type_code op (Arrow (pick_type input_bounds) (pick_type output_bounds)) }
      := MapCastDoInterp (MapCastDoCast (MapCastCompile MapCastPreProcess)).
  End MapCast.
End language.
