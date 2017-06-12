Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Notations.

Module Export Named.
  Section language.
    Context {base_type_code : Type}
            {op : flat_type base_type_code -> flat_type base_type_code -> Type}
            {Name : Type}
            {interp_base_type : base_type_code -> Type}
            {Context : Context Name interp_base_type}
            (interp_op : forall s d, op s d -> interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d)
            (interped_op_side_conditions : forall s d, op s d -> interp_flat_type interp_base_type s -> pointed_Prop).

    Local Notation exprf := (@exprf base_type_code op Name).
    Local Notation expr := (@expr base_type_code op Name).

    Fixpoint interpf_side_conditions_gen {t} (ctx : Context) (e : exprf t)
      : option (pointed_Prop * interp_flat_type interp_base_type t)
      := match e with
         | TT => Some (trivial, tt)
         | Var t' x => option_map (fun v => (trivial, v)) (lookupb t' ctx x)
         | Op t1 tR opc args
           => match @interpf_side_conditions_gen _ ctx args with
              | Some (args_cond, argsv)
                => Some (args_cond /\ interped_op_side_conditions _ _ opc argsv, interp_op _ _ opc argsv)
              | None => None
              end
         | LetIn _ n ex _ eC
           => match @interpf_side_conditions_gen _ ctx ex with
              | Some (x_cond, x)
                => match @interpf_side_conditions_gen _ (extend ctx n x) eC with
                   | Some (c_cond, cv)
                     => Some (x_cond /\ c_cond, cv)
                   | None => None
                   end
              | None => None
              end
         | Pair _ ex _ ey
           => match @interpf_side_conditions_gen _ ctx ex, @interpf_side_conditions_gen _ ctx ey with
              | Some (x_cond, xv), Some (y_cond, yv) => Some (x_cond /\ y_cond, (xv, yv))
              | None, _ | _, None => None
              end
         end%pointed_prop.
    Definition interpf_side_conditions {t} ctx e : option pointed_Prop
      := option_map (@fst _ _) (@interpf_side_conditions_gen t ctx e).
    Definition interp_side_conditions {t} ctx (e : expr t) : interp_flat_type interp_base_type (domain t) -> option pointed_Prop
      := fun x => interpf_side_conditions (extend ctx (Abs_name e) x) (invert_Abs e).
    Definition InterpSideConditions {t} (e : expr t) : interp_flat_type interp_base_type (domain t) -> option pointed_Prop
      := interp_side_conditions empty e.
  End language.
End Named.
