Require Import Coq.Bool.Sumbool.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.TypeUtil.
Require Import Crypto.Util.Notations.

Local Open Scope expr_scope.
Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (base_type_beq : base_type_code -> base_type_code -> bool)
          (base_type_bl_transparent : forall x y, base_type_beq x y = true -> x = y)
          (Cast : forall var A A', exprf base_type_code op (var:=var) (Tbase A) -> exprf base_type_code op (var:=var) (Tbase A')).

  Local Notation exprf := (@exprf base_type_code op).

  Definition SmartCast_base {var A A'} (x : exprf (var:=var) (Tbase A))
    : exprf (var:=var) (Tbase A')
    := match sumbool_of_bool (base_type_beq A A') with
       | left pf => match base_type_bl_transparent _ _ pf with
                    | eq_refl => x
                    end
       | right _ => Cast _ _ A' x
       end.

  Fixpoint SmartCast {var} A B
    : option (interp_flat_type var A -> exprf (var:=var) B)
    := match A, B return option (interp_flat_type var A -> exprf (var:=var) B) with
       | Tbase A, Tbase B => Some (fun v => SmartCast_base (Var (var:=var) v))
       | Prod A0 A1, Prod B0 B1
         => match @SmartCast _ A0 B0, @SmartCast _ A1 B1 with
            | Some f, Some g => Some (fun xy => Pair (f (fst xy)) (g (snd xy)))
            | _, _ => None
            end
       | Unit, Unit => Some (fun _ => TT)
       | Tbase _, _
       | Prod _ _, _
       | Unit, _
         => None
       end.
End language.
