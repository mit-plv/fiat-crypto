Require Import Coq.Bool.Sumbool.
Require Import Coq.FSets.FMapInterface.
Require Import Crypto.Reflection.NamedBase.Syntax.

Module FMapContextFun (E : DecidableType) (W : WSfun E).
  Section ctx.
    Context base_type_code (var : base_type_code -> Type)
            (base_type_code_beq : base_type_code -> base_type_code -> bool)
            (base_type_code_bl_transparent : forall x y, base_type_code_beq x y = true -> x = y).

    Definition var_cast {a b} (x : var a) : option (var b)
      := match Sumbool.sumbool_of_bool (base_type_code_beq a b) with
         | left pf => match base_type_code_bl_transparent _ _ pf with
                      | eq_refl => Some x
                      end
         | right _ => None
         end.
    Definition FMapContext : @Context base_type_code W.key var
      := {| ContextT := W.t { t : _ & var t };
            lookupb ctx n t
            := match W.find n ctx with
               | Some (existT t' v)
                 => var_cast v
               | None => None
               end;
            extendb ctx n t v
            := W.add n (existT _ t v) ctx;
            removeb ctx n t
            := W.remove n ctx;
            empty := W.empty _ |}.
  End ctx.
End FMapContextFun.

Module FMapContext (W : WS) := FMapContextFun W.E W.
