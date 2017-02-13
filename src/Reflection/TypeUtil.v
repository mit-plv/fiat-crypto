Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.Notations.

Local Open Scope expr_scope.

Section language.
  Context {base_type_code : Type}
          (base_type_beq : base_type_code -> base_type_code -> bool)
          (base_type_leb : base_type_code -> base_type_code -> bool).
  Local Infix "<=?" := base_type_leb : expr_scope.
  Local Infix "=?" := base_type_beq : expr_scope.

  Definition base_type_min (a b : base_type_code) : base_type_code
    := if a <=? b then a else b.
  Definition base_type_max (a b : base_type_code) : base_type_code
    := if a <=? b then b else a.
  Section gen.
    Context (join : base_type_code -> base_type_code -> base_type_code).
    Fixpoint flat_type_join {t : flat_type base_type_code}
      : interp_flat_type (fun _ => base_type_code) t -> option base_type_code
      := match t with
         | Tbase _ => fun v => Some v
         | Unit => fun _ => None
         | Prod A B
           => fun v => match @flat_type_join A (fst v), @flat_type_join B (snd v) with
                       | Some a, Some b => Some (join a b)
                       | Some a, None => Some a
                       | None, Some b => Some b
                       | None, None => None
                       end
         end.
  End gen.
  Definition flat_type_min {t} := @flat_type_join base_type_min t.
  Definition flat_type_max {t} := @flat_type_join base_type_max t.
End language.
