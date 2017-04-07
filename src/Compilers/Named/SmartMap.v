Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Named.Syntax.

Module Export Named.
  Section language.
    Context {base_type_code : Type}
            {interp_base_type : base_type_code -> Type}
            {op : flat_type base_type_code -> flat_type base_type_code -> Type}
            {Name : Type}.

    (** [SmartVar] is like [Var], except that it inserts
          pair-projections and [Pair] as necessary to handle
          [flat_type], and not just [base_type_code] *)
    Definition SmartVar {t} : interp_flat_type (fun _ => Name) t -> @exprf base_type_code op Name t
      := smart_interp_flat_map (f:=fun _ => Name) (g:=@exprf _ _ _) (fun t => Var) TT (fun A B x y => Pair x y).
  End language.
End Named.

Global Arguments SmartVar {_ _ _ _} _.
