Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ZRange.
Local Open Scope Z_scope.

Import API.Compilers.
Import Types.Notations Types.Types.

Section Expr.
  Context {p : Types.parameters}.
  Existing Instance Types.rep.Z.
  Existing Instance Types.rep.listZ_local. (* local list representation *)
  Definition max_range : zrange := {| lower := 0; upper := 2 ^ Semantics.width - 1 |}.
  Definition range_good (r : zrange) : bool := zrange_beq r max_range.

  (* for the second argument of shifts *)
  Definition width_range :=  r[0~>Semantics.width]%zrange.

  Local Notation Zcast r :=
    (@expr.App
       _ _ _ type_range (type.arrow type_Z type_Z)
       (expr.Ident ident.Z_cast)
       (expr.Ident (@ident.Literal base.type.zrange r))).
  Local Notation Zcast2 r1 r2 :=
    (@expr.App
       _ _ _ type_range2 (type.arrow type_ZZ type_ZZ)
       (expr.Ident ident.Z_cast2)
       (@expr.App
          _ _ _ type_range type_range2
          (@expr.App
             _ _ _ type_range (type.arrow type_range type_range2)
             (expr.Ident ident.pair)
             (expr.Ident (@ident.Literal base.type.zrange r1)))
          (expr.Ident (@ident.Literal base.type.zrange r2)))).

  (* Literal Zs that are in bounds and lists do not need casts *)
  Definition cast_exempt {t} (e : @API.expr ltype t)
    : bool :=
    match e with
    | (expr.Ident _ (ident.Literal base.type.Z z)) =>
      is_bounded_by_bool z max_range
    | (expr.Ident _ (ident.Literal base.type.nat n)) =>
      true
    | expr.Var (type.base (base.type.list _)) _ =>
      true
    | _ => false 
    end.

  Definition invert_literal (x : Syntax.expr) : option Z :=
    match x with
    | expr.literal x => Some x
    | _ => None
    end.
  Definition literal_eqb x y : bool :=
    match invert_literal x with
    | Some x => Z.eqb x y
    | None => false
    end.
  Definition literal_ltwidth x :=
    match invert_literal x with
    | Some x => is_bounded_by_bool x width_range
    | None => false
    end.

  Definition rshiftr
    : rtype (type_Z -> type_Z -> type_Z) :=
    fun x n =>
      if literal_ltwidth n
      then expr.op bopname.sru x n
      else base_make_error _.

  Definition rshiftl
    : rtype (type_Z -> type_Z -> type_Z -> type_Z) :=
    fun s x n =>
      if literal_eqb s Semantics.width
      then if literal_ltwidth n
           then expr.op bopname.slu x n
           else make_error type_Z
      else base_make_error _.

  Definition rnth_default
    : rtype (type_Z -> type_listZ -> type_nat -> type_Z) :=
    fun d l i =>
      match i with
      | expr.literal i =>
        nth_default d l (Z.to_nat i)
      | _ => base_make_error _
      end.

  Definition rmul_high
    : rtype (type_Z -> type_Z -> type_Z -> type_Z) :=
    fun s x y =>
      if literal_eqb s (2 ^ Semantics.width)
      then expr.op bopname.mulhuu x y
      else base_make_error _.

  Definition is_cast
             {t} (e : @API.expr ltype t) : bool :=
    match e with
    | Zcast r => range_good r
    | Zcast2 r1 r2 => range_good r1 && range_good r2
    | _ => false
    end.

  (* only require cast for the argument of App if:
     - f is not a cast
     - f is not mul_high (bc then arg = 2^width) *)
  Definition require_cast_for_arg
             {t} (e : @API.expr ltype t) : bool :=
    match e with
    | Zcast r => negb (range_good r)
    | Zcast2 r1 r2 => 
      negb (range_good r1 && range_good r2)
    | expr.Ident _ ident.Z_mul_high => false
    | _ => true
    end.

  Definition translate_binop {t} (i : ident.ident t)
    : option (rtype t) :=
    match i with
    | ident.Z_add => Some (expr.op bopname.add)
    | ident.Z_sub => Some (expr.op bopname.sub)
    | ident.Z_mul => Some (expr.op bopname.mul)
    | ident.Z_ltz => Some (expr.op bopname.ltu)
    | ident.Z_lor => Some (expr.op bopname.or)
    | ident.Z_land => Some (expr.op bopname.and)
    | _ => None 
    end.

  Fixpoint translate_ident
           {t} (i : ident.ident t) : rtype t :=
    match i in ident.ident t0 return rtype t0 with
    | ident.Literal base.type.Z x => expr.literal x
    | ident.Literal base.type.nat x => expr.literal (Z.of_nat x)
    | ident.fst _ _ => fst
    | ident.snd _ _ => snd
    | ident.List_nth_default base_Z => rnth_default
    | ident.Z_shiftr => rshiftr
    | ident.Z_truncating_shiftl => rshiftl
    | ident.Z_mul_high => rmul_high
    | ident.Z_cast => fun _ x => x
    | ident.Z_cast2 => fun _ x => x
    | i => match translate_binop i with
           | Some x => x
           | None => make_error _
           end
    end.

  Fixpoint translate_expr
           (require_cast : bool)
           {t} (e : @API.expr ltype t) : rtype t :=
    if (require_cast && negb (cast_exempt e))%bool
    then
      match e in expr.expr t0 return rtype t0 with
      | expr.App _ _ f x =>
        if is_cast f
        then translate_expr false f (translate_expr false x)
        else make_error _
      | _ => make_error _
      end
    else
      match e in expr.expr t0 return rtype t0 with
      | expr.App _ _ f x =>
        let rc := require_cast_for_arg f in
        translate_expr false f (translate_expr rc x)
      | expr.Ident _ i => translate_ident i
      | expr.Var _ x => rtype_of_ltype _ x
      | _ => make_error _
      end.
End Expr.
