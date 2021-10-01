Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ZRange.
Local Open Scope Z_scope.

Import API.Compilers.
Import Types.Notations.

Section Expr.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Context {ok : ok}.
  Existing Instance Types.rep.Z.
  Existing Instance Types.rep.listZ_local. (* local list representation *)
  Definition max_range : zrange := {| lower := 0; upper := 2 ^ width - 1 |}.
  Definition range_good (r : zrange) : bool := zrange_beq r max_range.

  (* for the second argument of shifts *)
  Definition width_range :=  r[0~>width-1]%zrange.

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

  (* Literal Zs or nats, and lists, do not need casts *)
  Definition cast_exempt {var t} (e : @API.expr var t)
    : bool :=
    match e with
    | (expr.Ident _ (ident.Literal base.type.Z z)) =>
      true
    | (expr.Ident _ (ident.Literal base.type.nat n)) =>
      true
    | expr.Var _ _ =>
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
    : rtype (type_Z -> type_Z -> type_Z) :=
    fun x n =>
      if literal_ltwidth n
      then expr.op bopname.slu x n
      else base_make_error _.

  Definition rtruncating_shiftl
    : rtype (type_Z -> type_Z -> type_Z -> type_Z) :=
    fun s x n =>
      if literal_eqb s width
      then if literal_ltwidth n
           then expr.op bopname.slu x n
           else make_error type_Z
      else base_make_error _.

  Definition rlnot_modulo
    : rtype (type_Z -> type_Z -> type_Z) :=
    fun x m =>
      match invert_literal m with
      | Some m => if (2^(Z.log2 m) =? m)
                  then expr.op bopname.xor
                               (if Z.log2 m =? width (* is this a good place to do this optimization? *)
                                then x
                                else expr.op bopname.and x (expr.literal (Z.ones (Z.log2 m))))
                               (expr.literal (Z.ones (Z.log2 m)))
                  else make_error type_Z
      | None => make_error type_Z
      end.

  Definition rselect
    : rtype (type_Z -> type_Z -> type_Z -> type_Z) :=
    fun c x y =>
      if literal_eqb x 0
      then if literal_eqb y (2^width - 1)
           then expr.op bopname.add (expr.literal (-1))
                        (expr.op bopname.eq c (expr.literal 0))
           else base_make_error _
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
      if literal_eqb s (2 ^ width)
      then expr.op bopname.mulhuu x y
      else base_make_error _.

  Definition is_cast_literal_ident {t} (i : ident.ident t) : bool :=
    match i with
    | ident.Literal base.type.zrange r =>
      range_good r
    | _ => false
    end.
  Definition is_cast_literal
             {var t} (e : @API.expr var t) : bool :=
    match e with
    | expr.Ident type_range i =>
      is_cast_literal_ident i
    | _ => false
    end.

  Definition is_pair_range {t} (i : ident.ident t) : bool :=
    match i with
    | ident.pair base_range base_range => true
    | _ => false
    end.
  Definition is_cast2_literal_App2
             {var t} (e : @API.expr var t) : bool :=
    match e with
    | expr.Ident (type.arrow type_range
                             (type.arrow type_range type_range2))
                 i =>
      is_pair_range i
    | _ => false
    end.
  Definition is_cast2_literal_App1
             {var t} (e : @API.expr var t) : bool :=
    match e with
    | expr.App
        type_range (type.arrow type_range type_range2)
        f r1 =>
      is_cast2_literal_App2 f && is_cast_literal r1
    | _ => false
    end.
  Definition is_cast2_literal
             {var t} (e : @API.expr var t) : bool :=
    match e with
    | expr.App type_range type_range2 f r2 =>
      is_cast2_literal_App1 f && is_cast_literal r2
    | _ => false
    end.

  Definition is_cast_ident {t} (i : ident.ident t) : bool :=
    match i with
    | ident.Z_cast => true
    | ident.Z_cast2 => true
    | _ => false
    end.

  Definition is_cast_ident_expr {var t}
             (e : @API.expr var t) : bool :=
    match e with
    | expr.Ident _ i => is_cast_ident i
    | _ => false
    end.

  Definition is_cast
             {var t} (e : @API.expr var t) : bool :=
    match e with
    | expr.App type_range (type.arrow type_Z type_Z) f r =>
      is_cast_ident_expr f && is_cast_literal r
    | expr.App type_range2 (type.arrow type_ZZ type_ZZ) f r =>
      is_cast_ident_expr f && is_cast2_literal r
    | _ => false
    end.

  (* only require cast for the argument of (App f x) if:
     - f is not a cast
     - f is not mul_high (then, x = 2^width)
     - f is not (lnot_modulo _) (then x is allowed to be 2^width)
     - f is not (nth_default ?d ?l) (i doesn't need to fit in a word) *)
  Definition require_cast_for_arg
             {var t} (e : @API.expr var t) : bool :=
    match e with
    | Zcast r => negb (range_good r)
    | Zcast2 r1 r2 =>
      negb (range_good r1 && range_good r2)
    | expr.Ident _ ident.Z_mul_high => false
    | expr.App
        _ _ (expr.Ident _ ident.Z_lnot_modulo)
        _ => false
    | expr.App
        _ _ (expr.App
               _ _ (expr.Ident _ (ident.List_nth_default _))
                      _) _ => false
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
    | ident.Z_lxor => Some (expr.op bopname.xor)
    | _ => None
    end.

  Definition translate_ident
           {t} (i : ident.ident t) : rtype t :=
    match i in ident.ident t0 return rtype t0 with
    | ident.fst _ _ => fst
    | ident.snd _ _ => snd
    | ident.Z_opp => fun x => expr.op bopname.sub (expr.literal 0) x
    | ident.List_nth_default base_Z => rnth_default
    | ident.Z_shiftr => rshiftr
    | ident.Z_shiftl => rshiftl
    | ident.Z_truncating_shiftl => rtruncating_shiftl
    | ident.Z_lnot_modulo => rlnot_modulo
    | ident.Z_zselect => rselect
    | ident.Z_mul_high => rmul_high
    | ident.Z_cast => fun _ x => x
    | ident.Z_cast2 => fun _ x => x
    | i => match translate_binop i with
           | Some x => x
           | None => make_error _
           end
    end.

  Definition translate_cast_exempt {t}
             (require_in_bounds : bool)
             (e : @API.expr ltype t) : rtype t :=
    match e in expr.expr t0 return rtype t0 with
    | (expr.Ident type_Z (ident.Literal base.type.Z z)) =>
      if require_in_bounds
      then if is_bounded_by_bool z max_range
           then expr.literal z
           else make_error _
      else expr.literal z
    | (expr.Ident type_nat (ident.Literal base.type.nat n)) =>
      expr.literal (Z.of_nat n)
    | expr.Var type_listZ x => map expr.var x
    | expr.Var type_Z x => expr.var x
    | _ => make_error _
    end.

  Fixpoint translate_expr
           (require_cast : bool)
           {t} (e : @API.expr ltype t) : rtype t :=
    if cast_exempt e
    then translate_cast_exempt require_cast e
    else if require_cast
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
