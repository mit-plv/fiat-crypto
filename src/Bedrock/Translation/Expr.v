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

  Local Notation App_Zcast r x :=
    (@expr.App
       _ _ _ type_Z type_Z
         (@expr.App
            _ _ _ type_range (type.arrow type_Z type_Z)
            (expr.Ident ident.Z_cast)
            (expr.Ident (@ident.Literal base.type.zrange r))) x).
  Local Notation App_Zcast2 r1 r2 x :=
    (@expr.App
       _ _ _ type_ZZ type_ZZ
       (@expr.App
          _ _ _ type_range2 (type.arrow type_ZZ type_ZZ)
          (expr.Ident ident.Z_cast2)
          (@expr.App
             _ _ _ type_range type_range2
             (@expr.App
                _ _ _ type_range (type.arrow type_range type_range2)
                (expr.Ident ident.pair)
                (expr.Ident (@ident.Literal base.type.zrange r1)))
             (expr.Ident (@ident.Literal base.type.zrange r2)))) x).

  Section Casts.
    (* checks that the expression is either a) a literal nat or Z that
       falls within the allowed range or b) an expression surrounded by
       casts that fall within the allowed range *)
    Definition has_casts {t} (e : @API.expr ltype t) : bool :=
      match e with
      | App_Zcast r x => range_good r
      | App_Zcast2 r1 r2 x => range_good r1 && range_good r2
      | (expr.Ident _ (ident.Literal base.type.Z z)) =>
        is_bounded_by_bool z max_range
      | (expr.App _ (type.base (base.type.list _)) _ _) =>
        (* lists get a pass *)
        true
      | _ => false
      end.
  End Casts.

  Definition translate_binop {t}
             (i : ident.ident t)
    :  option bopname :=
    match i with
    | ident.Z_add =>  Some bopname.add
    | ident.Z_sub =>  Some bopname.sub
    | ident.Z_mul =>  Some bopname.mul
    | ident.Z_ltz =>  Some bopname.ltu
    | ident.Z_land => Some bopname.and
    | ident.Z_lor =>  Some bopname.or
    | _ => None
    end.

  Definition translate_mul_high {t} (i : ident.ident t) (s : Z)
    : option bopname :=
    match i with
    | ident.Z_mul_high =>
      if Z.eqb s (2 ^ Semantics.width)
      then Some bopname.mulhuu
      else None
    | _ => None
    end.

  (* second argument is required to be < width *)
  Definition translate_shiftl {var t}
             (i : ident.ident t) (s : Z)
    : (@API.expr var type_Z) -> option bopname :=
    match i with
    | ident.Z_truncating_shiftl =>
      fun n =>
        match n return option bopname with
        | expr.Ident _ (ident.Literal base.type.Z z) =>
          if is_bounded_by_bool z r[0~>Semantics.width]%zrange
          then if Z.eqb s Semantics.width
               then Some bopname.slu
               else None
          else None
        | _ => None
        end
    | _ => fun _ => None
    end.

  (* second argument is required to be < width *)
  Definition translate_shiftr {var t}
             (i : ident.ident t)
    : (@API.expr var type_Z) -> option bopname :=
    match i with
    | ident.Z_shiftr =>
      fun n =>
        match n return option bopname with
        | expr.Ident _ (ident.Literal base.type.Z z) =>
          if is_bounded_by_bool z r[0~>Semantics.width]%zrange
          then Some bopname.sru
          else None
        | _ => None
        end
    | _ => fun _ => None
    end.

  (* Translate an API.expr (without LetIn statements) into a bedrock2
     Syntax.expr *)
  Fixpoint translate_expr
           (require_cast : bool)
           {t} (e : @API.expr ltype (type.base t)) : base_rtype t :=
    if (require_cast && negb (has_casts e))%bool
    then base_make_error _
    else
      match e in expr.expr t0 return rtype t0 with
      (* Z_cast : clear casts because has_casts already checked for them *)
      | (expr.App
           type_Z type_Z
           (expr.App
              type_range (type.arrow type_Z type_Z)
              (expr.Ident _ ident.Z_cast) _) x) =>
        translate_expr false x
      (* Z_cast2 : clear casts because has_casts already checked for them *)
      | (expr.App
           type_ZZ type_ZZ
           (expr.App
              type_range2 (type.arrow type_ZZ type_ZZ)
              (expr.Ident _ ident.Z_cast2) _) x) => translate_expr false x
                                                                   (*
      (* fst : since the [rtype] of a product type is a tuple, simply use Coq's [fst] *)
      | (expr.App
           (type.base (base.type.prod base_Z _)) type_Z
           (expr.Ident _ (ident.fst base_Z _))
           x) =>
        fst (translate_expr true x)
      (* snd : since the [rtype] of a product type is a tuple, simply Coq's [snd] *)
      | (expr.App
           (type.base (base.type.prod _ base_Z)) type_Z
           (expr.Ident _ (ident.snd _ base_Z))
           x) =>
        snd (translate_expr true x)
*)
      (* List_nth_default : lists are represented by lists of variables, so we
         can perform the nth_default inline. This saves us from having to
         prove that all indexing into lists is in-bounds. *)
      | (expr.App
           type_nat type_Z
           (expr.App
              type_listZ _
              (expr.App type_Z _
                        (expr.Ident _ (ident.List_nth_default _))
                        d) (expr.Var type_listZ l))
           (expr.Ident _ (ident.Literal base.type.nat i))) =>
        let l : list String.string := l in
        let i : nat := i in
        let d : Syntax.expr.expr := translate_expr true d in
        nth_default d (map expr.var l) i
      (* Literal (Z) -> Syntax.expr.literal *)
      | expr.Ident type_Z (ident.Literal base.type.Z x) =>
        expr.literal x
      (* Var : use rtype_of_ltype to convert the expression *)
                     (*
      | expr.Var (type.base _) x => base_rtype_of_ltype x
      (* basic binary operation *)
      | (expr.App
           type_Z type_Z
           (expr.App type_Z (type.arrow type_Z type_Z)
                     (expr.Ident (type.arrow type_Z (type.arrow type_Z type_Z)) i) x) y) =>
        match translate_binop i with
        | Some op => expr.op op (translate_expr true x) (translate_expr true y)
        | None =>
          match translate_shiftr i y with
          | Some op => expr.op op (translate_expr true x) (translate_expr true y)
          | None => base_make_error _
          end
        end
      (* truncating binary operation *)
      | (expr.App
           type_Z type_Z
           (expr.App type_Z (type.arrow type_Z type_Z)
                     (expr.App type_Z (type.arrow type_Z (type.arrow type_Z type_Z))
                               (expr.Ident _ i)
                               (expr.Ident _ (ident.Literal base.type.Z s)))
                     x) y) =>
        match translate_mul_high i s with
        | Some op => expr.op op (translate_expr true x)
                             (translate_expr true y)
        | None => match translate_shiftl i s y with
                  | Some op =>
                    expr.op op (translate_expr true x)
                            (translate_expr true y)
                  | None => base_make_error _
                  end
        end
*)
      (* if no clauses matched the expression, return an error *)
      | _ => make_error _
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
      else make_error type_Z.

  Definition rmul_high
    : rtype (type_Z -> type_Z -> type_Z -> type_Z) :=
    fun s x y =>
      if literal_eqb s (2 ^ Semantics.width)
      then expr.op bopname.mulhuu x y
      else make_error type_Z. 

  Definition rshiftl
    : rtype (type_Z -> type_Z -> type_Z -> type_Z) :=
    fun s x n =>
      if literal_eqb s Semantics.width
      then if literal_ltwidth n
           then expr.op bopname.slu x n
           else make_error type_Z
      else make_error type_Z.

  About expr.Ident.
  Print invert_expr.

  Compute (rtype (type_nat)).
  Fixpoint translate_ident
           {t} (i : ident.ident t) : rtype t :=
    match i in ident.ident t0 return rtype t0 with
    | ident.Literal base.type.Z x => expr.literal x
    | ident.Literal base.type.nat x => expr.literal (Z.of_nat x)
    | ident.fst _ _ => fst
    | ident.snd _ _ => snd
    | ident.Z_shiftr => rshiftr
    | ident.Z_mul_high => rmul_high
    | ident.Z_truncating_shiftl => rshiftl
    | ident.Z_add => expr.op bopname.add
    | ident.Z_sub => expr.op bopname.sub
    | ident.Z_mul => expr.op bopname.mul
    | ident.Z_ltz => expr.op bopname.ltu
    | ident.Z_lor => expr.op bopname.or
    | ident.Z_land => expr.op bopname.and
    | _ => make_error _
    end.
  
  (*
    | ident.List_nth_default =>
      fun d l i =>
        nth_default d l i
        
      | (expr.App
           type_nat type_Z
           (expr.App
              type_listZ _
              (expr.App type_Z _
                        (expr.Ident _ (ident.List_nth_default _))
                        d) (expr.Var type_listZ l))
           (expr.Ident _ (ident.Literal base.type.nat i))) =>
        let l : list String.string := l in
        let i : nat := i in
        let d : Syntax.expr.expr := translate_expr true d in
        nth_default d (map expr.var l) i
    | _ => make_error _
    end.
*)

  (* Literal Zs that are in bounds and lists do not need casts *)
  Definition cast_exempt {t} (e : @API.expr ltype t)
    : bool :=
    match e with
    | (expr.Ident _ (ident.Literal base.type.Z z)) =>
      is_bounded_by_bool z max_range
    | (expr.App _ (type.base (base.type.list _)) _ _) =>
      true
    | _ => false 
    end.

  (* remove outermost casts, returning None if no casts to the correct ranges
     are found *)
  Definition strip_casts {t}
    : @API.expr ltype t -> option (@API.expr ltype t) :=
    match t as t0 return
          expr.expr t0 -> option (expr.expr t0) with
    | type_Z =>
      fun e =>
        match invert_expr.invert_App_Z_cast e with
        | Some (r, x) =>
          if range_good r then Some x else None
        | None => None
        end
    | type_ZZ =>
      fun e =>
        match invert_expr.invert_App_Z_cast2 e with
        | Some (r1, r2, e) =>
          if (range_good r1 && range_good r2)%bool
          then Some e else None
        | None => None
        end
    | _ => fun e => if cast_exempt e then Some e else None
    end.
  Definition is_cast {t} (e : @API.expr ltype t) : bool :=
    match invert_expr.invert_Z_cast e with
    | Some r => range_good r
    | None =>
        match invert_expr.invert_Z_cast2 e with
        | Some (r1, r2) =>
          (range_good r1 && range_good r2)%bool
        | None => false
        end
    end.

  Fixpoint translate_expr2
           (require_cast : bool)
           {t} (e : @API.expr ltype t) : rtype t :=
    if (require_cast && negb (cast_exempt e))%bool
    then match e with
         | expr.App type_Z type_Z f x =>
           if is_cast f
           then translate_expr2 false x
           else make_error _
         | expr.App type_ZZ type_ZZ f x =>
           if is_cast f
           then translate_expr2 false x
           else make_error _
         | _ => make_error _
         end
    else
      match e in expr.expr t0 return rtype t0 with
      (* strip casts; has_casts already checked if needed *)
      | expr.App _ _ f x =>
        translate_expr2 false f (translate_expr2 true x)
      | expr.Ident _ i => translate_ident i
      (* Var : use rtype_of_ltype to convert the expression *)
      | expr.Var _ x => rtype_of_ltype _ x
      (* if no clauses matched the expression, return an error *)
      | _ => make_error _
      end.
  Time Print translate_expr2.
  Time Print translate_expr.
  (* version  emacs  make    proofs-emacs  proofs-make
     orig     0.78s  0.96s   100.79s       101.01s
  *)
End Expr.
