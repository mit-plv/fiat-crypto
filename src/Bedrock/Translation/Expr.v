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

  Section Casts.
    Definition max_range : zrange := {| lower := 0; upper := 2 ^ Semantics.width - 1 |}.
    Definition range_good (r : zrange) : bool := zrange_beq r max_range.

    (* checks that the expression is either a) a literal nat or Z that
       falls within the allowed range or b) an expression surrounded by
       casts that fall within the allowed range *)
    Definition has_casts {t} (e : @API.expr ltype t) : bool :=
      match e with
      | (expr.App
           type_Z type_Z
           (expr.App
              type_range (type.arrow type_Z type_Z)
              (expr.Ident _ ident.Z_cast)
              (expr.Ident _ (ident.Literal base.type.zrange r))) _) =>
        range_good r
      | (expr.App
           type_ZZ type_ZZ
           (expr.App
              type_range2 (type.arrow type_ZZ type_ZZ)
              (expr.Ident _ ident.Z_cast2)
              (expr.App
                 type_range type_range2
                 (expr.App
                    type_range (type.arrow type_range type_range2)
                    (expr.Ident _ (ident.pair _ _))
                    (expr.Ident _ (ident.Literal base.type.zrange r1)))
                 (expr.Ident _ (ident.Literal base.type.zrange r2)))) _) =>
        range_good r1 && range_good r2
      | (expr.Ident _ (ident.Literal base.type.Z z)) =>
        is_bounded_by_bool z max_range
      | (expr.App _ (type.base (base.type.list _)) _ _) =>
        (* lists get a pass *)
        true
      | _ => false
      end.
  End Casts.

  (* Special case for shiftr, because second argument needs to be < width
     instead of < 2 ^ width. This means we can only accept right-shifts by
     literals. *)
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

  (* Note: mul_high and truncating_shiftl use different expressions for
     truncation (width vs 2 ^ width). If that changes, and they use the same
     structure, put the ifs in translate_expr and don't pass s. *)
  Definition translate_truncating_binop {t} (i : ident.ident t) (s : Z)
    : option bopname :=
    match i with
    | ident.Z_truncating_shiftl =>
      if Z.eqb s Semantics.width
      then Some bopname.slu
      else None
    | ident.Z_mul_high =>
      if Z.eqb s (2 ^ Semantics.width)
      then Some bopname.mulhuu
      else None
    | _ => None
    end.

  (*
  (* TODO : remove if unused *)
  Fixpoint translate_binop2 {t} (e : @API.expr ltype (type.base t))
    : option Syntax.bopname :=
    match e with
    (* basic binary operation *)
    | (expr.App
         type_Z type_Z
         (expr.App type_Z (type.arrow type_Z type_Z)
                   (expr.Ident
                      (type.arrow type_Z (type.arrow type_Z type_Z))
                      i) x) y) =>
      translate_binop (t:=type_Z -> type_Z -> type_Z) i (x, (y, tt))
    (* truncating binary operation *)
    | (expr.App
         type_Z type_Z
         (expr.App type_Z (type.arrow type_Z type_Z)
                   (expr.App type_Z (type.arrow type_Z (type.arrow type_Z type_Z))
                             (expr.Ident _ i)
                             (expr.Ident _ (ident.Literal base.type.Z s)))
                   x) y) =>
      translate_truncating_binop i s
    | _ => None
    end.
   *)

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
        match translate_truncating_binop i s with
        | Some op => expr.op op (translate_expr true x) (translate_expr true y)
        | None => base_make_error _
        end

          (* TODO: remove if unused
      (* binary operation *)
      | expr.App type_Z type_Z
                 (expr.App type_Z (type.arrow type_Z type_Z)
                           f x) y =>
        match translate_binop2 (expr.App (expr.App f x) y) with
        | Some op => expr.op op (translate_expr true x) (translate_expr true y)
        | None => base_make_error _
        end
*)
      (* if no clauses matched the expression, return an error *)
      | _ => make_error _
      end.
End Expr.
