Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ZRange.
Local Open Scope Z_scope.

Import API.Compilers.
Import Wf.Compilers.expr.
Import Types.Notations Types.Types.

Section Expr.
  Context {p : Types.parameters}.
  Existing Instance Types.rep.Z.
  Existing Instance Types.rep.listZ_local. (* local list representation *)

  Section Casts.
    Definition max_range : zrange := {| lower := 0; upper := 2 ^ Semantics.width |}.
    Definition range_good (r : zrange) : bool := is_tighter_than_bool r max_range.

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
      (* Z_mul_split : compute high and low separately and assign to two
         different variables *)
      (* TODO : don't duplicate argument expressions *)
      | (expr.App
           type_Z type_ZZ
           (expr.App type_Z (type.arrow type_Z type_ZZ)
                     (expr.App type_Z (type.arrow type_Z (type.arrow type_Z type_ZZ))
                               (expr.Ident _ ident.Z_mul_split)
                               (expr.Ident _ (ident.Literal base.type.Z s)))
                     x) y) =>
        if Z.eqb s maxint
        then
          let low := Syntax.expr.op
                       Syntax.bopname.mul
                       (translate_expr true x) (translate_expr true y) in
          let high := Syntax.expr.op
                        Syntax.bopname.mulhuu
                        (translate_expr true x) (translate_expr true y) in
          (low, high)
        else base_make_error _
      (* Z_add -> bopname.add *)
      | (expr.App
         type_Z type_Z
         (expr.App type_Z (type.arrow type_Z type_Z)
                   (expr.Ident _ ident.Z_add) x) y) =>
      Syntax.expr.op Syntax.bopname.add (translate_expr true x) (translate_expr true y)
    (* Z_mul -> bopname.mul *)
    | (expr.App
         type_Z type_Z
         (expr.App type_Z (type.arrow type_Z type_Z)
                   (expr.Ident _ ident.Z_mul) x) y) =>
      Syntax.expr.op Syntax.bopname.mul (translate_expr true x) (translate_expr true y)
    (* Z_land -> bopname.and *)
    | (expr.App
         type_Z type_Z
         (expr.App type_Z (type.arrow type_Z type_Z)
                   (expr.Ident _ ident.Z_land) x) y) =>
      Syntax.expr.op Syntax.bopname.and (translate_expr true x) (translate_expr true y)
    (* Z_lor -> bopname.or *)
    | (expr.App
         type_Z type_Z
         (expr.App type_Z (type.arrow type_Z type_Z)
                   (expr.Ident _ ident.Z_lor) x) y) =>
      Syntax.expr.op Syntax.bopname.or (translate_expr true x) (translate_expr true y)
    (* Z_shiftr -> bopname.sru *)
    | (expr.App
         type_Z type_Z
         (expr.App type_Z (type.arrow type_Z type_Z)
                   (expr.Ident _ ident.Z_shiftr) x) y) =>
      Syntax.expr.op Syntax.bopname.sru (translate_expr true x) (translate_expr true y)
    (* Z_truncating_shiftl : convert to bopname.slu if the truncation matches *)
    | (expr.App
         type_Z type_Z
         (expr.App type_Z (type.arrow type_Z type_Z)
                   (expr.App type_Z (type.arrow type_Z (type.arrow type_Z type_Z))
                             (expr.Ident _ ident.Z_truncating_shiftl)
                             (expr.Ident _ (ident.Literal base.type.Z s)))
                   x) y) =>
      if Z.eqb s Semantics.width
      then Syntax.expr.op Syntax.bopname.slu (translate_expr true x) (translate_expr true y)
      else base_make_error _
    (* fst : since the [rtype] of a product type is a tuple, simply use Coq's [fst] *)
    | (expr.App
         (type.base (base.type.prod (base.type.type_base base.type.Z) _)) type_Z
         (expr.Ident _ (ident.fst (base.type.type_base base.type.Z) _))
         x) =>
      fst (translate_expr false x)
    (* snd : since the [rtype] of a product type is a tuple, simply Coq's [snd] *)
    | (expr.App
         (type.base (base.type.prod _ (base.type.type_base base.type.Z))) type_Z
         (expr.Ident _ (ident.snd _ (base.type.type_base base.type.Z)))
         x) =>
      snd (translate_expr false x)
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
      let l : list Syntax.varname := l in
      let i : nat := i in
      let d : Syntax.expr.expr := translate_expr true d in
      nth_default d (map Syntax.expr.var l) i
    (* Literal (Z) -> Syntax.expr.literal *)
    | expr.Ident type_Z (ident.Literal base.type.Z x) =>
      Syntax.expr.literal x
    (* Var : use rtype_of_ltype to convert the expression *)
    | expr.Var (type.base _) x => rtype_of_ltype x
    (* if no clauses matched the expression, return an error *)
    | _ => make_error _
    end.

  Section Proofs.
    Context {p_ok : @ok p}.

    (* TODO: are these all needed? *)
    Local Instance sem_ok : Semantics.parameters_ok semantics
      := semantics_ok.
    Local Instance mem_ok : Interface.map.ok Semantics.mem
      := Semantics.mem_ok.
    Local Instance varname_eqb_spec x y : BoolSpec _ _ _
      := Semantics.varname_eqb_spec x y.

    Inductive valid_expr
      : forall {t},
        bool (* require_casts *) ->
        @API.expr (fun _ => unit) t -> Prop :=
    | valid_cast1 :
        forall rc r x,
          valid_expr false x ->
          range_good r = true ->
          valid_expr (t:=type_Z) rc
                           (expr.App
                              (expr.App (expr.Ident ident.Z_cast)
                                        (expr.Ident (ident.Literal (t:=base.type.zrange) r))) x)
    | valid_cast2 :
        forall (rc : bool) r1 r2 x,
          valid_expr false x ->
          range_good r1 = true ->
          range_good r2 = true ->
          valid_expr (t:=type_ZZ) rc
                           (expr.App
                              (expr.App (expr.Ident ident.Z_cast2)
                                        (expr.App
                                           (expr.App
                                              (expr.Ident ident.pair)
                                              (expr.Ident (ident.Literal (t:=base.type.zrange) r1)))
                                           (expr.Ident (ident.Literal (t:=base.type.zrange) r2)))) x)
    | valid_literalz :
        forall rc z,
          (* either bounded or casts not required *)
          (is_bounded_by_bool z max_range || negb rc = true)%bool ->
          valid_expr (t:=type_Z) rc (expr.Ident (ident.Literal (t:=base.type.Z) z))
    | valid_add :
        forall x y,
          valid_expr true x ->
          valid_expr true y ->
          valid_expr false (expr.App (expr.App (expr.Ident ident.Z_add) x) y)
    | valid_nth_default :
        forall rc d l i,
          valid_expr true d ->
          valid_expr
            (t:=type_Z)
            rc (* casts not required, since a list of vars must be already cast *)
            (expr.App (expr.App (expr.App (expr.Ident ident.List_nth_default) d)
                                (expr.Var (t:=type_listZ) l))
            (expr.Ident (ident.Literal i)))
    | valid_var :
        forall t v, valid_expr (t:=type.base t) false (expr.Var v)
    (* TODO: need many more cases here, one for each in translate_expr --
       this is just a small set to test proof strategies *)
    .

    (* 3-way equivalence (for single elements of the context list G
       from wf3 preconditions) *)
    Definition equiv3 {var1}
               (locals : Interface.map.rep (map:=Semantics.locals))
               (x : {t : API.type
                         & (var1 t * API.interp_type t * ltype t)%type})
      : Prop :=
      match x with
      | existT (type.base b) (w, x, y) =>
        locally_equivalent x (rtype_of_ltype y) locals
      | existT (type.arrow _ _) _ => False (* no functions allowed *)
      end.

    Definition context_equiv {var1} G locals
      : Prop := Forall (equiv3 (var1:= var1) locals) G.

    Lemma translate_expr_correct {t}
          (* three exprs, representing the same Expr with different vars *)
          (e1 : @API.expr (fun _ => unit) (type.base t))
          (e2 : @API.expr API.interp_type (type.base t))
          (e3 : @API.expr ltype (type.base t))
          (require_cast : bool) :
      (* e1 is a valid input to translate_carries_correct *)
      valid_expr require_cast e1 ->
      forall G locals,
        wf3 G e1 e2 e3 ->
        let out := translate_expr require_cast e3 in
        context_equiv G locals ->
        locally_equivalent (API.interp e2) out locals.
    Admitted.
  End Proofs.
End Expr.