Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Translation.Expr.
Require Import Crypto.Language.API.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

(* for [eauto with lia] *)
Require Import Crypto.BoundsPipeline.

Import API.Compilers.
Import Types.Notations.

Section Cmd.
  Context
    {width BW word mem locals env ext_spec varname_gen add_carryx sub_borrowx error}
    `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen add_carryx sub_borrowx error}.
  Existing Instance Types.rep.Z.
  Existing Instance Types.rep.listZ_local. (* local list representation *)

  Fixpoint assign_list (nextn : nat) (xs : base_rtype base_listZ)
    : nat * base_ltype base_listZ * Syntax.cmd.cmd :=
    match xs with
      | [] => (0%nat, [], Syntax.cmd.skip)
      | x :: xs' =>
        let rec := assign_list (S nextn) xs' in
        (S (fst (fst rec)), varname_gen nextn :: snd (fst rec),
         Syntax.cmd.seq (Syntax.cmd.set (varname_gen nextn) x) (snd rec))
    end.

  Fixpoint assign_base {t : base.type} (nextn : nat)
    : base_rtype t -> (nat * base_ltype t * Syntax.cmd.cmd) :=
    match t with
    | base.type.prod a b =>
      fun rhs =>
        let assign1 := assign_base nextn (fst rhs) in
        let assign2 := assign_base (nextn + fst (fst assign1)) (snd rhs) in
        ((fst (fst assign1) + fst (fst assign2))%nat,
         (snd (fst assign1), snd (fst assign2)),
         Syntax.cmd.seq (snd assign1) (snd assign2))
    | base.type.list (base.type.type_base base.type.Z) =>
      assign_list nextn
    | base.type.list _ | base.type.option _ | base.type.unit
    | base.type.type_base _ =>
      fun rhs =>
        let v := varname_gen nextn in
        (1%nat, v, Syntax.cmd.set v rhs)
    end.

  Definition assign {t} (nextn : nat)
    : rtype t -> (nat * ltype t * Syntax.cmd.cmd) :=
    match t as t0 return
          rtype t0 -> nat * ltype t0 * _ with
    | type.base b => assign_base (t:=b) nextn
    | _ =>
      fun _ =>
        (0%nat, dummy_ltype _, Syntax.cmd.skip)
    end.

  Definition translate_ident2_for_cmd {a b c} (i : ident (a -> b -> c))
    : ltype a -> ltype b -> option (ltype c)
    := match i in ident t return ltype (type.domain t) -> ltype (type.domain (type.codomain t)) -> option (ltype (type.codomain (type.codomain t))) with
       | ident.cons base_Z => fun x xs => Some (x :: xs)
       | ident.pair _ _ => fun x y => Some (x, y)
       | _ => fun _ _ => None
       end.

  (* TODO: move to rewriter/src/Rewriter/Language/Language.v along with
     invert_AppIdent2_cps and friends. *)
  Definition invert_AppIdent3_cps
             {base_type : Type} {ident var : type base_type -> Type}
             {t Q R S} (e : expr (ident:=ident) (var:=var) t)
             (F1 : forall t, expr (ident:=ident) (var:=var) t -> Q t)
             (F2 : forall t, expr (ident:=ident) (var:=var) t -> R t)
             (F3 : forall t, expr (ident:=ident) (var:=var) t -> S t)
    : option {argtypes : type base_type * type base_type * type base_type
                         & (ident (fst (fst argtypes)
                                   -> snd (fst argtypes)
                                   -> snd argtypes -> t)%etype
                            * Q (fst (fst argtypes))
                            * R (snd (fst argtypes))
                            * S (snd argtypes))%type }
    :=
      (e <- invert_expr.invert_App_cps
             e (fun _ _ e => invert_expr.invert_AppIdent2_cps e F1 F2) F3;
      let '(existT t3 (e,x3)) := e in
      e <- e;
      let '(existT t12 (f, x1, x2)) := e in
      Some (existT _ (t12, t3) (f, x1, x2, x3)))%option.
  Definition invert_AppIdent4_cps
             {base_type : Type} {ident var : type base_type -> Type}
             {t Q R S T} (e : expr (ident:=ident) (var:=var) t)
             (F1 : forall t, expr (ident:=ident) (var:=var) t -> Q t)
             (F2 : forall t, expr (ident:=ident) (var:=var) t -> R t)
             (F3 : forall t, expr (ident:=ident) (var:=var) t -> S t)
             (F4 : forall t, expr (ident:=ident) (var:=var) t -> T t)
    : option {argtypes : type base_type * type base_type * type base_type * type base_type
                         & (ident (fst (fst (fst argtypes))
                                   -> snd (fst (fst argtypes))
                                   -> snd (fst argtypes)
                                   -> snd argtypes
                                   -> t)%etype
                            * Q (fst (fst (fst argtypes)))
                            * R (snd (fst (fst argtypes)))
                            * S (snd (fst argtypes))
                            * T (snd argtypes))%type }
    :=
      (e <- invert_expr.invert_App_cps
             e (fun _ _ e =>
                  invert_expr.invert_App_cps
                    e (fun _ _ e =>
                         invert_expr.invert_AppIdent2_cps e F1 F2) F3) F4;
      let '(existT t4 (e,x4)) := e in
      e <- e;
      let '(existT t3 (e,x3)) := e in
      e <- e;
      let '(existT t12 (f, x1, x2)) := e in
      Some (existT _ (t12, t3, t4) (f, x1, x2, x3, x4)))%option.

  Check translate_expr.
  (* End of day braindump:

     - current prototype is probably shortest path to something that works for 3-4 functions
     - downsides: breaks abstraction a bit to handle the details of casts etc. at the Cmd level
     - general work to do:
       - adapt valid_cmd to special-case the set of separate functions with their casts
       - create specs for them and fix proofs
       - adapt the computable version of valid_cmd to match and fix equivalence proof
       - add 4-argument functions
       - adjust pipeline args in Defaults.v as needed

    Alternatives:
      1. Unify translate_expr and translate_cmd layers
         - Cmd handles variable naming and list/tuple assembly
         - variable naming uses a counter -> introduces state for rec calls
         - Expr handles most complicated logic; having no rec state is nice
      2. Make translate_expr return Syntax.cmd.cmd but not handle the counter
         - have translate_cmd look ahead to see if the expression is a special function
         - if so, translate_cmd passes enough variable names to translate_expr to bind result
         - translate_expr fails if wrong number of names
         - downsides: extra argument to trace through translate_expr, proof complexity


    Example add_get_carry occurrence for reference:

                    (eApp
                      (eApp (eIdent Compilers.ident_Z_cast2)
                         (eApp
                            (eApp (eIdent Compilers.ident_pair)
                               (eIdent
                                  (Compilers.ident_Literal
                                     {| ZRange.lower := 0; ZRange.upper := 4294967295 |})))
                            (eIdent (Compilers.ident_Literal {| ZRange.lower := 0; ZRange.upper := 1 |}))))
                      (eApp
                         (eApp
                            (eApp (eIdent Compilers.ident_Z_add_get_carry)
                               (eIdent (Compilers.ident_Literal 4294967296%Z)))
                            (eApp
                               (eApp (eIdent Compilers.ident_Z_cast)
                                  (eIdent
                                     (Compilers.ident_Literal
                                        {| ZRange.lower := 0; ZRange.upper := 4294967295 |})))
                               (eApp
                                  (eApp
                                     (eApp (eIdent Compilers.ident_List_nth_default)
                                        (eIdent (Compilers.ident_Literal 0%Z))) 
                                     (eVar x0)) (eIdent (Compilers.ident_Literal 0)))))
                         (eApp
                            (eApp (eIdent Compilers.ident_Z_cast)
                               (eIdent
                                  (Compilers.ident_Literal
                                     {| ZRange.lower := 0; ZRange.upper := 4294967295 |})))
                            (eApp
                               (eApp
                                  (eApp (eIdent Compilers.ident_List_nth_default)
                                     (eIdent (Compilers.ident_Literal 0%Z))) (eVar x1))
                               (eIdent (Compilers.ident_Literal 0))))))
   *)

  (* Translate 3-argument special functions. *)
  Definition translate_ident_special3 {var a b c d} (i : ident (a -> b -> c -> d)) (nextn : nat)
    : API.expr (var:=var) a -> API.expr b -> API.expr c -> option (nat * ltype d * Syntax.cmd.cmd)
    := match i in ident t return
             API.expr (type.domain t) ->
             API.expr (type.domain (type.codomain t)) ->
             API.expr (type.domain (type.codomain (type.codomain t))) ->
             option (nat
                     * ltype (type.codomain (type.codomain (type.codomain t)))
                     * Syntax.cmd.cmd) with
       | ident.Z_add_get_carry =>
         fun s x y =>
           (s <- invert_expr.invert_Literal s;
           let x := translate_expr true x in
           let y := translate_expr true y in
           if s =? 2 ^ width
           then
             let sum := varname_gen nextn in
             let carry := varname_gen (S nextn) in
             Some (2%nat, (sum,carry), Syntax.cmd.call [sum;carry] add_carryx [x; y; Syntax.expr.literal 0])
           else None)%option
       | ident.Z_sub_get_borrow =>
         fun s x y =>
           (s <- invert_expr.invert_Literal s;
           let x := translate_expr true x in
           let y := translate_expr true y in
           if s =? 2 ^ width
           then
             let diff := varname_gen nextn in
             let borrow := varname_gen (S nextn) in
             Some (2%nat, (diff, borrow), Syntax.cmd.call [diff;borrow] sub_borrowx [x; y; Syntax.expr.literal 0])
           else None)%option
       | _ => fun _ _ _ => None
       end.

  (* Translates 3-argument special operations or returns None. *)
  Definition translate_if_special3
           {t} (e : @API.expr ltype t) (nextn : nat)
    : option (nat * ltype t * Syntax.cmd.cmd)
    := (ixyz <- invert_AppIdent3_cps e (fun _ x => x) (fun _ x => x) (fun _ x => x);
       let '(existT _ (i, x, y, z)) := ixyz in
       translate_ident_special3 i nextn x y z)%option.

  Fixpoint range_base_good {t} : Language.Compilers.base.interp (fun _ => ZRange.zrange) t -> bool :=
    match t as t0 return Language.Compilers.base.interp (base:=Compilers.base) (fun _ => ZRange.zrange) t0 -> bool with
    | base.type.type_base t => range_good (width:=width)
    | base.type.prod A B => fun x => (range_base_good (fst x) && range_base_good (snd x))%bool
    | _ => fun x => false
    end.
  Definition range_type_good {t}
    : type.interp (Language.Compilers.base.interp (fun _ => ZRange.zrange)) t -> bool :=
    match t with
    | type.base b => range_base_good
    | _ => fun x => false
    end.

  Definition translate_if_special_function
             {t} (e : @API.expr ltype t) (nextn : nat)
    : option (nat * ltype t * Syntax.cmd.cmd) :=
    (* Expect an outer cast and strip it off. *)
    (rx <- invert_expr.invert_App_cast e;
    if range_type_good (fst rx)
    then
      (* Translate the rest of the function. *)
      translate_if_special3 (snd rx) nextn
    else None)%option.

  Fixpoint translate_cmd
           {t} (e : @API.expr ltype t) (nextn : nat)
    : nat (* number of variable names used *)
      * ltype t (* variables in which return values are stored *)
      * Syntax.cmd.cmd (* actual program *) :=
    match e in expr.expr t0
          return (nat * ltype t0 * Syntax.cmd.cmd) with
    | expr.LetIn (type.base t1) (type.base t2) x f =>
      (* Special handling for functions that should result in calls to bedrock2
         functions, e.g. add_carryx. *)
      let result_if_special := translate_if_special_function (t:=type.base t1) x nextn in
      let trx := match result_if_special with
                 | Some res => res
                 | None => assign nextn (translate_expr true x)
                 end in
      let trf := translate_cmd (f (snd (fst trx))) (nextn + fst (fst trx)) in
      ((fst (fst trx) + fst (fst trf))%nat,
       snd (fst trf),
       Syntax.cmd.seq (snd trx) (snd trf))
    | expr.App _ _ _ _ as e
      =>
      (* Special handling for `pair` and `cons` operations, which need to
         recursively call `translate_cmd` on their arguments; this routine
         returns `None` for any other identifiers. *)
      let result_if_ident2
          := (ixy <- invert_expr.invert_AppIdent2_cps e (@translate_cmd) (@translate_cmd);
             let '(existT _ (i, translate_cmd_x, translate_cmd_y)) := ixy in
             let trx := translate_cmd_x nextn in
             let try := translate_cmd_y (nextn + fst (fst trx))%nat in
             vars <- translate_ident2_for_cmd i (snd (fst trx)) (snd (fst try));
             Some ((fst (fst trx) + fst (fst try))%nat,
                   vars,
                   Syntax.cmd.seq (snd trx) (snd try)))%option in
      match result_if_ident2 with
      | Some res => res
      | None =>
        let v := translate_expr true e in
        assign nextn v
      end
    | expr.Ident type_listZ (ident.nil _) =>
      (0%nat, [], Syntax.cmd.skip)
    | expr.Ident _ i =>
      let v := translate_expr true (expr.Ident i) in
      assign nextn v
    | expr.Var _ v =>
      let v := translate_expr true (expr.Var v) in
      assign nextn v
    | _ => (0%nat, dummy_ltype _, Syntax.cmd.skip)
    end.
End Cmd.
