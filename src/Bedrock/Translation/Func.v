Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Translation.Cmd.
Require Import Crypto.Bedrock.Translation.Expr.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.
Import ListNotations. Local Open Scope Z_scope.

Import API.Compilers.
Import Wf.Compilers.expr.
Import Types.Notations Types.Types.

Section Func.
  Context {p : parameters}.
  Existing Instance rep.Z.

  Section Lists.
    Fixpoint base_list_lengths t : Type :=
      match t with
      | base.type.prod a b => base_list_lengths a * base_list_lengths b
      | base_listZ => nat
      | _ => unit
      end.

    Fixpoint list_lengths t : Type :=
      match t with
      | type.base t => base_list_lengths t
      | _ => unit
      end.

    Definition load_list_item (start : Syntax.expr.expr) (i : nat)
      : Syntax.expr.expr :=
      let offset := expr.literal (Z.of_nat i * word_size_in_bytes) in
      let loc := expr.op bopname.add start offset in
      expr.load access_size.word loc.

    Definition load_list (start : Syntax.expr.expr) (len nextn : nat)
      : nat * list varname * Syntax.cmd.cmd :=
      let exprs := map (load_list_item start) (seq 0 len) in
      let varnames := map varname_gen (seq nextn len) in
      let sets := map2 cmd.set varnames exprs in
      (len, varnames, fold_right cmd.seq cmd.skip sets).

    Fixpoint load_all_lists {t : base.type} (nextn : nat)
      : base_ltype (listZ:=rep.listZ_mem) t ->
        base_list_lengths t ->
        nat * base_ltype (listZ:=rep.listZ_local) t * cmd.cmd :=
      match t with
      | base.type.prod a b =>
        fun x l =>
          let load1 :=  load_all_lists nextn (fst x) (fst l) in
          let nextn1 := (nextn + fst (fst load1))%nat in
          let load2 := load_all_lists nextn1 (snd x) (snd l) in
          let nvars := (fst (fst load1) + fst (fst load2))%nat in
          (nvars, (snd (fst load1), snd (fst load2)),
           cmd.seq (snd load1) (snd load2))
      | base_listZ =>
        fun (x : varname) (l : nat) =>
          load_list (expr.var x) l nextn
      | _ =>
        fun (x : varname) (l : unit) => (0%nat, x, cmd.skip)
      end.

    (* read lists from arguments; changes the type system from in-memory
     lists to local lists *)
    Fixpoint load_arguments {t} (nextn : nat)
      : type.for_each_lhs_of_arrow (ltype (listZ:=rep.listZ_mem)) t ->
        type.for_each_lhs_of_arrow list_lengths t ->
        nat (* number of fresh variable names used *)
        * type.for_each_lhs_of_arrow (ltype (listZ:=rep.listZ_local)) t
        * cmd.cmd :=
      match t with
      | type.base b =>
        fun (args : unit) llengths => (0%nat, args, cmd.skip)
      | type.arrow (type.base s) d =>
        fun (args : base_ltype s * type.for_each_lhs_of_arrow _ d)
            (llengths : base_list_lengths s * type.for_each_lhs_of_arrow _ d) =>
          let load_fst := load_all_lists nextn (fst args) (fst llengths) in
          let nextn' := (nextn + fst (fst load_fst))%nat in
          let load_snd := load_arguments nextn' (snd args) (snd llengths) in
          let nvars := (fst (fst load_fst) + fst (fst load_snd))%nat in
          let args' := (snd (fst load_fst), snd (fst load_snd)) in
          let cmd := cmd.seq (snd load_fst) (snd load_snd) in
          (nvars, args', cmd)
      | type.arrow _ d =>
        (* no arrow arguments allowed; insert unit type *)
        fun args llengths =>
          let load_snd := load_arguments nextn (snd args) (snd llengths) in
          (fst (fst load_snd), (tt, snd (fst load_snd)), snd load_snd)
      end.

    Definition store_list_item (start value : Syntax.expr.expr) (i : nat)
      : Syntax.cmd.cmd :=
      let offset := expr.literal (Z.of_nat i * word_size_in_bytes) in
      let loc := expr.op bopname.add start offset in
      cmd.store access_size.word loc value.

    Definition store_list
               (start : Syntax.expr.expr)
               (values : list Syntax.expr.expr)
      : Syntax.cmd.cmd :=
      let stores := map2 (store_list_item start)
                         values (seq 0 (length values)) in
      fold_right cmd.seq cmd.skip stores.

    Fixpoint store_return_values {t : base.type}
      : base_ltype (listZ:=rep.listZ_local) t ->
        base_ltype (listZ:=rep.listZ_mem) t ->
        cmd.cmd :=
      match t with
      | base.type.prod a b =>
        fun x y =>
          cmd.seq (store_return_values (fst x) (fst y))
                  (store_return_values (snd x) (snd y))
      | base_listZ =>
        (* store list in memory *)
        fun (x : list varname) (y : varname) =>
          store_list (expr.var y) (map expr.var x)
      | _ =>
        (* rename variable *)
        fun (x y : varname) => cmd.set y (expr.var x)
      end.
  End Lists.

  Fixpoint translate_func' {t} (e : @API.expr ltype t) (nextn : nat)
    : type.for_each_lhs_of_arrow ltype t -> (* args *)
      type.for_each_lhs_of_arrow list_lengths t -> (* list lengths *)
      nat * base_ltype (type.final_codomain t) * cmd.cmd :=
    match e with
    | expr.Abs (type.base s) d f =>
      (* if we have an abs, peel off one argument and recurse *)
      fun (args : base_ltype s * type.for_each_lhs_of_arrow _ d)
          (lengths : base_list_lengths s * _) =>
        translate_func' (f (fst args)) nextn (snd args) (snd lengths)
    (* if any expression that outputs a base type, call translate_cmd *)
    | expr.Ident (type.base b) idc =>
      fun (_ _:unit) => translate_cmd (expr.Ident idc) nextn
    | expr.Var (type.base b) v =>
      fun (_ _:unit) => translate_cmd (expr.Var v) nextn
    | expr.App _ (type.base b) f x =>
      fun (_ _:unit) => translate_cmd (expr.App f x) nextn
    | expr.LetIn _ (type.base b) x f =>
      fun (_ _:unit) => translate_cmd (expr.LetIn x f) nextn
    (* if the expression does not have a base type and is not an Abs,
       return garbage *)
    | _ => fun _ _ => (0%nat, dummy_base_ltype _, cmd.skip)
    end.

  (* Translates functions in 3 steps:
     1) load any lists from the arguments
     2) call translate_cmd to translate the function body and get the
        return values
     3) store the return values in the designated variables (with
        lists being written into memory)

    The reason for the load/translate/store pattern is so that, for
    the inductive proof of translate_cmd, there is no need to reason
    about the memory. Since fiat-crypto doesn't do any list
    manipulations in the middle of functions, but only uses lists in
    arguments/return values, it's a convenient formalization. *)
  Definition translate_func {t} (e : @API.expr ltype t)
             (args : type.for_each_lhs_of_arrow ltype t)
             (lengths : type.for_each_lhs_of_arrow list_lengths t)
             (rets : base_ltype (type.final_codomain t))
    : cmd.cmd :=
    (* load arguments *)
    let load_args_out := load_arguments 0%nat args lengths in
    let nextn' := fst (fst load_args_out) in
    let args' := snd (fst load_args_out) in
    let load_args_cmd := snd load_args_out in
    (* translate *)
    let out := translate_func' e nextn' args' lengths in
    (* store return values *)
    let store_rets_cmd := store_return_values (snd (fst out)) rets in
    cmd.seq (cmd.seq load_args_cmd (snd out)) store_rets_cmd.

  Section Proofs.
    Context {p_ok : @ok p}.

    (* TODO: are these all needed? *)
    Local Instance sem_ok : Semantics.parameters_ok semantics
      := semantics_ok.
    Local Instance mem_ok : Interface.map.ok Semantics.mem
      := Semantics.mem_ok.
    Local Instance varname_eqb_spec x y : BoolSpec _ _ _
      := Semantics.varname_eqb_spec x y.


  Inductive valid_func : forall {t}, @API.expr (fun _ => unit) t -> Prop :=
    | validf_Abs :
        forall {s d} f, valid_func (f tt) ->
                        valid_func (expr.Abs (s:=type.base s) (d:=d) f)
    | validf_base :
        forall {b} e, valid_cmd e -> valid_func (t:=type.base b) e
    .
  End Proofs.
End Func.