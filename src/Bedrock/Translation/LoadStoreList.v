Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.
Import ListNotations. Local Open Scope Z_scope.

Import API.Compilers.
Import Types.Notations Types.Types.

(* For proofs, it's ideal to assume that at the "cmd" level of abstraction, the
   memory doesn't change. This is actually true for fiat-crypto functions, which
   follow a pattern in which they read all their from input lists, then only deal
   with local variables until they store their results in output lists.

   Therefore, at the "func" level of abstraction, we first read the data from
   memory and then pass the local variables to the "cmd" level. The "cmd" level
   then returns local variables which we store. This file handles the
   loading/storing part of that process. *)
Section Lists.
  Context {p : parameters}.
  Existing Instance rep.Z.
  Local Notation bedrock_func := (string * (list string * list string * cmd))%type.

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
    : nat * list string * Syntax.cmd.cmd :=
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
      fun (x : string) (l : nat) =>
        load_list (expr.var x) l nextn
    | _ =>
      fun (x : string) (l : unit) => (0%nat, x, cmd.skip)
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
                       values (seq 0 (Datatypes.length values)) in
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
      fun (x : list string) (y : string) =>
        store_list (expr.var y) (map expr.var x)
    | _ =>
      (* rename variable *)
      fun (x y : string) => cmd.set y (expr.var x)
    end.
End Lists.
