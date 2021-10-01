(* IF YOU CHANGE THIS FILE YOU MUST ALSO CHANGE src/Bedrock/Field/Stringification/LoadStoreListVarData.v ! *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Array.
Require Import bedrock2.Scalars.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZRange.
Import ListNotations. Local Open Scope Z_scope.

Import API.Compilers.
Import Types.Notations.

(* For proofs, it's ideal to assume that at the "cmd" level of abstraction, the
   memory doesn't change. This is actually true for fiat-crypto functions, which
   follow a pattern in which they read all their from input lists, then only deal
   with local variables until they store their results in output lists.

   Therefore, at the "func" level of abstraction, we first read the data from
   memory and then pass the local variables to the "cmd" level. The "cmd" level
   then returns local variables which we store. This file handles the
   loading/storing part of that process. *)
Section Lists.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Local Existing Instance rep.Z.

  Fixpoint extract_listnames {t}
    : base_ltype (listZ:=rep.listZ_mem) t ->
      listonly_base_ltype t * listexcl_base_ltype t
    :=
      match t as t0 return
            base_ltype t0 ->
            listonly_base_ltype t0
            * listexcl_base_ltype t0 with
      | base.type.prod a b =>
        fun x =>
          let p1 := extract_listnames (fst x) in
          let p2 := extract_listnames (snd x) in
          ((fst p1, fst p2), (snd p1, snd p2))
      | base_listZ => fun x => (x, tt)
      | _ => fun x => (tt, x)
      end.

  Definition load_list_item
             (load_size : access_size)
             (start : Syntax.expr.expr) (i : nat)
    : Syntax.expr.expr :=
    let nbytes := Memory.bytes_per (width:=width) load_size in
    let offset := expr.literal (Z.of_nat (nbytes * i)) in
    let loc := expr.op bopname.add start offset in
    expr.load load_size loc.

  Fixpoint load_list
           (load_size : access_size)
           (start : Syntax.expr.expr) (i rem nextn : nat)
    : nat * list string * Syntax.cmd.cmd :=
    match rem with
    | O => (0%nat, [], cmd.skip)
    | S rem' =>
      let rec := load_list load_size start (S i) rem' (S nextn) in
      (S (fst (fst rec)), (varname_gen nextn) :: snd (fst rec),
       cmd.seq (cmd.set (varname_gen nextn)
                        (load_list_item load_size start i))
               (snd rec))
    end.

  Fixpoint load_all_lists {t : base.type} (nextn : nat)
    : base_ltype (listZ:=rep.listZ_mem) t ->
      base_listonly nat t ->
      base_access_sizes (listZ:=rep.listZ_mem) t ->
      nat * base_ltype (listZ:=rep.listZ_local) t * cmd.cmd :=
    match t with
    | base.type.prod a b =>
      fun x l s =>
        let load1 :=  load_all_lists nextn (fst x) (fst l) (fst s) in
        let nextn1 := (nextn + fst (fst load1))%nat in
        let load2 := load_all_lists nextn1 (snd x) (snd l) (snd s) in
        let nvars := (fst (fst load1) + fst (fst load2))%nat in
        (nvars, (snd (fst load1), snd (fst load2)),
         cmd.seq (snd load1) (snd load2))
    | base_listZ =>
      fun (x : string) (l : nat) (s : access_size) =>
        load_list s (expr.var x) 0 l nextn
    | _ =>
      fun (x : string) (l s : unit) => (0%nat, x, cmd.skip)
    end.

  (* read lists from arguments; changes the type system from in-memory
     lists to local lists *)
  Fixpoint load_arguments {t} (nextn : nat)
    : type.for_each_lhs_of_arrow (ltype (listZ:=rep.listZ_mem)) t ->
      type.for_each_lhs_of_arrow list_lengths t ->
      type.for_each_lhs_of_arrow access_sizes t ->
      nat (* number of fresh variable names used *)
      * type.for_each_lhs_of_arrow (ltype (listZ:=rep.listZ_local)) t
      * cmd.cmd :=
    match t as t0 return
          type.for_each_lhs_of_arrow _ t0 ->
          type.for_each_lhs_of_arrow _ t0 ->
          type.for_each_lhs_of_arrow _ t0 ->
          _ * type.for_each_lhs_of_arrow _ t0 * _
    with
    | type.base b =>
      fun (args bounds sizes : unit) => (0%nat, args, cmd.skip)
    | type.arrow (type.base s) d =>
      fun (args : base_ltype s * type.for_each_lhs_of_arrow _ d)
          (llengths : base_listonly nat s * type.for_each_lhs_of_arrow _ d)
          (sizes : base_access_sizes s
                   * type.for_each_lhs_of_arrow _ d) =>
        let load_fst :=
            load_all_lists nextn (fst args) (fst llengths) (fst sizes) in
        let nextn' := (nextn + fst (fst load_fst))%nat in
        let load_snd :=
            load_arguments nextn' (snd args) (snd llengths) (snd sizes) in
        let nvars := (fst (fst load_fst) + fst (fst load_snd))%nat in
        let args' := (snd (fst load_fst), snd (fst load_snd)) in
        let cmd := cmd.seq (snd load_fst) (snd load_snd) in
        (nvars, args', cmd)
    | type.arrow _ d =>
      (* no arrow arguments allowed; insert unit type *)
      fun args bounds sizes =>
        let load_snd :=
            load_arguments nextn (snd args) (snd bounds) (snd sizes) in
        (fst (fst load_snd), (tt, snd (fst load_snd)), snd load_snd)
    end.

  Definition store_list_item
             (size : access_size)
             (start value : Syntax.expr.expr) (i : nat)
    : cmd.cmd :=
    let nbytes := Memory.bytes_per (width:=width) size in
    let offset := expr.literal (Z.of_nat (nbytes * i)) in
    let loc := expr.op bopname.add start offset in
    cmd.store size loc value.

  Fixpoint store_list
             (size : access_size)
             (start : Syntax.expr.expr)
             (values : list Syntax.expr.expr)
             (i : nat)
    : cmd.cmd :=
    match values with
    | [] => cmd.skip
    | v :: values' =>
      cmd.seq (store_list_item size start v i)
              (store_list size start values' (S i))
    end.

  Fixpoint store_return_values {t : base.type}
    : base_ltype (listZ:=rep.listZ_local) t ->
      base_ltype (listZ:=rep.listZ_mem) t ->
      access_sizes (listZ:=rep.listZ_mem) (type.base t) ->
      list_lengths (type.base t) * cmd.cmd :=
    match t as t0 return
          base_ltype t0 -> base_ltype t0 -> access_sizes (type.base t0) ->
          list_lengths (type.base t0) * _ with
    | base.type.prod a b =>
      fun x y s =>
        let a := store_return_values (fst x) (fst y) (fst s) in
        let b := store_return_values (snd x) (snd y) (snd s) in
        ((fst a, fst b), cmd.seq (snd a) (snd b))
    | base_listZ =>
      (* store list at location pointed to by y *)
      fun (x : list string) (y : string) (s : access_size) =>
        (length x, store_list s (expr.var y) (map expr.var x) 0)
    | _ =>
      (* rename variable *)
      fun (x y : string) _ => (tt, cmd.set y (expr.var x))
    end.
End Lists.
