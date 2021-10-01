Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Semantics.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Array bedrock2.Scalars.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Language.API.
Local Open Scope Z_scope.

Import API.Compilers.
Import Types.Notations.

Section Equivalent.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters
     width BW word mem locals env ext_spec varname_gen error}.
  Local Notation parameters := (ltac:(let t := type of parameters_sentinel in exact t)) (only parsing).
  Context {listZ : rep.rep base_listZ}.
  Existing Instance rep.Z.

  (* relation that states whether a fiat-crypto value and a bedrock2 value are
     equivalent in a given bedrock2 context *)
  Fixpoint equivalent_base {t}
    : base.interp t -> (* fiat-crypto value *)
      base_rtype t -> (* bedrock2 value *)
      base_access_sizes t -> (* size in memory (if applicable) *)
      locals ->
      mem -> Prop :=
    match t with
    | base.type.prod a b =>
      fun (x : base.interp a * base.interp b)
          (y : base_rtype a * base_rtype b)
          (s : base_access_sizes a * base_access_sizes b)
          locals =>
        sep (equivalent_base (fst x) (fst y) (fst s) locals)
            (equivalent_base (snd x) (snd y) (snd s) locals)
    | base_listZ => rep.equiv
    | base_Z => rep.equiv
    |  _ => fun _ _ _ _ => emp False
    end.

  (* produces a separation-logic condition stating that the values of
     arguments are equivalent *)
  Fixpoint equivalent_args {t}
    : type.for_each_lhs_of_arrow
        API.interp_type t -> (* fiat-crypto value *)
      type.for_each_lhs_of_arrow rtype t -> (* bedrock2 value *)
      type.for_each_lhs_of_arrow
        access_sizes t -> (* sizes in memory *)
      locals ->
      mem -> Prop :=
    match t with
    | type.base b => fun _ _ _ _ _ => True
    | type.arrow (type.base a) b =>
      fun (x : base.interp a * _) (y : base_rtype a * _)
          (s : base_access_sizes a * _) locals mem =>
        (exists R,
            sep (equivalent_base (fst x) (fst y) (fst s) locals) R mem)
        /\ (equivalent_args (snd x) (snd y) (snd s) locals mem)
    | _ => fun _ _ _ _ _ => False
    end.

  Definition locally_equivalent_base {t} x y locals :=
    @equivalent_base t x y (base_dummy_access_sizes t) locals map.empty.

  Definition locally_equivalent_args {t} x y locals :=
    @equivalent_args t x y (dummy_access_sizes_args t) locals map.empty.

  (* wrapper that uses non-base types *)
  Definition equivalent {t : API.type}
    : API.interp_type t -> (* fiat-crypto value *)
      rtype t -> (* bedrock2 value *)
      access_sizes t -> (* sizes in memory *)
      locals ->
      mem -> Prop :=
    match t with
    | type.base b => equivalent_base
    | _ => fun _ _ _ _ _ => False
    end.
  Definition locally_equivalent {t} x y locals :=
    @equivalent t x y (dummy_access_sizes t) locals map.empty.

  Fixpoint equivalent_listonly {t}
    : base.interp t -> (* fiat-crypto value *)
      listonly_base_rtype t -> (* bedrock2 value *)
      base_access_sizes t ->
      locals ->
      mem -> Prop :=
    match t with
    | base.type.prod a b =>
      fun x y s locals =>
        sep (equivalent_listonly (fst x) (fst y) (fst s) locals)
            (equivalent_listonly (snd x) (snd y) (snd s) locals)
    | base_listZ => rep.equiv
    | base_Z => fun _ _ _ _ => emp True
    |  _ => fun _ _ _ _ => emp False
    end.

  Fixpoint equivalent_listexcl {t}
    : base.interp t -> (* fiat-crypto value *)
      listexcl_base_rtype t -> (* bedrock2 value *)
      base_access_sizes t ->
      locals ->
      mem -> Prop :=
    match t with
    | base.type.prod a b =>
      fun x y s locals =>
        sep (equivalent_listexcl (fst x) (fst y) (fst s) locals)
            (equivalent_listexcl (snd x) (snd y) (snd s) locals)
    | base_listZ => fun _ _ _ _ => emp True
    | base_Z => rep.equiv
    |  _ => fun _ _ _ _ => emp False
    end.
End Equivalent.

(* equivalence with flat lists of words *)
Section EquivalentFlat.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters
     width BW word mem locals env ext_spec varname_gen error}.
  Local Notation parameters := (ltac:(let t := type of parameters_sentinel in exact t)) (only parsing).
  Existing Instances rep.listZ_mem rep.Z.

  Fixpoint equivalent_flat_base {t}
    : base.interp t ->
      list word ->
      base_access_sizes t ->
      mem -> Prop :=
    match t as t0 return
          base.interp t0 -> list word
          -> base_access_sizes t0 -> _ with
    | base.type.prod a b =>
      fun (x : base.interp a * base.interp b) words sizes =>
        Lift1Prop.ex1
          (fun i =>
             sep (equivalent_flat_base (fst x) (firstn i words) (fst sizes))
                 (equivalent_flat_base (snd x) (skipn i words) (snd sizes)))
    | base_listZ =>
      fun (x : list Z) words (sizes : rep.size) =>
        (* since this is in-memory representation, [words] should be one word
             that indicates the memory location of the head of the list *)
        sep
          (map:=mem)
          (emp (length words = 1%nat))
          (let addr := word.unsigned (hd (word.of_Z 0%Z) words) in
           rep.equiv (rep:=rep.listZ_mem)
                     x (Syntax.expr.literal addr) sizes map.empty)
    | base_Z =>
      fun (x : Z) words sizes =>
        sep
          (map:=mem)
          (emp (length words = 1%nat))
          (let w := word.unsigned (hd (word.of_Z 0%Z) words) in
           rep.equiv (rep:=rep.Z) x
                     (Syntax.expr.literal w) sizes map.empty)
    | _ => fun _ _ _ => emp False
    end.

  Fixpoint equivalent_flat_args {t}
    : type.for_each_lhs_of_arrow API.interp_type t ->
      list word ->
      type.for_each_lhs_of_arrow access_sizes t ->
      mem -> Prop :=
    match t as t0
          return type.for_each_lhs_of_arrow _ t0 -> _ ->
                 type.for_each_lhs_of_arrow _ t0 -> _
    with
    | type.base _ => fun (_:unit) words _ _ => words = nil
    | type.arrow (type.base a) b =>
      fun x words sizes mem =>
        exists i,
          (exists R,
              sep (equivalent_flat_base
                     (fst x) (firstn i words) (fst sizes)) R mem)
          /\ (equivalent_flat_args
                (snd x) (skipn i words) (snd sizes) mem)
    | _ => fun _ _ _ _ => False (* invalid argument *)
    end.
  Fixpoint equivalent_listexcl_flat_base {t}
    : base.interp t ->
      list word ->
      base_access_sizes t ->
      mem -> Prop :=
    match t as t0 return
          base.interp t0 -> _ -> base_access_sizes t0
          -> mem -> Prop with
    | base.type.prod a b =>
      fun (x : base.interp a * base.interp b) words s=>
        Lift1Prop.ex1
          (fun i =>
             sep (equivalent_listexcl_flat_base
                    (fst x) (firstn i words) (fst s))
                 (equivalent_listexcl_flat_base
                    (snd x) (skipn i words) (snd s)))
    | base_listZ => fun _ words _ => emp (words = nil)
    | base_Z => equivalent_flat_base
    | _ => fun _ _ _ => emp False
    end.

  Fixpoint equivalent_listonly_flat_base {t}
    : base.interp t ->
      list word ->
      base_access_sizes t ->
      mem -> Prop :=
    match t as t0 return
          base.interp t0 -> _ -> base_access_sizes t0
          -> mem -> Prop with
    | base.type.prod a b =>
      fun (x : base.interp a * base.interp b) words sizes =>
        Lift1Prop.ex1
          (fun i =>
             sep (equivalent_listonly_flat_base
                    (fst x) (firstn i words) (fst sizes))
                 (equivalent_listonly_flat_base
                    (snd x) (skipn i words) (snd sizes)))
    | base_listZ => equivalent_flat_base
    | base_Z => fun _ words _ => emp (words = nil)
    | _ => fun _ _ _ => emp False
    end.
End EquivalentFlat.
