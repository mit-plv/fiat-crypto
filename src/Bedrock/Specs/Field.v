Require Import coqutil.Byte.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Local Open Scope Z_scope.

Class FieldParameters :=
  { (** mathematical parameters **)
    M_pos : positive; (* modulus *)
    M : Z := Z.pos M_pos;
    a24 : F M_pos; (* (a+2) / 4 or (a-2) / 4, depending on the implementation *)

    (* special wrapper for copy so that compilation lemmas can recognize it *)
    fe_copy := (@id (F M_pos));

    (** function names **)
    mul : string; add : string; sub : string; opp : string;
    square : string; scmula24 : string; inv : string;
    from_bytes : string; to_bytes : string;

    (* felem_small_literal p x :=
         store p (expr.literal x);
         store (p+4) (expr.literal 0);
         ...

       felem_copy pX pY :=
         store pX (load pY);
         store (pX+4) (load (pY+4));
         ... *)
    felem_copy : string;
    felem_small_literal : string;
  }.

Class FieldParameters_ok {field_parameters : FieldParameters} :=
  { M_prime : Znumtheory.prime M;
    (* TODO: a24_ok *)
  }.

Class FieldRepresentation
      {field_parameters : FieldParameters}
      {semantics : Semantics.parameters} :=
  { felem : Type;
    feval : felem -> F M_pos;
    feval_bytes : list byte -> F M_pos;
    felem_size_in_bytes : Z; (* for stack allocation *)
    encoded_felem_size_in_bytes : nat; (* number of bytes when serialized *)
    bytes_in_bounds : list byte -> Prop;

    (* Memory layout *)
    FElem : word -> felem -> Semantics.mem -> Prop;
    FElemBytes : word -> list byte -> Semantics.mem -> Prop :=
      fun addr bs =>
        (emp (length bs = encoded_felem_size_in_bytes)
         * array ptsto (word.of_Z 1) addr bs)%sep;

    bounds : Type;
    bounded_by : bounds -> felem -> Prop;
    (* for saturated implementations, loose/tight bounds are the same *)
    loose_bounds : bounds;
    tight_bounds : bounds;
  }.

Definition Placeholder
           {field_parameters : FieldParameters}
           {semantics : Semantics.parameters}
           {field_representation : FieldRepresentation}
           (p : Semantics.word) : Semantics.mem -> Prop :=
  Memory.anybytes p felem_size_in_bytes.

Class FieldRepresentation_ok
      {field_parameters : FieldParameters}
      {semantics : Semantics.parameters}
      {field_representation : FieldRepresentation} :=
  {  felem_size_in_bytes_mod :
       felem_size_in_bytes mod Memory.bytes_per_word Semantics.width = 0;
     FElem_from_bytes :
      forall px,
        Lift1Prop.iff1 (Placeholder px) (Lift1Prop.ex1 (FElem px));
    relax_bounds :
      forall X : felem, bounded_by tight_bounds X
                        -> bounded_by loose_bounds X;
  }.
Section FunctionSpecs.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.

  Class UnOp (name: string) :=
    { un_model: F M_pos -> F M_pos;
      un_xbounds: bounds;
      un_outbounds: bounds }.

  Definition unop_spec {name} (op: UnOp name) :=
    fnspec! name (pout px : word) / (out x : felem) Rr,
    { requires tr mem :=
        bounded_by un_xbounds x
        /\ (exists Ra, (FElem px x * Ra)%sep mem)
        /\ (FElem pout out * Rr)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          feval out = un_model (feval x)
          /\ bounded_by un_outbounds out
          /\ (FElem pout out * Rr)%sep mem' }.

  Instance spec_of_UnOp {name} (op: UnOp name) : spec_of name :=
    unop_spec op.

  Class BinOp (name: string) :=
    { bin_model: F M_pos -> F M_pos -> F M_pos;
      bin_xbounds: bounds;
      bin_ybounds: bounds;
      bin_outbounds: bounds }.

  Definition binop_spec  {name} (op: BinOp name) :=
    fnspec! name (pout px py : word) / (out x y : felem) Rr,
    { requires tr mem :=
        bounded_by bin_xbounds x
        /\ bounded_by bin_ybounds y
        /\ (exists Ra, (FElem px x * FElem py y * Ra)%sep mem)
        /\ (FElem pout out * Rr)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          feval out = bin_model (feval x) (feval y)
          /\ bounded_by bin_outbounds out
          /\ (FElem pout out * Rr)%sep mem' }.

  Instance spec_of_BinOp {name} (op: BinOp name) : spec_of name :=
    binop_spec op.

  Instance bin_mul : BinOp mul :=
    {| bin_model := F.mul; bin_xbounds := loose_bounds; bin_ybounds := loose_bounds; bin_outbounds := tight_bounds |}.
  Instance un_square : UnOp square :=
    {| un_model := fun x => F.pow x 2; un_xbounds := loose_bounds; un_outbounds := tight_bounds |}.
  Instance bin_add : BinOp add :=
    {| bin_model := F.add; bin_xbounds := tight_bounds; bin_ybounds := tight_bounds; bin_outbounds := loose_bounds |}.
  Instance bin_sub : BinOp sub :=
    {| bin_model := F.sub; bin_xbounds := tight_bounds; bin_ybounds := tight_bounds; bin_outbounds := loose_bounds |}.
  Instance un_scmula24 : UnOp scmula24 :=
    {| un_model := F.mul a24; un_xbounds := loose_bounds; un_outbounds := tight_bounds |}.
  Instance un_inv : UnOp inv := (* TODO: what are the bounds for inv? *)
    {| un_model := F.inv; un_xbounds := tight_bounds; un_outbounds := loose_bounds |}.
  Instance un_opp : UnOp opp :=
    {| un_model := F.opp; un_xbounds := tight_bounds; un_outbounds := loose_bounds |}.

  Instance spec_of_from_bytes : spec_of from_bytes :=
    fnspec! from_bytes (pout px : word) / out (bs : list byte) Rr,
    { requires tr mem :=
        (exists Ra, (FElemBytes px bs * Ra)%sep mem)
        /\ (FElem pout out * Rr)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists X, feval X = feval_bytes bs
             /\ bounded_by tight_bounds X
             /\ (FElem pout X * Rr)%sep mem' }.

  Instance spec_of_to_bytes : spec_of to_bytes :=
    fnspec! to_bytes (pout px : word) / (out : list byte) (x : felem) Rr,
    { requires tr mem :=
        bounded_by tight_bounds x /\
        (exists Ra, (FElem px x * Ra)%sep mem)
        /\ (FElemBytes pout out * Rr)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists bs, feval_bytes bs = feval x
                   /\ (FElemBytes pout bs * Rr)%sep mem' }.

  Instance spec_of_felem_copy : spec_of felem_copy :=
    fnspec! felem_copy (pout px : word) / (out x : felem) R,
    { requires tr mem :=
        (FElem px x * FElem pout out * R)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (FElem px x * FElem pout x * R)%sep mem' }.

  Instance spec_of_felem_small_literal : spec_of felem_small_literal :=
    fnspec! felem_small_literal (pout x : word) / out R,
    { requires tr mem :=
        (FElem pout out * R)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists X, feval X = F.of_Z _ (word.unsigned x)
             /\ bounded_by tight_bounds X
             /\ (FElem pout X * R)%sep mem' }.
End FunctionSpecs.

Existing Instances spec_of_UnOp spec_of_BinOp bin_mul un_square bin_add bin_sub
         un_scmula24 un_inv spec_of_felem_copy spec_of_felem_small_literal.

Section SpecProperties.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.

  Lemma FElem_to_bytes px x :
    Lift1Prop.impl1 (FElem px x) (Placeholder px).
  Proof.
    rewrite FElem_from_bytes.
    repeat intro; eexists; eauto.
  Qed.

  Lemma M_nonzero : M <> 0.
  Proof. cbv [M]. congruence. Qed.
End SpecProperties.
