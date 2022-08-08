Require Import coqutil.Byte.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Field.Common.Arrays.MaxBounds.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Util.ZUtil.ModInv.
Local Open Scope Z_scope.
Import bedrock2.Memory.

Section FieldSpecs.

  (*The classes here generel enough to accomodate finite fields of prime order as well as higher degree extensions, e.g. the quadratic extensions used for the BLS12-381 curves.*)

  Class FieldParameters :=
    { F : Type;
      Fzero : F; Fone : F;
      Feq : F -> F -> Prop;
      Fopp : F -> F; Finv : F -> F;
      Fadd : F -> F -> F; Fsub : F -> F -> F; Fmul : F -> F -> F; Fdiv : F -> F -> F; (*consider collecting these in a separate class.*)

      Feq_dec : DecidableRel Feq;

      a24 : F; (* (a+2) / 4 or (a-2) / 4, depending on the implementation *)

      (* special wrapper for copy so that compilation lemmas can recognize it *)
      fe_copy := (@id (F));

      (** function names **)
      mul : string; add : string; sub : string; opp : string;
      square : string; scmula24 : string; inv : string;
      from_bytes : string; to_bytes : string;
      select_znz : string;
      felem_copy : string;
      from_word : string;
    }.

  Class FieldParameters_ok {field_parameters : FieldParameters} := {
    fld:@Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv
  }.

  Class FieldRepresentation
        {field_parameters : FieldParameters}
        {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}
        :=
    { felem := list word;
      feval : felem -> F;

      feval_bytes : list byte -> F;
      felem_size_in_words : nat;
      felem_size_in_bytes : Z := Z.of_nat felem_size_in_words * bytes_per_word width; (* for stack allocation *)
      encoded_felem_size_in_bytes : nat; (* number of bytes when serialized *)
      bytes_in_bounds : list byte -> Prop;

      (* Memory layout *)
      FElem : word -> list word -> mem -> Prop := Bignum felem_size_in_words;
      FElemBytes : word -> list byte -> mem -> Prop :=
        fun addr bs =>
          (emp (length bs = encoded_felem_size_in_bytes
                /\ bytes_in_bounds bs)
          * array ptsto (word.of_Z 1) addr bs)%sep;

      bounds : Type;
      bounded_by : bounds -> felem -> Prop;
      (* for saturated implementations, loose/tight bounds are the same *)
      loose_bounds : bounds;
      tight_bounds : bounds;
    }.

  Definition Placeholder
            {field_parameters : FieldParameters}
            {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}
            {field_representation : FieldRepresentation(mem:=mem)}
            (p : word) : mem -> Prop :=
    Memory.anybytes(mem:=mem) p felem_size_in_bytes.

  Class FieldRepresentation_ok
        {field_parameters : FieldParameters}
        {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}
        {field_representation : FieldRepresentation} := {
      relax_bounds :
        forall X : felem, bounded_by tight_bounds X
                          -> bounded_by loose_bounds X;
    }.

  Section BignumToFieldRepresentationAdapterLemmas.
    Context
    {field_parameters : FieldParameters}
    {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}
    {field_representation : FieldRepresentation}.
    Context {word_ok : @word.ok width word} {map_ok : @map.ok word Init.Byte.byte mem}.

    Lemma felem_size_in_bytes_mod :
          felem_size_in_bytes mod Memory.bytes_per_word width = 0.
    Proof. apply Z_mod_mult. Qed.
    Lemma FElem_from_bytes p : Lift1Prop.iff1 (Placeholder p) (Lift1Prop.ex1 (FElem p)).
    Proof.
      cbv [Placeholder FElem felem_size_in_bytes].
      repeat intro.
      cbv [Lift1Prop.ex1]; split; intros;
        repeat match goal with
              | H : anybytes _ _ _ |- _ => eapply Array.anybytes_to_array_1 in H
              | H : exists _, _ |- _ => destruct H
              | H : _ /\ _ |- _ => destruct H
              end.
        all : repeat match goal with
              | H : anybytes _ _ _ |- _ => eapply Array.anybytes_to_array_1 in H
              | H : exists _, _ |- _ => destruct H
              | H : _ /\ _ |- _ => destruct H
              end.
      { eexists; eapply Bignum_of_bytes; try eassumption.
        destruct Bitwidth.width_cases; subst width; revert H0; cbn; lia. }
      { eapply Bignum_to_bytes in H; sepsimpl.
        let H := match goal with
                | H : Array.array _ _ _ _ _ |- _ => H end in
        eapply Array.array_1_to_anybytes in H.
        unshelve (erewrite (_:_*_=_); eassumption).
        rewrite H; destruct Bitwidth.width_cases as [W|W];
          symmetry in W; destruct W; cbn; clear; lia. }
    Qed.
  End BignumToFieldRepresentationAdapterLemmas.

  Section ToFromBytes.
    Definition nth_byte (x : Z) (n : nat) : byte :=
      byte.of_Z (Z.shiftr x (8 * Z.of_nat n)).
    Definition Z_to_bytes (x : Z) (n : nat) : list byte :=
      List.map (nth_byte x) (seq 0 n).
    Definition Z_from_bytes (bs : list byte) : Z :=
      List.fold_right
        (fun b acc => Z.shiftl acc 8 + byte.unsigned b) 0 bs.
  End ToFromBytes.

  Section FunctionSpecs.
    Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
    Context {locals: map.map String.string word}.
    Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
    Context {ext_spec: bedrock2.Semantics.ExtSpec}.
    Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
    Context {locals_ok : map.ok locals}.
    Context {env_ok : map.ok env}.
    Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
    Context {field_parameters : FieldParameters}
            {field_representation : FieldRepresentation}.

    Local Definition Fsquare (x : F) := Fmul x x.

    Class UnOp (name: string) :=
      { un_model: F -> F;
        un_xbounds: bounds;
        un_outbounds: bounds }.

    Import WeakestPrecondition.

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
      { bin_model: F -> F -> F;
        bin_xbounds: bounds;
        bin_ybounds: bounds;
        bin_outbounds: bounds }.

    Definition binop_spec  {name} (op: BinOp name) :=
      fnspec! name (pout px py : word) / (out x y : felem) Rr,
      { requires tr mem :=
          bounded_by bin_xbounds x
          /\ bounded_by bin_ybounds y
          /\ (exists Rx, (FElem px x * Rx)%sep mem)
          /\ (exists Ry, (FElem py y * Ry)%sep mem)
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
      {| bin_model := Fmul; bin_xbounds := loose_bounds; bin_ybounds := loose_bounds; bin_outbounds := tight_bounds |}.
    Instance un_square : UnOp square :=
      {| un_model := fun x => Fsquare x; un_xbounds := loose_bounds; un_outbounds := tight_bounds |}.
    Instance bin_add : BinOp add :=
      {| bin_model := Fadd; bin_xbounds := tight_bounds; bin_ybounds := tight_bounds; bin_outbounds := loose_bounds |}.
    Instance bin_sub : BinOp sub :=
      {| bin_model := Fsub; bin_xbounds := tight_bounds; bin_ybounds := tight_bounds; bin_outbounds := loose_bounds |}.
    Instance un_scmula24 : UnOp scmula24 :=
      {| un_model := Fmul a24; un_xbounds := loose_bounds; un_outbounds := tight_bounds |}.
    Instance un_inv : UnOp inv := (* TODO: what are the bounds for inv? *)
      {| un_model := Finv; un_xbounds := tight_bounds; un_outbounds := loose_bounds |}.
    Instance un_opp : UnOp opp :=
      {| un_model := Fopp; un_xbounds := tight_bounds; un_outbounds := loose_bounds |}.

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
          exists bs,
            feval x = feval_bytes bs /\
            (FElemBytes pout bs * Rr)%sep mem' }.

    Instance spec_of_felem_copy : spec_of felem_copy :=
      fnspec! felem_copy (pout px : word) / (out x : felem) R,
      { requires tr mem :=
          (FElem px x * FElem pout out * R)%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          (FElem px x * FElem pout x * R)%sep mem' }.

      Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}.

      Instance spec_of_selectznz  : spec_of select_znz :=
      fnspec! select_znz (pout pc px py : word) / out Rout Rx Ry x y,
      {
          requires tr mem :=
          (FElem pout out * Rout)%sep mem /\
          (FElem px x * Rx)%sep mem /\
          (FElem py y * Ry)%sep mem /\
          ZRange.is_bounded_by_bool (word.unsigned pc) bit_range = true;
          ensures tr' mem' :=
          if ((word.unsigned pc) =? 1)
              then ((FElem pout y * Rout)%sep mem')
              else ((FElem pout x * Rout)%sep mem')
      }.

  End FunctionSpecs.

  Existing Instances spec_of_UnOp spec_of_BinOp bin_mul un_square bin_add bin_sub
          un_scmula24 un_inv spec_of_felem_copy.

  Section SpecProperties.
    Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
    Context {locals: map.map String.string word}.
    Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
    Context {ext_spec: bedrock2.Semantics.ExtSpec}.
    Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
    Context {locals_ok : map.ok locals}.
    Context {env_ok : map.ok env}.
    Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
    Context {field_parameters : FieldParameters}
            {field_representation : FieldRepresentation}
            {field_representation_ok : FieldRepresentation_ok}.

    Lemma FElem_to_bytes px x :
      Lift1Prop.impl1 (FElem px x) (Placeholder px).
    Proof.
      rewrite FElem_from_bytes.
      repeat intro; eexists; eauto.
    Qed.

  End SpecProperties.
End FieldSpecs.