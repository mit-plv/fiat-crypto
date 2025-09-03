Require Import coqutil.Byte coqutil.Word.LittleEndianList.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Field.Common.Arrays.MaxBounds.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Util.ZUtil.ModInv.
Local Open Scope Z_scope.
Import bedrock2.Memory.

Class FieldParameters :=
  { (** mathematical parameters **)
    M_pos : positive; (* modulus *)
    M : Z := Z.pos M_pos;
    a24 : F M_pos; (* (a+2) / 4 or (a-2) / 4, depending on the implementation *)

    (* special wrapper for copy so that compilation lemmas can recognize it *)
    fe_copy := (@id (F M_pos));

    (** function names **)
    mul : string; add : string; carry_add : string; sub : string; carry_sub : string; opp : string;
    square : string; scmula24 : string; inv : string;
    from_bytes : string; to_bytes : string;
    select_znz : string;

    felem_copy : string;
    from_word : string;
  }.

Class FieldParameters_ok {field_parameters : FieldParameters} := {
  M_prime : Znumtheory.prime M
}.

Class FieldRepresentation
      {field_parameters : FieldParameters}
      {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}
       :=
  { felem := list word;
    feval : felem -> F M_pos;

    feval_bytes : list byte -> F M_pos;
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
        (p : word) (bs : list byte): mem -> Prop :=
(sep (map.of_list_word_at p bs)
  (emp (Z.of_nat (length bs) = felem_size_in_bytes))).

Class FieldRepresentation_ok
      {field_parameters : FieldParameters}
      {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}
      {field_representation : FieldRepresentation} := {
    relax_bounds :
      forall X : felem, bounded_by tight_bounds X
                        -> bounded_by loose_bounds X;
    felem_size_ok : felem_size_in_bytes <= 2^width
  }.

Section FunctionSpecs.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.

  Class UnOp (name: string) :=
    { un_model: F M_pos -> F M_pos;
      un_xbounds: bounds;
      un_outbounds: bounds }.

  Import WeakestPrecondition.

  Definition unop_spec {name} (op: UnOp name) :=
    fnspec! name (pout px : word) / (x : felem) out Rr,
    { requires tr mem :=
        bounded_by un_xbounds x
        /\ (exists Ra, (FElem px x * Ra)%sep mem)
        /\ (Placeholder pout out * Rr)%sep mem;
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
    fnspec! name (pout px py : word) / (x y : felem) out Rr,
    { requires tr mem :=
        bounded_by bin_xbounds x
        /\ bounded_by bin_ybounds y
        /\ (exists Rx, (FElem px x * Rx)%sep mem)
        /\ (exists Ry, (FElem py y * Ry)%sep mem)
        /\ (Placeholder pout out * Rr)%sep mem;
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
  Instance bin_carry_add : BinOp carry_add :=
    {| bin_model := F.add; bin_xbounds := tight_bounds; bin_ybounds := tight_bounds; bin_outbounds := tight_bounds |}.
  Instance bin_sub : BinOp sub :=
    {| bin_model := F.sub; bin_xbounds := tight_bounds; bin_ybounds := tight_bounds; bin_outbounds := loose_bounds |}.
  Instance bin_carry_sub : BinOp carry_sub :=
    {| bin_model := F.sub; bin_xbounds := tight_bounds; bin_ybounds := tight_bounds; bin_outbounds := tight_bounds |}.
  Instance un_scmula24 : UnOp scmula24 :=
    {| un_model := F.mul a24; un_xbounds := loose_bounds; un_outbounds := tight_bounds |}.
  Instance un_inv : UnOp inv := (* TODO: what are the bounds for inv? *)
    {| un_model := F.inv; un_xbounds := tight_bounds; un_outbounds := loose_bounds |}.
  Instance un_opp : UnOp opp :=
    {| un_model := F.opp; un_xbounds := tight_bounds; un_outbounds := loose_bounds |}.

  Instance spec_of_from_bytes : spec_of from_bytes :=
    fnspec! from_bytes (pout px : word) / (out bs : list byte) Rr,
    { requires tr mem :=
        (exists Ra, (array ptsto (word.of_Z 1) px bs * Ra)%sep mem)
        /\ (Placeholder pout out * Rr)%sep mem
        /\ Field.bytes_in_bounds bs;
      ensures tr' mem' :=
        tr = tr' /\
        exists X, feval X = feval_bytes bs
             /\ bounded_by tight_bounds X
             /\ (FElem pout X * Rr)%sep mem' }.

  Instance spec_of_to_bytes : spec_of to_bytes :=
    fnspec! to_bytes (pout px : word) / (out : list byte) (x : felem) Rr,
    { requires tr mem :=
        (array ptsto (word.of_Z 1) pout out * Rr)%sep mem /\
        length out = encoded_felem_size_in_bytes /\
        (exists Ra, (FElem px x * Ra)%sep mem) /\
        bounded_by tight_bounds x;
      ensures tr' mem' := tr = tr' /\
        let bs := le_split encoded_felem_size_in_bytes (F.to_Z (feval x)) in
        (array ptsto (word.of_Z 1) pout bs * Rr)%sep mem' /\
        Field.bytes_in_bounds bs }.

  Instance spec_of_felem_copy : spec_of felem_copy :=
    fnspec! felem_copy (pout px : word) / (x : felem) out R,
    { requires tr mem :=
        (FElem px x * Placeholder pout out * R)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (FElem px x * FElem pout x * R)%sep mem' }.

  Instance spec_of_from_word : spec_of from_word :=
    fnspec! from_word (pout x : word) / out R,
    { requires tr mem :=
        (Placeholder pout out * R)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists X, feval X = F.of_Z _ (word.unsigned x)
             /\ bounded_by tight_bounds X
             /\ (FElem pout X * R)%sep mem' }.

    Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}.

    Instance spec_of_selectznz  : spec_of select_znz :=
    fnspec! select_znz (pout pc px py : word) / out Rout Rx Ry x y,
    {
        requires tr mem :=
        (Placeholder pout out * Rout)%sep mem /\
        (FElem px x * Rx)%sep mem /\
        (FElem py y * Ry)%sep mem /\
        ZRange.is_bounded_by_bool (word.unsigned pc) bit_range = true;
        ensures tr' mem' :=
        if ((word.unsigned pc) =? 1)
            then ((FElem pout y * Rout)%sep mem')
            else ((FElem pout x * Rout)%sep mem')
    }.

    (*Parameters for word-by-word Montgomery arithmetic*)
    Definition r := 2 ^ width.
    Definition m' := Z.modinv (- M) r.
    Definition r' := Z.modinv (r) M.

    Definition from_mont_model x := F.mul x (@F.of_Z M_pos (r' ^ (Z.of_nat felem_size_in_words)%Z)).
    Definition to_mont_model x := F.mul x (@F.of_Z M_pos (r ^ (Z.of_nat felem_size_in_words)%Z)).

    Instance un_from_mont {from_mont : string} : UnOp from_mont :=
      {| un_model := from_mont_model; un_xbounds := tight_bounds; un_outbounds := loose_bounds |}.

    Instance un_to_mont {to_mont : string} : UnOp to_mont :=
      {| un_model := to_mont_model; un_xbounds := tight_bounds; un_outbounds := loose_bounds|}.

End FunctionSpecs.

#[global]
Existing Instances spec_of_UnOp spec_of_BinOp bin_mul un_square bin_add bin_sub
         un_scmula24 un_inv spec_of_felem_copy spec_of_from_word.

Section SpecProperties.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.
  
  Lemma felem_size_in_bytes_mod :
         felem_size_in_bytes mod Memory.bytes_per_word width = 0.
  Proof. apply Z_mod_mult. Qed.


  (* In principle, these are just repetitions of what we already know about Bignum and array but on the abstraction level of FElem and Placeholder.
     Might be able to simplify with a bit of transitivity use with array ptsto and Bignum as steps in between, etc. 
     TODO clean up these proofs. *)
    
  Lemma Placeholder_iff_FElem p : Lift1Prop.iff1 (Lift1Prop.ex1 (Placeholder p)) (Lift1Prop.ex1 (FElem p)).
  Proof.
    cbv [FElem Placeholder].
    repeat intro.
    cbv [Lift1Prop.ex1]; split; intros.
      all : repeat match goal with
             | H : exists _, _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             end.
    { extract_ex1_and_emp_in_hyps. eapply array1_iff_eq_of_list_word_at in H; try assumption.
      eexists; eapply Bignum_of_bytes; try eassumption.
      unfold felem_size_in_bytes in *. ZnWords.
      pose felem_size_ok. lia. }
    { eapply Bignum_to_bytes in H; sepsimpl.
      let H := match goal with
               | H : Array.array _ _ _ _ _ |- _ => H end in
      eapply Array.array_1_to_anybytes in H.
      destruct H0 as [bs [E [L LT] ] ].
      eexists; extract_ex1_and_emp_in_goal; split; try eassumption.
      pose felem_size_ok. rewrite L. rewrite H. unfold felem_size_in_bytes.
      pose Types.word_size_in_bytes_pos. lia.
    }
  Qed.
  
  (* Should Bignum take care of this? Like, provide a function to translate. 
    wait, it kind of does... *)
  Local Notation lew_combine := (fun c => word.of_Z (width:=width) (LittleEndianList.le_combine c)).
  Local Notation k := (bytes_per_word width).
  Local Notation lew_split := (fun w => LittleEndianList.le_split (Z.to_nat k) (word.unsigned w)).
  Local Coercion Z.to_nat : Z >-> nat.

  Lemma Placeholder_impl_FElem_bytes p bs : 
    Lift1Prop.impl1 (Placeholder p bs) (FElem p (List.map lew_combine (chunk (Z.to_nat k) bs))).
  Proof.
    repeat intro.
    pose (Bignum_of_bytes felem_size_in_words p bs) as HBignum.
    epose (array1_iff_eq_of_list_word_at p bs) as HArray.
    pose felem_size_ok.
    cbv [FElem Placeholder felem_size_in_bytes] in *.
    intros.
    extract_ex1_and_emp_in_hyps. apply HBignum. lia. 
      apply HArray. lia. assumption.
  Qed.

  Lemma Placeholder_impl_FElem_words p ws : 
    Lift1Prop.impl1 (FElem p ws) (Placeholder p (List.flat_map lew_split ws)).
  Proof.
    repeat intro.
    pose (Bignum_to_bytes felem_size_in_words p ws) as HBignum.
    pose felem_size_ok.
    cbv [FElem Placeholder felem_size_in_bytes] in *.
    apply HBignum in H. extract_ex1_and_emp_in_hyps.
    rewrite (@length_flat_map _ _ _ k _) in H_emp0.
    2: { intros. apply length_le_split. }
    extract_ex1_and_emp_in_goal; split.
      apply array1_iff_eq_of_list_word_at; try assumption. 
      rewrite (@length_flat_map _ _ _ k _). 2: { intros. apply length_le_split. }
      lia. 
rewrite (@length_flat_map _ _ _ k _). 2: { intros. apply length_le_split. }
pose Types.word_size_in_bytes_pos.
    lia.
  Qed.


  Lemma Placeholder_iff_FElem_bytes p bs : 
    Lift1Prop.iff1 (Placeholder p bs) (sep (FElem p (List.map lew_combine (chunk (Z.to_nat k) bs))) (emp (Datatypes.length bs = felem_size_in_bytes))).
  Proof.
    repeat intro.
    pose (Bignum_of_bytes felem_size_in_words p bs) as HBignum.
    epose (array1_iff_eq_of_list_word_at p bs) as HArray.
    pose felem_size_ok.
    cbv [FElem Placeholder felem_size_in_bytes] in *.
    split; intros.
    - sepsimpl. apply HBignum. lia. 
      apply HArray. lia. assumption.
      lia. 
    - sepsimpl. apply HArray; try lia. apply HBignum; try lia.
      assumption. pose Types.word_size_in_bytes_pos. lia.
  Qed.

  Lemma Placeholder_iff_FElem_words p ws : 
    Lift1Prop.iff1 (sep (Placeholder p (List.flat_map lew_split ws)) (emp (Datatypes.length ws = felem_size_in_words))) (FElem p ws).
  Proof.
    repeat intro.
    pose (Bignum_to_bytes felem_size_in_words p ws) as HBignum.
    pose felem_size_ok.
    cbv [FElem Placeholder felem_size_in_bytes] in *.
    split; intros.
    - sepsimpl. apply HBignum.
      sepsimpl; try lia.
      apply array1_iff_eq_of_list_word_at; try assumption; try lia.
    - apply HBignum in H. sepsimpl.
      apply array1_iff_eq_of_list_word_at; try assumption; lia.
      rewrite H. pose Types.word_size_in_bytes_pos. lia.
      rewrite (@length_flat_map _ _ _ k _) in H; try lia.
      pose Types.word_size_in_bytes_pos.
      cbv [k] in *. nia. 
      intros. apply length_le_split.
  Qed.

  (* this is almost bytearray_iff_bytes *)
  Lemma Placeholder_iff_array1 p bs : 
    Datatypes.length bs = felem_size_in_bytes ->
    Lift1Prop.iff1 (Placeholder p bs) (array ptsto (word.of_Z 1) p bs).
  Proof.
    repeat intro.
    cbv [Placeholder].
    pose felem_size_ok.
    pose Types.word_size_in_bytes_pos.
    split; intros.
    - sepsimpl. apply array1_iff_eq_of_list_word_at; try assumption; try lia. 
    - sepsimpl. apply array1_iff_eq_of_list_word_at; try assumption; try lia.
    rewrite H. cbv [felem_size_in_bytes]. lia. (* TODO figure out if this can be done easier *)
  Qed.


  Lemma M_nonzero : M <> 0.
  Proof. cbv [M]. congruence. Qed.
End SpecProperties.

