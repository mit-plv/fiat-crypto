Require Import bedrock2.Array.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.Loops.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ZnWords.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.OfListWord.
From coqutil.Tactics Require Import Tactics letexists eabstract rdelta reference_to_string ident_of_string.
Require Import coqutil.Word.Bitwidth64.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Group.ScalarMult.CSwap.
Require Import Crypto.Bedrock.Secp256k1.Field256k1.
Require Import Crypto.Bedrock.Secp256k1.JacobianCoZ.
Require Import Crypto.Bedrock.Secp256k1.Addchain.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Util.Decidable.
Require Import Curves.Weierstrass.Jacobian.Jacobian.
Require Import Curves.Weierstrass.Jacobian.CoZ.
Require Import Curves.Weierstrass.Jacobian.ScalarMult.
Require Import Lia.
Require Crypto.Bedrock.Field.Synthesis.New.Signature.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Import LittleEndianList.
Import ListNotations.
Import ProgramLogic.Coercions.
Import WeakestPrecondition.

Local Existing Instance field_parameters.
Local Instance frep256k1 : Field.FieldRepresentation := field_representation Field256k1.m.
Local Existing Instance frep256k1_ok.

Definition secp256k1_laddermul (scalarbitsz : Z) :=
  func! (oX, oY, k, X, Y) {
    i = coq:(1);
    swap = (load1(k+i>>coq:(3))>>(i&coq:(7)))&coq:(1);
    stackalloc 32 as X0;
    stackalloc 32 as Y0;
    stackalloc 32 as X1;
    stackalloc 32 as Y1;
    stackalloc 32 as Z;
    stackalloc 32 as oZ;
    secp256k1_tplu(X1, Y1, X0, Y0, Z, X, Y);
    i = coq:(2);
    while (i < coq:(scalarbitsz)) {
      b = (load1(k+i>>coq:(3))>>(i&coq:(7)))&coq:(1);
      swap = swap ^ b;
      felem_cswap(swap, X0, X1);
      felem_cswap(swap, Y0, Y1);
      secp256k1_zdau(X1, Y1, X0, Y0, Z);
      swap = b;
      i = i+coq:(1)
    };
    felem_cswap(swap, X0, X1);
    felem_cswap(swap, Y0, Y1);
    stackalloc 32 as tX;
    stackalloc 32 as tY;
    secp256k1_make_co_z(tX, tY, X, Y, Z);
    secp256k1_opp(tY, tY);
    secp256k1_zaddu(oX, oY, X1, Y1, oZ, X0, Y0, tX, tY, Z);
    i = coq:(0);
    swap = (load1(k+i>>coq:(3))>>(i&coq:(7)))&coq:(1);
    felem_cswap(swap, oX, X1);
    felem_cswap(swap, oY, Y1);
    secp256k1_inv(Z, oZ);
    secp256k1_mul(oY, oY, Z);
    secp256k1_mul(Z, Z, Z);
    secp256k1_mul(oX, oX, Z);
    secp256k1_mul(oY, oY, Z)
}.

Section WithParameters.
  Context {two_lt_M: 2 < M_pos}.
  Context {char_ge_3 : (@Ring.char_ge (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos BinNat.N.two))}.
  Context {field:@Algebra.Hierarchy.field (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}.
  Context {secp256k1_prime: Znumtheory.prime m}.
  Context {F_M_pos : Z.pos M_pos = m}.
  Context {a b : F M_pos}.
  Context {zero_a : id a = F.zero}
          {seven_b : id b = F.of_Z _ 7}.
  Context {scalarbitsz : Z} {scalarbitsz_small : word.wrap scalarbitsz = scalarbitsz}.

  Add Ring Private_ring : (F.ring_theory M_pos) (morphism (F.ring_morph M_pos), constants [F.is_constant]).

  Local Coercion F.to_Z : F >-> Z.
  Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
  Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").

  Local Notation FElem := (FElem(FieldRepresentation:=frep256k1)).
  Local Notation word := (Naive.word 64).
  Local Notation felem := (felem(FieldRepresentation:=frep256k1)).
  Local Notation Wpoint := (WeierstrassCurve.W.point(F:=F M_pos)(Feq:=Logic.eq)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(b:=b)).
  Local Notation Wzero := (WeierstrassCurve.W.zero(F:=F M_pos)(Feq:=Logic.eq)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(b:=b)).
  Local Notation point := (Jacobian.point(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(b:=b)(Feq_dec:=F.eq_dec)).
  Local Notation co_z_points := (ScalarMult.co_z_points(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(b:=b)(Feq_dec:=F.eq_dec)).
  Local Notation zaddu_co_z_points := (ScalarMult.zaddu_co_z_points(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)(Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)(a:=a)(b:=b)(field:=field)(Feq_dec:=F.eq_dec)).
  Local Notation zdau_co_z_points := (ScalarMult.zdau_co_z_points(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)(a:=a)(b:=b)(field:=field)(Feq_dec:=F.eq_dec)).
  Local Notation cswap_co_z_points := (ScalarMult.cswap_co_z_points(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)(a:=a)(b:=b)(field:=field)(Feq_dec:=F.eq_dec)).
  Local Notation make_co_z_points := (ScalarMult.make_co_z_points(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)(a:=a)(b:=b)(field:=field)(Feq_dec:=F.eq_dec)).

  Local Instance spec_of_secp256k1_opp : spec_of "secp256k1_opp" := Field.spec_of_UnOp un_opp.
  Local Instance spec_of_secp256k1_square : spec_of "secp256k1_square" := Field.spec_of_UnOp un_square.
  Local Instance spec_of_secp256k1_mul : spec_of "secp256k1_mul" := Field.spec_of_BinOp bin_mul.
  Local Instance spec_of_secp256k1_add : spec_of "secp256k1_add" := Field.spec_of_BinOp bin_add.
  Local Instance spec_of_secp256k1_sub : spec_of "secp256k1_sub" := Field.spec_of_BinOp bin_sub.
  Local Instance spec_of_secp256k1_inv : spec_of "secp256k1_inv" := Addchain.spec_of_inv.
  Local Instance spec_of_secp256k1_cswap : spec_of "felem_cswap" := CSwap.spec_of_cswap.
  Local Instance spec_of_secp256k1_tplu : spec_of "secp256k1_tplu" := (@spec_of_tplu field a b).
  Local Instance spec_of_secp256k1_make_co_z : spec_of "secp256k1_make_co_z" := (@spec_of_make_co_z field a b).
  Local Instance spec_of_secp256k1_zaddu : spec_of "secp256k1_zaddu" := (@spec_of_zaddu field a b).
  Local Instance spec_of_secp256k1_zdau : spec_of "secp256k1_zdau" := (@spec_of_zdau field a b).

  Local Arguments word.rep : simpl never.
  Local Arguments word.wrap : simpl never.
  Local Arguments word.unsigned : simpl never.
  Local Arguments word.of_Z : simpl never.

  Local Ltac solve_mem :=
    repeat match goal with
      | |- exists _ : _ -> Prop, _%sep _ => eexists
      | |- _%sep _ => ecancel_assumption
      end.

  Local Ltac cbv_bounds H :=
    cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds] in H;
    cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds].

  Local Ltac solve_bounds :=
    match goal with
      | H: bounded_by _ ?x |- bounded_by _ ?x => apply H
      end.

  Local Ltac solve_stack :=
    (* Rewrites the `stack$@a` term in H to use a Bignum instead *)
    match goal with
    | H: _%sep ?m |- (Bignum.Bignum felem_size_in_words ?a _ * _)%sep ?m =>
        seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 4 a) H
    end;
    [> transitivity 32%nat; trivial | ];
    (* proves the memory matches up *)
    use_sep_assumption; cancel; cancel_seps_at_indices 0%nat 0%nat; cbn; [> trivial | eapply RelationClasses.reflexivity].

  Local Ltac single_step :=
    repeat straightline; straightline_call; ssplit; try solve_mem; try solve_bounds; try solve_stack.

  Local Instance spec_of_laddermul : spec_of "secp256k1_laddermul" :=
    fnspec! "secp256k1_laddermul"
      (OXptr OYptr kptr Xptr Yptr : word) /
      (OX OY X Y : felem) (P : Wpoint) (HPnz : P <> Wzero) kbytes (k : Z) (R : _ -> Prop),
    { requires t m :=
        proj1_sig P = inl ((feval X), (feval Y)) /\
        bounded_by loose_bounds X /\
        bounded_by loose_bounds Y /\
        LittleEndianList.le_combine kbytes = k /\
        2 <= scalarbitsz <= 8*Z.of_nat (List.length kbytes) /\
        m =* (FElem OXptr OX) * (FElem OYptr OY) * kbytes$@kptr *
             (FElem Xptr X) * (FElem Yptr Y) * R;
      ensures t' m' :=
        t = t' /\
        match proj1_sig (ScalarMult.joye_ladder scalarbitsz (Z.testbit k) P HPnz) with
        | inl (X', Y') =>
            exists OX' OY',
              X' = (feval OX') /\ Y' = (feval OY') /\
              bounded_by tight_bounds OX' /\
              bounded_by tight_bounds OY' /\
              m' =* (FElem OXptr OX') * (FElem OYptr OY') * kbytes$@kptr *
                    (FElem Xptr X) * (FElem Yptr Y) * R
        | _ => (* result is point at infinity *)
            exists OX' OY',
              0%F = (feval OX') /\ 0%F = (feval OY') /\
              m' =* (FElem OXptr OX') * (FElem OYptr OY') * kbytes$@kptr *
                    (FElem Xptr X) * (FElem Yptr Y) * R
        end
    }.

  Lemma spec_of_testbit functions tr mem loc post :
    forall var kptr kbytes k wi i R,
      map.get loc "k" = Some kptr ->
      map.get loc "i" = Some wi ->
      (kbytes$@kptr * R)%sep mem ->
      LittleEndianList.le_combine kbytes = k ->
      wi = word.of_Z i ->
      (0 <= i < 2 ^ 64)%Z ->
      (i < 8 * Z.of_nat (List.length kbytes)) ->

      (forall tr' mem' loc',
         (tr' = tr /\
          mem' = mem /\
          loc' = map.put loc var (Core.word.b2w (Z.testbit k i))) ->
         post tr' mem' loc') ->

      cmd functions
          bedrock_func_body:(
            $var = load1(coq:(expr.var "k") + coq:(expr.var "i") >> coq:(expr.literal 3)) >> (coq:(expr.var "i") & coq:(expr.literal 7)) & coq:(expr.literal 1))
          tr mem loc post.
  Proof.
    repeat straightline.
    repeat (eexists; split; repeat Tactics.straightline'; eauto); cbn [Semantics.interp_binop].

    - subst wi.
      eapply load_one_of_sep.
      unshelve (
        let Hrw := open_constr:(@bytearray_index_inbounds _ _ _ _ _ _ _ _ _ : Lift1Prop.iff1 _ _) in
        seprewrite0_in Hrw H1; ecancel_assumption).
      all: repeat rewrite ?Core.word.unsigned_of_Z_b2z, ?word.unsigned_of_Z, ?word.unsigned_and_nowrap, ?word.unsigned_sru_nowrap.
      all: cbv [word.wrap]; rewrite ?Z.mod_small; try lia.
      rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8. lia.
    - eapply H6. ssplit; auto.
      f_equal.
      eapply word.unsigned_inj.
      unfold Core.word.b2w, wi.
      repeat rewrite ?Core.word.unsigned_of_Z_b2z, ?word.unsigned_of_Z, ?word.unsigned_and_nowrap, ?word.unsigned_sru_nowrap.
      all: cbv [word.wrap]; repeat rewrite ?Z.mod_small; try lia.
      2: match goal with | |- context [byte.unsigned ?n] => generalize (byte.unsigned_range n); lia end.
      all: change 7 with (Z.ones 3); change 1 with (Z.ones 1); rewrite ?Z.land_ones by lia.
      2: lia.
      rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; change (2^1) with 2.
      rewrite <-?List.hd_skipn_nth_default.
      rewrite <- Z.testbit_spec' by lia; f_equal.
      rewrite <- (LittleEndianList.split_le_combine kbytes), H2.
      rewrite LittleEndianList.nth_default_le_split, byte.unsigned_of_Z, Z2Nat.id by lia.
      cbv [byte.wrap]; rewrite <-Z.land_ones, Z.land_spec, Z.ones_spec_low by lia.
      rewrite Z.shiftr_spec, Bool.andb_true_r by lia; f_equal. lia.
  Qed.

  Lemma while_is_iter {A:Type} test body fuel s:
    @Loops.while.while A test body fuel s = Nat.iter (S fuel) (fun s => if test s then body s else s) s.
  Proof.
    revert s; induction fuel; [reflexivity|]; intros.
    rewrite Nat.iter_succ_r.
    simpl Loops.while.while. rewrite IHfuel.
    destruct (test s) eqn:Htest; [reflexivity|].
    clear -Htest.
    induction fuel; [simpl; rewrite Htest; reflexivity|].
    rewrite Nat.iter_succ_r, Htest. apply IHfuel.
  Qed.

  Lemma car_cswap {A} swap x y :
    Core.P2.car (@cswap A swap x y) = if swap then y else x.
  Proof. destruct swap; reflexivity. Qed.

  Lemma cdr_cswap {A} swap x y :
    Core.P2.cdr (@cswap A swap x y) = if swap then x else y.
  Proof. destruct swap; reflexivity. Qed.

  Lemma co_z_conv (PQ: co_z_points) : Jacobian.co_z (fst (proj1_sig PQ)) (snd (proj1_sig PQ)).
  Proof.
    generalize (proj2_sig PQ). rewrite (surjective_pairing (proj1_sig PQ)) at 1.
    auto.
  Qed.

  Lemma proj1_sig_zdau_co_z_points PQ :
    proj1_sig (zdau_co_z_points PQ) = (fst (Jacobian.zdau (fst (proj1_sig PQ)) (snd (proj1_sig PQ)) (co_z_conv PQ)), snd (Jacobian.zdau (fst (proj1_sig PQ)) (snd (proj1_sig PQ)) (co_z_conv PQ))).
  Proof.
    destruct PQ as (PQ' & ?). destruct PQ' as (P & Q).
    unfold zdau_co_z_points. cbv [proj1_sig].
    rewrite (surjective_pairing (Jacobian.zdau P Q _)).
    repeat f_equal; apply Eqdep_dec.UIP_dec; apply F.eq_dec.
  Qed.

  Lemma proj1_sig_cswap_co_z_points swap PQ :
    proj1_sig (cswap_co_z_points swap PQ) = (if swap then snd (proj1_sig PQ) else fst (proj1_sig PQ), if swap then fst (proj1_sig PQ) else snd (proj1_sig PQ)).
  Proof.
    destruct PQ as (PQ' & ?). destruct PQ' as (P & Q).
    unfold cswap_co_z_points. cbv [proj1_sig].
    destruct swap; reflexivity.
  Qed.

  Lemma proj1_sig_zaddu_co_z_points PQ :
    proj1_sig (zaddu_co_z_points PQ) = (fst (Jacobian.zaddu (fst (proj1_sig PQ)) (snd (proj1_sig PQ)) (co_z_conv PQ)), snd (Jacobian.zaddu (fst (proj1_sig PQ)) (snd (proj1_sig PQ)) (co_z_conv PQ))).
  Proof.
    destruct PQ as (PQ' & ?). destruct PQ' as (P & Q).
    unfold zaddu_co_z_points. cbv [proj1_sig].
    rewrite (surjective_pairing (Jacobian.zaddu P Q _)).
    repeat f_equal; apply Eqdep_dec.UIP_dec; apply F.eq_dec.
  Qed.

  Lemma zdau_eq (P: point) P' Q Q' HPQ HPQ' :
    P = P' ->
    Q = Q' ->
    Jacobian.zdau P Q HPQ = Jacobian.zdau P' Q' HPQ'.
  Proof.
    intros. subst P' Q'.
    assert (HPQ = HPQ') as -> by (apply Eqdep_dec.UIP_dec; apply F.eq_dec).
    reflexivity.
  Qed.

  Lemma zaddu_eq (P: point) P' Q Q' HPQ HPQ' :
    P = P' ->
    Q = Q' ->
    Jacobian.zaddu P Q HPQ = Jacobian.zaddu P' Q' HPQ'.
  Proof.
    intros. subst P' Q'.
    assert (HPQ = HPQ') as -> by (apply Eqdep_dec.UIP_dec; apply F.eq_dec).
    reflexivity.
  Qed.

  Lemma spec_of_inner_loop functions tr mem loc post :
    forall kptr kbytes k X0ptr X1ptr Y0ptr Y1ptr Zptr X0 X1 Y0 Y1 Z (R0 R1:point) R,
      spec_of_secp256k1_cswap functions ->
      spec_of_secp256k1_zdau functions ->
      map.get loc "k" = Some kptr ->
      map.get loc "i" = Some (word.of_Z 2) ->
      map.get loc "swap" = Some (Core.word.b2w (Z.testbit k 1)) ->
      map.get loc "X0" = Some X0ptr ->
      map.get loc "Y0" = Some Y0ptr ->
      map.get loc "X1" = Some X1ptr ->
      map.get loc "Y1" = Some Y1ptr ->
      map.get loc "Z" = Some Zptr ->
      LittleEndianList.le_combine kbytes = k ->
      2 <= scalarbitsz <= 8*Z.of_nat (List.length kbytes) ->
      (kbytes$@kptr * FElem X0ptr X0 * FElem Y0ptr Y0 * FElem X1ptr X1 * FElem Y1ptr Y1 * FElem Zptr Z * R)%sep mem ->
      proj1_sig R0 = (feval X0, feval Y0, feval Z) ->
      proj1_sig R1 = (feval X1, feval Y1, feval Z) ->
      bounded_by loose_bounds X0 ->
      bounded_by loose_bounds Y0 ->
      bounded_by loose_bounds X1 ->
      bounded_by loose_bounds Y1 ->
      bounded_by loose_bounds Z ->

      (forall tr' mem' loc',
          (tr' = tr) ->
          (exists (R1R0_co_z : Jacobian.co_z R1 R0),
           let R1R0 := exist (fun '(P, Q) => Jacobian.co_z P Q) (R1, R0) R1R0_co_z in
           let '(R1R0', vswap, _) :=
             Loops.while.while (fun '(_, _, i) => i <? scalarbitsz)
               (fun '(R1R0, swap, i) => (zdau_co_z_points (cswap_co_z_points (xorb swap (Z.testbit k i)) R1R0), Z.testbit k i, Z.succ i)) (Z.to_nat (scalarbitsz - 2)) (R1R0, Z.testbit k 1, 2) in
           exists l, (forall s, s <> "b" -> map.get l s = map.get loc s) /\
           loc' = map.put (map.put l "swap" (Core.word.b2w vswap)) "i" (word.of_Z scalarbitsz) /\
           exists X0' Y0' X1' Y1' Z',
             (kbytes$@kptr * FElem X0ptr X0' * FElem Y0ptr Y0' * FElem X1ptr X1' * FElem Y1ptr Y1' * FElem Zptr Z' * R)%sep mem' /\
               bounded_by loose_bounds X0' /\
               bounded_by loose_bounds Y0' /\
               bounded_by loose_bounds X1' /\
               bounded_by loose_bounds Y1' /\
               bounded_by loose_bounds Z' /\
               let '(R1', R0') := proj1_sig R1R0' in
               proj1_sig R0' = (feval X0', feval Y0', feval Z') /\
               proj1_sig R1' = (feval X1', feval Y1', feval Z')) ->
          post tr' mem' loc'
      ) ->

      cmd functions
          bedrock_func_body:(
            while coq:(expr.var "i") < coq:(expr.literal scalarbitsz) {
              {$"b" = load1(coq:(expr.var "k") +
                            coq:(expr.var "i") >> coq:(expr.literal 3)) >>
                      (coq:(expr.var "i") & coq:(expr.literal 7)) & coq:(expr.literal 1)};
              {$"swap" = coq:(expr.var "swap") ^ coq:(expr.var "b")};
              {$"felem_cswap"(coq:(expr.var "swap"), coq:(expr.var "X0"), coq:(expr.var "X1"))};
              {$"felem_cswap"(coq:(expr.var "swap"), coq:(expr.var "Y0"), coq:(expr.var "Y1"))};
              {$"secp256k1_zdau"(coq:(expr.var "X1"), coq:(expr.var "Y1"),
                                 coq:(expr.var "X0"), coq:(expr.var "Y0"),
                                 coq:(expr.var "Z"))};
              {$"swap" = coq:(expr.var "b")};
              $"i" = coq:(expr.var "i") + coq:(expr.literal 1)
      }) tr mem loc post.
  Proof.
    intros. repeat straightline.
    assert (R1R0_z : Jacobian.co_z R1 R0) by (unfold Jacobian.co_z, Jacobian.z_of; rewrite H12, H13; reflexivity).
    pose (R1R0 := exist (fun '(P, Q) => Jacobian.co_z P Q) (R1, R0) R1R0_z).
    pose (test := (fun '(_, _, i) => (Z.ltb i scalarbitsz)):(co_z_points*bool*BinInt.Z)->bool).
    pose (body := (fun '(R1R0, swap, i) =>
              let b := Z.testbit k i in
              let swap := xorb swap b in
              let R1R0 := cswap_co_z_points swap R1R0 in
              let R1R0 := zdau_co_z_points R1R0 in
              let swap := b in
              let i := Z.succ i in
              (R1R0, swap, i)):(co_z_points*bool*BinInt.Z)->(co_z_points*bool*BinInt.Z)).
    pose (inv := fun (v: nat) (t: trace) (m: @map.rep word byte _) (l: @map.rep string word locals) =>
                   t = tr /\
                   exists i (Hi: 2 <= i <= scalarbitsz),
                     v = Z.to_nat (scalarbitsz - i) /\
                     let '(R1R0', swap', i') := Nat.iter (Z.to_nat (i - 2)) (fun s => if test s then body s else s) (R1R0, Z.testbit k 1, 2%Z) in
                     i' = i /\
                     exists loc', (forall s, s <> "b" -> map.get loc' s = map.get loc s) /\
                     l = map.put (map.put loc' "swap" (Core.word.b2w swap')) "i" (word.of_Z i) /\
                     exists X0' Y0' X1' Y1' Z',
                     (kbytes$@kptr * FElem X0ptr X0' * FElem Y0ptr Y0' * FElem X1ptr X1' * FElem Y1ptr Y1' * FElem Zptr Z' * R)%sep m /\
                     bounded_by loose_bounds X0' /\
                     bounded_by loose_bounds Y0' /\
                     bounded_by loose_bounds X1' /\
                     bounded_by loose_bounds Y1' /\
                     bounded_by loose_bounds Z' /\
                     let '(R1', R0') := proj1_sig R1R0' in
                     proj1_sig R0' = (feval X0', feval Y0', feval Z') /\
                     proj1_sig R1' = (feval X1', feval Y1', feval Z')).
    eapply wp_while. exists nat, lt, inv. ssplit; [eapply lt_wf|..].
    (* Invariant holds at beginning *)
    eexists. unfold inv; ssplit; [reflexivity|..].
    exists 2. exists (ltac:(lia): 2 <= 2 <= scalarbitsz). ssplit; [reflexivity|..].
    rewrite DecimalPos.Unsigned.nat_iter_0. ssplit; [reflexivity|..].
    exists loc. ssplit; [reflexivity|..].
    apply Core.map.ext_eq; intros s.
    destruct (String.eqb_spec "i" s); [subst s; rewrite map.get_put_same; assumption|rewrite map.get_put_diff by auto].
    destruct (String.eqb_spec "swap" s); [subst s; rewrite map.get_put_same; assumption|rewrite map.get_put_diff by auto].
    reflexivity. do 5 eexists; ssplit; [ecancel_assumption|..]; try solve_bounds.
    unfold R1R0. cbn [proj1_sig]. rewrite H12, H13. split; reflexivity.
    (* Invariant preservation *)
    intros fuel * Hinv. destruct Hinv as (-> & vi & Hvi & -> & Hiter).
    pose (iter_res := Nat.iter (Z.to_nat (vi - 2)) (fun s => if test s then body s else s) (R1R0, Z.testbit k 1, 2%Z)).
    fold iter_res in Hiter. rewrite (surjective_pairing iter_res) in Hiter.
    rewrite (surjective_pairing (fst iter_res)) in Hiter.
    destruct Hiter as (Hvi' & loc' & Hloc' & -> & Hmem).
    assert (Hsmall: scalarbitsz < 2 ^ 64) by (rewrite <- scalarbitsz_small; apply Z.mod_pos_bound; lia).
    eexists ?[b]; ssplit.
    eexists; split; [apply map.get_put_same|].
    eapply Core.WeakestPrecondition_dexpr_expr; [|apply ExprCompiler.expr_compile_Z_literal].
    cbn. rewrite <- Core.word.morph_ltu by lia.
    reflexivity.
    all: pose proof Zlt_cases vi scalarbitsz;
         intros Hnz; destruct (vi <? scalarbitsz);
         try (rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1 in Hnz;
              congruence); [].
    destruct Hmem as (X0' & Y0' & X1' & Y1' & Z' & Hmem & HX0' & HY0' & HX1' & HY1' & HZ' & Hprojs).
    rewrite (surjective_pairing (proj1_sig _)) in Hprojs.
    pose (R0' := snd (proj1_sig (fst (fst iter_res)))).
    pose (R1' := fst (proj1_sig (fst (fst iter_res)))).
    fold R0' R1' in Hprojs.
    destruct Hprojs as (Hproj0 & Hproj1).
    do 3 straightline. eapply spec_of_testbit; eauto.
    repeat (rewrite map.get_put_diff by congruence).
    rewrite Hloc' by congruence. eassumption.
    apply map.get_put_same. ecancel_assumption.
    lia. lia.
    intros ? ? ? (-> & -> & ->).
    repeat straightline. eexists; split.
    repeat straightline. eexists; split.
    repeat (rewrite map.get_put_diff by congruence).
    apply map.get_put_same. repeat straightline.
    eexists; split. apply map.get_put_same.
    unfold Core.word.b2w. rewrite <- Core.word.morph_xor.
    rewrite Core.Z.lxor_xorb. reflexivity.
    repeat straightline. eexists; split.
    eexists. split. apply map.get_put_same.
    repeat straightline. eexists; split.
    unfold l. repeat (rewrite map.get_put_diff by congruence).
    rewrite Hloc' by congruence. eassumption.
    repeat straightline. eexists; split.
    unfold l. repeat (rewrite map.get_put_diff by congruence).
    rewrite Hloc' by congruence. eassumption.
    repeat straightline.
    straightline_call; ssplit.
    destruct (xorb _ _); simpl; auto.
    rewrite <- Bignum_as_array. unfold FElem in Hmem.
    ecancel_assumption. repeat straightline.
    eexists. split. repeat straightline.
    eexists; split. apply map.get_put_same.
    repeat straightline. eexists; split.
    unfold l. repeat (rewrite map.get_put_diff by congruence).
    rewrite Hloc' by congruence. eassumption.
    repeat straightline. eexists; split.
    unfold l. repeat (rewrite map.get_put_diff by congruence).
    rewrite Hloc' by congruence. eassumption.
    repeat straightline.
    cbv [dlet.dlet] in H26.
    straightline_call; ssplit.
    destruct (xorb _ _); auto.
    rewrite <- Bignum_as_array. ecancel_assumption.
    repeat straightline.
    cbv [dlet.dlet] in H27.
    assert (Hlen: forall ptr v m R, (FElem ptr v * R)%sep m -> Datatypes.length v = felem_size_in_words).
    { unfold FElem. rewrite Bignum_as_array.
      intros * XX. apply Arrays.length_of_sizedlistarray_value_R in XX. exact XX. }
    repeat rewrite cswap_low_combine_eq in H27 by (repeat erewrite Hlen by ecancel_assumption; reflexivity).
    rewrite cswap_combine_eq in H27.
    2: destruct (xorb _ _); cbv; auto.
    2-3: symmetry; eapply Hlen; ecancel_assumption.
    rewrite cswap_combine_eq in H27.
    2: destruct (xorb _ _); cbv; auto.
    2-3: symmetry; eapply Hlen; ecancel_assumption.
    rewrite <- Bignum_as_array in H27.
    repeat rewrite car_cswap, cdr_cswap in H27.
    rewrite word.unsigned_eqb, Core.word.unsigned_of_Z_b2z, word.unsigned_of_Z_1 in H27.
    assert (XY: forall bb, (Z.b2z bb =? 1) = bb) by (destruct bb; auto).
    rewrite XY in H27; clear XY.
    eexists; split.
    repeat (repeat straightline; eexists; split; [unfold l; repeat rewrite map.get_put_diff by congruence; rewrite Hloc' by congruence; eassumption|]).
    repeat straightline. straightline_call; ssplit.
    8: unfold Field.FElem; ecancel_assumption_impl.
    instantiate (1 := if xorb (snd (fst iter_res)) (Z.testbit k vi) then R0' else R1').
    destruct (xorb _ _); [exact Hproj0|exact Hproj1].
    instantiate (1 := if xorb (snd (fst iter_res)) (Z.testbit k vi) then R1' else R0').
    destruct (xorb _ _); [exact Hproj1|exact Hproj0].
    1-4: destruct (xorb _ _); solve_bounds.
    solve_bounds.
    Unshelve. 3: unfold Jacobian.co_z, Jacobian.z_of; destruct (xorb _ _); rewrite Hproj0, Hproj1; reflexivity.
    repeat straightline.
    eexists. ssplit. repeat straightline.
    eexists. split. unfold l. repeat (rewrite map.get_put_diff by congruence).
    apply map.get_put_same. reflexivity.
    repeat straightline.
    eexists. ssplit. repeat straightline.
    eexists. split. unfold l0, l. repeat (rewrite map.get_put_diff by congruence).
    apply map.get_put_same. repeat straightline.
    repeat straightline. eexists. split.
    unfold inv; split; [reflexivity|].
    exists (vi + 1). exists (ltac:(lia): 2 <= vi + 1 <= scalarbitsz).
    ssplit; [reflexivity|].
    replace (Z.to_nat (vi + 1 - 2)) with (S (Z.to_nat (vi - 2))) by lia.
    rewrite Nat.iter_succ. fold iter_res.
    unfold test. rewrite (surjective_pairing iter_res), Hvi'.
    replace (vi <? scalarbitsz) with true by lia.
    rewrite (surjective_pairing (fst iter_res)).
    unfold body. ssplit; [reflexivity|].
    exists (map.put loc' "b" (Core.word.b2w (Z.testbit k vi))); ssplit.
    intros; rewrite map.get_put_diff by congruence. apply Hloc'; auto.
    apply Core.map.ext_eq; intros s.
    unfold l1. destruct (String.eqb_spec s "i"); [subst s; repeat rewrite map.get_put_same|repeat rewrite map.get_put_diff by congruence].
    rewrite word.ring_morph_add; reflexivity.
    unfold l0. destruct (String.eqb_spec s "swap"); [subst s; repeat rewrite map.get_put_same; reflexivity|repeat rewrite map.get_put_diff by congruence].
    unfold l. repeat rewrite map.get_put_diff by congruence.
    destruct (String.eqb_spec s "b"); [subst s; repeat rewrite map.get_put_same; reflexivity|repeat rewrite map.get_put_diff by congruence; reflexivity].
    do 5 eexists; ssplit; [ecancel_assumption_impl|..].
    1-5: solve_bounds.
    rewrite (surjective_pairing (proj1_sig _)).
    rewrite proj1_sig_zdau_co_z_points.
    unfold JacobianCoZ.frep256k1 in H28, H29.
    unfold frep256k1. rewrite <- H28, <- H29.
    rewrite <- (surjective_pairing (Jacobian.zdau _ _ _)).
    split; repeat f_equal; apply zdau_eq; rewrite proj1_sig_cswap_co_z_points; reflexivity.
    (* measure decreases *) lia.
    (* post condition *)
    assert (vi = scalarbitsz) as -> by lia.
    assert (iter_res = Nat.iter (S (Z.to_nat (scalarbitsz - 2))) (fun s : co_z_points * bool * BinNums.Z => if test s then body s else s) (R1R0, Z.testbit k 1, 2)).
    { rewrite Nat.iter_succ. fold iter_res.
      rewrite (surjective_pairing iter_res) at 2.
      rewrite Hvi'. simpl test.
      replace (scalarbitsz <? scalarbitsz) with false by lia.
      unfold iter_res. rewrite (surjective_pairing (fst _)).
      reflexivity. }
    rewrite <- while_is_iter in H22.
    unfold test, body in H22.
    apply H19; [reflexivity|].
    exists R1R0_z. fold R1R0. rewrite <- H22.
    rewrite (surjective_pairing (iter_res)).
    rewrite (surjective_pairing (fst (iter_res))).
    eexists; ssplit; eauto.
  Qed.

  Lemma spec_of_laddermul_ok : program_logic_goal_for_function! (secp256k1_laddermul scalarbitsz).
  Proof.
    Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds].

    repeat first [match goal with | |- cmd _ bedrock_func_body:($_ = load1(coq:(expr.var "k") + coq:(expr.var "i") >> coq:(expr.literal 3)) >> (coq:(expr.var "i") & coq:(expr.literal 7)) & coq:(expr.literal 1)) _ _ _ _ => idtac end |straightline].
    eapply spec_of_testbit; try reflexivity; try ecancel_assumption_impl; try lia.

    assert (HPaff: Jacobian.z_of (Jacobian.of_affine P) = F.one) by (apply (ScalarMult.ScalarMult.joye_ladder_obligation_1 P HPnz)).

    repeat straightline.
    single_step.
    instantiate (3 := Jacobian.of_affine P).
    unfold Jacobian.of_affine, Jacobian.of_affine_impl, WeierstrassCurve.W.coordinates.
    cbn [proj1_sig]. rewrite H15. eexists. reflexivity.
    1-2: solve_bounds.
    repeat match goal with
    | H: context [Array.array ptsto _ ?a _] |- context [Field.FElem ?a _] =>
        seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 4 a) H; [trivial|]
    end.
    multimatch goal with
    | |- _ ?m1 =>
        multimatch goal with
        | H:_ ?m2
          |- _ =>
            syntactic_unify._syntactic_unify_deltavar m1 m2;
            refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H
        end
    end.
    cancel. cancel_seps_at_indices 0%nat 4%nat; [reflexivity|].
    cancel_seps_at_indices 0%nat 3%nat; [reflexivity|].
    cancel_seps_at_indices 0%nat 2%nat; [reflexivity|].
    cancel_seps_at_indices 0%nat 1%nat; [reflexivity|].
    cancel_seps_at_indices 0%nat 0%nat; [reflexivity|].
    cancel_seps_at_indices 3%nat 0%nat; [reflexivity|].
    cancel_seps_at_indices 3%nat 0%nat; [reflexivity|].
    ecancel.

    repeat straightline.
    instantiate (1:=HPaff) in H48.
    eapply spec_of_inner_loop; try reflexivity; try ecancel_assumption_impl; try lia.
    exact H49. exact H48.
    1-5: solve_bounds.
    repeat straightline.
    rewrite H18 in H47.
    case_eq (Loops.while.while (fun '(_, _, i) => i <? scalarbitsz)
               (fun '(R1R0, swap, i) =>
                  (zdau_co_z_points (cswap_co_z_points (xorb swap (Z.testbit k i)) R1R0), Z.testbit k i, Z.succ i)) (Z.to_nat (scalarbitsz - 2))
               (exist (fun '(P, Q) => Jacobian.co_z P Q) (fst (Jacobian.tplu (Jacobian.of_affine P) HPaff), snd (Jacobian.tplu (Jacobian.of_affine P) HPaff)) x4, Z.testbit k 1, 2)); intros [R1R0' vswap] ?i Hloopeq.
    rewrite Hloopeq in H47. repeat straightline.

    eexists; ssplit. repeat straightline.
    eexists; ssplit; [unfold loc'0; repeat rewrite map.get_put_diff by congruence; apply map.get_put_same|repeat straightline].
    eexists; ssplit; [unfold loc'0; repeat rewrite map.get_put_diff by congruence; rewrite H46|]; repeat straightline. congruence.
    eexists; ssplit; [unfold loc'0; repeat rewrite map.get_put_diff by congruence; rewrite H46|]; repeat straightline. congruence.

    single_step. rewrite Core.word.b2w_if; destruct vswap; auto.
    rewrite <- Bignum_as_array. unfold FElem in H56. ecancel_assumption.
    repeat straightline. red in H64.
    assert (Hlen: forall ptr v m R, (FElem ptr v * R)%sep m -> Datatypes.length v = felem_size_in_words).
    { unfold FElem. rewrite Bignum_as_array.
      intros * XX. apply Arrays.length_of_sizedlistarray_value_R in XX. exact XX. }
    rewrite cswap_low_combine_eq in H64 by (repeat erewrite Hlen by ecancel_assumption; reflexivity).
    rewrite cswap_combine_eq in H64.
    2: destruct vswap; cbv; auto.
    2-3: symmetry; eapply Hlen; ecancel_assumption.
    repeat rewrite car_cswap, cdr_cswap in H64.
    rewrite word.unsigned_eqb, Core.word.unsigned_b2w, word.unsigned_of_Z_1 in H64.
    assert (XY: forall bb, (Z.b2z bb =? 1) = bb) by (destruct bb; auto).
    rewrite XY in H64; clear XY.
    rewrite <- Bignum_as_array in H64.
    eexists; ssplit. repeat straightline.
    eexists; ssplit; [unfold loc'0; repeat rewrite map.get_put_diff by congruence; apply map.get_put_same|repeat straightline].
    eexists; ssplit; [unfold loc'0; repeat rewrite map.get_put_diff by congruence; rewrite H46|]; repeat straightline. congruence.
    eexists; ssplit; [unfold loc'0; repeat rewrite map.get_put_diff by congruence; rewrite H46|]; repeat straightline. congruence.

    single_step. rewrite Core.word.b2w_if; destruct vswap; auto.
    rewrite <- Bignum_as_array. ecancel_assumption.
    repeat straightline. red in H65.
    rewrite cswap_low_combine_eq in H65 by (repeat erewrite Hlen by ecancel_assumption; reflexivity).
    rewrite cswap_combine_eq in H65.
    2: destruct vswap; cbv; auto.
    2-3: symmetry; eapply Hlen; ecancel_assumption.
    repeat rewrite car_cswap, cdr_cswap in H65.
    rewrite word.unsigned_eqb, Core.word.unsigned_b2w, word.unsigned_of_Z_1 in H65.
    assert (XY: forall bb, (Z.b2z bb =? 1) = bb) by (destruct bb; auto).
    rewrite XY in H65; clear XY.
    rewrite <- Bignum_as_array in H65.
    eexists; ssplit. repeat straightline.
    eexists; ssplit. unfold l9. rewrite map.get_put_diff by congruence.
    apply map.get_put_same. repeat straightline.
    eexists; ssplit; [apply map.get_put_same|]. repeat straightline.
    eexists; ssplit. unfold l9, l8, loc'0.
    repeat (rewrite map.get_put_diff by congruence).
    rewrite H46. repeat straightline. congruence.
    repeat straightline. eexists; ssplit. unfold l9, l8, loc'0.
    repeat (rewrite map.get_put_diff by congruence).
    rewrite H46. repeat straightline. congruence.
    repeat straightline. eexists; ssplit. unfold l9, l8, loc'0.
    repeat (rewrite map.get_put_diff by congruence).
    rewrite H46. repeat straightline. congruence.
    repeat straightline.
    destruct R1R0' as ((R1'& R0') & HR1R0') eqn:HeqR1R0'.
    destruct H62.
    single_step.
    exists (if vswap then feval x8 else feval x6).
    exists (if vswap then feval x9 else feval x7).
    instantiate (2:=if vswap then R1' else R0').
    destruct (vswap); [exact H68|exact H62].
    exists 1%F. instantiate (3:=Jacobian.of_affine P).
    unfold Jacobian.of_affine, WeierstrassCurve.W.coordinates.
    cbv [proj1_sig].
    assert (proj1_sig P = (let (xyi, _) := P in xyi)) as <- by (destruct P; reflexivity).
    rewrite H15. reflexivity.
    1-3:solve_bounds.
    repeat match goal with
    | H: context [Array.array ptsto _ ?a _] |- context [Field.FElem ?a _] =>
        seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 4 a) H; [trivial|]
    end.
    multimatch goal with
    | |- _ ?m1 =>
        multimatch goal with
        | H:_ ?m2
          |- _ =>
            syntactic_unify._syntactic_unify_deltavar m1 m2;
            refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H
        end
    end.
    cancel. cancel_seps_at_indices 0%nat 1%nat; [reflexivity|].
    cancel_seps_at_indices 0%nat 0%nat; [reflexivity|].
    cancel_seps_at_indices 6%nat 0%nat; [reflexivity|].
    cancel_seps_at_indices 6%nat 0%nat; [reflexivity|].
    cancel_seps_at_indices 5%nat 0%nat; [reflexivity|].
    ecancel.
    instantiate (1:=HPaff) in H73.
    repeat straightline.

    eexists; ssplit. repeat straightline.
    eexists; ssplit. apply map.get_put_same. repeat straightline.
    eexists; ssplit; [apply map.get_put_same|]; repeat straightline.
    single_step.
    2-3: ecancel_assumption_impl.
    solve_bounds.
    repeat straightline.
    eexists; split. unfold l9, l8, loc'0.
    repeat (repeat straightline; eexists; ssplit; [repeat (rewrite map.get_put_diff by congruence); rewrite H46; repeat straightline; congruence|]).
    repeat straightline. eexists; ssplit.
    repeat (rewrite map.get_put_diff by congruence); apply map.get_put_same.
    repeat straightline. eexists; ssplit.
    repeat (rewrite map.get_put_diff by congruence); apply map.get_put_same.
    repeat straightline. eexists; ssplit.
    repeat (rewrite map.get_put_diff by congruence); rewrite H46; repeat straightline; congruence.
    repeat straightline.
    cbv [un_model un_opp] in H79.

    assert (Hzaddu_ob: Jacobian.co_z (if vswap then R1' else R0') (Jacobian.opp (snd (Jacobian.make_co_z (if vswap then R1' else R0') (Jacobian.of_affine P) HPaff)))).
    { unfold Jacobian.co_z, Jacobian.z_of, Jacobian.opp.
      cbv [proj1_sig] in *. rewrite H75.
      destruct vswap; [rewrite H68|rewrite H62]; reflexivity. }
    single_step.
    instantiate (1:=x10).
    instantiate (1:=if vswap then x9 else x7).
    instantiate (1:=if vswap then x8 else x6).
    instantiate (1:=if vswap then R1' else R0').
    destruct vswap; [exact H68|exact H62].
    instantiate (1:=x13). instantiate (1:=x11).
    instantiate (1:=Jacobian.opp (snd (Jacobian.make_co_z (if vswap then R1' else R0') (Jacobian.of_affine P) HPaff))).
    unfold Jacobian.opp.
    cbv [proj1_sig]. cbv [proj1_sig] in H75. rewrite H75.
    unfold JacobianCoZ.frep256k1. unfold frep256k1 in H79.
    rewrite H79. reflexivity.
    1-2: destruct vswap; solve_bounds.
    1-3: solve_bounds.
    repeat match goal with
    | H: context [Array.array ptsto _ ?a _] |- context [Field.FElem ?a _] =>
        seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 4 a) H; [trivial|]
    end.
    multimatch goal with
    | |- _ ?m1 =>
        multimatch goal with
        | H:_ ?m2
          |- _ =>
            syntactic_unify._syntactic_unify_deltavar m1 m2;
            refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H
        end
    end.
    cancel. cancel_seps_at_indices 9%nat 0%nat; [reflexivity|].
    cancel_seps_at_indices 9%nat 0%nat; [reflexivity|].
    cancel_seps_at_indices 7%nat 0%nat; [reflexivity|].
    cancel_seps_at_indices 5%nat 0%nat; [reflexivity|].
    cancel_seps_at_indices 0%nat 0%nat; [reflexivity|].
    cancel_seps_at_indices 4%nat 0%nat; [reflexivity|].
    cancel_seps_at_indices 3%nat 0%nat; [reflexivity|].
    cancel_seps_at_indices 0%nat 0%nat; [reflexivity|].
    ecancel.
    instantiate (1:=Hzaddu_ob) in H73.
    repeat first [match goal with | |- cmd _ bedrock_func_body:($_ = load1(coq:(expr.var "k") + coq:(expr.var "i") >> coq:(expr.literal 3)) >> (coq:(expr.var "i") & coq:(expr.literal 7)) & coq:(expr.literal 1)) _ _ _ _ => idtac end |straightline].
    eapply spec_of_testbit; try reflexivity; try ecancel_assumption_impl; try lia.
    unfold l10, l9, l8, loc'0. repeat (rewrite map.get_put_diff by congruence).
    rewrite H46 by congruence. reflexivity.
    apply map.get_put_same. lia. lia.
    repeat straightline.

    eexists; ssplit. repeat straightline.
    eexists; ssplit; [apply map.get_put_same|].
    repeat straightline. eexists; ssplit.
    unfold loc'1, l10, l9, l8, loc'0. repeat (rewrite map.get_put_diff by congruence).
    rewrite H46 by congruence. reflexivity.
    repeat straightline. eexists; ssplit.
    unfold loc'1, l10, l9, l8, loc'0. repeat (rewrite map.get_put_diff by congruence).
    rewrite H46 by congruence. reflexivity.
    repeat straightline.
    rewrite H18.
    single_step.
    rewrite Core.word.b2w_if; destruct (Z.testbit k 0); auto.
    rewrite <- Bignum_as_array.
    unfold Field.FElem in H89. ecancel_assumption_impl.
    repeat straightline. red in H90.
    rewrite <- Bignum_as_array in H90.
    rewrite cswap_low_combine_eq in H90 by (repeat erewrite Hlen by ecancel_assumption_impl; reflexivity).
    rewrite cswap_combine_eq in H90.
    2: destruct (Z.testbit k 0); cbv; auto.
    2-3: symmetry; eapply Hlen; ecancel_assumption_impl.
    repeat rewrite car_cswap, cdr_cswap in H90.
    rewrite word.unsigned_eqb, Core.word.unsigned_b2w, word.unsigned_of_Z_1 in H90.
    assert (XY: forall bb, (Z.b2z bb =? 1) = bb) by (destruct bb; auto).
    rewrite XY in H90; clear XY.
    eexists; ssplit. repeat straightline.
    eexists; ssplit; [apply map.get_put_same|].
    repeat straightline. eexists; ssplit.
    unfold loc'1, l10, l9, l8, loc'0. repeat (rewrite map.get_put_diff by congruence).
    rewrite H46 by congruence. reflexivity.
    repeat straightline. eexists; ssplit.
    unfold loc'1, l10, l9, l8, loc'0. repeat (rewrite map.get_put_diff by congruence).
    rewrite H46 by congruence. reflexivity.
    repeat straightline.
    rewrite H18.
    single_step.
    destruct (Z.testbit k 0); cbv; auto.
    rewrite <- Bignum_as_array.
    unfold Field.FElem in H90. ecancel_assumption_impl.
    repeat straightline. red in H91.
    rewrite <- Bignum_as_array in H91.
    rewrite cswap_low_combine_eq in H91 by (repeat erewrite Hlen by ecancel_assumption_impl; reflexivity).
    rewrite cswap_combine_eq in H91.
    2: destruct (Z.testbit k 0); cbv; auto.
    2-3: symmetry; eapply Hlen; ecancel_assumption_impl.
    repeat rewrite car_cswap, cdr_cswap in H91.
    rewrite word.unsigned_eqb, Core.word.unsigned_b2w, word.unsigned_of_Z_1 in H91.
    assert (XY: forall bb, (Z.b2z bb =? 1) = bb) by (destruct bb; auto).
    rewrite XY in H91; clear XY.

    eexists; ssplit. repeat straightline. eexists; ssplit.
    unfold loc'1, l10, l9, l8, loc'0. repeat (rewrite map.get_put_diff by congruence).
    rewrite H46 by congruence. reflexivity.
    repeat straightline. eexists; ssplit.
    unfold loc'1, l10, l9, l8, loc'0. repeat (rewrite map.get_put_diff by congruence).
    rewrite H46 by congruence. reflexivity.
    repeat straightline.
    single_step.
    3: unfold Field.FElem; ecancel_assumption_impl.
    reflexivity. solve_bounds.
    repeat straightline.
    eexists; ssplit. repeat straightline. eexists; ssplit.
    unfold loc'1, l10, l9, l8, loc'0. repeat (rewrite map.get_put_diff by congruence).
    rewrite H46 by congruence. reflexivity.
    repeat straightline. eexists; ssplit.
    unfold loc'1, l10, l9, l8, loc'0. repeat (rewrite map.get_put_diff by congruence).
    rewrite H46 by congruence. reflexivity.
    repeat straightline. eexists; ssplit.
    unfold loc'1, l10, l9, l8, loc'0. repeat (rewrite map.get_put_diff by congruence).
    rewrite H46 by congruence. reflexivity.
    repeat straightline.
    single_step.
    3-5: unfold FElem; ecancel_assumption_impl.
    destruct (Z.testbit k 0); solve_bounds.
    solve_bounds.
    repeat straightline.
    eexists; ssplit. repeat straightline.
    repeat (eexists; ssplit; [unfold loc'1, l10, l9, l8, loc'0; repeat (rewrite map.get_put_diff by congruence); rewrite H46 by congruence; reflexivity|]; repeat straightline).
    cbv [bin_model bin_mul] in H95.

    single_step.
    3-5: unfold FElem in *; ecancel_assumption_impl.
    1-2: solve_bounds.
    repeat straightline.
    eexists; ssplit. repeat straightline.
    repeat (eexists; ssplit; [unfold loc'1, l10, l9, l8, loc'0; repeat (rewrite map.get_put_diff by congruence); rewrite H46 by congruence; reflexivity|]; repeat straightline).
    cbv [bin_model bin_mul] in H98.

    single_step.
    2-3: unfold FElem in *; ecancel_assumption_impl.
    destruct (Z.testbit k 0); solve_bounds.
    repeat straightline.
    eexists; ssplit. repeat straightline.
    repeat (eexists; ssplit; [unfold loc'1, l10, l9, l8, loc'0; repeat (rewrite map.get_put_diff by congruence); rewrite H46 by congruence; reflexivity|]; repeat straightline).
    cbv [bin_model bin_mul] in H101.

    single_step.
    3-5: unfold FElem in *; ecancel_assumption_impl.
    1-2: solve_bounds.
    repeat straightline.
    cbv [bin_model bin_mul] in H104.

    cbv [FElem] in *.
    replace JacobianCoZ.frep256k1 with frep256k1 in * by reflexivity.
    replace Addchain.frep256k1 with frep256k1 in * by reflexivity.
    repeat match goal with
    | |- context [anybytes ?a _ _] =>
        match goal with
        | H: _ ?a' |- context [map.split ?a' _ _] =>
            seprewrite_in (@Bignum.Bignum_to_bytes _ _ _ _ _ _ felem_size_in_words a) H
        end
    end.
    extract_ex1_and_emp_in H106.
    repeat straightline.

    unfold ScalarMult.joye_ladder.
    unfold ScalarMult.joye_ladder_inner.
    assert (ScalarMult.tplu_co_z_points (Jacobian.of_affine P) (ScalarMult.ScalarMult.joye_ladder_obligation_1 P HPnz) = exist (fun '(P, Q) => Jacobian.co_z P Q) (fst (Jacobian.tplu (Jacobian.of_affine P) HPaff), snd (Jacobian.tplu (Jacobian.of_affine P) HPaff)) x4) as ->.
    { unfold ScalarMult.tplu_co_z_points.
      apply eq_sig_hprop.
      - intros. destruct x24.
        apply Eqdep_dec.UIP_dec; apply F.eq_dec.
      - cbv [proj1_sig].
        rewrite <- (surjective_pairing (Jacobian.tplu (Jacobian.of_affine P) HPaff)).
        f_equal. apply Eqdep_dec.UIP_dec; apply F.eq_dec. }
    assert (Z.to_nat scalarbitsz - 2 = Z.to_nat (scalarbitsz - 2))%nat as -> by lia.
    match goal with
    | |- context [Loops.while.while ?test ?body ?fuel ?args] =>
        match type of Hloopeq with
        | context [Loops.while.while ?test1 ?body1 ?fuel1 ?args1] =>
            replace (Loops.while.while test body fuel args) with (Loops.while.while test1 body1 fuel1 args1) by reflexivity
        end
    end.
    rewrite Hloopeq.
    rewrite (proj1_sig_cswap_co_z_points vswap).
    assert (red_proj1_sig: forall (A : Type) (P : A -> Prop) (x : A) (Px : P x), proj1_sig (exist P x Px) = x) by reflexivity.
    rewrite red_proj1_sig.
    cbv [fst snd].
    rewrite proj1_sig_cswap_co_z_points, proj1_sig_zaddu_co_z_points.
    rewrite <- (surjective_pairing (Jacobian.zaddu _ _ _)).
    assert (Jacobian.zaddu
              (fst (proj1_sig (make_co_z_points (if vswap then R1' else R0') (Jacobian.opp (Jacobian.of_affine P)) (ScalarMult.opp_of_affine P HPnz))))
              (snd (proj1_sig (make_co_z_points (if vswap then R1' else R0') (Jacobian.opp (Jacobian.of_affine P)) (ScalarMult.opp_of_affine P HPnz))))
              (co_z_conv (make_co_z_points (if vswap then R1' else R0') (Jacobian.opp (Jacobian.of_affine P)) (ScalarMult.opp_of_affine P HPnz))) =
              Jacobian.zaddu (if vswap then R1' else R0')
                (Jacobian.opp (snd (Jacobian.make_co_z (if vswap then R1' else R0') (Jacobian.of_affine P) HPaff))) Hzaddu_ob) as ->.
    { apply zaddu_eq.
      - unfold make_co_z_points. rewrite red_proj1_sig.
        unfold Jacobian.make_co_z. cbv [fst].
        apply eq_sig_hprop; [|rewrite red_proj1_sig].
        + intros. destruct x24 as ((?X & ?Y) & ?Z).
          destruct (dec (Z = 0%F)). destruct p, q; reflexivity.
          apply Eqdep_dec.UIP_dec; apply F.eq_dec.
        + destruct (Jacobian.of_affine P) as (((?X & ?Y) & ?Z) & ?H).
          destruct R1' as (((?X & ?Y) & ?Z) & ?H).
          destruct R0' as (((?X & ?Y) & ?Z) & ?H).
          destruct vswap; cbv [Jacobian.opp]; repeat rewrite red_proj1_sig; reflexivity.
      - unfold make_co_z_points. rewrite red_proj1_sig.
        unfold Jacobian.make_co_z. cbv [snd].
        apply eq_sig_hprop; [|rewrite red_proj1_sig].
        + intros. destruct x24 as ((?X & ?Y) & ?Z).
          destruct (dec (Z = 0%F)). destruct p, q; reflexivity.
          apply Eqdep_dec.UIP_dec; apply F.eq_dec.
        + unfold Jacobian.opp; repeat rewrite red_proj1_sig.
          destruct (Jacobian.of_affine P) as (((?X & ?Y) & ?Z) & ?H).
          destruct R1' as (((?X & ?Y) & ?Z) & ?H).
          destruct R0' as (((?X & ?Y) & ?Z) & ?H).
          destruct vswap; repeat rewrite red_proj1_sig; f_equal; f_equal; ring. }
    unfold Jacobian.to_affine, Jacobian.to_affine_impl. rewrite red_proj1_sig.
    destruct (Z.testbit k 0); [rewrite H83|rewrite H82];
    match goal with
    | |- context [if ?test then _ else _] => destruct test
    end; do 2 eexists; ssplit; try ecancel_assumption_impl; try solve_bounds;
    repeat match goal with
           | H : feval ?a = _ |- context [feval ?a] => rewrite H
           end.
    1,2,5,6: rewrite F.inv_0; ring.
    Add Field Private_field : (Algebra.Field.field_theory_for_stdlib_tactic (T:=F M_pos)).
    Import Field_tac.
    1-4: field; exact n.
  Qed.

End WithParameters.

Require Import bedrock2.ToCString.
Require Import coqutil.Macros.WithBaseName.
Definition funcs :=
  let secp256k1_laddermul := (secp256k1_laddermul 256%Z) in
  List.app
  [ secp256k1_opp;
    secp256k1_mul;
    secp256k1_add;
    secp256k1_sub;
    secp256k1_square;
    secp256k1_to_bytes;
    secp256k1_from_bytes;
    secp256k1_from_mont;
    secp256k1_to_mont;
    secp256k1_select_znz;
    secp256k1_felem_copy;
    ("felem_cswap", secp256k1_felem_cswap)]
  &[,secp256k1_make_co_z;
     secp256k1_zaddu;
     secp256k1_dblu;
     secp256k1_tplu;
     secp256k1_zdau;
     secp256k1_inv;
     secp256k1_laddermul
     ].

Lemma link_secp256k1_felem_copy :
  spec_of_secp256k1_felem_copy (map.of_list funcs).
Proof. apply secp256k1_felem_copy_correct. reflexivity. Qed.
(* ^-- Why is only felem_copy so slow ???!!! *)

(* Assume m = 2 ^ 256 - 2 ^ 32 - 977 is prime *)
Lemma link_secp256k1_laddermul (secp256k1_prime: Znumtheory.prime m) :
  @spec_of_laddermul (F.field_modulo M_pos) (0%F) (F.of_Z _ 7%Z) (256%Z) (map.of_list funcs).
Proof.
  eapply spec_of_laddermul_ok; repeat
  match goal with
  | |- map.get _ _ = _ => reflexivity
  | |- spec_of_secp256k1_tplu _ => eapply secp256k1_tplu_ok
  | |- spec_of_dblu _ => eapply secp256k1_dblu_ok
  | |- spec_of_zaddu _ => eapply secp256k1_zaddu_ok
  | |- spec_of_secp256k1_opp _ => eapply secp256k1_opp_correct
  | |- spec_of_secp256k1_zaddu _ => eapply secp256k1_zaddu_ok
  | |- spec_of_secp256k1_zdau _ => eapply secp256k1_zdau_ok
  | |- spec_of_secp256k1_make_co_z _ => eapply secp256k1_make_co_z_ok
  | |- spec_of_secp256k1_inv _ => eapply secp256k1_inv_ok
  | |- JacobianCoZ.spec_of_secp256k1_add _ => eapply secp256k1_add_correct
  | |- JacobianCoZ.spec_of_secp256k1_sub _ => eapply secp256k1_sub_correct
  | |- spec_of_secp256k1_mul _ => eapply secp256k1_mul_correct
  | |- JacobianCoZ.spec_of_secp256k1_mul _ => eapply secp256k1_mul_correct
  | |- JacobianCoZ.spec_of_secp256k1_square _ => eapply secp256k1_square_correct
  | |- Addchain.spec_of_secp256k1_mul _ => eapply secp256k1_mul_correct
  | |- Addchain.spec_of_secp256k1_square _ => eapply secp256k1_square_correct
  | |- spec_of_secp256k1_cswap _ => eapply cswap_body_correct
  | |- spec_of_secp256k1_felem_copy _ => apply link_secp256k1_felem_copy
  | |- Z.of_nat _ < 2 ^ 64 => unfold field_representation, Signature.field_representation, Representation.frep; cbn; cbv; trivial
  | |- Core.__rupicola_program_marker _ => cbv [Core.__rupicola_program_marker]; tauto
  | _ => idtac
  end.
  Unshelve.
  all: cbn; reflexivity.
Qed.

(* Compute (ToCString.c_module funcs). *)
