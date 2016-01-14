Require Import Galois GaloisTheory Galois.BaseSystem Galois.ModularBaseSystem.
Require Import List Util.ListUtil.
Import ListNotations.
Require Import ZArith.ZArith Zpower ZArith Znumtheory.
Require Import QArith.QArith QArith.Qround.
Require Import VerdiTactics.
Close Scope Q.

Ltac twoIndices i j base := 
    intros;
    assert (In i (seq 0 (length base))) by nth_tac;
    assert (In j (seq 0 (length base))) by nth_tac;
    repeat match goal with [ x := _ |- _ ] => subst x end;
    simpl in *; repeat break_or_hyp; try omega; vm_compute; reflexivity.

Module Base25Point5_10limbs <: BaseCoefs.
  Local Open Scope Z_scope.
  Definition base := map (fun i => two_p (Qceiling (Z_of_nat i *255 # 10))) (seq 0 10).
  Lemma base_positive : forall b, In b base -> b > 0.
  Proof.
    compute; intuition; subst; intuition.
  Qed.

  Lemma b0_1 : forall x, nth_default x base 0 = 1.
  Proof.
    auto.
  Qed.

  Lemma base_good :
    forall i j, (i+j < length base)%nat ->
    let b := nth_default 0 base in
    let r := (b i * b j) / b (i+j)%nat in
    b i * b j = r * b (i+j)%nat.
  Proof.
    twoIndices i j base.
  Qed.
End Base25Point5_10limbs.

Module Modulus25519 <: Modulus.
  Local Open Scope Z_scope.
  Definition two_255_19 := two_p 255 - 19.
  Lemma two_255_19_prime : prime two_255_19. Admitted.
  Definition prime25519 := exist _ two_255_19 two_255_19_prime.
  Definition modulus := prime25519.
End Modulus25519.

Module GF25519Base25Point5Params <: PseudoMersenneBaseParams Base25Point5_10limbs Modulus25519.
  Import Base25Point5_10limbs.
  Import Modulus25519.
  Local Open Scope Z_scope.
  (* TODO: do we actually want B and M "up there" in the type parameters? I was
  * imagining writing something like "Paramter Module M : Modulus". *)

  Definition k := 255.
  Definition c := 19.
  Lemma modulus_pseudomersenne :
    primeToZ modulus = 2^k - c.
  Proof.
    auto.
  Qed.

  Lemma base_matches_modulus :
    forall i j,
    (i   <  length base)%nat ->
    (j   <  length base)%nat ->
    (i+j >= length base)%nat ->
    let b := nth_default 0 base in
    let r := (b i * b j)  /   (2^k * b (i+j-length base)%nat) in
              b i * b j = r * (2^k * b (i+j-length base)%nat).
  Proof.
    twoIndices i j base.
  Qed.

  Lemma base_succ : forall i, ((S i) < length base)%nat -> 
    let b := nth_default 0 base in
    b (S i) mod b i = 0.
  Proof.
    intros; twoIndices i (S i) base.
  Qed.

  Lemma base_tail_matches_modulus:
    2^k mod nth_default 0 base (pred (length base)) = 0.
  Proof.
    auto.
  Qed.

  Lemma b0_1 : forall x, nth_default x base 0 = 1.
  Proof.
    auto.
  Qed.

  Lemma k_nonneg : 0 <= k.
  Proof.
    rewrite Zle_is_le_bool; auto.
  Qed.
End GF25519Base25Point5Params.

Module GF25519Base25Point5 := GFPseudoMersenneBase Base25Point5_10limbs Modulus25519 GF25519Base25Point5Params.

Ltac expand_list ls :=
  let Hlen := fresh "Hlen" in
  match goal with [H: ls = ?lsdef |- _ ] =>
      assert (Hlen:length ls=length lsdef) by (f_equal; exact H)
  end;
  simpl in Hlen;
  repeat progress (let n:=fresh ls in destruct ls as [|n ]; try solve [revert Hlen; clear; discriminate]);
  clear Hlen.

Ltac letify r :=
  match goal with
  | [ H' : r = _ |- _ ] =>
    match goal with
    | [ H : ?x = ?e |- _ ] =>
      is_var x;
      match goal with (* only letify equations that appear nowhere other than r *)
      | _ => clear H H' x; fail 1
      | _ => fail 2
      end || idtac;
      pattern x in H';
      match type of H' with
      | (fun z => r = @?e' z) x =>
        let H'' := fresh "H" in
        assert (H'' : r = let x := e in e' x) by
          (* congruence is slower for every subsequent letify *)
          (rewrite H'; subst x; reflexivity);
        clear H'; subst x; rename H'' into H'; cbv beta in H'
      end
    end
  end.

Ltac expand_list_equalities := repeat match goal with
  | [H: (?x::?xs = ?y::?ys) |- _ ] =>
      let eq_head := fresh "Heq" x in
      assert (x = y) as eq_head by (eauto using cons_eq_head);
      assert (xs = ys) by (eauto using cons_eq_tail);
      clear H
  | [H:?x = ?x|-_] => clear H
end.

Section GF25519Base25Point5Formula.
  Import GF25519Base25Point5.
  Import Field.

  Hint Rewrite
    Z.mul_0_l
    Z.mul_0_r
    Z.mul_1_l
    Z.mul_1_r
    Z.add_0_l
    Z.add_0_r
    Z.add_assoc
    Z.mul_assoc
    : Z_identities.

  Ltac deriveModularMultiplicationWithCarries carryscript :=
  let h := fresh "h" in
  let fg := fresh "fg" in
  let Hfg := fresh "Hfg" in
  intros;
  repeat match goal with
  | [ Hf: rep ?fs ?f, Hg: rep ?gs ?g |- rep _ ?ret ] =>
      remember (carry_sequence carryscript (mul fs gs)) as fg;
      assert (rep fg ret) as Hfg; [subst fg; apply carry_sequence_rep, mul_rep; eauto|]
  | [ H: In ?x carryscript |- ?x < ?bound ] => abstract (revert H; clear; cbv; intros; repeat break_or_hyp; intuition)
  | [ Heqfg: fg = carry_sequence _ (mul _ _) |- rep _ ?ret ] =>
      (* expand bignum multiplication *)
      cbv [plus
        seq rev app length map fold_right fold_left skipn firstn nth_default nth_error value error
        mul reduce B.add Base25Point5_10limbs.base GF25519Base25Point5Params.c
        E.add E.mul E.mul' E.mul_each E.mul_bi E.mul_bi' E.zeros EC.base] in Heqfg;
      repeat match goal with [H:context[E.crosscoef ?a ?b] |- _ ] => (* do this early for speed *)
          let c := fresh "c" in set (c := E.crosscoef a b) in H; compute in c; subst c end;
      autorewrite with Z_identities in Heqfg;
      (* speparate out carries *)
      match goal with [ Heqfg: fg = carry_sequence _ ?hdef |- _ ] => remember hdef as h end;
      (* one equation per limb *)
      expand_list h; expand_list_equalities;
      (* expand carry *)
      cbv [GF25519Base25Point5.carry_sequence fold_right rev app] in Heqfg
  | [H1: ?a = ?b, H2: ?b = ?c |- _ ] => subst a
  | [Hfg: context[carry ?i (?x::?xs)] |- _ ] => (* simplify carry *)
      let cr := fresh "cr" in
      remember (carry i (x::xs)) as cr in Hfg;
      match goal with [ Heq : cr = ?crdef |- _ ] =>
          (* is there any simpler way to do this? *)
          cbv [carry carry_simple carry_and_reduce] in Heq;
          simpl eq_nat_dec in Heq; cbv iota beta in Heq;
          cbv [set_nth nth_default nth_error value add_to_nth] in Heq;
          expand_list cr; expand_list_equalities
      end
  | [H: context[cap ?i] |- _ ] => let c := fresh "c" in remember (cap i) as c in H;
      match goal with [Heqc: c = cap i |- _ ] =>
          (* is there any simpler way to do this? *)
          unfold cap, Base25Point5_10limbs.base in Heqc;
          simpl eq_nat_dec in Heqc;
          cbv [nth_default nth_error value error] in Heqc;
          simpl map in Heqc;
          cbv [GF25519Base25Point5Params.k] in Heqc
      end;
      subst c;
      repeat rewrite Zdiv_1_r in H;
      repeat rewrite two_power_pos_equiv in H;
      repeat rewrite <- Z.pow_sub_r in H by (abstract (clear; firstorder));
      repeat rewrite <- Z.land_ones in H by (abstract (apply Z.leb_le; reflexivity));
      repeat rewrite <- Z.shiftr_div_pow2 in H by (abstract (apply Z.leb_le; reflexivity));
      simpl Z.sub in H;
      unfold  GF25519Base25Point5Params.c in H
  | [H: context[Z.ones ?l] |- _ ] =>
          (* postponing this to the main loop makes the autorewrite slow *)
        let c := fresh "c" in set (c := Z.ones l) in H; compute in c; subst c
  | [ |- _ ] => abstract (solve [auto])
  | [ |- _ ] => progress intros
  end.

  Lemma GF25519Base25Point5_mul_reduce_formula :
    forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 
      g0 g1 g2 g3 g4 g5 g6 g7 g8 g9,
      {ls | forall f g, rep [f0;f1;f2;f3;f4;f5;f6;f7;f8;f9] f
                        -> rep [g0;g1;g2;g3;g4;g5;g6;g7;g8;g9] g
                        -> rep ls (f*g)%GF}.
  Proof.

    eexists.

    Time deriveModularMultiplicationWithCarries (rev [0;1;2;3;4;5;6;7;8;9;0]).
    (* pretty-print: sh -c "tr -d '\n' | tr 'Z' '\n' | tr -d \% | sed 's:\s\s*\*\s\s*:\*:g' | column -o' ' -t" *)

    Time repeat letify fg; subst fg; eauto.
  Time Defined.
End GF25519Base25Point5Formula.

Extraction "/tmp/test.ml" GF25519Base25Point5_mul_reduce_formula.
(* It's easy enough to use extraction to get the proper nice-looking formula.
 * More Ltac acrobatics will be needed to get out that formula for further use in Coq.
 * The easiest fix will be to make the proof script above fully automated,
 * using [abstract] to contain the proof part. *)



