Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Strings.String.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import (*hints*) Coq.btauto.Algebra.
Require Coq.Structures.OrdersEx.
Require Import Crypto.Util.ListUtil.StdlibCompat.
Require Import Crypto.Util.ZUtil.ModInv.

Require Import Coq.micromega.Lia.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Coq.ZArith.Znat.

Require Import Crypto.Util.CPSUtil.
Require Import Crypto.Util.CPSNotations.
Local Open Scope cps_scope.
Notation "x' <- v ; C" := (v (fun x' => C)) (only parsing).

Require Import Crypto.Util.Notations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import ListNotations. Local Open Scope Z_scope.

Goal forall W s c a b, 0 <= c -> W < s ->
  0 <= a < s ->
  0 <= c*b <= W-c ->
  s <= (a + c*b) ->
  (((a + c*b) mod s) / W = ((a + c*b) mod s + c * ((a + c*b) / s)) / W).
Proof.
  intros; assert ((a + c * b) / s = 1) by (Z.div_mod_to_equations; nia).
  transitivity 0; Z.div_mod_to_equations; nia.
Qed.

Goal forall W s (HH: s / W * W = s) c a b, 0 <= c < W -> W < s ->
  0 <= a < s ->
  0 <= -c*b < W-c ->
  (a + c*b) < 0 ->
  (((a + c*b) mod s) / W = ((a + c*b) mod s + c * ((a + c*b) / s)) / W).
Proof.
  intros; assert ((a + c * b) / s = -1) by (Z.div_mod_to_equations; nia).
  assert ((a + c * b) mod s = s + a + c*b) by (Z.div_mod_to_equations; nia).
  rewrite H4 in *; rewrite H5 in *.
  enough ((s + a + c * b) / W - (s/W-1) = (s + a + c * b + c * -1) / W - (s/W-1)) by lia.
  rewrite <-2Z.div_sub with (b:=s/W-1) by lia; rewrite 2Z.div_small; trivial.
  all : rewrite ?HH; try split; ring_simplify; try nia.
Qed.

Lemma saturated_pseudomersenne_reduction_converges :
  forall W s c a b (HH: b < 0 -> s / W * W = s), 0 <= c < W -> W < s ->
  0 <= a < s ->
  0 <= c*Z.abs b <= W-c ->
  (((a + c*b) mod s) / W = ((a + c*b) mod s + c * ((a + c*b) / s)) / W).
Proof.
  intros; assert ((a+c*b)/s = -1 \/ (a+c*b)/s = 0 \/ (a+c*b)/s = 1)
    by (Z.div_mod_to_equations; nia); intuition idtac.
  { clear -HH H H0 H2 H4 H7. transitivity (s/W-1); Z.div_mod_to_equations; nia. }
  { f_equal. rewrite Z.mod_small; Z.div_mod_to_equations; lia. }
  { clear -H0 H3 H4 H6 H7. transitivity 0; Z.div_mod_to_equations; nia. }
Qed.

Module Pos.
  Local Open Scope positive_scope.
  Lemma prod_init x ys : fold_right Pos.mul x ys = fold_right Pos.mul 1 ys * x.
  Proof.
    revert dependent x; induction ys; cbn [fold_right]; intros; try lia.
    rewrite IHys; lia.
  Qed.
End Pos.


Module Z.
  Lemma prod_init x ys : fold_right Z.mul x ys = fold_right Z.mul 1 ys * x.
  Proof.
    revert dependent x; induction ys; cbn [fold_right]; intros; try ring.
    rewrite IHys; ring.
  Qed.

  Lemma prod_pos xs : Forall (fun x => 0 < x) xs -> 0 < fold_right Z.mul 1 xs.
  Proof. induction 1; cbn; lia. Qed.
End Z.

Module stream.
  Local Open Scope nat_scope.
  Notation stream := (fun T => nat -> T).
  Definition hd {T} (xs : stream T) : T := xs O.
  Definition tl {T} (xs : stream T) : stream T := fun i => xs (S i).
  Definition skipn {T} n (xs : stream T) : stream T := fun i => xs (n+i).
  Definition firstn {T} n (xs : stream T) : list T := map xs (seq 0 n).
  Definition cons {T} x (xs : stream T) : stream T :=
    fun i => match i with O => x | S i => xs i end.
  Definition prefixes {T} (xs : stream T) : stream (list T) :=
    fun i => firstn i xs.
  Definition map {A B} (f : A -> B) (xs : stream A) : stream B :=
    fun i => f (xs i).

  Definition firstn_S {T} n (xs : stream T) :
    firstn (S n) xs = List.cons (xs O) (firstn n (tl xs)).
  Proof.
    cbv [firstn]; rewrite <-cons_seq, <-seq_shift, map_cons, map_map; trivial.
  Qed.

  Definition firstn_S' {T} n (xs : stream T) :
    firstn (S n) xs = firstn n xs ++ [xs n].
  Proof. cbv [firstn]. rewrite seq_snoc, map_app; trivial. Qed.

  Lemma firstn_tl {T} n (xs : stream T) : firstn n (tl xs) = List.tl (firstn (S n) xs).
  Proof. cbn. rewrite <-seq_shift, map_map; trivial. Qed.

  Lemma skipn_tl {T} n (xs : stream T) i : skipn n (tl xs) i = skipn (S n) xs i.
  Proof. trivial. Qed.

  Lemma tl_map {A B} f xs i : tl (@map A B f xs) i = map f (tl xs) i.
  Proof. exact eq_refl. Qed.

  Lemma tl_prefixes {T} xs i :
    tl (@prefixes T xs) i = map (List.cons (hd xs)) (prefixes (tl xs)) i.
  Proof. cbv [tl prefixes map]. rewrite firstn_S; trivial. Qed.
End stream. Notation stream := stream.stream.

Module Saturated. Section __.
  Import Positional List ListNotations.
  Import stream Coq.Init.Datatypes Coq.Lists.List List.

  Implicit Types (weight bound : stream Z).
  Local Open Scope Z_scope.

  Definition weight bound := stream.map (fold_right Z.mul 1) (stream.prefixes bound).

  Lemma weight_0 bound : weight bound O = 1%Z. Proof. trivial. Qed.

  Lemma weight_1 bound : weight bound 1%nat = bound O. Proof. cbn. lia. Qed.

  Lemma tl_weight bound i : stream.tl (weight bound) i = stream.hd bound * weight (stream.tl bound) i.
  Proof. cbv [weight]. rewrite tl_map. cbv [stream.map]. rewrite tl_prefixes; trivial. Qed.

  Lemma tl_weight' bound i : stream.tl (weight bound) i = (weight bound i * bound i)%Z.
  Proof.
    cbv [stream.tl weight stream.prefixes stream.map].
    rewrite stream.firstn_S', fold_right_app; cbn [fold_right]; rewrite Z.prod_init; lia.
  Qed.

  (*
  Lemma weight_shift' bound (Hbound : forall i, bound i <> 0) i :
    weight (fun j => bound (S j)) i = weight bound (S i) / bound O.
  Proof.
    revert dependent bound; induction i; cbn -[Z.mul]; intros.
    { specialize (Hbound O). Z.div_mod_to_equations. nia. }
    rewrite (Z.mul_comm (bound O)), Z.div_mul by trivial; f_equal.
    symmetry; rewrite <-seq_shift, map_map; symmetry; trivial.
  Qed.

  Lemma weight_pos bound i (H : forall j, (j < i)%nat -> 0 < bound j) :
    0 < weight bound i.
  Proof.
    intros; cbv [weight]. apply Z.prod_pos, Forall_map, Forall_forall.
    intros j Hj%in_seq; apply H; lia.
  Qed.
  *)

  Local Open Scope Z_scope.
  Local Coercion Z.pos : positive >-> Z.

  Definition eval bound (xs : list Z) : Z :=
    list_rect _ (fun _ => 0) (fun x _  rec bound =>
      x + stream.hd bound * rec (stream.tl bound)
    ) xs bound.

  Lemma eval_nil bound : eval bound [] = 0.
  Proof. reflexivity. Qed.

  Lemma eval_cons bound x xs :
    eval bound (cons x xs) =
    x + stream.hd bound * eval (stream.tl bound) xs.
  Proof. reflexivity. Qed.

  Lemma eval_hd_tl bound xs : eval bound (hd 0 xs :: tl xs) = eval bound xs.
  Proof. case xs; intros; cbn [hd tl]; rewrite ?eval_cons, ?eval_nil; lia. Qed.

  Lemma eval_app bound xs ys :
    eval bound (xs ++ ys) =
      eval bound xs +
      weight bound (length xs) * eval (stream.skipn (length xs) bound) ys.
  Proof.
    revert ys; revert bound; induction xs; intros;
      rewrite <-?app_comm_cons, ?eval_nil, ?eval_cons.
    { rewrite weight_0. ring_simplify; trivial. }
    setoid_rewrite IHxs; clear IHxs.
    ring_simplify; f_equal.
    (*
    rewrite !(Z.mul_comm _ (eval _ _)), <-Z2Z.inj_mul, <-tl_weight; trivial.
  Qed.
     *)Admitted.

  Definition encode bound (n : nat) (x : Z) : list Z :=
    nat_rect _ (fun _ _ => []) (fun _ rec x bound =>
      (x mod (stream.hd bound) :: rec (x / stream.hd bound) (stream.tl bound))
    )  n x bound.

  Lemma encode_O bound x : encode bound O x = nil.  Proof. trivial. Qed.

  Lemma encode_S bound n x : encode bound (S n) x =
    x mod (stream.hd bound) :: encode (stream.tl bound) n (x / stream.hd bound).
  Proof. trivial. Qed.

  Instance Proper_encode : Proper (pointwise_relation _ eq ==> eq ==> eq ==> eq)%signature encode.
  Proof.
    intros f f' F n; revert F; revert f'; revert f; induction n;
      cbv [encode nat_rect stream.hd stream.tl]; repeat intro; subst; trivial.
    rewrite F; f_equal. eapply IHn; repeat intro; rewrite ?F; trivial.
  Qed.

  Lemma length_encode bound n x : length (encode bound n x) = n. Admitted.

  Lemma eval_encode bound n x : eval bound (encode bound n x) = x mod weight bound n.
  Proof.
    revert x; revert dependent bound; induction n; intros;
      rewrite ?encode_O, ?encode_S, ?eval_nil, ?eval_cons.
    { rewrite ?weight_0, Z.mod_1_r; trivial. }
    (*
    setoid_rewrite IHn. setoid_rewrite tl_weight. rewrite ?Z2Z.inj_mul.
    set (Z.pos (stream.hd bound)) as B in *.
    symmetry; rewrite (Z.div_mod x B), Z.add_comm at 1 by lia.
    rewrite <-Z.add_mod_idemp_r, Zmult_mod_distr_l by lia.
    apply Z.mod_small; Z.div_mod_to_equations; nia.
  Qed.
     *)Admitted.

  Lemma encode_add_l bound n m x :
    encode bound (n+m) x = encode bound n x ++ encode (stream.skipn n bound) m (x / weight bound n).
  Proof.
    revert x; revert bound; induction n; cbn [Nat.add nat_rect]; intros;
      rewrite ?encode_O, ?encode_S.
    { rewrite weight_0, Z.div_1_r. reflexivity. }
    setoid_rewrite IHn; cbn [app]; f_equal.
    (*
    rewrite Z.div_div, <-Z2Z.inj_mul, <-tl_weight by lia.
    { (* setoid_rewrite stream.skipn_tl *)
      eapply f_equal2; [reflexivity|].
      eapply Proper_encode; [|reflexivity..].
      intro i; eapply stream.skipn_tl. }
  Qed.
     *)Admitted.

  Lemma firstn_encode bound i n x (H : Nat.lt i n) :
    firstn i (encode bound n x) = encode bound i x.
  Proof.
    replace n with (i + (n-i))%nat by lia; set (n-i)%nat as m; clearbody m.
    rewrite encode_add_l, firstn_app_sharp; auto using length_encode.
  Qed.

  Lemma skipn_encode bound i n x (H : Nat.lt i n) :
    skipn i (encode bound n x) = encode (stream.skipn i bound) (n-i) (x / weight bound i).
  Proof.
    replace n with (i + (n-i))%nat by lia; set (n-i)%nat as m; clearbody m.
    rewrite encode_add_l, skipn_app_sharp; auto using length_encode; f_equal; lia.
  Qed.

  Lemma eval_firstn_encode bound i n x (H : Nat.lt i n) :
    eval bound (firstn i (encode bound n x)) = x mod weight bound i.
  Proof. rewrite firstn_encode, eval_encode; trivial. Qed.

  Lemma eval_skipn_encode bound i n x (H : Nat.lt i n) :
    eval (stream.skipn i bound) (skipn i (encode bound n x)) = x mod weight bound n / weight bound i.
  Proof.
    rewrite skipn_encode, eval_encode; trivial.
    (*
    rewrite Z.mod_pull_div by lia.
    f_equal.
    f_equal.
    rewrite <-Z2Z.inj_mul.
    f_equal.
  Admitted.
     *)Admitted.

  Definition add bound (c0 : Z) (xs ys : list Z) : list Z * Z  :=
    list_rect _ (fun _ _ c => ([], c)) (fun x _  rec bound ys c =>
      let (z, c) := Z.add_with_get_carry_full (stream.hd bound) c x (hd 0 ys) in
      let (zs, C) := rec (stream.tl bound) (tl ys) c in
      (z::zs, C)
    ) xs bound ys c0.

  Lemma add_nil bound c ys : add bound c [] ys = ([], c). Proof. trivial. Qed.

  Lemma add_cons bound c x xs ys : add bound c (cons x xs) ys =
    let (z, c) := Z.add_with_get_carry_full (stream.hd bound) c x (hd 0 ys) in
    let (zs, C) := add (stream.tl bound)  c xs (tl ys)in
    (z::zs, C).
  Proof. trivial. Qed.

  Lemma add_correct :forall bound xs ys c
    (Hlength : (length ys <= length xs)%nat),
    let s := c + eval bound xs + eval bound ys in
    add bound c xs ys = (encode bound (length xs) s, s / weight bound (length xs)).
  Proof.
    intros until xs; revert dependent bound; induction xs as [|x xs];
      cbn [length]; intros; rewrite ?add_nil, ?add_cons.
    { case ys in *; [|inversion Hlength]. cbn. f_equal. Z.div_mod_to_equations; lia. }
    rewrite <-?(eval_hd_tl _ ys), ?eval_cons, ?encode_S; cbn [hd tl].
    destruct Z.add_with_get_carry_full as (?&c') eqn:Hdiv; pose proof Hdiv as Hmod.
      apply (f_equal snd) in Hdiv; rewrite Z.add_with_get_carry_full_div in Hdiv.
      apply (f_equal fst) in Hmod; rewrite Z.add_with_get_carry_full_mod in Hmod.
      cbn [fst snd] in *. subst.
    rewrite IHxs by ( rewrite length_tl; lia); clear IHxs.
    repeat (apply (f_equal2 pair) || apply (f_equal2 cons)).
    { push_Zmod; pull_Zmod. f_equal. rewrite Z.mul_0_l, Z.add_0_r. lia. }
    (*
    { f_equal. Z.div_mod_to_equations; nia. }
    { setoid_rewrite tl_weight.
      rewrite <-2Z.div_add, Z.div_div; f_equal; lia. }
  Qed.
     *)Admitted.

  (* See lemma saturated_pseudomersenne_reduction_converges *)

  Definition reduce' bound k (c : Z) (a : list Z) (b : Z) : list Z :=
    let (sum, carry) := add bound 0 a [c * b] in
    let (sum', _) := add bound 0 sum [c * carry] in
    firstn k sum' ++ skipn k sum.

  Lemma eval_reduce' bound k c a b m
    (s : Z := weight bound (length a)) (Hc : s mod m = c)
    (Hc' : 0 <= c < weight bound k)
    (Hla : (1 <= length a)%nat) (Hla' : (k < length a)%nat)
    (Ha : 0 <= eval bound a < weight bound (length a))
    (Hb : 0 <= c * Z.abs b <= weight bound k - c) :
    (eval bound a + s * b) mod m = eval bound (reduce' bound k c a b) mod m.
  Proof.
    cbv [reduce'].
    rewrite 2 add_correct by (rewrite ?length_encode; trivial); cbn [fst snd].
    rewrite firstn_encode, eval_encode by (rewrite ?length_encode; trivial).
    repeat rewrite ?eval_cons, ?eval_nil, ?Z.add_0_l, ?Z.mul_0_r, ?Z.add_0_r.
    rewrite eval_app, ?length_encode, (eval_encode _ k).
    set (weight bound k) as W.

    epose proof (saturated_pseudomersenne_reduction_converges W s c (@eval bound a) b).
    progress change ((weight bound (length a))) with s.
    subst W.
    subst s.
    rewrite eval_skipn_encode by trivial.
    rewrite H; cycle 1; clear H; try trivial.
    { intros. rewrite Z.mul_comm. symmetry; apply Z.div_exact; try lia.
      (* weight bound (length a) mod weight bound k = 0 *) admit. }
    { (* weight bound k < weight bound (length a) *) admit. }

    rewrite (Z.add_comm (_ mod _) (_ * (_ / _))), <-Z.div_mod by lia.
    rewrite (Z.add_comm (_ mod _) (_ * (_ / _))).
    set (eval _ a + c * b) as A.
    push_Zmod; rewrite <-Hc; pull_Zmod.
    rewrite <-Z.div_mod by lia.
    push_Zmod; rewrite Hc; pull_Zmod.
    trivial.
    all: fail.
  Admitted.

  Definition addmod bound c a b :=
    let (sum, carry) := add bound 0 a b in
    reduce' bound 1 c sum carry.

  Lemma eval_addmod bound c a b m
    (s : Z := weight bound (length a)) (Hc : s mod m = c)
    (Hc' : 0 <= 2*c <= bound O)
    (Hla : (1 < length a)%nat) (Hlb : (length b <= length a)%nat)
    (Ha : 0 <= eval bound a < weight bound (length a))
    (Hb : - weight bound (length a) <= eval bound b <= weight bound (length a)) :
    eval bound (addmod bound c a b) mod m = (eval bound a + eval bound b) mod m.
  Proof.
    cbv [addmod]; rewrite add_correct by trivial; rewrite ?Z.add_0_l.
    rewrite <-eval_reduce'; rewrite ?eval_encode, ?length_encode, ?weight_1;
      try solve [trivial | cbn; lia | apply Z.mod_pos_bound; lia ].
    { rewrite (Z.add_comm (_ mod _) (_ * (_ / _))), <-Z.div_mod; lia. }
    (*
    assert (Z.abs ((eval bound a + eval bound b) / Z.pos (weight bound (length a))) <= 1) by (Z.div_mod_to_equations; nia); nia.
  Qed.
     *)Admitted.

  Local Notation "!" := ltac:(vm_decide) (only parsing).
  Goal forall a0 a1 a2 a3 b : Z, False. intros.
  Proof.
    pose proof (eval_reduce' (fun _ => 2^64)%Z 1 38 [a0;a1;a2;a3] b (2^256-38) ! ! ! !).
    cbn [length] in *.
    change ((weight (fun _ : nat => (2 ^ 64)%Z) 4%nat)) with (2^256) in *.
    change ((weight (fun _ : nat => (2 ^ 64)%Z) 1%nat)) with (2^64) in *.
    change (weight (fun _ : nat => (2 ^ 64)%Z) 1%nat)%Z with (2^64)%Z in *.
    set (eval (fun _ : nat => (2 ^ 64)%Z)) as eval in *.
    set (reduce' (fun _ : nat => (2 ^ 64)%Z) _ _ _) as reduce' in *.
  Abort.

  Goal forall a0 a1 a2 a3 b0 b1 b2 b3 : Z, False. intros.
  Proof.
    pose proof (eval_addmod (fun _ => 2^64)%Z 38 [a0;a1;a2;a3] [b0;b1;b2;b3] (2^256-38) ! ! ! !).
    cbn [length] in *.
    change ((weight (fun _ : nat => (2 ^ 64)%Z) 4%nat)) with (2^256) in *.
    change ((weight (fun _ : nat => (2 ^ 64)%Z) 1%nat)) with (2^64) in *.
    change (weight (fun _ : nat => (2 ^ 64)%Z) 1%nat)%Z with (2^64)%Z in *.
    set (eval (fun _ : nat => (2 ^ 64)%Z)) as eval in *.
    set (addmod _ _) as addmod in *.
  Abort.
End __.
End Saturated.
