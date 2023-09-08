Require Import Coq.Lists.List Crypto.Util.ListUtil Crypto.Util.ListUtil.StdlibCompat.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Import ListNotations. Local Open Scope list_scope. Local Open Scope Z_scope.

(*
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
 *)

Lemma saturated_pseudomersenne_reduction_converges :
  forall W s c a b (HH: b < 0 -> s / W * W = s), 0 <= c < W -> W <= s ->
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

Require Import Crypto.Language.PreExtra.

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

  (* TODO: move *)
  Lemma mul_split_correct s x y :
    Z.mul_split s x y = (x * y mod s, x * y / s).
  Proof.
    rewrite (surjective_pairing (Z.mul_split _ _ _)).
    rewrite Z.mul_split_mod, Z.mul_split_div; trivial.
  Qed.

  Lemma add_with_get_carry_full_correct s c x y :
    Z.add_with_get_carry_full s c x y = ((c + x + y) mod s, (c + x + y) / s).
  Proof.
    rewrite (surjective_pairing (Z.add_with_get_carry_full _ _ _ _)).
    rewrite Z.add_with_get_carry_full_mod, Z.add_with_get_carry_full_div; trivial.
  Qed.
End Z.

Module Nat.
  Lemma max_S_r a b : Nat.max a (S b) = S (Nat.max (a-1) b). Proof. lia. Qed.
  Lemma max_S_l a b : Nat.max (S a) b = S (Nat.max a (b-1)). Proof. lia. Qed.
End Nat.

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

  Lemma hd_const {T} (x : T) : hd (fun _ => x) = x. trivial. Qed.
  Lemma tl_const {T} (x : T) i : tl (fun _ => x) i = x. trivial. Qed.
  Lemma skipn_const {T} n (x : T) i : skipn n (fun _ => x) i = x. trivial. Qed.

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

  Lemma firstn_add {T} i j xs : @firstn T (i + j) xs = firstn i xs ++ firstn j (skipn i xs).
  Proof.
    cbv [firstn skipn].
    rewrite seq_add, map_app; apply f_equal, eq_sym, map_seq_ext; intros; f_equal; lia.
  Qed.

  Lemma skipn_tl {T} n (xs : stream T) i : skipn n (tl xs) i = skipn (S n) xs i.
  Proof. trivial. Qed.

  Lemma tl_map {A B} f xs i : tl (@map A B f xs) i = map f (tl xs) i.
  Proof. exact eq_refl. Qed.

  Lemma tl_prefixes {T} xs i :
    tl (@prefixes T xs) i = map (List.cons (hd xs)) (prefixes (tl xs)) i.
  Proof. cbv [tl prefixes map]. rewrite firstn_S; trivial. Qed.
End stream. Notation stream := stream.stream.

Module Saturated. Section __.
  Import List ListNotations.
  Import stream Coq.Init.Datatypes Coq.Lists.List List.

  Implicit Types (weight bound : stream positive).
  Local Open Scope positive_scope.

  Definition weight bound := stream.map (fold_right Pos.mul 1) (stream.prefixes bound).

  Lemma weight_0 bound : weight bound O = 1. Proof. trivial. Qed.

  Lemma weight_1 bound : weight bound 1%nat = bound O. Proof. cbn. lia. Qed.

  Lemma tl_weight bound i : stream.tl (weight bound) i = (stream.hd bound * weight (stream.tl bound) i).
  Proof. cbv [weight]. rewrite tl_map. cbv [stream.map]. rewrite tl_prefixes; trivial. Qed.

  Lemma tl_weight' bound i : stream.tl (weight bound) i = (weight bound i * bound i).
  Proof.
    cbv [stream.tl weight stream.prefixes stream.map].
    rewrite stream.firstn_S', fold_right_app; cbn [fold_right]; rewrite Pos.prod_init; lia.
  Qed.

  Lemma weight_add bound i j : weight bound (i+j) = weight bound i * weight (stream.skipn i bound) j.
  Proof.
    cbv [weight stream.map stream.prefixes].
    rewrite <-Pos.prod_init, <-fold_right_app; apply f_equal, stream.firstn_add.
  Qed.

  Lemma weight_mono_le bound i j : Nat.le i j -> weight bound i <= weight bound j.
  Proof. intros. replace j with (i+(j-i))%nat by lia; rewrite weight_add. nia. Qed.

  Local Open Scope Z_scope.
  Local Coercion Z.pos : positive >-> Z.

  Lemma mod_weight_le bound i j : Nat.le i j -> weight bound j mod weight bound i = 0.
  Proof.
    intros.
    replace j with (i+(j-i))%nat by lia; rewrite weight_add.
    rewrite Pos.mul_comm, Pos2Z.inj_mul, Z.mod_mul; lia.
  Qed.

  Definition eval bound (xs : list Z) : Z :=
    list_rect_fbb_b (fun _ => 0) (fun x _  rec bound =>
      x + stream.hd bound * rec (stream.tl bound)
    ) xs bound.

  Lemma eval_nil bound : eval bound [] = 0.
  Proof. reflexivity. Qed.

  Lemma eval_cons bound x xs :
    eval bound (cons x xs) =
    x + stream.hd bound * eval (stream.tl bound) xs.
  Proof. reflexivity. Qed.

  Import Morphisms.

  Instance Proper_eval : Proper (pointwise_relation _ eq==>eq==>eq)%signature eval.
  Proof.
    cbv [pointwise_relation].
    intros f g fg l; revert fg; revert g; revert f; induction l; intros;
      subst; rewrite ?eval_nil, ?eval_cons; repeat (eauto||f_equal).
  Qed.

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
    rewrite !(Z.mul_comm _ (eval _ _)), <-Pos2Z.inj_mul, <-tl_weight; trivial.
  Qed.

  Lemma eval_firstn bound n xs :
    eval bound (firstn n xs) mod weight bound n =
    eval bound xs mod weight bound n.
  Proof.
    epose proof eval_app bound _ _ as H; rewrite (firstn_skipn n xs) in H.
    rewrite H; clear H.
    rewrite firstn_length.
    case (Nat.min_dec n (length xs)) as [e|e]; rewrite e.
    { rewrite Z.mul_comm, Z.mod_add; lia. }
    rewrite ListUtil.skipn_all, eval_nil, Z.mul_0_r, Z.add_0_r by lia; trivial.
  Qed.

  Definition encode bound n x :=
    nat_rect_fbb_b_b (fun _ _ => []) (fun _ rec bound x =>
      (x mod (stream.hd bound) :: rec (stream.tl bound) (x / stream.hd bound))
    ) n bound x.

  Lemma encode_O bound x : encode bound O x = nil.  Proof. trivial. Qed.

  Lemma encode_S bound n x : encode bound (S n) x =
    x mod (stream.hd bound) :: encode (stream.tl bound) n (x / stream.hd bound).
  Proof. trivial. Qed.

  Instance Proper_encode : Proper (pointwise_relation _ eq ==> eq ==> eq ==> eq)%signature encode.
  Proof.
    intros f f' F n; revert F; revert f'; revert f; induction n;
      repeat intro; subst; rewrite ?encode_O, ?encode_S; trivial.
    cbv [stream.hd stream.tl]; rewrite F; f_equal; [].
    eapply IHn; repeat intro; rewrite ?F; trivial.
  Qed.

  Lemma length_encode bound n x : length (encode bound n x) = n.
  Proof.
    revert bound; revert x; induction n; intros;
    rewrite ?encode_O, ?encode_S; cbn [length]; erewrite ?IHn; trivial.
  Qed.

  Lemma eval_encode bound n x : eval bound (encode bound n x) = x mod weight bound n.
  Proof.
    revert x; revert dependent bound; induction n; intros;
      rewrite ?encode_O, ?encode_S, ?eval_nil, ?eval_cons.
    { rewrite ?weight_0, Z.mod_1_r; trivial. }
    setoid_rewrite IHn. setoid_rewrite tl_weight. rewrite ?Pos2Z.inj_mul.
    set (Z.pos (stream.hd bound)) as B in *.
    symmetry; rewrite (Z.div_mod x B), Z.add_comm at 1 by lia.
    rewrite <-Z.add_mod_idemp_r, Zmult_mod_distr_l by lia.
    apply Z.mod_small; Z.div_mod_to_equations; nia.
  Qed.

  Lemma encode_add_l bound n m x :
    encode bound (n+m) x = encode bound n x ++ encode (stream.skipn n bound) m (x / weight bound n).
  Proof.
    revert x; revert bound; induction n; cbn [Nat.add nat_rect]; intros;
      rewrite ?encode_O, ?encode_S.
    { rewrite weight_0, Z.div_1_r. reflexivity. }
    setoid_rewrite IHn; cbn [app]; f_equal.
    rewrite Z.div_div, <-Pos2Z.inj_mul, <-tl_weight by lia.
    { (* setoid_rewrite stream.skipn_tl *)
      eapply f_equal2; [reflexivity|].
      eapply Proper_encode; [|reflexivity..].
      intro i; eapply stream.skipn_tl. }
  Qed.

  Lemma firstn_encode bound i n x (H : Nat.le i n) :
    firstn i (encode bound n x) = encode bound i x.
  Proof.
    replace n with (i + (n-i))%nat by lia; set (n-i)%nat as m; clearbody m.
    rewrite encode_add_l, firstn_app_sharp; auto using length_encode.
  Qed.

  Lemma skipn_encode bound i n x (H : Nat.le i n) :
    skipn i (encode bound n x) = encode (stream.skipn i bound) (n-i) (x / weight bound i).
  Proof.
    replace n with (i + (n-i))%nat by lia; set (n-i)%nat as m; clearbody m.
    rewrite encode_add_l, skipn_app_sharp; auto using length_encode; f_equal; lia.
  Qed.

  Lemma eval_firstn_encode bound i n x (H : Nat.le i n) :
    eval bound (firstn i (encode bound n x)) = x mod weight bound i.
  Proof. rewrite firstn_encode, eval_encode; trivial. Qed.

  Lemma eval_skipn_encode bound i n x (H : Nat.le i n) :
    eval (stream.skipn i bound) (skipn i (encode bound n x)) = x mod weight bound n / weight bound i.
  Proof.
    rewrite skipn_encode, eval_encode; trivial.
    rewrite Z.mod_pull_div by lia; f_equal; f_equal.
    rewrite <-Pos2Z.inj_mul; f_equal.
    replace n with (i+(n-i))%nat at 2 by lia; rewrite weight_add; lia.
  Qed.

  Definition add' bound (c0 : Z) (xs ys : list Z) : list Z * Z  :=
    list_rect_fbb_b_b_b (fun _ _ c => ([], c)) (fun x _  rec bound ys c =>
      let (z, c) := Z.add_with_get_carry_full (stream.hd bound) c x (hd 0 ys) in
      let (zs, C) := rec (stream.tl bound) (tl ys) c in
      (z::zs, C)
    ) xs bound ys c0.

  Lemma add'_nil bound c ys : add' bound c [] ys = ([], c). Proof. trivial. Qed.

  Lemma add'_cons bound c x xs ys : add' bound c (cons x xs) ys =
    let (z, c) := Z.add_with_get_carry_full (stream.hd bound) c x (hd 0 ys) in
    let (zs, C) := add' (stream.tl bound)  c xs (tl ys)in
    (z::zs, C).
  Proof. trivial. Qed.

  Lemma add'_correct :forall bound xs ys c
    (Hlength : (length ys <= length xs)%nat),
    let s := c + eval bound xs + eval bound ys in
    add' bound c xs ys = (encode bound (length xs) s, s / weight bound (length xs)).
  Proof.
    intros until xs; revert dependent bound; induction xs as [|x xs];
      cbn [length]; intros; rewrite ?add'_nil, ?add'_cons.
    { case ys in *; [|inversion Hlength]. cbn. f_equal. Z.div_mod_to_equations; lia. }
    rewrite <-?(eval_hd_tl _ ys), ?eval_cons, ?encode_S; cbn [hd tl].
    rewrite Z.add_with_get_carry_full_correct.
    rewrite IHxs by ( rewrite length_tl; lia); clear IHxs.
    repeat (apply (f_equal2 pair) || apply (f_equal2 cons)).
    { push_Zmod; pull_Zmod. f_equal. rewrite Z.mul_0_l, Z.add_0_r. lia. }
    { f_equal. Z.div_mod_to_equations; nia. }
    { setoid_rewrite tl_weight.
      rewrite <-2Z.div_add, Z.div_div; f_equal; lia. }
  Qed.

  Definition add bound c (xs ys : list Z) :=
    if (Z.of_nat (length ys) <=? Z.of_nat (length xs))
    then add' bound c xs ys
    else add' bound c ys xs.

  Lemma add_correct :forall bound xs ys c,
    let s := c + eval bound xs + eval bound ys in
    let n := Nat.max (length xs) (length ys) in
    add bound c xs ys = (encode bound n s, s / weight bound n).
  Proof.
    cbv [add]; intros.
    match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end;
    rewrite ?add'_correct; repeat (lia || f_equal).
  Qed.

  Definition product_scan' bound (acc : list Z) (pps : list (Z*Z)) h c o : list Z * (Z*Z*Z) :=
    list_rect_fbb_b_b_b_b_b
      (fun bound acc h c o => ([], (h, c, o)))
      (fun x_y _ rec bound acc h c o =>
      let '(x, y) := x_y in (* workaround for Reify *)
      let (p, h') := Z.mul_split (stream.hd bound) x y in
      let (z, c) := Z.add_with_get_carry_full (stream.hd bound) c (hd 0 acc) h in
      let (z, o) := Z.add_with_get_carry_full (stream.hd bound) o z p in
      let (zs, C) := rec (stream.tl bound) (tl acc) h' c o in
      (z::zs, C)
    ) pps bound acc h c o.

  Lemma product_scan'_nil bound acc h c o :
    product_scan' bound acc [] h c o = ([], (h, c, o)).
  Proof. trivial. Qed.

  Lemma hd_firstn_S {A} d n l : @hd A d (firstn (S n) l) = hd d l.
  Proof. case l; trivial. Qed.

  Lemma tl_firstn_S {A} n l : @tl A (firstn (S n) l) = firstn n (tl l).
  Proof. case l; cbn; rewrite ?firstn_nil; trivial. Qed.

  Lemma product_scan'_cons bound acc x y pps h c o :
    product_scan' bound acc ((x, y)::pps) h c o =
      let (p, h') := Z.mul_split (stream.hd bound) x y in
      let (z, c) := Z.add_with_get_carry_full (stream.hd bound) c (hd 0 acc) h in
      let (z, o) := Z.add_with_get_carry_full (stream.hd bound) o z p in
      let (zs, C) := product_scan' (stream.tl bound) (tl acc) pps h' c o in
      (z::zs, C).
  Proof. trivial. Qed.

  Lemma product_scan'_correct : forall bound acc pps h c o,
    let n := length pps in
    let z := eval bound (firstn n acc) + h + c + o + eval bound (map (uncurry Z.mul) pps) in
    exists h' c' o',
    product_scan' bound acc pps h c o = (encode bound n z, (h', c', o')) /\
    h' + c' + o' = z / weight bound n.
  Proof.
    intros ? ? ?; revert acc; revert bound; induction pps as [|[x y] pps];
      cbn [length]; intros; rewrite ?product_scan'_nil, ?product_scan'_cons.
    { eexists _, _, _; split; trivial. cbn. Z.div_mod_to_equations; lia. }
    edestruct IHpps as (h'&c'&o'&Hlo&Hhi).
    eexists _, _, _.
    repeat rewrite <-?(eval_hd_tl _ (firstn _ acc)), ?Z.mul_split_correct, ?Z.add_with_get_carry_full_correct, ?map_cons, ?eval_cons, ?Hlo, ?Hhi, ?length_tl, ?hd_firstn_S, ?tl_firstn_S, ?Nat.max_S_r, ?encode_S; clear IHpps Hhi Hlo; cbn [uncurry].
    split.
    1: f_equal; f_equal.
    all : push_Zmod; pull_Zmod.
    rewrite ?Z.mul_0_l, ?Z.add_0_r.
    { f_equal; Z.div_mod_to_equations. nia. }
    { f_equal. Z.div_mod_to_equations. nia. }
    setoid_rewrite tl_weight.
      set (eval (stream.tl bound) (map (uncurry Z.mul) pps)) as PPS.
      set (eval (stream.tl bound) (firstn (length pps) (tl acc))) as ACC.
      set (stream.hd bound) as B.
      set (weight _ _) as W.
      assert (0 < W) by (subst W; lia).
    Z.div_mod_to_equations; nia.
  Qed.

  Definition product_scan bound acc (pps : list (Z*Z)) h c o : list Z * Z :=
    let z := eval bound (firstn (length pps) acc) + h + c + o + eval bound (map (uncurry Z.mul) pps) in
    let '(lo, (h, c, o)) := product_scan' bound acc pps h c o in
    (lo, 
      let zc := z / weight bound (length lo) in
      if  ((0 <=? zc) && (zc <? bound (length lo)))%bool
      then
        dlet h := fst (Z.add_with_get_carry_full (bound (length lo)) c h 0) in
        dlet h := fst (Z.add_with_get_carry_full (bound (length lo)) o h 0) in
        h
      else h+c+o).

  Lemma eval_map_mul bound x ys : eval bound (map (Z.mul x) ys) = x * eval bound ys.
  Proof.
    revert bound; induction ys; intros;
      rewrite ?map_cons, ?eval_nil, ?eval_cons, ?IHys; ring.
  Qed.

  Lemma product_scan_correct bound acc pps h c o :
    let n := length pps in
    let z := eval bound (firstn n acc) + h + c + o + eval bound (map (uncurry Z.mul) pps) in
    product_scan bound acc pps h c o = (encode bound n z, z / weight bound n).
  Proof.
    cbv [product_scan Let_In].
    edestruct product_scan'_correct as (h'&c'&o'&Hlo&Hhi); rewrite Hlo, Hhi; clear Hlo.
    rewrite ?map_map, ?map_length, ?eval_app, ?eval_encode, ?length_encode, ?eval_cons, ?eval_nil, ?Z.add_with_get_carry_full_mod in *.
    cbn [uncurry] in *; rewrite ?eval_map_mul, ?Z.mul_0_r ,?Z.add_0_r in *; f_equal.
    match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end; trivial.
    match goal with |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b) end; trivial; cbn [andb].
    push_Zmod; pull_Zmod; rewrite Z.mod_small; [lia|]. lia.
  Qed.

  Lemma length_add_mul_limb' bound acc pps :
    length (fst (product_scan bound acc pps 0 0 0)) = length pps.
  Proof. rewrite product_scan_correct; apply length_encode. Qed.

  Definition add_ bound c xs ys : list Z :=
    let (lo, hi) := add bound c xs ys in lo ++ [hi].

  Lemma eval_add_ bound c xs ys :
    eval bound (add_ bound c xs ys) = c + eval bound xs + eval bound ys.
  Proof.
    cbv [add_].
    break_match; Prod.inversion_prod; subst;
    rewrite add_correct, eval_app, eval_cons, eval_nil by lia; cbn [fst snd]; ring_simplify.
    rewrite eval_encode, length_encode; Z.div_mod_to_equations; nia.
  Qed.

  Definition product_scan_ bound acc pps h c o :=
    let '(l, h) := product_scan bound acc pps h c o in
    dlet r := l ++ if Z.of_nat (length pps) <? Z.of_nat (length acc)
                   then add_ bound 0 (skipn (length pps) acc) [h]
                   else [h] in
    r.

  Definition add_mul_small bound acc x ys : list Z * Z :=
    let '(lo, (h, c, o)) := product_scan' bound acc (map (pair x) ys) 0 0 0 in
    dlet hi := h + c + o in
    if (Z.of_nat (length acc) <=? Z.of_nat (length ys))
    then (lo, hi)
    else
      let (mid, hi) := add (stream.skipn (length ys) bound) (*suboptimal*)0 (skipn (length ys) acc) [hi] in
      (lo ++ mid, hi).

  Lemma add_mul_small_correct bound acc x ys :
    let z := eval bound acc + x * eval bound ys in
    let n := Nat.max (length acc) (length ys) in
    add_mul_small bound acc x ys = (encode bound n z, z / weight bound n).
  Proof.
  Admitted.

  Definition add_mul_limb bound acc x ys : list Z * Z :=
    let (lo, hi) := product_scan bound acc (map (pair x) ys) 0 0 0 in
    if (Z.of_nat (length acc) <=? Z.of_nat (length ys))
    then (lo, hi)
    else
      let (mid, hi) := add (stream.skipn (length ys) bound) (*suboptimal*)0 (skipn (length ys) acc) [hi] in
      (lo ++ mid, hi).

  Lemma add_mul_limb_correct bound acc x ys :
    let z := eval bound acc + x * eval bound ys in
    let n := Nat.max (length acc) (length ys) in
    add_mul_limb bound acc x ys = (encode bound n z, z / weight bound n).
  Proof.
    intros. cbv [add_mul_limb].
    match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end; trivial.
    { rewrite product_scan_correct; rewrite ?firstn_nil, ?eval_nil; trivial.
      subst n; rewrite firstn_all2, Nat.max_r; rewrite ?map_length; trivial; try lia. admit. }
    rewrite product_scan_correct, add_correct, eval_cons, eval_nil, Z.mul_0_r, Z.add_0_l, Z.add_0_r, skipn_length, Nat.max_l by (cbn [length]; lia); f_equal.
    
    (*
    eval_app, eval_encode, length_encode, eval_add_, eval_cons, eval_nil; ring_simplify.
    epose proof eval_app bound _ _ as H; rewrite (firstn_skipn (length ys) acc) in H.
    destruct (Nat.leb_spec (length ys) (length acc)).
    { rewrite firstn_length_le in H by trivial. Z.div_mod_to_equations; nia. }
    { rewrite !skipn_all2, eval_nil in * by lia. Z.div_mod_to_equations; nia. }
     *)
  Admitted.

  Definition add_mul_limb_ bound acc x ys : list Z :=
    let (lo, hi) := add_mul_limb bound acc x ys in lo ++ [hi].

  Lemma eval_add_mul_limb_ bound acc x ys :
    eval bound (add_mul_limb_ bound acc x ys) = eval bound acc + x * eval bound ys.
  Proof.
    cbv [add_mul_limb_].
    break_match; Prod.inversion_prod; subst;
    rewrite add_mul_limb_correct, eval_app, eval_cons, eval_nil by lia; cbn [fst snd]; ring_simplify.
    rewrite eval_encode, length_encode; Z.div_mod_to_equations; nia.
  Qed.

  Definition add_mul bound (acc xs ys : list Z) : list Z :=
    list_rect_fbb_b_b (fun _ acc => acc)
    (fun x _ rec bound acc =>
      dlet acc := add_mul_limb_ bound acc x ys in
      hd 0 acc :: rec (stream.tl bound) (tl acc)
    ) xs bound acc.

  Definition add_mul_nil bound acc ys : add_mul bound acc [] ys = acc.
  Proof. trivial. Qed.

  Definition add_mul_cons bound acc x xs ys :
    add_mul bound acc (x::xs) ys =
      let acc := add_mul_limb_ bound acc x ys in
      hd 0 acc :: add_mul (stream.tl bound) (tl acc) xs ys.
  Proof. trivial. Qed.

  Lemma eval_add_mul B (bound := fun _ => B) acc xs ys :
    eval bound (add_mul bound acc xs ys) =
    eval bound acc + eval bound xs * eval bound ys.
  Proof.
    revert ys; revert acc; induction xs; intros;
      rewrite ?add_mul_nil, ?add_mul_cons, ?eval_nil, ?eval_cons, ?IHxs.
    { ring. }
    pose proof eval_add_mul_limb_ bound acc a ys as HH.
    rewrite <-eval_hd_tl, eval_cons in HH.
    rewrite Z.mul_add_distr_r, Z.add_assoc, <-HH; ring_simplify.
    setoid_rewrite (tl_const _ : pointwise_relation _ eq (stream.tl bound) bound).
    ring.
  Qed.

  Definition mul bound := add_mul bound [].

  Lemma eval_mul B (bound := fun _ => B) xs ys :
    eval bound (mul bound xs ys) = eval bound xs * eval bound ys.
  Proof. cbv [mul]. subst bound; rewrite eval_add_mul, ?firstn_nil, ?eval_nil. ring. Qed.
  
  Lemma length_mul bound xs ys : ys <> [] ->  length (mul bound xs ys) = (length xs + length ys)%nat.
  Admitted.


  (* See lemma saturated_pseudomersenne_reduction_converges *)
  Definition reduce' bound k (c : Z) (a : list Z) (b : list Z) : list Z :=
    let (sum, carry) := add_mul_small bound a c b in
    let (sum', _) := add bound 0 sum [c * carry] in
    firstn k sum' ++ skipn k sum.

  Lemma eval_reduce' bound k c a b m
    (s : Z := weight bound (Nat.max (length a) (length b))) (Hc : s mod m = c)
    (Hc' : 0 <= c < weight bound k) (Hla : (k <= length a)%nat)
    (Ha : 0 <= eval bound a < weight bound (length a))
    (Hb : c * Z.abs (eval bound b) <= weight bound k - c) :
    eval bound (reduce' bound k c a b) mod m = (eval bound a + s * eval bound b) mod m.
  Proof.
    cbv [reduce'] in *.
    repeat (rewrite ?add_mul_small_correct, ?add_correct, ?firstn_encode, ?eval_app,
      ?eval_encode, ?length_encode, ?eval_skipn_encode, ?eval_cons, ?eval_nil,
      ?Z.add_0_l, ?Z.mul_0_r, ?Z.add_0_r by lia; cbn [fst snd length]); fold s.
    rewrite saturated_pseudomersenne_reduction_converges, <-Z.div_mod''; try split; try lia.
    { rewrite (Zmod_eq _ s) by lia. push_Zmod. rewrite ?Hc. pull_Zmod. f_equal. ring. }
    { intros. rewrite Z.mul_comm. symmetry; apply Z.div_exact; try apply mod_weight_le; lia. }
    { apply weight_mono_le; lia. }
    { enough (weight bound (length a) <= s) by lia. apply weight_mono_le. lia. }
  Qed.

  Definition reduce bound k (c : Z) (a : list Z) (b : list Z) : list Z :=
    (* NOTE: it would be nice if we had an "if" that threw error messages during specialization *)
    if ((Z.of_nat k <=? Z.of_nat (length a))
    && (Z.of_nat (length b) <=? Z.of_nat (length a))
    && (0 <=? c)
    && (c <? weight bound k)
    && (0 <=? eval bound a)
    && (eval bound a <? weight bound (length a))
    && (c*Z.abs (eval bound b) <=? weight bound k - c))%bool
    then reduce' bound k c a b
    else a ++ b.

  Lemma eval_reduce bound k c a b m
    (s : Z := weight bound (length a)) (Hc : s mod m = c)
    (Hbound : pointwise_relation nat eq (stream.skipn (length a) bound) bound) :
    eval bound (reduce bound k c a b) mod m = (eval bound a + s * eval bound b) mod m.
  Proof.
    cbv [reduce]; break_match.
    { repeat match goal with H : _ |- _ => apply Bool.andb_prop in H; case H as [H ?] end.
      Require Import Crypto.Util.Decidable.Bool2Prop.
      rewrite eval_reduce'; rewrite ?Nat.max_l; repeat split; auto; try apply Nat2Z.inj_le; auto. }
    { rewrite eval_app; subst s. f_equiv. f_equiv. f_equiv. f_equiv. trivial. }
  Qed.

  (*
  Definition mul_short_mod bound c n (a b : list Z) :=
    let p := mul bound a b in
    let (lo, hi) := (firstn n p, skipn n p) in
    if (* true by range analysis *) c*Z.abs (eval bound hi) <=? weight bound (length hi) - c
    then reduce' bound (length hi) c  lo hi
    else p.
  *)

  Definition mulmod bound n c a b :=
    dlet p := mul bound a b in
    let (lo, hi) := add_mul_limb bound (firstn n p) c (skipn n p) in
    if (* true by range analysis *) c*Z.abs hi <=? weight bound 1 - c
    then reduce' bound 1 c lo [hi]
    else lo ++ [hi].

  Lemma eval_mulmod B (bound := fun _ => B) n a b m
    (s : Z := weight bound n) (c := s mod m) (Hc' : 0 <= c < stream.hd bound)
    (Hn : (n <= length a + length b <= n + n)%nat) (Hb : b <> nil)
    : eval bound (mulmod bound n c a b) mod m = (eval bound a * eval bound b) mod m.
  Proof.
    cbv [Let_In mulmod].
    assert (1 <= length b)%nat by (destruct b; cbn [length] in *; congruence || lia).
    pose proof (eq_refl : weight bound n mod m = c) as Hc.
    pose proof eval_mul B a b as Hmul; fold bound in Hmul.
    epose proof eq_sym (eval_app _ (firstn n _) (skipn n _)) as Hsplit.
    erewrite firstn_skipn, Hmul in Hsplit.
    replace (length (firstn n (mul bound a b))) with n in *
      by (rewrite firstn_length, length_mul; trivial; lia).
    apply (f_equal (fun x => x mod m)) in Hsplit.
    revert Hsplit; push_Zmod; rewrite ?Hc; pull_Zmod; intro.
    change (stream.skipn n bound) with bound in *.
    rewrite add_mul_limb_correct.
    set (t := eval bound (firstn n (mul bound a b)) +
      c * eval bound (skipn n (mul bound a b))) in *.
    progress replace (Nat.max (length (firstn n (mul bound a b))) (length (skipn n (mul bound a b))))
      with n in * by (rewrite firstn_length, skipn_length, !length_mul; trivial; lia).
    break_match; [rewrite eval_reduce', eval_encode, Z.add_comm | rewrite eval_app];
    repeat rewrite ?length_encode, ?firstn_length, ?skipn_length, ?length_mul, ?eval_cons,
                   ?eval_encode, ?eval_nil, ?Z.mul_0_r, ?Z.add_0_r, ?weight_1 in *;
    cbn [length]; replace (Nat.max n 1) with n by lia; trivial; try lia.
    { rewrite <-Z.div_mod by lia. rewrite Hsplit; trivial. }
    { apply Z.mod_pos_bound. lia. }
    rewrite Z.add_comm. rewrite <-Z.div_mod; lia.
  Qed.

  Definition addmod bound c a b :=
    let (sum, carry) := add bound 0 a b in
    reduce' bound 1 c sum [carry].

  Lemma eval_addmod bound c a b m
    (s : Z := weight bound (length a)) (Hc : s mod m = c)
    (Hc' : 0 <= 2*c <= bound O)
    (Hla : (1 < length a)%nat) (Hlb : (length b <= length a)%nat)
    (Ha : 0 <= eval bound a < weight bound (length a))
    (Hb : - weight bound (length a) <= eval bound b <= weight bound (length a)) :
    eval bound (addmod bound c a b) mod m = (eval bound a + eval bound b) mod m.
  Proof.
    cbv [addmod]; rewrite add_correct by trivial; rewrite ?Z.add_0_l.
    rewrite eval_reduce'; rewrite ?eval_encode, ?length_encode, ?weight_1,
    ?eval_cons, ?eval_nil; cbn [length]; rewrite ?Nat.max_l, ?Z.mul_0_r, ?Z.add_0_r by lia; 
      try solve [trivial | cbn; lia | apply Z.mod_pos_bound; lia ].
    { rewrite (Z.add_comm (_ mod _) (_ * (_ / _))), <-Z.div_mod; lia. }
    assert (Z.abs ((eval bound a + eval bound b) / Z.pos (weight bound (length a))) <= 1) by (Z.div_mod_to_equations; nia); nia.
  Qed.

  Lemma eval_map_opp bound xs : eval bound (map Z.opp xs) = - eval bound xs.
  Proof. revert bound; induction xs; trivial; intros; rewrite ?map_cons, ?eval_cons, ?IHxs; lia. Qed.

  Definition submod bound c a b := addmod bound c a (map Z.opp b).

  Lemma eval_submod bound c a b m
    (s : Z := weight bound (length a)) (Hc : s mod m = c)
    (Hc' : 0 <= 2*c <= bound O)
    (Hla : (1 < length a)%nat) (Hlb : (length b <= length a)%nat)
    (Ha : 0 <= eval bound a < weight bound (length a))
    (Hb : - weight bound (length a) <= eval bound b <= weight bound (length a)) :
    eval bound (submod bound c a b) mod m = (eval bound a - eval bound b) mod m.
  Proof. cbv [submod]; rewrite eval_addmod; rewrite ?map_length, ?eval_map_opp; auto; lia. Qed.

  Definition select c a b := map (uncurry (Z.zselect c)) (combine a b).

  Lemma select_correct c a b : length a = length b -> select c a b = if dec (c = 0) then a else b.
  Proof.
    revert b; induction a, b; cbn; try inversion 1; rewrite ?Z.zselect_correct;
      break_match; f_equal; eauto.
  Qed.

  Definition cswap c a b := (select c a b, select c b a).

  Lemma cswap_correct c a b : length a = length b -> cswap c a b = if dec (c = 0) then (a, b) else (b, a).
  Proof. cbv [cswap]; intros; rewrite !select_correct; break_match; congruence. Qed.

  Definition condsub bound a b := let (lo, hi) := add bound 0 a (map Z.opp b) in select (-hi) lo a.

  Lemma condsub_correct bound a b :
    0 <= eval bound a < weight bound (length a) ->
    0 <= eval bound b < weight bound (length a) ->
    (length b <= length a)%nat ->
    condsub bound a b =
    if dec (eval bound a < eval bound b)
    then a
    else encode bound (length a) (eval bound a - eval bound b).
  Proof.
    cbv [condsub]; intros.
    rewrite add_correct, select_correct, eval_map_opp; rewrite ?map_length, ?length_encode, ?Nat.max_l ; try lia.
    break_match; rewrite ?eval_encode, ?Z.add_0_l, ?Z.add_opp_r in *; trivial; try (Z.div_mod_to_equations; nia).
  Qed.

  Definition canon bound m (x : list Z) :=
    dlet m' := encode bound (length x) m in
    NatUtil.nat_rect_arrow_nodep id (fun _ rec x => dlet x := condsub bound x m' in rec x)
    (Z.to_nat (weight bound (length x)/m)) x.

  Lemma canon_correct bound m x
    (Hm : 0 < m < weight bound (length x))
    (Hcanon : encode bound (length x) (eval bound x) = x) :
    canon bound m x = encode bound (length x) (eval bound x mod m).
  Proof.
    pose proof eval_encode bound (length x) (eval bound x) as Heval; rewrite Hcanon in Heval.
    assert (0 <= eval bound x < m + Z.of_nat (Z.to_nat (weight bound (length x) / m)) * m)
      by (Z.div_mod_to_equations; nia).
    cbv [canon Let_In];
    remember (length x) as n in *; set (Z.to_nat (weight bound n / m)) as q in *; clearbody q.
    clear Heval; revert dependent x; induction q; cbn -[condsub Z.of_nat]; intros; subst n.
    { rewrite Z.mod_small; auto; lia. }
    rewrite ?Nat2Z.inj_succ, <-Z.add_1_l, Z.mul_add_distr_r, Z.mul_1_l, Z.add_assoc in *.
    pose proof eval_encode bound (length x) (eval bound x) as Heval; rewrite Hcanon in Heval.
    rewrite condsub_correct; rewrite ?eval_encode, ?length_encode; try (Z.div_mod_to_equations; nia).
    break_match; rewrite ?(Z.mod_small m) in * by lia.
    { rewrite IHq; trivial; try split; try (Z.div_mod_to_equations; nia). }
    rewrite IHq; rewrite ?eval_encode, ?length_encode; try lia.
    { f_equal. rewrite (Z.mod_small _ (weight _ _)); try split; try (Z.div_mod_to_equations; nia).
      push_Zmod; pull_Zmod; rewrite ?Z.sub_0_r; trivial. }
    { f_equal; rewrite ?Z.mod_small; Z.div_mod_to_equations; nia. }
    { rewrite Z.mod_small; try split; try (Z.div_mod_to_equations; lia). }
  Qed.


  Definition divmodw bound (xs : list Z) (s : Z) : Z * list Z :=
    list_rect_fbb_b_b (fun _ _ => (0, [])) (fun x xs  rec bound s =>
      if ((stream.hd bound <? s) && (s mod stream.hd bound =? 0) && (0 <=? x) && (x <? stream.hd bound))%bool
      then let (q, r) := rec (stream.tl bound) (s / stream.hd bound) in (q + x/s, x :: r)
      else let v := eval bound (x::xs) in (v/s, encode bound (length (x::xs)) (v mod s))
    ) xs bound s.

  Lemma divmodw_nil bound s : divmodw bound [] s = (0, []). Proof. trivial. Qed.

  Lemma divmodw_cons bound x xs s : divmodw bound (x::xs) s =
    if ((stream.hd bound <? s) && (s mod stream.hd bound =? 0) && (0 <=? x) && (x <? stream.hd bound))%bool
    then let (q, r) := divmodw (stream.tl bound) xs (s / stream.hd bound) in (q + x/s, x :: r)
    else let v := eval bound (x::xs) in (v/s, encode bound (length (x::xs)) (v mod s)).
  Proof. trivial. Qed.

  Lemma divmodw_correct bound xs s (Hs : 0 < s) :
    divmodw bound xs s = (eval bound xs / s, encode bound (length xs) (eval bound xs mod s)).
  Proof.
    revert dependent s; revert bound; induction xs; intros; rewrite ?divmodw_nil, ?divmodw_cons;
    destruct (Z.ltb_spec (stream.hd bound) s) as [H|H]; cbn [andb]; trivial; [].
    destruct (Z.eqb_spec (s mod stream.hd bound) 0) as [E|E]; cbn [andb]; trivial; [].
    destruct (Z.leb_spec 0 a) as [L|L]; cbn [andb]; trivial; [].
    destruct (Z.ltb_spec a (stream.hd bound)) as [U|U]; cbn [andb]; trivial; [].
    rewrite ?eval_nil, ?eval_cons, ?length_cons, ?encode_S, ?Zmod_0_l, ?Zdiv_0_l, ?IHxs
      by (Z.div_mod_to_equations; nia).
    set (s / stream.hd bound) as s' in *.
    replace s with (stream.hd bound * s') in * by (Z.div_mod_to_equations; nia); clearbody s'; clear s.
    set (stream.hd bound) as B in *.
    rewrite <-!Z.div_div by lia.
    rewrite !(Z.mul_comm B), Z.div_add, <-!(Z.mul_comm B) by lia.
    f_equal.
    { rewrite (Z.div_small a B), Z.div_0_l, Z.add_0_l, Z.add_0_r; lia. }
    { rewrite PullPush.Z.add_mod_r_push by exact I.
      rewrite PullPush.Z.mul_mod_r_push by exact I.
      rewrite <-PullPush.Z.add_mod_r_push by exact I.
      rewrite Z.add_comm, Z.add_mul_mod_distr_l by (try apply Z.mod_pos_bound; nia).
      rewrite Z.mod_add_l' by lia.
      f_equal. { rewrite Z.mod_small; lia. }
      rewrite (Z.mul_comm B), Z_div_plus_full_l by lia.
      rewrite Z.div_small, Z.add_0_r by lia.
      f_equal.
      rewrite (Z.mul_comm B).
      rewrite Z.rem_mul_r by nia.
      rewrite Z.mod_add', Z.mod_mod by lia; trivial. }
  Qed.


  Local Notation "!" := ltac:(vm_decide) (only parsing).
  Goal forall a0 a1 a2 a3 b : Z, False. intros.
  Proof.
    pose proof (eval_reduce' (fun _ => 2^64)%positive 1 38 [a0;a1;a2;a3] [b] (2^256-38) ! ! !).
    cbn [length] in *.
    change ((weight (fun _ : nat => (2 ^ 64)%positive) 4%nat)) with (2^256)%positive in *.
    change ((weight (fun _ : nat => (2 ^ 64)%positive) 1%nat)) with (2^64)%positive in *.
    change (weight (fun _ : nat => (2 ^ 64)%positive) 1%nat)%positive with (2^64)%positive in *.
    set (eval (fun _ : nat => (2 ^ 64)%positive)) as eval in *.
    set (reduce' (fun _ : nat => (2 ^ 64)%positive) _ _ _) as reduce' in *.
  Abort.

  Goal forall a0 a1 a2 a3 b0 b1 b2 b3 : Z, False. intros.
  Proof.
    pose proof (eval_addmod (fun _ => 2^64)%positive 38 [a0;a1;a2;a3] [b0;b1;b2;b3] (2^256-38) ! ! ! !).
    cbn [length] in *.
    change ((weight (fun _ : nat => (2 ^ 64)%positive) 4%nat)) with (2^256)%positive in *.
    change ((weight (fun _ : nat => (2 ^ 64)%positive) 1%nat)) with (2^64)%positive in *.
    change (weight (fun _ : nat => (2 ^ 64)%positive) 1%nat)%positive with (2^64)%positive in *.
    set (eval (fun _ : nat => (2 ^ 64)%positive)) as eval in *.
    set (addmod _ _) as addmod in *.
  Abort.

  Goal forall a0 a1 a2 a3 b0 b1 b2 b3 : Z, False. intros.
  Proof.
    pose proof (eval_mulmod (2^64)%positive 4 [a0;a1;a2;a3] [b0;b1;b2;b3] (2^256-38) ! ! !).
    cbn [length] in *.
    change ((weight (fun _ : nat => (2 ^ 64)%positive) 4%nat)) with (2^256)%positive in *.
    set (eval (fun _ : nat => (2 ^ 64)%positive)) as eval in *.
    change (2 ^ 256 mod (2 ^ 256 - 38)) with 38 in *.
    set (mulmod _ _) as mulmod in *.
  Abort.
End __.
End Saturated.
