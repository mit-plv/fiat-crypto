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

Module Saturated.
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

  Global Instance Proper_eval : Proper (pointwise_relation _ eq==>eq==>eq)%signature eval.
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

  Global Instance Proper_encode : Proper (pointwise_relation _ eq ==> eq ==> eq ==> eq)%signature encode.
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

  Definition forallb [A : Type] (f : A -> bool) (xs : list A) : bool :=
    list_rect (fun _ => bool) true (fun x _  rec => andb (f x) rec) xs.
  
  Lemma forallb_cons [A] f x xs : @forallb A f (cons x xs) = andb (f x) (forallb f xs).
  Proof. trivial. Qed.
  
  Definition isbounded bound x :=
    forallb
      (fun '(b, xi) => (0 <=? xi) && (xi <? Z.pos b))%bool
      (List.combine (stream.firstn (length x) bound) x).
  
  Import Crypto.Util.ListUtil Crypto.Util.ZUtil.Modulo.
  Lemma isbounded_correct' bound x : isbounded bound x = ListUtil.list_beq _ Z.eqb (encode bound (length x) (eval bound x)) x.
  Proof.
    cbv [isbounded].
    revert bound; induction x; intros; trivial.
    rewrite length_cons, encode_S, eval_cons, stream.firstn_S, combine_cons, forallb_cons; cbn [ListUtil.list_beq].
    change (stream.hd ?x) with (x O).
    rewrite IHx; clear IHx.
    rewrite Z.mod_add'_full.
    rewrite Z.mul_comm, Z.div_add by lia.
    pose proof Z.mod_small_iff a (bound O) ltac:(lia).
    destruct (Z.eqb_spec (a mod bound O) a); cbn [andb];
      destruct (Z.leb_spec 0 a) as [L|L]; cbn [andb]; try lia;
      destruct (Z.ltb_spec a (bound 0%nat)) as [R|R]; cbn [andb]; try lia.
    assert (a / bound 0%nat = 0) as -> by (Z.div_mod_to_equations; nia); rewrite ?Z.add_0_l; trivial.
  Qed.
  
  Lemma isbounded_correct bound x : Bool.reflect (encode bound (length x) (eval bound x) = x) (isbounded bound x).
  Proof.
    rewrite isbounded_correct'.
    destruct ListUtil.list_beq eqn:?; constructor; [|intro HX].
    apply (ListUtil.internal_list_dec_bl _ Z.eqb ltac:(lia) (encode bound (length x) (eval bound x)) x); trivial.
    apply (ListUtil.internal_list_dec_lb _ Z.eqb ltac:(lia) (encode bound (length x) (eval bound x)) x) in HX.
    congruence.
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

  Lemma eval_repeat_0 n : forall bound, eval bound (repeat 0 n) = 0.
  Proof. induction n; trivial; cbn [repeat]; intros. rewrite eval_cons, IHn; lia. Qed.

  Lemma eval_app_repeat_0_r n xs bound : eval bound (xs ++ repeat 0 n) = eval bound xs.
  Proof. rewrite eval_app, eval_repeat_0; nia. Qed.

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
                   then add_ (stream.skipn (length l) bound) 0 (skipn (length pps) acc) [h]
                   else [h] in
    r.

  Lemma eval_product_scan_ bound acc pps h c o :
    eval bound (product_scan_ bound acc pps h c o)
    = eval bound acc + h + c + o + eval bound (map (uncurry Z.mul) pps).
  Proof.
    cbv [product_scan_ Let_In].
    rewrite product_scan_correct, eval_app, eval_encode, length_encode.
    case (Z.ltb_spec (Z.of_nat (length pps)) (Z.of_nat (length acc))) as [H|H]; cycle 1;
      repeat rewrite ?eval_cons, ?eval_nil, ?Z.mul_0_r, ?eval_add_, ?Z.add_0_l, ?Z.add_0_r.
    { rewrite <-!Z.add_assoc, <-Z.add_mod_idemp_l, eval_firstn, Z.add_mod_idemp_l, !Z.add_assoc by lia.
      rewrite ?firstn_all2 by lia. Z.div_mod_to_equations; nia. }
    pose proof firstn_skipn (length pps) acc as Hacc.
    eapply (f_equal (eval bound)) in Hacc; erewrite eval_app in Hacc.
    rewrite firstn_length, Nat.min_l in * by lia.
    Z.div_mod_to_equations; nia.
  Qed.

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

  Definition add_mul_limb_ bound acc x ys : list Z :=
    product_scan_ bound acc (map (pair x) ys) 0 0 0.

  Lemma eval_add_mul_limb_ bound acc x ys :
    eval bound (add_mul_limb_ bound acc x ys) = eval bound acc + x * eval bound ys.
  Proof.
    cbv [add_mul_limb_].
    rewrite eval_product_scan_, map_map.
    cbv [uncurry]. rewrite eval_map_mul.
    nia.
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

  Definition select' c a b := map (uncurry (Z.zselect c)) (combine a b).

  Lemma select'_correct c a b : length a = length b -> select' c a b = if dec (c = 0) then a else b.
  Proof.
    revert b; induction a, b; cbn; try inversion 1; rewrite ?Z.zselect_correct;
      break_match; f_equal; eauto.
  Qed.

  Lemma length_select' c a b : length (select' c a b) = Nat.min (length a) (length b).
  Proof. cbv [select']. rewrite map_length, combine_length; lia. Qed.

  Definition select c a b : list Z :=
    dlet a := a in
    dlet b := b in
    select' c (a ++ repeat 0 (length b - length a)%nat) (b ++ repeat 0 (length a - length b)%nat).

  Lemma eval_select bound c a b : eval bound (select c a b) = eval bound (if dec (c = 0) then a else b).
  Proof.
    cbv [select Let_In].
    rewrite select'_correct by (rewrite ?app_length, ?repeat_length; lia).
    break_match; rewrite eval_app_repeat_0_r; trivial.
  Qed.

  Lemma length_select c a b : length (select c a b) = Nat.max (length a) (length b).
  Proof. cbv [select Let_In]. rewrite length_select', ?app_length, ?repeat_length; lia. Qed.

  Definition cswap' c a b := (select' c a b, select' c b a).

  Lemma cswap_correct c a b : length a = length b -> cswap' c a b = if dec (c = 0) then (a, b) else (b, a).
  Proof. cbv [cswap']; intros; rewrite !select'_correct; break_match; congruence. Qed.

  Definition condsub bound a b := let (lo, hi) := add bound 0 a (map Z.opp b) in select (-hi) lo a.

  Lemma eval_map_opp bound xs : eval bound (map Z.opp xs) = - eval bound xs.
  Proof. revert bound; induction xs; trivial; intros; rewrite ?map_cons, ?eval_cons, ?IHxs; lia. Qed.

  Lemma Z__opp_zero_iff z : Z.opp z = 0 <-> z = 0. Proof. lia. Qed.

  Lemma eval_condsub' bound a b :
    eval bound (condsub bound a b) =
    eval bound a - Z.b2z (((eval bound a - eval bound b) / weight bound (Nat.max (length a) (length b)) =? 0)) * eval bound b.
  Proof.
    cbv [condsub]; intros.
    destruct add eqn:H.
    rewrite add_correct in H; Prod.inversion_pair; subst.
    rewrite eval_map_opp, eval_select;
      break_match; rewrite Z__opp_zero_iff, map_length, Z.add_0_l, Z.add_opp_r in * by lia;
      match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end; try contradiction;
      simpl Z.b2z; rewrite ?Z.mul_1_l, ?Z.mul_0_l, ?Z.sub_0_r; trivial.
    rewrite eval_encode, Z.mod_small; trivial; Z.div_mod_to_equations; lia.
  Qed.

  Lemma eval_condsub bound a b
    (Ha : eval bound a < weight bound (Nat.max (length a) (length b)))
    (Hb : 0 <= eval bound b) :
    eval bound (condsub bound a b) =
    eval bound a - Z.b2z (eval bound b <=? eval bound a) * eval bound b.
  Proof.
    rewrite eval_condsub'. f_equal. f_equal. f_equal. eapply Bool.eq_true_iff_eq.
    rewrite Z.eqb_eq, Z.div_small_iff, Z.leb_le by lia.
    intuition try lia.
  Qed.

  Lemma length_condsub bound a b : length (condsub bound a b) = Nat.max (length a) (length b).
  Proof. cbv [condsub]. rewrite add_correct. rewrite length_select, length_encode,map_length. lia. Qed.

  Definition condsubs bound n (a b : list Z) : list Z :=
    NatUtil.nat_rect_arrow_nodep id (fun _ rec x => dlet x := condsub bound x b in rec x) n a.

  Lemma eval_condsubs bound n a b
    (Ha : 0 <= eval bound a < weight bound (Nat.max (length a) (length b)))
    (Hb : 0 <= eval bound b) :
    eval bound (condsubs bound n a b) = eval bound a - (Z.min (Z.of_nat n) (eval bound a / eval bound b)) * eval bound b.
  Proof.
    revert dependent a; induction n; cbn -[condsub Z.mul Z.of_nat eval]; cbv [Let_In id]; intros.
    { rewrite Z.min_l; Z.div_mod_to_equations; nia. }
    etransitivity; [eapply IHn|];
      rewrite eval_condsub, ?length_condsub, <-?Nat.max_assoc, ?Nat.max_id;
      try lia; destruct Z.leb eqn:?; simpl Z.b2z; intuition try lia; [|].
    { assert (eval bound a / eval bound b = Z.succ (Z.pred (eval bound a / eval bound b))) as -> by lia.
      rewrite Nat2Z.inj_succ, <-Z.succ_min_distr.
      ring_simplify.
      destruct (Z.eqb_spec (eval bound b) 0); try (Z.div_mod_to_equations; nia).
      f_equal. f_equal. f_equal. f_equal. Z.div_mod_to_equations; nia. }
    { rewrite ?Z.mul_0_l, ?Z.sub_0_r. rewrite 2Z.min_r; Z.div_mod_to_equations; nia. }
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
End Saturated.
