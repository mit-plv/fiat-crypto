(* Following http://adam.chlipala.net/theses/andreser.pdf chapter 3 *)
Require Import Coq.ZArith.ZArith Coq.micromega.Lia Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop Crypto.Algebra.Nsatz.
Require Import Coq.Strings.String.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.derive.Derive.
Require Import Crypto.Util.Pointed.
Require Import Crypto.Util.Tactics.UniquePose Crypto.Util.Decidable.
Require Import Crypto.Util.Tuple Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.NatUtil.
Require Import QArith.QArith_base QArith.Qround Crypto.Util.QUtil.
Require Import Crypto.Algebra.Ring Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Algebra.SubsetoidRing.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.BarrettReduction.Generalized.
Require Import Crypto.Arithmetic.MontgomeryReduction.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.Proofs.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.Tactics.RunTacticAsConstr.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Hints.PullPush.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Le.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Log2.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Shift.
Require Import Crypto.Util.ZUtil.LandLorShiftBounds.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.HexString.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.CC Crypto.Util.ZUtil.Rshi.
Require Import Crypto.Util.ZUtil.Zselect Crypto.Util.ZUtil.AddModulo.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Hints.PullPush.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.Tactics.DebugPrint.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Equality.
Import ListNotations. Local Open Scope Z_scope.

(** Kludgy hack to get this file to be faster *)
Strategy 0 [LetIn.Let_In LetIn.Let_In_pf].

Module Associational.
  Definition eval (p:list (Z*Z)) : Z :=
    fold_right (fun x y => x + y) 0%Z (map (fun t => fst t * snd t) p).

  Lemma eval_nil : eval nil = 0.
  Proof using Type. trivial.                                             Qed.
  Lemma eval_cons p q : eval (p::q) = fst p * snd p + eval q.
  Proof using Type. trivial.                                             Qed.
  Lemma eval_app p q: eval (p++q) = eval p + eval q.
  Proof using Type. induction p; rewrite <-?List.app_comm_cons;
           rewrite ?eval_nil, ?eval_cons; nsatz.              Qed.

#[global]
  Hint Rewrite eval_nil eval_cons eval_app : push_eval.
  Local Ltac push := autorewrite with
      push_eval push_map push_partition push_flat_map
      push_fold_right push_nth_default cancel_pair.

  Lemma eval_map_mul (a x:Z) (p:list (Z*Z))
  : eval (List.map (fun t => (a*fst t, x*snd t)) p) = a*x*eval p.
  Proof using Type. induction p; push; nsatz.                            Qed.
#[global]
  Hint Rewrite eval_map_mul : push_eval.

  Definition mul (p q:list (Z*Z)) : list (Z*Z) :=
    flat_map (fun t =>
      map (fun t' =>
        (fst t * fst t', snd t * snd t'))
    q) p.
  Lemma eval_mul p q : eval (mul p q) = eval p * eval q.
  Proof using Type. induction p; cbv [mul]; push; nsatz.                 Qed.
#[global]
  Hint Rewrite eval_mul : push_eval.

  Definition negate_snd (p:list (Z*Z)) : list (Z*Z) :=
    map (fun cx => (fst cx, -snd cx)) p.
  Lemma eval_negate_snd p : eval (negate_snd p) = - eval p.
  Proof using Type. induction p; cbv [negate_snd]; push; nsatz.          Qed.
#[global]
  Hint Rewrite eval_negate_snd : push_eval.

  Example base10_2digit_mul (a0:Z) (a1:Z) (b0:Z) (b1:Z) :
    {ab| eval ab = eval [(10,a1);(1,a0)] * eval [(10,b1);(1,b0)]}.
    eexists ?[ab].
    (* Goal: eval ?ab = eval [(10,a1);(1,a0)] * eval [(10,b1);(1,b0)] *)
    rewrite <-eval_mul.
    (* Goal: eval ?ab = eval (mul [(10,a1);(1,a0)] [(10,b1);(1,b0)]) *)
    cbv -[Z.mul eval]; cbn -[eval].
    (* Goal: eval ?ab = eval [(100,(a1*b1));(10,a1*b0);(10,a0*b1);(1,a0*b0)]%RT *)
    trivial.                                              Defined.

  Definition split (s:Z) (p:list (Z*Z)) : list (Z*Z) * list (Z*Z)
    := let hi_lo := partition (fun t => fst t mod s =? 0) p in
       (snd hi_lo, map (fun t => (fst t / s, snd t)) (fst hi_lo)).
  Lemma eval_split s p (s_nz:s<>0) :
    eval (fst (split s p)) + s * eval (snd (split s p)) = eval p.
  Proof using Type. cbv [Let_In split]; induction p;
    repeat match goal with
    | |- context[?a/?b] =>
      unique pose proof (Z_div_exact_full_2 a b ltac:(trivial) ltac:(trivial))
    | _ => progress push
    | _ => progress break_match
    | _ => progress nsatz                                end. Qed.

  Lemma reduction_rule a b s c (modulus_nz:s-c<>0) :
    (a + s * b) mod (s - c) = (a + c * b) mod (s - c).
  Proof using Type. replace (a + s * b) with ((a + c*b) + b*(s-c)) by nsatz.
    rewrite Z.add_mod,Z_mod_mult,Z.add_0_r,Z.mod_mod;trivial. Qed.

  Definition reduce (s:Z) (c:list _) (p:list _) : list (Z*Z) :=
    let lo_hi := split s p in fst lo_hi ++ mul c (snd lo_hi).

  Lemma eval_reduce s c p (s_nz:s<>0) (modulus_nz:s-eval c<>0) :
    eval (reduce s c p) mod (s - eval c) = eval p mod (s - eval c).
  Proof using Type. cbv [reduce]; push.
         rewrite <-reduction_rule, eval_split; trivial.      Qed.
#[global]
  Hint Rewrite eval_reduce : push_eval.

  Definition bind_snd (p : list (Z*Z)) :=
    map (fun t => dlet_nd t2 := snd t in (fst t, t2)) p.

  Lemma bind_snd_correct p : bind_snd p = p.
  Proof using Type.
    cbv [bind_snd]; induction p as [| [? ?] ];
      push; [|rewrite IHp]; reflexivity.
  Qed.

  Lemma eval_rev p : eval (rev p) = eval p.
  Proof using Type. induction p; cbn [rev]; push; lia. Qed.

  Section Carries.
    Definition carryterm (w fw:Z) (t:Z * Z) :=
      if (Z.eqb (fst t) w)
      then dlet_nd t2 := snd t in
           dlet_nd d2 := t2 / fw in
           dlet_nd m2 := t2 mod fw in
           [(w * fw, d2);(w,m2)]
      else [t].

    Lemma eval_carryterm w fw (t:Z * Z) (fw_nonzero:fw<>0):
      eval (carryterm w fw t) = eval [t].
    Proof using Type*.
      cbv [carryterm Let_In]; break_match; push; [|trivial].
      pose proof (Z.div_mod (snd t) fw fw_nonzero).
      rewrite Z.eqb_eq in *.
      nsatz.
    Qed. Hint Rewrite eval_carryterm using auto : push_eval.

    Definition carry (w fw:Z) (p:list (Z * Z)):=
      flat_map (carryterm w fw) p.

    Lemma eval_carry w fw p (fw_nonzero:fw<>0):
      eval (carry w fw p) = eval p.
    Proof using Type*. cbv [carry]; induction p; push; nsatz. Qed.
    Hint Rewrite eval_carry using auto : push_eval.
  End Carries.
  Module Export Hints.
#[global]
    Hint Rewrite eval_nil eval_cons eval_app : push_eval.
#[global]
    Hint Rewrite eval_map_mul : push_eval.
#[global]
    Hint Rewrite eval_mul : push_eval.
#[global]
    Hint Rewrite eval_negate_snd : push_eval.
#[global]
    Hint Rewrite eval_reduce : push_eval.
  End Hints.
End Associational.
Export Associational.Hints.

Module Positional. Section Positional.
  Context (weight : nat -> Z)
          (weight_0 : weight 0%nat = 1)
          (weight_nz : forall i, weight i <> 0).

  Definition to_associational (n:nat) (xs:list Z) : list (Z*Z)
    := combine (map weight (List.seq 0 n)) xs.
  Definition eval n x := Associational.eval (@to_associational n x).
  Lemma eval_to_associational n x :
    Associational.eval (@to_associational n x) = eval n x.
  Proof using Type. trivial.                                             Qed.
  Hint Rewrite @eval_to_associational : push_eval.
  Lemma eval_nil n : eval n [] = 0.
  Proof using Type. cbv [eval to_associational]. rewrite combine_nil_r. reflexivity. Qed.
  Hint Rewrite eval_nil : push_eval.
  Lemma eval0 p : eval 0 p = 0.
  Proof using Type. cbv [eval to_associational]. reflexivity. Qed.
  Hint Rewrite eval0 : push_eval.

  Lemma eval_snoc n m x y : n = length x -> m = S n -> eval m (x ++ [y]) = eval n x + weight n * y.
  Proof using Type.
    cbv [eval to_associational]; intros; subst n m.
    rewrite seq_snoc, map_app.
    rewrite combine_app_samelength by distr_length.
    autorewrite with push_eval. simpl.
    autorewrite with push_eval cancel_pair; ring.
  Qed.

  (* SKIP over this: zeros, add_to_nth *)
  Local Ltac push := autorewrite with push_eval push_map distr_length
    push_flat_map push_fold_right push_nth_default cancel_pair natsimplify.
  Definition zeros n : list Z := repeat 0 n.
  Lemma length_zeros n : length (zeros n) = n. Proof using Type. clear. cbv [zeros]; distr_length. Qed.
  Hint Rewrite length_zeros : distr_length.
  Lemma eval_zeros n : eval n (zeros n) = 0.
  Proof using Type.
    clear.
    cbv [eval Associational.eval to_associational zeros].
    rewrite <- (seq_length n 0) at 2.
    generalize dependent (List.seq 0 n); intro xs.
    induction xs; simpl; nsatz.                               Qed.
  Definition add_to_nth i x (ls : list Z) : list Z
    := ListUtil.update_nth i (fun y => x + y) ls.
  Lemma length_add_to_nth i x ls : length (add_to_nth i x ls) = length ls.
  Proof using Type. clear. cbv [add_to_nth]; distr_length. Qed.
  Hint Rewrite length_add_to_nth : distr_length.
  Lemma eval_add_to_nth (n:nat) (i:nat) (x:Z) (xs:list Z) (H:(i<length xs)%nat)
        (Hn : length xs = n) (* N.B. We really only need [i < Nat.min n (length xs)] *) :
    eval n (add_to_nth i x xs) = weight i * x + eval n xs.
  Proof using Type.
    clear -H Hn.
    subst n.
    cbv [eval to_associational add_to_nth].
    rewrite ListUtil.combine_update_nth_r at 1.
    rewrite <-(update_nth_id i (List.combine _ _)) at 2.
    rewrite <-!(ListUtil.splice_nth_equiv_update_nth_update _ _
      (weight 0, 0)) by (push; lia); cbv [ListUtil.splice_nth id].
    repeat match goal with
           | _ => progress push
           | _ => progress break_match
           | _ => progress (apply Zminus_eq; ring_simplify)
           | _ => rewrite <-ListUtil.map_nth_default_always
           end; lia.                                          Qed.
  Hint Rewrite @eval_add_to_nth eval_zeros : push_eval.

  Definition place (t:Z*Z) (i:nat) : nat * Z :=
    nat_rect
      (fun _ => (nat * Z)%type)
      (O, fst t * snd t)
      (fun i' place_i'
       => let i := S i' in
          if (fst t mod weight i =? 0)
          then (i, let c := fst t / weight i in c * snd t)
          else place_i')
      i.

  Lemma place_in_range (t:Z*Z) (n:nat) : (fst (place t n) < S n)%nat.
  Proof using Type. clear. induction n; cbv [place nat_rect] in *; break_match; autorewrite with cancel_pair; try lia. Qed.
  Lemma weight_place t i : weight (fst (place t i)) * snd (place t i) = fst t * snd t.
  Proof using weight_nz weight_0. clear -weight_nz weight_0. induction i; cbv [place nat_rect] in *; break_match; push;
    repeat match goal with |- context[?a/?b] =>
      unique pose proof (Z_div_exact_full_2 a b ltac:(auto) ltac:(auto))
           end; nsatz.                                        Qed.
  Hint Rewrite weight_place : push_eval.

  Definition from_associational n (p:list (Z*Z)) :=
    List.fold_right (fun t ls =>
      dlet_nd p := place t (pred n) in
      add_to_nth (fst p) (snd p) ls ) (zeros n) p.
  Lemma eval_from_associational n p (n_nz:n<>O \/ p = nil) :
    eval n (from_associational n p) = Associational.eval p.
  Proof using weight_0 weight_nz. destruct n_nz; [ induction p | subst p ];
  cbv [from_associational Let_In] in *; push; try
  pose proof place_in_range a (pred n); try lia; try nsatz;
  apply fold_right_invariant; cbv [zeros add_to_nth];
  intros; rewrite ?map_length, ?List.repeat_length, ?seq_length, ?length_update_nth;
  try lia; destruct n; cbn [Init.Nat.pred] in *; try lia.   Qed.
  Hint Rewrite @eval_from_associational : push_eval.
  Lemma length_from_associational n p : length (from_associational n p) = n.
  Proof using Type. cbv [from_associational Let_In]. apply fold_right_invariant; intros; distr_length. Qed.
  Hint Rewrite length_from_associational : distr_length.

  Section mulmod.
    Context (s:Z) (s_nz:s <> 0)
            (c:list (Z*Z))
            (m_nz:s - Associational.eval c <> 0).
    Definition mulmod (n:nat) (a b:list Z) : list Z
      := let a_a := to_associational n a in
         let b_a := to_associational n b in
         let ab_a := Associational.mul a_a b_a in
         let abm_a := Associational.reduce s c ab_a in
         from_associational n abm_a.
    Lemma eval_mulmod n (f g:list Z)
          (Hf : length f = n) (Hg : length g = n) :
      eval n (mulmod n f g) mod (s - Associational.eval c)
      = (eval n f * eval n g) mod (s - Associational.eval c).
    Proof using m_nz s_nz weight_0 weight_nz. cbv [mulmod]; push; trivial.
    destruct f, g; simpl in *; [ right; subst n | left; try lia.. ].
    clear; cbv -[Associational.reduce].
    induction c as [|?? IHc]; simpl; trivial.                 Qed.
  End mulmod.
  Hint Rewrite @eval_mulmod : push_eval.

  Definition add (n:nat) (a b:list Z) : list Z
    := let a_a := to_associational n a in
       let b_a := to_associational n b in
       from_associational n (a_a ++ b_a).
  Lemma eval_add n (f g:list Z)
        (Hf : length f = n) (Hg : length g = n) :
    eval n (add n f g) = (eval n f + eval n g).
  Proof using weight_0 weight_nz. cbv [add]; push; trivial. destruct n; auto.          Qed.
  Hint Rewrite @eval_add : push_eval.
  Lemma length_add n f g
        (Hf : length f = n) (Hg : length g = n) :
    length (add n f g) = n.
  Proof using Type. clear -Hf Hf; cbv [add]; distr_length.               Qed.
  Hint Rewrite @length_add : distr_length.

  Section Carries.
    Definition carry n m (index:nat) (p:list Z) : list Z :=
      from_associational
        m (@Associational.carry (weight index)
                                (weight (S index) / weight index)
                                (to_associational n p)).

    Lemma length_carry n m index p : length (carry n m index p) = m.
    Proof using Type. cbv [carry]; distr_length. Qed.
    Lemma eval_carry n m i p: (n <> 0%nat) -> (m <> 0%nat) ->
                              weight (S i) / weight i <> 0 ->
      eval m (carry n m i p) = eval n p.
    Proof using weight_0 weight_nz.
      cbv [carry]; intros; push; [|tauto].
      rewrite @Associational.eval_carry by eauto.
      apply eval_to_associational.
    Qed. Hint Rewrite @eval_carry : push_eval.

    Definition carry_reduce n (s:Z) (c:list (Z * Z))
               (index:nat) (p : list Z) :=
      from_associational
        n (Associational.reduce
             s c (to_associational (S n) (@carry n (S n) index p))).

    Lemma eval_carry_reduce n s c index p :
      (s <> 0) -> (s - Associational.eval c <> 0) -> (n <> 0%nat) ->
      (weight (S index) / weight index <> 0) ->
      eval n (carry_reduce n s c index p) mod (s - Associational.eval c)
      = eval n p mod (s - Associational.eval c).
    Proof using weight_0 weight_nz. cbv [carry_reduce]; intros; push; auto.            Qed.
    Hint Rewrite @eval_carry_reduce : push_eval.
    Lemma length_carry_reduce n s c index p
      : length p = n -> length (carry_reduce n s c index p) = n.
    Proof using Type. cbv [carry_reduce]; distr_length.                  Qed.
    Hint Rewrite @length_carry_reduce : distr_length.

    (* N.B. It is important to reverse [idxs] here, because fold_right is
      written such that the first terms in the list are actually used
      last in the computation. For example, running:

      `Eval cbv - [Z.add] in (fun a b c d => fold_right Z.add d [a;b;c]).`

      will produce [fun a b c d => (a + (b + (c + d)))].*)
    Definition chained_carries n s c p (idxs : list nat) :=
      fold_right (fun a b => carry_reduce n s c a b) p (rev idxs).

    Lemma eval_chained_carries n s c p idxs :
      (s <> 0) -> (s - Associational.eval c <> 0) -> (n <> 0%nat) ->
      (forall i, In i idxs -> weight (S i) / weight i <> 0) ->
      eval n (chained_carries n s c p idxs) mod (s - Associational.eval c)
      = eval n p mod (s - Associational.eval c).
    Proof using Type*.
      cbv [chained_carries]; intros; push.
      apply fold_right_invariant; [|intro; rewrite <-in_rev];
        destruct n; intros; push; auto.
    Qed. Hint Rewrite @eval_chained_carries : push_eval.
    Lemma length_chained_carries n s c p idxs
      : length p = n -> length (@chained_carries n s c p idxs) = n.
    Proof using Type.
      intros; cbv [chained_carries]; induction (rev idxs) as [|x xs IHxs];
        cbn [fold_right]; distr_length.
    Qed. Hint Rewrite @length_chained_carries : distr_length.

    (* carries without modular reduction; useful for converting between bases *)
    Definition chained_carries_no_reduce n p (idxs : list nat) :=
      fold_right (fun a b => carry n n a b) p (rev idxs).
    Lemma eval_chained_carries_no_reduce n p idxs:
      (forall i, In i idxs -> weight (S i) / weight i <> 0) ->
      eval n (chained_carries_no_reduce n p idxs) = eval n p.
    Proof using weight_0 weight_nz.
      cbv [chained_carries_no_reduce]; intros.
      destruct n; [push;reflexivity|].
      apply fold_right_invariant; [|intro; rewrite <-in_rev];
        intros; push; auto.
    Qed. Hint Rewrite @eval_chained_carries_no_reduce : push_eval.

    (* Reverse of [eval]; translate from Z to basesystem by putting
    everything in first digit and then carrying. *)
    Definition encode n s c (x : Z) : list Z :=
      chained_carries n s c (from_associational n [(1,x)]) (seq 0 n).
    Lemma eval_encode n s c x :
      (s <> 0) -> (s - Associational.eval c <> 0) -> (n <> 0%nat) ->
      (forall i, In i (seq 0 n) -> weight (S i) / weight i <> 0) ->
      eval n (encode n s c x) mod (s - Associational.eval c)
      = x mod (s - Associational.eval c).
    Proof using Type*. cbv [encode]; intros; push; auto; f_equal; lia. Qed.
    Lemma length_encode n s c x
      : length (encode n s c x) = n.
    Proof using Type. cbv [encode]; repeat distr_length.                 Qed.

  End Carries.
  Hint Rewrite @eval_encode : push_eval.
  Hint Rewrite @length_encode : distr_length.

  Section sub.
    Context (n:nat)
            (s:Z) (s_nz:s <> 0)
            (c:list (Z * Z))
            (m_nz:s - Associational.eval c <> 0)
            (coef:Z).

    Definition negate_snd (a:list Z) : list Z
      := let A := to_associational n a in
         let negA := Associational.negate_snd A in
         from_associational n negA.

    Definition scmul (x:Z) (a:list Z) : list Z
      := let A := to_associational n a in
         let R := Associational.mul A [(1, x)] in
         from_associational n R.

    Definition balance : list Z
      := scmul coef (encode n s c (s - Associational.eval c)).

    Definition sub (a b:list Z) : list Z
      := let ca := add n balance a in
         let _b := negate_snd b in
         add n ca _b.
    Lemma eval_sub a b
      : (forall i, In i (seq 0 n) -> weight (S i) / weight i <> 0) ->
        (List.length a = n) -> (List.length b = n) ->
        eval n (sub a b) mod (s - Associational.eval c)
        = (eval n a - eval n b) mod (s - Associational.eval c).
    Proof using m_nz s_nz weight_0 weight_nz.
      cbv [sub balance scmul negate_snd];
        destruct (zerop n); subst; try reflexivity.
      intros; push; repeat distr_length;
        eauto with lia.
      push_Zmod; push; pull_Zmod; push_Zmod; pull_Zmod; distr_length; eauto.
    Qed.
    Hint Rewrite eval_sub : push_eval.
    Lemma length_sub a b
      : length a = n -> length b = n ->
        length (sub a b) = n.
    Proof using Type. intros; cbv [sub balance scmul negate_snd]; repeat distr_length. Qed.
    Hint Rewrite length_sub : distr_length.
    Definition opp (a:list Z) : list Z
      := sub (zeros n) a.
    Lemma eval_opp
          (a:list Z)
      : (length a = n) ->
        (forall i, In i (seq 0 n) -> weight (S i) / weight i <> 0) ->
        eval n (opp a) mod (s - Associational.eval c)
        = (- eval n a) mod (s - Associational.eval c).
    Proof using m_nz s_nz weight_0 weight_nz. intros; cbv [opp]; push; distr_length; auto.       Qed.
    Lemma length_opp a
      : length a = n -> length (opp a) = n.
    Proof using Type. cbv [opp]; intros; repeat distr_length.            Qed.
  End sub.
  Hint Rewrite @eval_opp @eval_sub : push_eval.
  Hint Rewrite @length_sub @length_opp : distr_length.
End Positional.
(* Hint Rewrite disappears after the end of a section *)
Module Export Hints.
#[global]
  Hint Rewrite length_zeros length_add_to_nth length_from_associational @length_add @length_carry_reduce @length_chained_carries @length_encode @length_sub @length_opp : distr_length.
End Hints.
End Positional.
Export Positional.Hints.

Record weight_properties {weight : nat -> Z} :=
  {
    weight_0 : weight 0%nat = 1;
    weight_positive : forall i, 0 < weight i;
    weight_multiples : forall i, weight (S i) mod weight i = 0;
    weight_divides : forall i : nat, 0 < weight (S i) / weight i;
  }.
Global Hint Resolve weight_0 weight_positive weight_multiples weight_divides.

Section mod_ops.
  Import Positional.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion QArith_base.inject_Z : Z >-> Q.
  (* Design constraints:
     - inputs must be [Z] (b/c reification does not support Q)
     - internal structure must not match on the arguments (b/c reification does not support [positive]) *)
  Context (limbwidth_num limbwidth_den : Z)
          (limbwidth_good : 0 < limbwidth_den <= limbwidth_num)
          (s : Z)
          (c : list (Z*Z))
          (n : nat)
          (len_c : nat)
          (idxs : list nat)
          (len_idxs : nat)
          (m_nz:s - Associational.eval c <> 0) (s_nz:s <> 0)
          (Hn_nz : n <> 0%nat)
          (Hc : length c = len_c)
          (Hidxs : length idxs = len_idxs).
  Definition weight (i : nat)
    := 2^(-(-(limbwidth_num * i) / limbwidth_den)).

  Local Ltac Q_cbv :=
    cbv [Qceiling inject_Z Qle Qfloor Qdiv Qnum Qden Qmult Qinv Qopp].

  Local Lemma weight_ZQ_correct i
        (limbwidth := (limbwidth_num / limbwidth_den)%Q)
    : weight i = 2^Qceiling(limbwidth*i).
  Proof using limbwidth_good.
    clear -limbwidth_good.
    cbv [limbwidth weight]; Q_cbv.
    destruct limbwidth_num, limbwidth_den, i; try reflexivity;
      repeat rewrite ?Pos.mul_1_l, ?Pos.mul_1_r, ?Z.mul_0_l, ?Zdiv_0_l, ?Zdiv_0_r, ?Z.mul_1_l, ?Z.mul_1_r, <- ?Z.opp_eq_mul_m1, ?Pos2Z.opp_pos;
      try reflexivity; try lia.
  Qed.

  Local Ltac t_weight_with lem :=
    clear -limbwidth_good;
    intros; rewrite !weight_ZQ_correct;
    apply lem;
    try lia; Q_cbv; destruct limbwidth_den; cbn; try lia.

  Definition wprops : @weight_properties weight.
  Proof.
    constructor.
    { cbv [weight Z.of_nat]; autorewrite with zsimplify_fast; reflexivity. }
    { intros; apply Z.gt_lt. t_weight_with (@pow_ceil_mul_nat_pos 2). }
    { t_weight_with (@pow_ceil_mul_nat_multiples 2). }
    { intros; apply Z.gt_lt. t_weight_with (@pow_ceil_mul_nat_divide 2). }
  Defined.
  Local Hint Immediate (weight_0 wprops).
  Local Hint Immediate (weight_positive wprops).
  Local Hint Immediate (weight_multiples wprops).
  Local Hint Immediate (weight_divides wprops).
  Local Hint Resolve Z.positive_is_nonzero Z.lt_gt.

  Local Lemma weight_1_gt_1 : weight 1 > 1.
  Proof using limbwidth_good.
    clear -limbwidth_good.
    cut (1 < weight 1); [ lia | ].
    cbv [weight Z.of_nat]; autorewrite with zsimplify_fast.
    apply Z.pow_gt_1; [ lia | ].
    Z.div_mod_to_quot_rem_in_goal; nia.
  Qed.

  Derive carry_mulmod
         SuchThat (forall (f g : list Z)
                          (Hf : length f = n)
                          (Hg : length g = n),
                      (eval weight n (carry_mulmod f g)) mod (s - Associational.eval c)
                      = (eval weight n f * eval weight n g) mod (s - Associational.eval c))
         As eval_carry_mulmod.
  Proof.
    intros.
    rewrite <-eval_mulmod with (s:=s) (c:=c) by auto.
    etransitivity;
      [ | rewrite <- @eval_chained_carries with (s:=s) (c:=c) (idxs:=idxs)
          by auto; reflexivity ].
    eapply f_equal2; [|trivial]. eapply f_equal.
    expand_lists ().
    subst carry_mulmod; reflexivity.
  Qed.

  Derive carrymod
         SuchThat (forall (f : list Z)
                          (Hf : length f = n),
                      (eval weight n (carrymod f)) mod (s - Associational.eval c)
                      = (eval weight n f) mod (s - Associational.eval c))
         As eval_carrymod.
  Proof.
    intros.
    etransitivity;
      [ | rewrite <- @eval_chained_carries with (s:=s) (c:=c) (idxs:=idxs)
          by auto; reflexivity ].
    eapply f_equal2; [|trivial]. eapply f_equal.
    expand_lists ().
    subst carrymod; reflexivity.
  Qed.

  Derive addmod
         SuchThat (forall (f g : list Z)
                          (Hf : length f = n)
                          (Hg : length g = n),
                      (eval weight n (addmod f g)) mod (s - Associational.eval c)
                      = (eval weight n f + eval weight n g) mod (s - Associational.eval c))
         As eval_addmod.
  Proof.
    intros.
    rewrite <-eval_add by auto.
    eapply f_equal2; [|trivial]. eapply f_equal.
    expand_lists ().
    subst addmod; reflexivity.
  Qed.

  Derive submod
         SuchThat (forall (coef:Z)
                          (f g : list Z)
                          (Hf : length f = n)
                          (Hg : length g = n),
                      (eval weight n (submod coef f g)) mod (s - Associational.eval c)
                      = (eval weight n f - eval weight n g) mod (s - Associational.eval c))
         As eval_submod.
  Proof.
    intros.
    rewrite <-eval_sub with (coef:=coef) by auto.
    eapply f_equal2; [|trivial]. eapply f_equal.
    expand_lists ().
    subst submod; reflexivity.
  Qed.

  Derive oppmod
         SuchThat (forall (coef:Z)
                          (f: list Z)
                          (Hf : length f = n),
                      (eval weight n (oppmod coef f)) mod (s - Associational.eval c)
                      = (- eval weight n f) mod (s - Associational.eval c))
         As eval_oppmod.
  Proof.
    intros.
    rewrite <-eval_opp with (coef:=coef) by auto.
    eapply f_equal2; [|trivial]. eapply f_equal.
    expand_lists ().
    subst oppmod; reflexivity.
  Qed.

  Derive encodemod
         SuchThat (forall (f:Z),
                      (eval weight n (encodemod f)) mod (s - Associational.eval c)
                      = f mod (s - Associational.eval c))
         As eval_encodemod.
  Proof.
    intros.
    etransitivity.
    2:rewrite <-@eval_encode with (weight:=weight) (n:=n) by auto; reflexivity.
    eapply f_equal2; [|trivial]. eapply f_equal.
    expand_lists ().
    subst encodemod; reflexivity.
  Qed.
End mod_ops.

Module Saturated.
  Global Hint Resolve weight_positive weight_0 weight_multiples weight_divides.
  Global Hint Resolve Z.positive_is_nonzero Z.lt_gt Nat2Z.is_nonneg.

  Section Weight.
    Context weight {wprops : @weight_properties weight}.

    Lemma weight_multiples_full' j : forall i, weight (i+j) mod weight i = 0.
    Proof using wprops.
      induction j; intros;
        repeat match goal with
               | _ => rewrite Nat.add_succ_r
               | _ => rewrite IHj
               | |- context [weight (S ?x) mod weight _] =>
                 rewrite (Z.div_mod (weight (S x)) (weight x)), weight_multiples by auto
               | _ => progress autorewrite with push_Zmod natsimplify zsimplify_fast
               | _ => reflexivity
               end.
    Qed.

    Lemma weight_multiples_full j i : (i <= j)%nat -> weight j mod weight i = 0.
    Proof using wprops.
      intros; replace j with (i + (j - i))%nat by lia.
      apply weight_multiples_full'.
    Qed.

    Lemma weight_divides_full j i : (i <= j)%nat -> 0 < weight j / weight i.
    Proof using wprops. auto using Z.gt_lt, Z.div_positive_gt_0, weight_multiples_full. Qed.

    Lemma weight_div_mod j i : (i <= j)%nat -> weight j = weight i * (weight j / weight i).
    Proof using wprops. intros. apply Z.div_exact; auto using weight_multiples_full. Qed.
  End Weight.

  Module Associational.
    Section Associational.

      Definition sat_multerm s (t t' : (Z * Z)) : list (Z * Z) :=
        dlet_nd xy := Z.mul_split s (snd t) (snd t') in
              [(fst t * fst t', fst xy); (fst t * fst t' * s, snd xy)].

      Definition sat_mul s (p q : list (Z * Z)) : list (Z * Z) :=
        flat_map (fun t => flat_map (fun t' => sat_multerm s t t') q) p.

      Lemma eval_map_sat_multerm s a q (s_nonzero:s<>0):
        Associational.eval (flat_map (sat_multerm s a) q) = fst a * snd a * Associational.eval q.
      Proof using Type.
        cbv [sat_multerm Let_In]; induction q;
          repeat match goal with
                 | _ => progress autorewrite with cancel_pair push_eval to_div_mod in *
                 | _ => progress simpl flat_map
                 | _ => rewrite IHq
                 | _ => rewrite Z.mod_eq by assumption
                 | _ => ring_simplify; lia
                 end.
      Qed.
      Hint Rewrite eval_map_sat_multerm using (lia || assumption) : push_eval.

      Lemma eval_sat_mul s p q (s_nonzero:s<>0):
        Associational.eval (sat_mul s p q) = Associational.eval p * Associational.eval q.
      Proof using Type.
        cbv [sat_mul]; induction p; [reflexivity|].
        repeat match goal with
               | _ => progress (autorewrite with push_flat_map push_eval in * )
               | _ => rewrite IHp
               | _ => ring_simplify; lia
               end.
      Qed.
      Hint Rewrite eval_sat_mul : push_eval.

      Definition sat_multerm_const s (t t' : (Z * Z)) : list (Z * Z) :=
        if snd t =? 1
        then [(fst t * fst t', snd t')]
        else if snd t =? -1
             then [(fst t * fst t', - snd t')]
             else if snd t =? 0
                  then nil
                  else dlet_nd xy := Z.mul_split s (snd t) (snd t') in
              [(fst t * fst t', fst xy); (fst t * fst t' * s, snd xy)].

      Definition sat_mul_const s (p q : list (Z * Z)) : list (Z * Z) :=
        flat_map (fun t => flat_map (fun t' => sat_multerm_const s t t') q) p.

      Lemma eval_map_sat_multerm_const s a q (s_nonzero:s<>0):
        Associational.eval (flat_map (sat_multerm_const s a) q) = fst a * snd a * Associational.eval q.
      Proof using Type.
        cbv [sat_multerm_const Let_In]; induction q;
          repeat match goal with
                 | _ => progress autorewrite with cancel_pair push_eval to_div_mod in *
                 | _ => progress simpl flat_map
                 | H : _ = 1 |- _ => rewrite H
                 | H : _ = -1 |- _ => rewrite H
                 | H : _ = 0 |- _ => rewrite H
                 | _ => progress break_match; Z.ltb_to_lt
                 | _ => rewrite IHq
                 | _ => rewrite Z.mod_eq by assumption
                 | _ => ring_simplify; lia
                 end.
      Qed.
      Hint Rewrite eval_map_sat_multerm_const using (lia || assumption) : push_eval.

      Lemma eval_sat_mul_const s p q (s_nonzero:s<>0):
        Associational.eval (sat_mul_const s p q) = Associational.eval p * Associational.eval q.
      Proof using Type.
        cbv [sat_mul_const]; induction p; [reflexivity|].
        repeat match goal with
               | _ => progress (autorewrite with push_flat_map push_eval in * )
               | _ => rewrite IHp
               | _ => ring_simplify; lia
               end.
      Qed.
      Hint Rewrite eval_sat_mul_const : push_eval.
    End Associational.
  End Associational.

  Section DivMod.
    Lemma mod_step a b c d: 0 < a -> 0 < b ->
                            c mod a + a * ((c / a + d) mod b) = (a * d + c) mod (a * b).
    Proof using Type.
      intros; rewrite Z.rem_mul_r by lia. push_Zmod.
      autorewrite with zsimplify pull_Zmod. repeat (f_equal; try ring).
    Qed.

    Lemma div_step a b c d : 0 < a -> 0 < b ->
                             (c / a + d) / b = (a * d + c) / (a * b).
    Proof using Type. intros; Z.div_mod_to_quot_rem_in_goal; nia. Qed.

    Lemma add_mod_div_multiple a b n m:
      n > 0 ->
      0 <= m / n ->
      m mod n = 0 ->
      (a / n + b) mod (m / n) = (a + n * b) mod m / n.
    Proof using Type.
      intros. rewrite <-!Z.div_add' by auto using Z.positive_is_nonzero.
      rewrite Z.mod_pull_div, Z.mul_div_eq' by auto using Z.gt_lt.
      repeat (f_equal; try lia).
    Qed.

    Lemma add_mod_l_multiple a b n m:
      0 < n / m -> m <> 0 -> n mod m = 0 ->
      (a mod n + b) mod m = (a + b) mod m.
    Proof using Type.
      intros.
      rewrite (proj2 (Z.div_exact n m ltac:(auto))) by auto.
      rewrite Z.rem_mul_r by auto.
      push_Zmod. autorewrite with zsimplify.
      pull_Zmod. reflexivity.
    Qed.

    Definition is_div_mod {T} (evalf : T -> Z) dm y n :=
      evalf (fst dm) = y mod n /\ snd dm = y / n.

    Lemma is_div_mod_step {T} evalf1 evalf2 dm1 dm2 y1 y2 n1 n2 x :
      n1 > 0 ->
      0 < n2 / n1 ->
      n2 mod n1 = 0 ->
      evalf2 (fst dm2) = evalf1 (fst dm1) + n1 * ((snd dm1 + x) mod (n2 / n1)) ->
      snd dm2 = (snd dm1 + x) / (n2 / n1) ->
      y2 = y1 + n1 * x ->
      @is_div_mod T evalf1 dm1 y1 n1 ->
      @is_div_mod T evalf2 dm2 y2 n2.
    Proof using Type.
      intros; subst y2; cbv [is_div_mod] in *.
      repeat match goal with
             | H: _ /\ _ |- _ => destruct H
             | H: ?LHS = _ |- _ => match LHS with context [dm2] => rewrite H end
             | H: ?LHS = _ |- _ => match LHS with context [dm1] => rewrite H end
             | _ => rewrite mod_step by lia
             | _ => rewrite div_step by lia
             | _ => rewrite Z.mul_div_eq_full by lia
             end.
      split; f_equal; lia.
    Qed.

    Lemma is_div_mod_result_equal {T} evalf dm y1 y2 n :
      y1 = y2 ->
      @is_div_mod T evalf dm y1 n ->
      @is_div_mod T evalf dm y2 n.
    Proof using Type. congruence. Qed.
  End DivMod.
End Saturated.

Module Columns.
  Import Saturated.
  Section Columns.
    Context weight {wprops : @weight_properties weight}.

    Definition eval n (x : list (list Z)) : Z := Positional.eval weight n (map sum x).

    Lemma eval_nil n : eval n [] = 0.
    Proof using Type. cbv [eval]; simpl. apply Positional.eval_nil. Qed.
    Hint Rewrite eval_nil : push_eval.
    Lemma eval_snoc n x y : n = length x -> eval (S n) (x ++ [y]) = eval n x + weight n * sum y.
    Proof using Type.
      cbv [eval]; intros; subst. rewrite map_app. simpl map.
      apply Positional.eval_snoc; distr_length.
    Qed. Hint Rewrite eval_snoc using (solve [distr_length]) : push_eval.

    Hint Rewrite <- Z.div_add' using lia : pull_Zdiv.

    Ltac cases :=
      match goal with
      | |- _ /\ _ => split
      | H: _ /\ _ |- _ => destruct H
      | H: _ \/ _ |- _ => destruct H
      | _ => progress break_match; try discriminate
      end.

    Section Flatten.
      Section flatten_column.
        Context (fw : Z). (* maximum size of the result *)

        (* Outputs (sum, carry) *)
        Definition flatten_column (digit: list Z) : (Z * Z) :=
          list_rect (fun _ => (Z * Z)%type) (0,0)
                    (fun xx tl flatten_column_tl =>
                       list_rect
                         (fun _ => (Z * Z)%type) (xx mod fw, xx / fw)
                         (fun yy tl' _ =>
                            list_rect
                              (fun _ => (Z * Z)%type) (dlet_nd x := xx in dlet_nd y := yy in Z.add_get_carry_full fw x y)
                              (fun _ _ _ =>
                                 dlet_nd x := xx in
                                   dlet_nd rec := flatten_column_tl in (* recursively get the sum and carry *)
                                   dlet_nd sum_carry := Z.add_get_carry_full fw x (fst rec) in (* add the new value to the sum *)
                                   dlet_nd carry' := snd sum_carry + snd rec in (* add the two carries together *)
                                   (fst sum_carry, carry'))
                              tl')
                         tl)
                    digit.
      End flatten_column.

      Definition flatten_step (digit:list Z) (acc_carry:list Z * Z) : list Z * Z :=
        dlet sum_carry := flatten_column (weight (S (length (fst acc_carry))) / weight (length (fst acc_carry))) (snd acc_carry::digit) in
              (fst acc_carry ++ fst sum_carry :: nil, snd sum_carry).

      Definition flatten (xs : list (list Z)) : list Z * Z :=
        fold_right (fun a b => flatten_step a b) (nil,0) (rev xs).

      Ltac push_fast :=
        repeat match goal with
               | _ => progress cbv [Let_In]
               | |- context [list_rect _ _ _ ?ls] => rewrite single_list_rect_to_match; destruct ls
               | _ => progress (unfold flatten_step in *; fold flatten_step in * )
               | _ => rewrite Nat.add_1_r
               | _ => rewrite Z.mul_div_eq_full by (auto; lia)
               | _ => rewrite weight_multiples
               | _ => reflexivity
               | _ => solve [repeat (f_equal; try ring)]
               | _ => congruence
               | _ => progress cases
               end.
      Ltac push :=
        repeat match goal with
               | _ => progress push_fast
               | _ => progress autorewrite with cancel_pair to_div_mod
               | _ => progress autorewrite with push_sum push_fold_right push_nth_default in *
               | _ => progress autorewrite with pull_Zmod pull_Zdiv zsimplify_fast
               | _ => progress autorewrite with list distr_length push_eval
               end.

      Lemma flatten_column_mod fw (xs : list Z) :
        fst (flatten_column fw xs)  = sum xs mod fw.
      Proof using Type.
        induction xs; simpl flatten_column; cbv [Let_In];
          repeat match goal with
                 | _ => rewrite IHxs
                 | _ => progress push
                 end.
      Qed. Hint Rewrite flatten_column_mod : to_div_mod.

      Lemma flatten_column_div fw (xs : list Z) (fw_nz : fw <> 0) :
        snd (flatten_column fw xs)  = sum xs / fw.
      Proof using Type.
        induction xs; simpl flatten_column; cbv [Let_In];
          repeat match goal with
                 | _ => rewrite IHxs
                 | _ => rewrite Z.mul_div_eq_full by lia
                 | _ => progress push
                 end.
      Qed. Hint Rewrite flatten_column_div using auto with zarith : to_div_mod.

      Hint Rewrite Positional.eval_nil : push_eval.
      Local Hint Resolve Z.gt_lt.

      Lemma length_flatten_step digit state :
        length (fst (flatten_step digit state)) = S (length (fst state)).
      Proof using Type. cbv [flatten_step]; push. Qed.
      Hint Rewrite length_flatten_step : distr_length.
      Lemma length_flatten inp : length (fst (flatten inp)) = length inp.
      Proof using Type. cbv [flatten]. induction inp using rev_ind; push. Qed.
      Hint Rewrite length_flatten : distr_length.

      Lemma flatten_div_mod n inp :
        length inp = n ->
        (Positional.eval weight n (fst (flatten inp))
         = (eval n inp) mod (weight n))
        /\ (snd (flatten inp) = eval n inp / weight n).
      Proof using wprops.
        (* to make the invariant take the right form, we make everything depend on output length, not input length *)
        intro. subst n. rewrite <-(length_flatten inp). cbv [flatten].
        induction inp using rev_ind; intros; [push|].
        repeat match goal with
               | _ => rewrite Nat.add_1_r
               | _ => progress (fold (flatten inp) in * )
               | _ => erewrite Positional.eval_snoc by (distr_length; reflexivity)
               | H: _ = _ mod (weight _) |- _ => rewrite H
               | H: _ = _ / (weight _) |- _ => rewrite H
               | _ => progress rewrite ?mod_step, ?div_step by auto
               | _ => progress autorewrite with cancel_pair to_div_mod push_sum list push_fold_right push_eval
               | _ => progress (distr_length; push_fast)
               end.
      Qed.

      Lemma flatten_mod {n} inp :
        length inp = n ->
        (Positional.eval weight n (fst (flatten inp)) = (eval n inp) mod (weight n)).
      Proof using wprops. apply flatten_div_mod. Qed.
      Hint Rewrite @flatten_mod : push_eval.

      Lemma flatten_div {n} inp :
        length inp = n -> snd (flatten inp) = eval n inp / weight n.
      Proof using wprops. apply flatten_div_mod. Qed.
      Hint Rewrite @flatten_div : push_eval.

      Lemma flatten_snoc x inp : flatten (inp ++ [x]) = flatten_step x (flatten inp).
      Proof using Type. cbv [flatten]. rewrite rev_unit. reflexivity. Qed.

      Lemma flatten_partitions inp:
        forall n i, length inp = n -> (i < n)%nat ->
                    nth_default 0 (fst (flatten inp)) i = ((eval n inp) mod (weight (S i))) / weight i.
      Proof using wprops.
        induction inp using rev_ind; intros; destruct n; distr_length.
        rewrite flatten_snoc.
        push; distr_length;
          [rewrite IHinp with (n:=n) by lia; rewrite weight_div_mod with (j:=n) (i:=S i) by (eauto; lia); push_Zmod; push |].
        repeat match goal with
               | _ => progress replace (length inp) with n by lia
               | _ => progress replace i with n by lia
               | _ => progress push
               | _ => erewrite flatten_div by eauto
               | _ => rewrite <-Z.div_add' by auto
               | _ => rewrite Z.mul_div_eq' by auto
               | _ => rewrite Z.mod_pull_div by auto using Z.lt_le_incl
               | _ => progress autorewrite with push_nth_default natsimplify
               end.
      Qed.
    End Flatten.

    Section FromAssociational.
      (* nils *)
      Definition nils n : list (list Z) := repeat nil n.
      Lemma length_nils n : length (nils n) = n. Proof using Type. cbv [nils]. distr_length. Qed.
      Hint Rewrite length_nils : distr_length.
      Lemma eval_nils n : eval n (nils n) = 0.
      Proof using Type.
        erewrite <-Positional.eval_zeros by eauto.
        cbv [eval nils]; rewrite List.map_repeat; reflexivity.
      Qed. Hint Rewrite eval_nils : push_eval.

      (* cons_to_nth *)
      Definition cons_to_nth i x (xs : list (list Z)) : list (list Z) :=
        ListUtil.update_nth i (fun y => cons x y) xs.
      Lemma length_cons_to_nth i x xs : length (cons_to_nth i x xs) = length xs.
      Proof using Type. cbv [cons_to_nth]. distr_length. Qed.
      Hint Rewrite length_cons_to_nth : distr_length.
      Lemma cons_to_nth_add_to_nth xs : forall i x,
          map sum (cons_to_nth i x xs) = Positional.add_to_nth i x (map sum xs).
      Proof using Type.
        cbv [cons_to_nth]; induction xs as [|? ? IHxs];
          intros i x; destruct i; simpl; rewrite ?IHxs; reflexivity.
      Qed.
      Lemma eval_cons_to_nth n i x xs : (i < length xs)%nat -> length xs = n ->
                                        eval n (cons_to_nth i x xs) = weight i * x + eval n xs.
      Proof using Type.
        cbv [eval]; intros. rewrite cons_to_nth_add_to_nth.
        apply Positional.eval_add_to_nth; distr_length.
      Qed. Hint Rewrite eval_cons_to_nth using (solve [distr_length]) : push_eval.

      Hint Rewrite Positional.eval_zeros : push_eval.
      Hint Rewrite Positional.length_from_associational : distr_length.
      Hint Rewrite Positional.eval_add_to_nth using (solve [distr_length]): push_eval.

      (* from_associational *)
      Definition from_associational n (p:list (Z*Z)) : list (list Z) :=
        List.fold_right (fun t ls =>
                           dlet_nd p := Positional.place weight t (pred n) in
                           cons_to_nth (fst p) (snd p) ls ) (nils n) p.
      Lemma length_from_associational n p : length (from_associational n p) = n.
      Proof using Type. cbv [from_associational Let_In]. apply fold_right_invariant; intros; distr_length. Qed.
      Hint Rewrite length_from_associational: distr_length.
      Lemma eval_from_associational n p (n_nonzero:n<>0%nat\/p=nil):
        eval n (from_associational n p) = Associational.eval p.
      Proof using wprops.
        erewrite <-Positional.eval_from_associational by eauto.
        induction p; [ autorewrite with push_eval; solve [auto] |].
        cbv [from_associational Positional.from_associational]; autorewrite with push_fold_right.
        fold (from_associational n p); fold (Positional.from_associational weight n p).
        cbv [Let_In].
        match goal with |- context [Positional.place _ ?x ?n] =>
                        pose proof (Positional.place_in_range weight x n) end.
        repeat match goal with
               | _ => rewrite Nat.succ_pred in * by auto
               | _ => rewrite IHp by auto
               | _ => progress autorewrite with push_eval
               | _ => progress cases
               | _ => congruence
               end.
      Qed.

      Lemma from_associational_step n t p :
        from_associational n (t :: p) =
        cons_to_nth (fst (Positional.place weight t (Nat.pred n)))
                    (snd (Positional.place weight t (Nat.pred n)))
                    (from_associational n p).
      Proof using Type. reflexivity. Qed.
    End FromAssociational.
  End Columns.
End Columns.

Module Rows.
  Import Saturated.
  Section Rows.
    Context weight {wprops : @weight_properties weight}.

    Local Notation rows := (list (list Z)) (only parsing).
    Local Notation cols := (list (list Z)) (only parsing).

    Hint Rewrite Positional.eval_nil Positional.eval0 @Positional.eval_snoc
         Positional.eval_to_associational
         Columns.eval_nil Columns.eval_snoc using (auto; solve [distr_length]) : push_eval.
    Local Hint Resolve in_eq in_cons.

    Definition eval n (inp : rows) :=
      sum (map (Positional.eval weight n) inp).
    Lemma eval_nil n : eval n nil = 0.
    Proof using Type. cbv [eval]. rewrite map_nil, sum_nil; reflexivity. Qed.
    Hint Rewrite eval_nil : push_eval.
    Lemma eval0 x : eval 0 x = 0.
    Proof using Type. cbv [eval]. induction x; autorewrite with push_map push_sum push_eval; lia. Qed.
    Hint Rewrite eval0 : push_eval.
    Lemma eval_cons n r inp : eval n (r :: inp) = Positional.eval weight n r + eval n inp.
    Proof using Type. cbv [eval]; autorewrite with push_map push_sum; reflexivity. Qed.
    Hint Rewrite eval_cons : push_eval.
    Lemma eval_app n x y : eval n (x ++ y) = eval n x + eval n y.
    Proof using Type. cbv [eval]; autorewrite with push_map push_sum; reflexivity. Qed.
    Hint Rewrite eval_app : push_eval.

    Ltac In_cases :=
      repeat match goal with
             | H: In _ (_ ++ _) |- _ => apply in_app_or in H; destruct H
             | H: In _ (_ :: _) |- _ => apply in_inv in H; destruct H
             | H: In _ nil |- _ => contradiction H
             | H: forall x, In x (?y :: ?ls) -> ?P |- _ =>
               unique pose proof (H y ltac:(apply in_eq));
               unique assert (forall x, In x ls -> P) by auto
             | H: forall x, In x (?ls ++ ?y :: nil) -> ?P |- _ =>
               unique pose proof (H y ltac:(auto using in_or_app, in_eq));
               unique assert (forall x, In x ls -> P) by eauto using in_or_app
             end.

    Section FromAssociational.
      (* extract row *)
      Definition extract_row (inp : cols) : cols * list Z := (map (fun c => tl c) inp, map (fun c => hd 0 c) inp).

      Lemma eval_extract_row (inp : cols): forall n,
          length inp = n ->
          Positional.eval weight n (snd (extract_row inp)) = Columns.eval weight n inp - Columns.eval weight n (fst (extract_row inp)) .
      Proof using Type.
        cbv [extract_row].
        induction inp using rev_ind; [ | destruct n ];
          repeat match goal with
                 | _ => progress intros
                 | _ => progress distr_length
                 | _ => rewrite Positional.eval_snoc with (n:=n) by distr_length
                 | _ => progress autorewrite with cancel_pair push_eval push_map in *
                 | _ => ring
                 end.
        rewrite IHinp by distr_length.
        destruct x; cbn [hd tl]; rewrite ?sum_nil, ?sum_cons; ring.
      Qed. Hint Rewrite eval_extract_row using (solve [distr_length]) : push_eval.

      Lemma length_fst_extract_row n (inp : cols) :
        length inp = n -> length (fst (extract_row inp)) = n.
      Proof using Type. cbv [extract_row]; autorewrite with cancel_pair; distr_length. Qed.
      Hint Rewrite length_fst_extract_row : distr_length.

      Lemma length_snd_extract_row n (inp : cols) :
        length inp = n -> length (snd (extract_row inp)) = n.
      Proof using Type. cbv [extract_row]; autorewrite with cancel_pair; distr_length. Qed.
      Hint Rewrite length_snd_extract_row : distr_length.

      (* max column size *)
      Definition max_column_size (x:cols) := fold_right (fun a b => Nat.max a b) 0%nat (map (fun c => length c) x).

      (* TODO: move to where list is defined *)
      Hint Rewrite @app_nil_l : list.
      Hint Rewrite <-@app_comm_cons: list.

      Lemma max_column_size_nil : max_column_size nil = 0%nat.
      Proof using Type. reflexivity. Qed. Hint Rewrite max_column_size_nil : push_max_column_size.
      Lemma max_column_size_cons col (inp : cols) :
        max_column_size (col :: inp) = Nat.max (length col) (max_column_size inp).
      Proof using Type. reflexivity. Qed. Hint Rewrite max_column_size_cons : push_max_column_size.
      Lemma max_column_size_app (x y : cols) :
        max_column_size (x ++ y) = Nat.max (max_column_size x) (max_column_size y).
      Proof using Type. induction x; autorewrite with list push_max_column_size; lia. Qed.
      Hint Rewrite max_column_size_app : push_max_column_size.
      Lemma max_column_size0 (inp : cols) :
        forall n,
          length inp = n -> (* this is not needed to make the lemma true, but prevents reliance on the implementation of Columns.eval*)
          max_column_size inp = 0%nat -> Columns.eval weight n inp = 0.
      Proof using Type.
        induction inp as [|x inp] using rev_ind; destruct n; try destruct x; intros;
          autorewrite with push_max_column_size push_eval push_sum distr_length in *; try lia.
        rewrite IHinp; distr_length; lia.
      Qed.

      (* from_columns *)
      Definition from_columns' n start_state : cols * rows :=
        fold_right (fun _ (state : cols * rows) =>
                      let cols'_row := extract_row (fst state) in
                      (fst cols'_row, snd state ++ [snd cols'_row])
                   ) start_state (repeat 0 n).

      Definition from_columns (inp : cols) : rows := snd (from_columns' (max_column_size inp) (inp, [])).

      Lemma eval_from_columns'_with_length m st n:
        (length (fst st) = n) ->
        length (fst (from_columns' m st)) = n /\
        ((forall r, In r (snd st) -> length r = n) ->
         forall r, In r (snd (from_columns' m st)) -> length r = n) /\
        eval n (snd (from_columns' m st)) = Columns.eval weight n (fst st) + eval n (snd st)
                                                                             - Columns.eval weight n (fst (from_columns' m st)).
      Proof using Type.
        cbv [from_columns']; intros.
        apply fold_right_invariant; intros;
          repeat match goal with
                 | _ => progress (intros; subst)
                 | _ => progress autorewrite with cancel_pair push_eval
                 | _ => progress In_cases
                 | _ => split; try lia
                 | H: _ /\ _ |- _ => destruct H
                 | _ => solve [auto using length_fst_extract_row, length_snd_extract_row]
                 end.
      Qed.
      Lemma length_fst_from_columns' m st :
        length (fst (from_columns' m st)) = length (fst st).
      Proof using weight. apply eval_from_columns'_with_length; reflexivity. Qed.
      Hint Rewrite length_fst_from_columns' : distr_length.
      Lemma length_snd_from_columns' m st :
        (forall r, In r (snd st) -> length r = length (fst st)) ->
        forall r, In r (snd (from_columns' m st)) -> length r = length (fst st).
      Proof using weight. apply eval_from_columns'_with_length. reflexivity. Qed.
      Hint Rewrite length_snd_from_columns' : distr_length.
      Lemma eval_from_columns' m st n :
        (length (fst st) = n) ->
        eval n (snd (from_columns' m st)) = Columns.eval weight n (fst st) + eval n (snd st)
                                                                             - Columns.eval weight n (fst (from_columns' m st)).
      Proof using Type. apply eval_from_columns'_with_length. Qed.
      Hint Rewrite eval_from_columns' using (auto; solve [distr_length]) : push_eval.

      Lemma max_column_size_extract_row inp :
        max_column_size (fst (extract_row inp)) = (max_column_size inp - 1)%nat.
      Proof using Type.
        cbv [extract_row]. autorewrite with cancel_pair.
        induction inp; [ reflexivity | ].
        autorewrite with push_max_column_size push_map distr_length.
        rewrite IHinp. auto using Nat.sub_max_distr_r.
      Qed.
      Hint Rewrite max_column_size_extract_row : push_max_column_size.

      Lemma max_column_size_from_columns' m st :
        max_column_size (fst (from_columns' m st)) = (max_column_size (fst st) - m)%nat.
      Proof using Type.
        cbv [from_columns']; induction m; intros; cbn - [max_column_size extract_row];
          autorewrite with push_max_column_size; lia.
      Qed.
      Hint Rewrite max_column_size_from_columns' : push_max_column_size.

      Lemma eval_from_columns (inp : cols) :
        forall n, length inp = n -> eval n (from_columns inp) = Columns.eval weight n inp.
      Proof using Type.
        intros; cbv [from_columns];
          repeat match goal with
                 | _ => progress autorewrite with cancel_pair push_eval push_max_column_size
                 | _ => rewrite max_column_size0 with (inp := fst (from_columns' _ _)) by
                       (autorewrite with push_max_column_size; distr_length)
                 | _ => lia
                 end.
      Qed.
      Hint Rewrite eval_from_columns using (auto; solve [distr_length]) : push_eval.

      Lemma length_from_columns inp:
        forall r, In r (from_columns inp) -> length r = length inp.
      Proof using weight.
        cbv [from_columns]; intros.
        change inp with (fst (inp, @nil (list Z))).
        eapply length_snd_from_columns'; eauto.
        autorewrite with cancel_pair; intros; In_cases.
      Qed.
      Hint Rewrite length_from_columns : distr_length.

      (* from associational *)
      Definition from_associational n (p : list (Z * Z)) := from_columns (Columns.from_associational weight n p).

      Lemma eval_from_associational n p: (n <> 0%nat \/ p = nil) ->
                                         eval n (from_associational n p) = Associational.eval p.
      Proof using wprops.
        intros. cbv [from_associational].
        rewrite eval_from_columns by auto using Columns.length_from_associational.
        auto using Columns.eval_from_associational.
      Qed.

      Lemma length_from_associational n p :
        forall r, In r (from_associational n p) -> length r = n.
      Proof using Type.
        cbv [from_associational]; intros.
        match goal with H: _ |- _ => apply length_from_columns in H end.
        rewrite Columns.length_from_associational in *; auto.
      Qed.

      Lemma max_column_size_zero_iff x :
        max_column_size x = 0%nat <-> (forall c, In c x -> c = nil).
      Proof using Type.
        cbv [max_column_size]; induction x; intros; [ cbn; tauto | ].
        autorewrite with push_fold_right push_map.
        rewrite max_0_iff, IHx.
        split; intros; [ | rewrite length_zero_iff_nil; solve [auto] ].
        match goal with H : _ /\ _ |- _ => destruct H end.
        In_cases; subst; auto using length0_nil.
      Qed.

      Lemma max_column_size_Columns_from_associational n p :
        n <> 0%nat -> p <> nil ->
        max_column_size (Columns.from_associational weight n p) <> 0%nat.
      Proof using Type.
        intros.
        rewrite max_column_size_zero_iff.
        intro. destruct p; [congruence | ].
        rewrite Columns.from_associational_step in *.
        cbv [Columns.cons_to_nth] in *.
        match goal with H : forall c, In c (update_nth ?n ?f ?ls) -> _ |- _ =>
                        assert (n < length (update_nth n f ls))%nat;
                          [ | specialize (H (nth n (update_nth n f ls) nil) ltac:(auto using nth_In)) ]
        end.
        { distr_length.
          rewrite Columns.length_from_associational.
          remember (Nat.pred n) as m. replace n with (S m) by lia.
          apply Positional.place_in_range. }
        rewrite <-nth_default_eq in *.
        autorewrite with push_nth_default in *.
        rewrite eq_nat_dec_refl in *.
        congruence.
      Qed.

      Lemma from_associational_nonnil n p :
        n <> 0%nat -> p <> nil ->
        from_associational n p <> nil.
      Proof using Type.
        intros; cbv [from_associational from_columns from_columns'].
        pose proof (max_column_size_Columns_from_associational n p ltac:(auto) ltac:(auto)).
        case_eq (max_column_size (Columns.from_associational weight n p)); [lia|].
        intros; cbn.
        rewrite <-length_zero_iff_nil. distr_length.
      Qed.
    End FromAssociational.

    Section Flatten.
      Local Notation fw := (fun i => weight (S i) / weight i) (only parsing).

      Section SumRows.
        Definition sum_rows' start_state (row1 row2 : list Z) : list Z * Z * nat :=
          fold_right (fun next (state : list Z * Z * nat) =>
                        let i := snd state in
                        let low_high' :=
                            let low_high := fst state in
                            let low := fst low_high in
                            let high := snd low_high in
                          dlet_nd sum_carry := Z.add_with_get_carry_full (fw i) high (fst next) (snd next) in
                          (low ++ [fst sum_carry], snd sum_carry) in
                     (low_high', S i)) start_state (rev (combine row1 row2)).
        Definition sum_rows row1 row2 := fst (sum_rows' (nil, 0, 0%nat) row1 row2).

        Ltac push :=
          repeat match goal with
                 | _ => progress intros
                 | _ => progress cbv [Let_In]
                 | _ => rewrite Nat.add_1_r
                 | _ => erewrite Positional.eval_snoc by eauto
                 | H : length _ = _ |- _ => rewrite H
                 | H: 0%nat = _ |- _ => rewrite <-H
                 | [p := _ |- _] => subst p
                 | _ => progress autorewrite with cancel_pair natsimplify push_sum_rows list push_nth_default
                 | _ => progress autorewrite with cancel_pair in *
                 | _ => progress distr_length
                 | _ => progress break_match
                 | _ => ring
                 | _ => solve [ repeat (f_equal; try ring) ]
                 | _ => tauto
                 | _ => solve [eauto]
                 end.

        Lemma sum_rows'_cons state x1 row1 x2 row2 :
          sum_rows' state (x1 :: row1) (x2 :: row2) =
          sum_rows' (fst (fst state) ++ [(snd (fst state) + x1 + x2) mod (fw (snd state))],
                     (snd (fst state) + x1 + x2) / fw (snd state),
                     S (snd state)) row1 row2.
        Proof using Type.
          cbv [sum_rows' Let_In]; autorewrite with push_combine.
          rewrite !fold_left_rev_right. cbn [fold_left].
          autorewrite with cancel_pair to_div_mod. congruence.
        Qed.

        Lemma sum_rows'_nil state :
          sum_rows' state nil nil = state.
        Proof using Type. reflexivity. Qed.

        Hint Rewrite sum_rows'_cons sum_rows'_nil : push_sum_rows.

        Lemma sum_rows'_div_mod_length row1 :
          forall nm start_state row2 row1' row2',
            let m := snd start_state in
            let n := length row1 in
            length row2 = n ->
            length row1' = m ->
            length row2' = m ->
            length (fst (fst start_state)) = m ->
            (nm = n + m)%nat ->
            let eval := Positional.eval weight in
            is_div_mod (eval m) (fst start_state) (eval m row1' + eval m row2') (weight m) ->
            length (fst (fst (sum_rows' start_state row1 row2))) = nm
            /\ is_div_mod (eval nm) (fst (sum_rows' start_state row1 row2))
                          (eval nm (row1' ++ row1) + eval nm (row2' ++ row2))
                          (weight nm).
        Proof using wprops.
          induction row1 as [|x1 row1]; destruct row2 as [|x2 row2]; intros; subst nm; push; [ ].
          rewrite (app_cons_app_app _ row1'), (app_cons_app_app _ row2').
          apply IHrow1; clear IHrow1; autorewrite with cancel_pair distr_length in *; try lia.
          eapply is_div_mod_step with (x := x1 + x2); try eassumption; push.
        Qed.

        Lemma sum_rows_div_mod n row1 row2 :
          length row1 = n -> length row2 = n ->
          let eval := Positional.eval weight in
          is_div_mod (eval n) (sum_rows row1 row2) (eval n row1 + eval n row2) (weight n).
        Proof using wprops.
          cbv [sum_rows]; intros.
          apply sum_rows'_div_mod_length with (row1':=nil) (row2':=nil);
            cbv [is_div_mod]; autorewrite with cancel_pair push_eval zsimplify; distr_length.
        Qed.

        Lemma sum_rows_mod n row1 row2 :
          length row1 = n -> length row2 = n ->
          Positional.eval weight n (fst (sum_rows row1 row2))
          = (Positional.eval weight n row1 + Positional.eval weight n row2) mod (weight n).
        Proof using wprops. apply sum_rows_div_mod. Qed.
        Lemma sum_rows_div row1 row2 n:
          length row1 = n -> length row2 = n ->
          snd (sum_rows row1 row2)
          = (Positional.eval weight n row1 + Positional.eval weight n row2) / (weight n).
        Proof using wprops. apply sum_rows_div_mod. Qed.

        Lemma sum_rows'_partitions row1 :
          forall nm start_state row2 row1' row2',
            let m := snd start_state in
            let n := length row1 in
            length row2 = n ->
            length row1' = m ->
            length row2' = m ->
            length (fst (fst start_state)) = m ->
            nm = (n + m)%nat ->
            let eval := Positional.eval weight in
            snd (fst start_state) = (eval m row1' + eval m row2') / weight m ->
            (forall j, (j < m)%nat ->
                       nth_default 0 (fst (fst start_state)) j = ((eval m row1' + eval m row2') mod (weight (S j))) / (weight j)) ->
            forall i, (i < nm)%nat ->
                      nth_default 0 (fst (fst (sum_rows' start_state row1 row2))) i
                      = ((eval nm (row1' ++ row1) + eval nm (row2' ++ row2)) mod (weight (S i))) / (weight i).
        Proof using wprops.
          induction row1 as [|x1 row1]; destruct row2 as [|x2 row2]; intros; subst nm; push; [].

          rewrite (app_cons_app_app _ row1'), (app_cons_app_app _ row2').
          apply IHrow1; clear IHrow1; push;
            repeat match goal with
                   | H : ?LHS = _ |- _ =>
                     match LHS with context [start_state] => rewrite H end
                   | H : context [nth_default 0 (fst (fst start_state))] |- _ => rewrite H by lia
                   | _ => rewrite <-(Z.add_assoc _ x1 x2)
                   end.
          { rewrite div_step by auto using Z.gt_lt.
            rewrite Z.mul_div_eq_full by auto; rewrite weight_multiples by auto. push. }
          { rewrite weight_div_mod with (j:=snd start_state) (i:=S j) by (auto; lia).
            push_Zmod. autorewrite with zsimplify_fast. reflexivity. }
          { push. replace (snd start_state) with j in * by lia.
            push. rewrite add_mod_div_multiple by auto using Z.lt_le_incl.
            push. }
        Qed.

        Lemma sum_rows_partitions row1: forall row2 n i,
            length row1 = n -> length row2 = n -> (i < n)%nat ->
            nth_default 0 (fst (sum_rows row1 row2)) i
            = ((Positional.eval weight n row1 + Positional.eval weight n row2) mod weight (S i)) / (weight i).
        Proof using wprops.
          cbv [sum_rows]; intros. rewrite <-(Nat.add_0_r n).
          rewrite <-(app_nil_l row1), <-(app_nil_l row2).
          apply sum_rows'_partitions; intros;
            autorewrite with cancel_pair push_eval zsimplify_fast push_nth_default; distr_length.
        Qed.

        Lemma length_sum_rows row1 row2 n:
          length row1 = n -> length row2 = n ->
          length (fst (sum_rows row1 row2)) = n.
        Proof using wprops.
          cbv [sum_rows]; intros.
          eapply sum_rows'_div_mod_length; cbv [is_div_mod];
            autorewrite with cancel_pair; distr_length; auto using nil_length0.
        Qed. Hint Rewrite length_sum_rows : distr_length.
      End SumRows.
      Local Hint Resolve length_sum_rows.
      Hint Rewrite sum_rows_mod using (auto; solve [distr_length; auto]) : push_eval.

      Definition flatten' (start_state : list Z * Z) (inp : rows) : list Z * Z :=
        fold_right (fun next_row (state : list Z * Z)=>
                      let out_carry := sum_rows next_row (fst state) in
                      (fst out_carry, snd state + snd out_carry)) start_state inp.

      (* In order for the output to have the right length and bounds,
         we insert rows of zeroes if there are fewer than two rows. *)
      Definition flatten n (inp : rows) : list Z * Z :=
        let default := Positional.zeros n in
        flatten' (hd default inp, 0) (hd default (tl inp) :: tl (tl inp)).

      Lemma flatten'_cons state r inp :
        flatten' state (r :: inp) = (fst (sum_rows r (fst (flatten' state inp))), snd (flatten' state inp) + snd (sum_rows r (fst (flatten' state inp)))).
      Proof using Type. cbv [flatten']; autorewrite with list push_fold_right. reflexivity. Qed.
      Lemma flatten'_snoc state r inp :
        flatten' state (inp ++ r :: nil) = flatten' (fst (sum_rows r (fst state)), snd state + snd (sum_rows r (fst state))) inp.
      Proof using Type. cbv [flatten']; autorewrite with list push_fold_right. reflexivity. Qed.
      Lemma flatten'_nil state : flatten' state [] = state. Proof using Type. reflexivity. Qed.
      Hint Rewrite flatten'_cons flatten'_snoc flatten'_nil : push_flatten.

      Ltac push :=
        repeat match goal with
               | _ => progress intros
               | H: length ?x = ?n |- context [snd (sum_rows ?x _)] => rewrite sum_rows_div with (n:=n) by (distr_length; eauto)
               | H: length ?x = ?n |- context [snd (sum_rows _ ?x)] => rewrite sum_rows_div with (n:=n) by (distr_length; eauto)
               | H: length _ = _ |- _ => rewrite H
               | _ => progress autorewrite with cancel_pair push_flatten push_eval distr_length zsimplify_fast
               | _ => progress In_cases
               | |- _ /\ _ => split
               | |- context [?x mod ?y] => unique pose proof (Z.mul_div_eq_full x y ltac:(auto)); lia
               | _ => apply length_sum_rows
               | _ => solve [repeat (ring_simplify; f_equal; try ring)]
               | _ => congruence
               | _ => solve [eauto]
               end.

      Lemma flatten'_div_mod_length n inp : forall start_state,
        length (fst start_state) = n ->
        (forall row, In row inp -> length row = n) ->
        length (fst (flatten' start_state inp)) = n
        /\ (inp <> nil ->
            is_div_mod (Positional.eval weight n) (flatten' start_state inp)
                       (Positional.eval weight n (fst start_state) + eval n inp + weight n * snd start_state)
                       (weight n)).
      Proof using wprops.
        induction inp using rev_ind; push; [apply IHinp; push|].
        destruct (dec (inp = nil)); [subst inp; cbv [is_div_mod]
                                    | eapply is_div_mod_result_equal; try apply IHinp]; push.
        { autorewrite with zsimplify; push. }
        { rewrite Z.div_add' by auto; push. }
      Qed.

      Hint Rewrite (@Positional.length_zeros) : distr_length.
      Hint Rewrite (@Positional.eval_zeros weight) using auto : push_eval.

      Lemma flatten_div_mod inp n :
        (forall row, In row inp -> length row = n) ->
        is_div_mod (Positional.eval weight n) (flatten n inp) (eval n inp) (weight n).
      Proof using wprops.
        intros; cbv [flatten].
        destruct inp; [|destruct inp]; cbn [hd tl].
        { cbv [is_div_mod]; push.
          erewrite sum_rows_div by (distr_length; reflexivity).
          push. }
        { cbv [is_div_mod]; push. }
        { eapply is_div_mod_result_equal; try apply flatten'_div_mod_length; push. }
      Qed.

      Lemma flatten_mod inp n :
        (forall row, In row inp -> length row = n) ->
        Positional.eval weight n (fst (flatten n inp)) = (eval n inp) mod (weight n).
      Proof using wprops. apply flatten_div_mod. Qed.
      Lemma flatten_div inp n :
        (forall row, In row inp -> length row = n) ->
        snd (flatten n inp) = (eval n inp) / (weight n).
      Proof using wprops. apply flatten_div_mod. Qed.

      Lemma length_flatten' n start_state inp :
        length (fst start_state) = n ->
        (forall row, In row inp -> length row = n) ->
        length (fst (flatten' start_state inp)) = n.
      Proof using wprops. apply flatten'_div_mod_length. Qed.
      Hint Rewrite length_flatten' : distr_length.

      Lemma length_flatten n inp :
        (forall row, In row inp -> length row = n) ->
        length (fst (flatten n inp)) = n.
      Proof using wprops.
        intros.
        apply length_flatten'; push;
          destruct inp as [|? [|? ?] ]; try congruence; cbn [hd tl] in *; push;
            subst row; distr_length.
      Qed. Hint Rewrite length_flatten : distr_length.

      Lemma flatten'_partitions n inp : forall start_state,
        inp <> nil ->
        length (fst start_state) = n ->
        (forall row, In row inp -> length row = n) ->
        forall i, (i < n)%nat ->
                  nth_default 0 (fst (flatten' start_state inp)) i
                  = ((Positional.eval weight n (fst start_state) + eval n inp) mod weight (S i)) / (weight i).
      Proof using wprops.
        induction inp using rev_ind; push.
        destruct (dec (inp = nil)).
        { subst inp; push. rewrite sum_rows_partitions with (n:=n) by eauto. push. }
        { erewrite IHinp; push.
          rewrite add_mod_l_multiple by auto using weight_divides_full, weight_multiples_full.
          push. }
      Qed.

      Lemma flatten_partitions inp n :
        (forall row, In row inp -> length row = n) ->
        forall i, (i < n)%nat ->
                  nth_default 0 (fst (flatten n inp)) i = (eval n inp mod weight (S i)) / (weight i).
      Proof using wprops.
        intros; cbv [flatten].
        intros; destruct inp as [| ? [| ? ?] ]; try congruence; cbn [hd tl] in *;  try solve [push].
        { cbn. autorewrite with push_nth_default.
          rewrite sum_rows_partitions with (n:=n) by distr_length.
          autorewrite with push_eval zsimplify_fast.
          auto with zarith. }
        { push. rewrite sum_rows_partitions with (n:=n) by distr_length; push. }
        { rewrite flatten'_partitions with (n:=n); push. }
      Qed.

      Definition partition n x :=
        map (fun i => (x mod weight (S i)) / weight i) (seq 0 n).

      Lemma nth_default_partitions x : forall p n,
        (forall i, (i < n)%nat -> nth_default 0 p i = (x mod weight (S i)) / weight i) ->
        length p = n ->
        p = partition n x.
      Proof using Type.
        cbv [partition]; induction p using rev_ind; intros; distr_length; subst n; [reflexivity|].
        rewrite Nat.add_1_r, seq_snoc.
        autorewrite with natsimplify push_map.
        rewrite <-IHp; auto; intros;
          match goal with H : context [nth_default _ (p ++ [ _ ])] |- _ =>
                          rewrite <-H by lia end.
        { autorewrite with push_nth_default natsimplify. reflexivity. }
        { autorewrite with push_nth_default natsimplify.
          break_match; lia. }
      Qed.

      Lemma partition_step n x :
        partition (S n) x = partition n x ++ [(x mod weight (S n)) / weight n].
      Proof using Type.
        cbv [partition]. rewrite seq_snoc.
        autorewrite with natsimplify push_map. reflexivity.
      Qed.

      Lemma length_partition n x : length (partition n x) = n.
      Proof using Type. cbv [partition]; distr_length. Qed.
      Hint Rewrite length_partition : distr_length.

      Lemma eval_partition n x :
        Positional.eval weight n (partition n x) = x mod (weight n).
      Proof using wprops.
        induction n; intros.
        { cbn. rewrite (weight_0); auto with zarith. }
        { rewrite (Z.div_mod (x mod weight (S n)) (weight n)) by auto.
          rewrite <-Znumtheory.Zmod_div_mod by (try apply Z.mod_divide; auto).
          rewrite partition_step, Positional.eval_snoc with (n:=n) by distr_length.
          lia. }
      Qed.

      Lemma flatten_partitions' inp n :
        (forall row, In row inp -> length row = n) ->
        fst (flatten n inp) = partition n (eval n inp).
      Proof using wprops. auto using nth_default_partitions, flatten_partitions, length_flatten. Qed.
    End Flatten.

    Section Ops.
      Definition add n p q := flatten n [p; q].

      (* TODO: Although cleaner, using Positional.negate snd inserts
      dlets which prevent add-opp=>sub transformation in partial
      evaluation. Should probably either make partial evaluation
      handle that or remove the dlet in
      Positional.from_associational. *)
      Definition sub n p q := flatten n [p; map (fun x => dlet y := x in Z.opp y) q].

      Hint Rewrite eval_cons eval_nil using solve [auto] : push_eval.

      Definition mul base n m (p q : list Z) :=
        let p_a := Positional.to_associational weight n p in
        let q_a := Positional.to_associational weight n q in
        let pq_a := Associational.sat_mul base p_a q_a in
        flatten m (from_associational m pq_a).

      (* TODO : move sat_reduce and repeat_sat_reduce to Saturated.Associational *)
      Definition sat_reduce base s c (p : list (Z * Z)) :=
        let lo_hi := Associational.split s p in
        fst lo_hi ++ (Associational.sat_mul_const base c (snd lo_hi)).

      Definition repeat_sat_reduce base s c (p : list (Z * Z)) n :=
        fold_right (fun _ q => sat_reduce base s c q) p (seq 0 n).

      Definition mulmod base s c n nreductions (p q : list Z) :=
        let p_a := Positional.to_associational weight n p in
        let q_a := Positional.to_associational weight n q in
        let pq_a := Associational.sat_mul base p_a q_a in
        let r_a := repeat_sat_reduce base s c pq_a nreductions in
        flatten n (from_associational n r_a).

      Hint Rewrite Associational.eval_sat_mul_const Associational.eval_sat_mul Associational.eval_split using solve [auto] : push_eval.
      Hint Rewrite eval_from_associational using solve [auto] : push_eval.
      Hint Rewrite eval_partition using solve [auto] : push_eval.
      Ltac solver :=
        intros; cbv [sub add mul mulmod sat_reduce];
        rewrite ?flatten_partitions' by (intros; In_cases; subst; distr_length; eauto using length_from_associational);
        rewrite ?flatten_div by (intros; In_cases; subst; distr_length; eauto using length_from_associational);
        autorewrite with push_eval; ring_simplify_subterms;
        try reflexivity.

      Lemma add_partitions n p q :
        n <> 0%nat -> length p = n -> length q = n ->
        fst (add n p q) = partition n (Positional.eval weight n p + Positional.eval weight n q).
      Proof using wprops. solver. Qed.

      Lemma add_div n p q :
        n <> 0%nat -> length p = n -> length q = n ->
        snd (add n p q) = (Positional.eval weight n p + Positional.eval weight n q) / weight n.
      Proof using wprops. solver. Qed.

      Lemma eval_map_opp q :
        forall n, length q = n ->
                  Positional.eval weight n (map Z.opp q) = - Positional.eval weight n q.
      Proof using Type.
        induction q using rev_ind; intros;
          repeat match goal with
                 | _ => progress autorewrite with push_map push_eval
                 | _ => erewrite !Positional.eval_snoc with (n:=length q) by distr_length
                 | _ => rewrite IHq by auto
                 | _ => ring
                 end.
      Qed. Hint Rewrite eval_map_opp using solve [auto]: push_eval.

      Lemma sub_partitions n p q :
        n <> 0%nat -> length p = n -> length q = n ->
        fst (sub n p q) = partition n (Positional.eval weight n p - Positional.eval weight n q).
      Proof using wprops. solver. Qed.

      Lemma sub_div n p q :
        n <> 0%nat -> length p = n -> length q = n ->
        snd (sub n p q) = (Positional.eval weight n p - Positional.eval weight n q) / weight n.
      Proof using wprops. solver. Qed.

      Lemma mul_partitions base n m p q :
        base <> 0 -> n <> 0%nat -> m <> 0%nat -> length p = n -> length q = n ->
        fst (mul base n m p q) = partition m (Positional.eval weight n p * Positional.eval weight n q).
      Proof using wprops. solver. Qed.

      Lemma eval_sat_reduce base s c p :
        base <> 0 -> s - Associational.eval c <> 0 -> s <> 0 ->
        Associational.eval (sat_reduce base s c p) mod (s - Associational.eval c)
        = Associational.eval p mod (s - Associational.eval c).
      Proof using Type.
        intros; cbv [sat_reduce].
        autorewrite with push_eval.
        rewrite <-Associational.reduction_rule by lia.
        autorewrite with push_eval; reflexivity.
      Qed.
      Hint Rewrite eval_sat_reduce using auto : push_eval.

      Lemma eval_repeat_sat_reduce base s c p n :
        base <> 0 -> s - Associational.eval c <> 0 -> s <> 0 ->
        Associational.eval (repeat_sat_reduce base s c p n) mod (s - Associational.eval c)
        = Associational.eval p mod (s - Associational.eval c).
      Proof using Type.
        intros; cbv [repeat_sat_reduce].
        apply fold_right_invariant; intros; autorewrite with push_eval; auto.
      Qed.
      Hint Rewrite eval_repeat_sat_reduce using auto : push_eval.

      Lemma eval_mulmod base s c n nreductions p q :
        base <> 0 -> s <> 0 -> s - Associational.eval c <> 0 ->
        n <> 0%nat -> length p = n -> length q = n ->
        (Positional.eval weight n (fst (mulmod base s c n nreductions p q))
         + weight n * (snd (mulmod base s c n nreductions p q))) mod (s - Associational.eval c)
        = (Positional.eval weight n p * Positional.eval weight n q) mod (s - Associational.eval c).
      Proof using wprops.
        solver.
        rewrite <-Z.div_mod'' by auto.
        autorewrite with push_eval; reflexivity.
      Qed.
    End Ops.
  End Rows.
End Rows.

Module BaseConversion.
  Import Positional.
  Section BaseConversion.
    Local Hint Resolve Z.gt_lt.
    Context (sw dw : nat -> Z) (* source/destination weight functions *)
            {swprops : @weight_properties sw}
            {dwprops : @weight_properties dw}.

    Definition convert_bases (sn dn : nat) (p : list Z) : list Z :=
      let p' := Positional.from_associational dw dn (Positional.to_associational sw sn p) in
      chained_carries_no_reduce dw dn p' (seq 0 (pred dn)).

    Import Saturated.

    Lemma eval_convert_bases sn dn p :
      (dn <> 0%nat) -> length p = sn ->
      eval dw dn (convert_bases sn dn p) = eval sw sn p.
    Proof using dwprops.
      cbv [convert_bases]; intros.
      rewrite eval_chained_carries_no_reduce; auto using Z.positive_is_nonzero.
      rewrite eval_from_associational; auto.
    Qed.

    Hint Rewrite
         @Rows.eval_from_associational
         @Associational.eval_carry
         @Associational.eval_mul
         @Positional.eval_to_associational
         Associational.eval_carryterm
         @eval_convert_bases using solve [auto using Z.positive_is_nonzero] : push_eval.

    Ltac push_eval := intros; autorewrite with push_eval; auto with zarith.

    (* convert from positional in one weight to the other, then to associational *)
    Definition to_associational n m p : list (Z * Z) :=
      let p' := convert_bases n m p in
      Positional.to_associational dw m p'.

    (* TODO : move to Associational? *)
    Section reorder.
      Definition reordering_carry (w fw : Z) (p : list (Z * Z)) :=
        fold_right (fun t acc =>
                      let r := Associational.carryterm w fw t in
                      if fst t =? w then acc ++ r else r ++ acc) nil p.

      Lemma eval_reordering_carry w fw p (_:fw<>0):
        Associational.eval (reordering_carry w fw p) = Associational.eval p.
      Proof using Type.
        cbv [reordering_carry]. induction p; [reflexivity |].
        autorewrite with push_fold_right. break_match; push_eval.
      Qed.
    End reorder.
    Hint Rewrite eval_reordering_carry using solve [auto using Z.positive_is_nonzero] : push_eval.

    (* carry at specified indices in dw, then use Rows.flatten to convert to Positional with sw *)
    Definition from_associational idxs n (p : list (Z * Z)) : list Z :=
      (* important not to use Positional.carry here; we don't want to accumulate yet *)
      let p' := fold_right (fun i acc => reordering_carry (dw i) (dw (S i) / dw i) acc) (Associational.bind_snd p) (rev idxs) in
      fst (Rows.flatten sw n (Rows.from_associational sw n p')).

    Lemma eval_carries p idxs :
      Associational.eval (fold_right (fun i acc => reordering_carry (dw i) (dw (S i) / dw i) acc) p idxs) =
      Associational.eval p.
    Proof using dwprops. apply fold_right_invariant; push_eval. Qed.
    Hint Rewrite eval_carries: push_eval.

    Lemma eval_to_associational n m p :
      m <> 0%nat -> length p = n ->
      Associational.eval (to_associational n m p) = Positional.eval sw n p.
    Proof using dwprops. cbv [to_associational]; push_eval. Qed.
    Hint Rewrite eval_to_associational using solve [push_eval; distr_length] : push_eval.

    Lemma eval_from_associational idxs n p :
      n <> 0%nat -> 0 <= Associational.eval p < sw n ->
      Positional.eval sw n (from_associational idxs n p) = Associational.eval p.
    Proof using dwprops swprops.
      cbv [from_associational]; intros.
      rewrite Rows.flatten_mod by eauto using Rows.length_from_associational.
      rewrite Associational.bind_snd_correct.
      push_eval.
    Qed.
    Hint Rewrite eval_from_associational using solve [push_eval; distr_length] : push_eval.

    Lemma from_associational_partitions n idxs p  (_:n<>0%nat):
      forall i, (i < n)%nat ->
                nth_default 0 (from_associational idxs n p) i = (Associational.eval p) mod (sw (S i)) / sw i.
    Proof using dwprops swprops.
      intros; cbv [from_associational].
      rewrite Rows.flatten_partitions with (n:=n) by (eauto using Rows.length_from_associational; lia).
      rewrite Associational.bind_snd_correct.
      push_eval.
    Qed.

    Lemma from_associational_eq n idxs p  (_:n<>0%nat):
      from_associational idxs n p = Rows.partition sw n (Associational.eval p).
    Proof using dwprops swprops.
      intros. cbv [from_associational].
      rewrite Rows.flatten_partitions' with (n:=n) by eauto using Rows.length_from_associational.
      rewrite Associational.bind_snd_correct.
      push_eval.
    Qed.

    Derive from_associational_inlined
           SuchThat (forall idxs n p,
                        from_associational_inlined idxs n p = from_associational idxs n p)
           As from_associational_inlined_correct.
    Proof.
      intros.
      cbv beta iota delta [from_associational reordering_carry Associational.carryterm].
      cbv beta iota delta [Let_In]. (* inlines all shifts/lands from carryterm *)
      cbv beta iota delta [from_associational Rows.from_associational Columns.from_associational].
      cbv beta iota delta [Let_In]. (* inlines the shifts from place *)
      subst from_associational_inlined; reflexivity.
    Qed.

    Derive to_associational_inlined
           SuchThat (forall n m p,
                        to_associational_inlined n m p = to_associational n m p)
           As to_associational_inlined_correct.
    Proof.
      intros.
      cbv beta iota delta [ to_associational convert_bases
                                             Positional.to_associational
                                             Positional.from_associational
                                             chained_carries_no_reduce
                                             carry
                                             Associational.carry
                                             Associational.carryterm
                          ].
      cbv beta iota delta [Let_In].
      subst to_associational_inlined; reflexivity.
    Qed.

    (* carry chain that aligns terms in the intermediate weight with the final weight *)
    Definition aligned_carries (log_dw_sw nout : nat)
      := (map (fun i => ((log_dw_sw * (i + 1)) - 1))%nat (seq 0 nout)).

    Section mul_converted.
      Definition mul_converted
              n1 n2 (* lengths in original format *)
              m1 m2 (* lengths in converted format *)
              (n3 : nat) (* final length *)
              (idxs : list nat) (* carries to do -- this helps preemptively line up weights *)
              (p1 p2 : list Z) :=
        let p1_a := to_associational n1 m1 p1 in
        let p2_a := to_associational n2 m2 p2 in
        let p3_a := Associational.mul p1_a p2_a in
        from_associational idxs n3 p3_a.

      Lemma eval_mul_converted n1 n2 m1 m2 n3 idxs p1 p2 (_:n3<>0%nat) (_:m1<>0%nat) (_:m2<>0%nat):
        length p1 = n1 -> length p2 = n2 ->
        0 <= (Positional.eval sw n1 p1 * Positional.eval sw n2 p2) < sw n3 ->
        Positional.eval sw n3 (mul_converted n1 n2 m1 m2 n3 idxs p1 p2) = (Positional.eval sw n1 p1) * (Positional.eval sw n2 p2).
      Proof using dwprops swprops.  cbv [mul_converted]; push_eval. Qed.
      Hint Rewrite eval_mul_converted : push_eval.

      Lemma mul_converted_partitions n1 n2 m1 m2 n3 idxs p1 p2  (_:n3<>0%nat) (_:m1<>0%nat) (_:m2<>0%nat):
        length p1 = n1 -> length p2 = n2 ->
        mul_converted n1 n2 m1 m2 n3 idxs p1 p2 = Rows.partition sw n3 (Positional.eval sw n1 p1 * Positional.eval sw n2 p2).
      Proof using dwprops swprops.
        intros; cbv [mul_converted].
        rewrite from_associational_eq by auto. push_eval.
      Qed.
    End mul_converted.
  End BaseConversion.

  (* multiply two (n*k)-bit numbers by converting them to n k-bit limbs each, multiplying, then converting back *)
  Section widemul.
    Context (log2base : Z) (log2base_pos : 0 < log2base).
    Context (n : nat) (n_nz : n <> 0%nat) (n_le_log2base : Z.of_nat n <= log2base)
            (nout : nat) (nout_2 : nout = 2%nat). (* nout is always 2, but partial evaluation is overeager if it's a constant *)
    Let dw : nat -> Z := weight (log2base / Z.of_nat n) 1.
    Let sw : nat -> Z := weight log2base 1.

    Local Lemma base_bounds : 0 < 1 <= log2base. Proof using log2base_pos n_nz nout_2. auto with zarith. Qed.
    Local Lemma dbase_bounds : 0 < 1 <= log2base / Z.of_nat n. Proof using n_le_log2base n_nz nout_2. auto with zarith. Qed.
    Let dwprops : @weight_properties dw := wprops (log2base / Z.of_nat n) 1 dbase_bounds.
    Let swprops : @weight_properties sw := wprops log2base 1 base_bounds.

    Local Hint Resolve Z.gt_lt Z.positive_is_nonzero Nat2Z.is_nonneg.

    Definition widemul a b := mul_converted sw dw 1 1 n n nout (aligned_carries n nout) [a] [b].

    Lemma widemul_correct a b :
      0 <= a * b < 2^log2base * 2^log2base ->
      widemul a b = [(a * b) mod 2^log2base; (a * b) / 2^log2base].
    Proof using dwprops swprops.
      cbv [widemul]; intros.
      rewrite mul_converted_partitions by auto with zarith.
      clear dwprops swprops.
      subst nout sw; cbv [weight]; cbn.
      autorewrite with zsimplify.
      rewrite Z.pow_mul_r, Z.pow_2_r by lia.
      Z.rewrite_mod_small. reflexivity.
    Qed.

    Derive widemul_inlined
           SuchThat (forall a b,
                        0 <= a * b < 2^log2base * 2^log2base ->
                        widemul_inlined a b = [(a * b) mod 2^log2base; (a * b) / 2^log2base])
           As widemul_inlined_correct.
    Proof.
      intros.
      rewrite <-widemul_correct by auto.
      cbv beta iota delta [widemul mul_converted].
      rewrite <-to_associational_inlined_correct with (p:=[a]).
      rewrite <-to_associational_inlined_correct with (p:=[b]).
      rewrite <-from_associational_inlined_correct.
      subst widemul_inlined; reflexivity.
    Qed.

    Derive widemul_inlined_reverse
           SuchThat (forall a b,
                        0 <= a * b < 2^log2base * 2^log2base ->
                        widemul_inlined_reverse a b = [(a * b) mod 2^log2base; (a * b) / 2^log2base])
           As widemul_inlined_reverse_correct.
    Proof.
      intros.
      rewrite <-widemul_inlined_correct by assumption.
      cbv [widemul_inlined].
      match goal with |- _ = from_associational_inlined sw dw ?idxs ?n ?p =>
                      transitivity (from_associational_inlined sw dw idxs n (rev p));
                        [ | transitivity (from_associational sw dw idxs n p); [ | reflexivity ] ](* reverse to make addc chains line up *)
      end.
      Focus 2. {
        rewrite from_associational_inlined_correct by (subst nout; auto).
        cbv [from_associational].
        rewrite !Rows.flatten_partitions' by eauto using Rows.length_from_associational.
        rewrite !Rows.eval_from_associational by (rewrite ?nout_2 in *; auto).
        f_equal.
        rewrite !eval_carries, !Associational.bind_snd_correct, !Associational.eval_rev by auto.
        reflexivity. } Unfocus.
      subst widemul_inlined_reverse; reflexivity.
    Qed.
  End widemul.
End BaseConversion.

Module Import MOVEME.
  Fixpoint fold_andb_map {A B} (f : A -> B -> bool) (ls1 : list A) (ls2 : list B)
  : bool
    := match ls1, ls2 with
       | nil, nil => true
       | nil, _ => false
       | cons x xs, cons y ys => andb (f x y) (@fold_andb_map A B f xs ys)
       | cons _ _, _ => false
       end.
  Lemma fold_andb_map_map {A B C} f g ls1 ls2
    : @fold_andb_map A B f ls1 (@List.map C _ g ls2)
      = fold_andb_map (fun a b => f a (g b)) ls1 ls2.
  Proof using Type. revert ls1 ls2; induction ls1, ls2; cbn; congruence. Qed.

  Lemma fold_andb_map_length A B f ls1 ls2
        (H : @fold_andb_map A B f ls1 ls2 = true)
    : length ls1 = length ls2.
  Proof using Type.
    revert ls1 ls2 H; induction ls1, ls2; cbn; intros; Bool.split_andb; f_equal;
      try congruence; auto.
  Qed.
End MOVEME.

Definition expanding_id (n : nat) (ls : list Z) := expand_list (-1)%Z ls n.

Lemma expanding_id_id n ls (H : List.length ls = n)
  : expanding_id n ls = ls.
Proof using Type.
  unfold expanding_id. rewrite expand_list_correct by assumption; reflexivity.
Qed.

Module Ring.
  Local Notation is_bounded_by0 r v
    := ((lower r <=? v) && (v <=? upper r)).
  Local Notation is_bounded_by0o r
    := (match r with Some r' => fun v => is_bounded_by0 r' v | None => fun _ => true end).
  Local Notation is_bounded_by bounds ls
    := (fold_andb_map (fun r v => is_bounded_by0o r v) bounds ls).
  Local Notation is_bounded_by2 bounds ls
    := (let '(a, b) := ls in andb (is_bounded_by bounds a) (is_bounded_by bounds b)).

  Lemma length_is_bounded_by bounds ls
    : is_bounded_by bounds ls = true -> length ls = length bounds.
  Proof using Type.
    intro H.
    apply fold_andb_map_length in H; congruence.
  Qed.

  Section ring_goal.
    Context (limbwidth_num limbwidth_den : Z)
            (n : nat)
            (s : Z)
            (c : list (Z * Z))
            (tight_bounds : list (option zrange))
            (length_tight_bounds : length tight_bounds = n)
            (loose_bounds : list (option zrange))
            (length_loose_bounds : length loose_bounds = n).
    Local Notation weight := (weight limbwidth_num limbwidth_den).
    Local Notation eval := (Positional.eval weight n).
    Let prime_bound : zrange
      := r[0~>(s - Associational.eval c - 1)]%zrange.
    Let m := Z.to_pos (s - Associational.eval c).
    Context (m_eq : Z.pos m = s - Associational.eval c)
            (sc_pos : 0 < s - Associational.eval c)
            (Interp_rrelaxv : list Z -> list Z)
            (HInterp_rrelaxv : forall arg,
                is_bounded_by tight_bounds arg = true
                -> is_bounded_by loose_bounds (Interp_rrelaxv arg) = true
                   /\ Interp_rrelaxv arg = expanding_id n arg)
            (carry_mulmod : list Z -> list Z -> list Z)
            (Hcarry_mulmod
             : forall f g,
                length f = n -> length g = n ->
                (eval (carry_mulmod f g)) mod (s - Associational.eval c)
                = (eval f * eval g) mod (s - Associational.eval c))
            (Interp_rcarry_mulv : list Z * list Z -> list Z)
            (HInterp_rcarry_mulv : forall arg,
                is_bounded_by2 loose_bounds arg = true
                -> is_bounded_by tight_bounds (Interp_rcarry_mulv arg) = true
                   /\ Interp_rcarry_mulv arg = carry_mulmod (fst arg) (snd arg))
            (carrymod : list Z -> list Z)
            (Hcarrymod
             : forall f,
                length f = n ->
                (eval (carrymod f)) mod (s - Associational.eval c)
                = (eval f) mod (s - Associational.eval c))
            (Interp_rcarryv : list Z -> list Z)
            (HInterp_rcarryv : forall arg,
                is_bounded_by loose_bounds arg = true
                -> is_bounded_by tight_bounds (Interp_rcarryv arg) = true
                   /\ Interp_rcarryv arg = carrymod arg)
            (addmod : list Z -> list Z -> list Z)
            (Haddmod
             : forall f g,
                length f = n -> length g = n ->
                (eval (addmod f g)) mod (s - Associational.eval c)
                = (eval f + eval g) mod (s - Associational.eval c))
            (Interp_raddv : list Z * list Z -> list Z)
            (HInterp_raddv : forall arg,
                is_bounded_by2 tight_bounds arg = true
                -> is_bounded_by loose_bounds (Interp_raddv arg) = true
                   /\ Interp_raddv arg = addmod (fst arg) (snd arg))
            (submod : list Z -> list Z -> list Z)
            (Hsubmod
             : forall f g,
                length f = n -> length g = n ->
                (eval (submod f g)) mod (s - Associational.eval c)
                = (eval f - eval g) mod (s - Associational.eval c))
            (Interp_rsubv : list Z * list Z -> list Z)
            (HInterp_rsubv : forall arg,
                is_bounded_by2 tight_bounds arg = true
                -> is_bounded_by loose_bounds (Interp_rsubv arg) = true
                   /\ Interp_rsubv arg = submod (fst arg) (snd arg))
            (oppmod : list Z -> list Z)
            (Hoppmod
             : forall f,
                length f = n ->
                (eval (oppmod f)) mod (s - Associational.eval c)
                = (- eval f) mod (s - Associational.eval c))
            (Interp_roppv : list Z -> list Z)
            (HInterp_roppv : forall arg,
                is_bounded_by tight_bounds arg = true
                -> is_bounded_by loose_bounds (Interp_roppv arg) = true
                   /\ Interp_roppv arg = oppmod arg)
            (zeromod : list Z)
            (Hzeromod
             : (eval zeromod) mod (s - Associational.eval c)
                = 0 mod (s - Associational.eval c))
            (Interp_rzerov : list Z)
            (HInterp_rzerov : is_bounded_by tight_bounds Interp_rzerov = true
                              /\ Interp_rzerov = zeromod)
            (onemod : list Z)
            (Honemod
             : (eval onemod) mod (s - Associational.eval c)
                = 1 mod (s - Associational.eval c))
            (Interp_ronev : list Z)
            (HInterp_ronev : is_bounded_by tight_bounds Interp_ronev = true
                              /\ Interp_ronev = onemod)
            (encodemod : Z -> list Z)
            (Hencodemod
             : forall f,
                (eval (encodemod f)) mod (s - Associational.eval c)
                = f mod (s - Associational.eval c))
            (Interp_rencodev : Z -> list Z)
            (HInterp_rencodev : forall arg,
                is_bounded_by0 prime_bound arg = true
                -> is_bounded_by tight_bounds (Interp_rencodev arg) = true
                   /\ Interp_rencodev arg = encodemod arg).

    Local Notation T := (list Z) (only parsing).
    Local Notation encoded_ok ls
      := (is_bounded_by tight_bounds ls = true) (only parsing).
    Local Notation encoded_okf := (fun ls => encoded_ok ls) (only parsing).

    Definition Fdecode (v : T) : F m
      := F.of_Z m (Positional.eval weight n v).
    Definition T_eq (x y : T)
      := Fdecode x = Fdecode y.

    Definition encodedT := sig encoded_okf.

    Definition ring_mul (x y : T) : T
      := Interp_rcarry_mulv (Interp_rrelaxv x, Interp_rrelaxv y).
    Definition ring_add (x y : T) : T := Interp_rcarryv (Interp_raddv (x, y)).
    Definition ring_sub (x y : T) : T := Interp_rcarryv (Interp_rsubv (x, y)).
    Definition ring_opp (x : T) : T := Interp_rcarryv (Interp_roppv x).
    Definition ring_encode (x : F m) : T := Interp_rencodev (F.to_Z x).

    Definition GoodT : Prop
      := @subsetoid_ring
           (list Z) encoded_okf T_eq
           Interp_rzerov Interp_ronev ring_opp ring_add ring_sub ring_mul
         /\ @is_subsetoid_homomorphism
              (F m) (fun _ => True) eq 1%F F.add F.mul
              (list Z) encoded_okf T_eq Interp_ronev ring_add ring_mul ring_encode
         /\ @is_subsetoid_homomorphism
              (list Z) encoded_okf T_eq Interp_ronev ring_add ring_mul
              (F m) (fun _ => True) eq 1%F F.add F.mul
              Fdecode.

    Hint Rewrite ->@F.to_Z_add : push_FtoZ.
    Hint Rewrite ->@F.to_Z_mul : push_FtoZ.
    Hint Rewrite ->@F.to_Z_opp : push_FtoZ.
    Hint Rewrite ->@F.to_Z_of_Z : push_FtoZ.

    Lemma Fm_bounded_alt (x : F m)
      : (0 <=? F.to_Z x) && (F.to_Z x <=? Z.pos m - 1) = true.
    Proof using m_eq.
      clear -m_eq.
      destruct x as [x H]; cbn [F.to_Z proj1_sig].
      pose proof (Z.mod_pos_bound x (Z.pos m)).
      rewrite andb_true_iff; split; Z.ltb_to_lt; lia.
    Qed.

    Lemma Good : GoodT.
    Proof using HInterp_raddv HInterp_rcarry_mulv HInterp_rcarryv HInterp_rencodev HInterp_ronev HInterp_roppv HInterp_rrelaxv HInterp_rsubv HInterp_rzerov Haddmod Hcarry_mulmod Hcarrymod Hencodemod Honemod Hoppmod Hsubmod Hzeromod length_loose_bounds length_tight_bounds m_eq.
      split_and; simpl in *.
      eapply subsetoid_ring_by_ring_isomorphism;
        cbv [ring_opp ring_add ring_sub ring_mul ring_encode F.sub] in *;
        repeat match goal with
               | _ => solve [ auto using andb_true_intro, conj with nocore ]
               | _ => progress intros
               | _ => progress cbn [fst snd]
               | [ H : _ |- is_bounded_by _ _ = true ] => apply H
               | [ |- _ <-> _ ] => reflexivity
               | [ |- _ = _ :> Z ] => first [ reflexivity | rewrite <- m_eq; reflexivity ]
               | [ H : context[?x] |- Fdecode ?x = _ ] => rewrite H
               | [ H : context[?x _] |- Fdecode (?x _) = _ ] => rewrite H
               | [ H : context[?x _ _] |- Fdecode (?x _ _) = _ ] => rewrite H
               | _ => progress cbv [Fdecode]
               | [ |- _ = _ :> F _ ] => apply F.eq_to_Z_iff
               | _ => progress autorewrite with push_FtoZ
               | _ => rewrite m_eq
               | [ H : context[?x _ _] |- context[eval (?x _ _)] ] => rewrite H
               | [ H : context[?x _] |- context[eval (?x _)] ] => rewrite H
               | [ H : context[?x] |- context[eval ?x] ] => rewrite H
               | [ |- context[List.length ?x] ]
                 => erewrite (length_is_bounded_by _ x)
                   by eauto using andb_true_intro, conj with nocore
               | [ |- _ = _ :> Z ]
                 => push_Zmod; reflexivity
               | _ => pull_Zmod; rewrite Z.add_opp_r
               | _ => rewrite expanding_id_id
               | [ |- context[F.to_Z _ mod (_ - _)] ]
                 => rewrite <- m_eq, F.mod_to_Z
               | _ => rewrite <- m_eq; apply Fm_bounded_alt
               end.
    Qed.
  End ring_goal.
End Ring.

Module Compilers.
  Module type.
    Variant primitive := unit | Z | nat | bool.
    Inductive type := type_primitive (_:primitive) | prod (A B : type) | arrow (s d : type) | list (A : type).
    Module Export Coercions.
      Global Coercion type_primitive : primitive >-> type.
    End Coercions.

    (** Denote [type]s into their interpretation in [Type]/[Set] *)
    Fixpoint interp (t : type)
      := match t with
         | unit => Datatypes.unit
         | prod A B => interp A * interp B
         | arrow A B => interp A -> interp B
         | list A => Datatypes.list (interp A)
         | nat => Datatypes.nat
         | type_primitive Z => BinInt.Z
         | bool => Datatypes.bool
         end%type.

    Fixpoint final_codomain (t : type) : type
      := match t with
         | type_primitive _ as t
         | prod _ _ as t
         | list _ as t
           => t
         | arrow s d => final_codomain d
         end.

    Definition domain (t : type) : type
      := match t with
         | arrow s d => s
         | _ => type_primitive unit
         end.

    Definition codomain (t : type) : type
      := match t with
         | arrow s d => d
         | t => t
         end.

    Fixpoint try_transport (P : type -> Type) (t1 t2 : type) : P t1 -> option (P t2)
      := match t1, t2 return P t1 -> option (P t2) with
         | unit, unit
         | Z, Z
         | nat, nat
         | bool, bool
           => @Some _
         | prod A B, prod A' B'
           => fun v
              => (v <- try_transport (fun A => P (prod A B)) A A' v;
                    try_transport (fun B => P (prod A' B)) B B' v)%option
         | arrow s d, arrow s' d'
           => fun v
              => (v <- try_transport (fun s => P (arrow s d)) s s' v;
                    try_transport (fun d => P (arrow s' d)) d d' v)%option
         | list A, list A'
           => @try_transport (fun A => P (list A)) A A'
         | unit, _
         | Z, _
         | nat, _
         | bool, _
         | prod _ _, _
         | arrow _ _, _
         | list _, _
           => fun _ => None
         end.

    Ltac reify_primitive ty :=
      lazymatch eval cbv beta in ty with
      | Datatypes.unit => unit
      | Datatypes.nat => nat
      | Datatypes.bool => bool
      | BinInt.Z => Z
      | ?ty => let dummy := match goal with
                            | _ => fail 1 "Unrecognized type:" ty
                            end in
               constr:(I : I)
      end.

    Ltac reify ty :=
      lazymatch eval cbv beta in ty with
      | Datatypes.prod ?A ?B
        => let rA := reify A in
           let rB := reify B in
           constr:(prod rA rB)
      | ?A -> ?B
        => let rA := reify A in
           let rB := reify B in
           constr:(arrow rA rB)
      | Datatypes.list ?T
        => let rT := reify T in
           constr:(list rT)
      | type.interp ?T => T
      | _ => let rt := reify_primitive ty in
             constr:(type_primitive rt)
      end.

    Notation reify t := (ltac:(let rt := reify t in exact rt)) (only parsing).
    Notation reify_type_of e := (reify ((fun t (_ : t) => t) _ e)) (only parsing).

    Module Export Notations.
      Export Coercions.
      Delimit Scope ctype_scope with ctype.
      Bind Scope ctype_scope with type.
      Notation "()" := unit : ctype_scope.
      Notation "A * B" := (prod A B) : ctype_scope.
      Notation "A -> B" := (arrow A B) : ctype_scope.
      Notation type := type.
    End Notations.
  End type.
  Export type.Notations.

  Module Uncurried.
    Module expr.
      Inductive expr {ident : type -> type -> Type} {var : type -> Type} : type -> Type :=
      | Var {t} (v : var t) : expr t
      | TT : expr type.unit
      | AppIdent {s d} (idc : ident s d) (args : expr s) : expr d
      | App {s d} (f : expr (s -> d)) (x : expr s) : expr d
      | Pair {A B} (a : expr A) (b : expr B) : expr (A * B)
      | Abs {s d} (f : var s -> expr d) : expr (s -> d).

      Definition Expr {ident : type -> type -> Type} t := forall var, @expr ident var t.

      Definition APP {ident s d} (f : Expr (s -> d)) (x : Expr s) : Expr d
        := fun var => @App ident var s d (f var) (x var).

      Module Export Notations.
        Bind Scope expr_scope with expr.
        Delimit Scope expr_scope with expr.
        Bind Scope Expr_scope with Expr.
        Delimit Scope Expr_scope with Expr.

        Infix "@" := App : expr_scope.
        Infix "@" := APP : Expr_scope.
        Infix "@@" := AppIdent : expr_scope.
        Notation "( x , y , .. , z )" := (Pair .. (Pair x%expr y%expr) .. z%expr) : expr_scope.
        Notation "( )" := TT : expr_scope.
        Notation "()" := TT : expr_scope.
        Notation "'λ'  x .. y , t" := (Abs (fun x => .. (Abs (fun y => t%expr)) ..)) : expr_scope.
      End Notations.

      Section unexpr.
        Context {ident : type -> type -> Type}
                {var : type -> Type}.

        Fixpoint unexpr {t} (e : @expr ident (@expr ident var) t) : @expr ident var t
          := match e in expr t return expr t with
             | Var t v => v
             | TT => TT
             | AppIdent s d idc args => AppIdent idc (unexpr args)
             | App s d f x => App (unexpr f) (unexpr x)
             | Pair A B a b => Pair (unexpr a) (unexpr b)
             | Abs s d f => Abs (fun x => unexpr (f (Var x)))
             end.
      End unexpr.

      Section with_ident.
        Context {ident : type -> type -> Type}
                (interp_ident : forall s d, ident s d -> type.interp s -> type.interp d).

        (** Denote expressions *)
        Fixpoint interp {t} (e : @expr ident type.interp t) : type.interp t
          := match e with
             | Var t v => v
             | TT => tt
             | AppIdent s d idc args => interp_ident s d idc (@interp s args)
             | App s d f x => @interp _ f (@interp _ x)
             | Pair A B a b => (@interp A a, @interp B b)
             | Abs s d f => fun v => interp (f v)
             end.

        Definition Interp {t} (e : Expr t) := interp (e _).

        (** [Interp (APP _ _)] is the same thing as Gallina
            application of the [Interp]retations of the two arguments
            to [APP]. *)
        Definition Interp_APP {s d} (f : @Expr ident (s -> d)) (x : @Expr ident s)
          : Interp (f @ x)%Expr = Interp f (Interp x)
          := eq_refl.

        (** Same as [Interp_APP], but for any reflexive relation, not
            just [eq] *)
        Definition Interp_APP_rel_reflexive {s d} {R} {H:Reflexive R}
                   (f : @Expr ident (s -> d)) (x : @Expr ident s)
          : R (Interp (f @ x)%Expr) (Interp f (Interp x))
          := H _.
      End with_ident.

      Ltac require_primitive_const term :=
        lazymatch term with
        | S ?n => require_primitive_const n
        | O => idtac
        | true => idtac
        | false => idtac
        | tt => idtac
        | Z0 => idtac
        | Zpos ?p => require_primitive_const p
        | Zneg ?p => require_primitive_const p
        | xI ?p => require_primitive_const p
        | xO ?p => require_primitive_const p
        | xH => idtac
        | ?term => fail 0 "Not a known const:" term
        end.
      Ltac is_primitive_const term :=
        match constr:(Set) with
        | _ => let check := match goal with
                            | _ => require_primitive_const term
                            end in
               true
        | _ => false
        end.

      Module var_context.
        Inductive list {var : type -> Type} :=
        | nil
        | cons {t} (gallina_v : type.interp t) (v : var t) (ctx : list).
      End var_context.

      (* cf COQBUG(https://github.com/coq/coq/issues/5448) , COQBUG(https://github.com/coq/coq/issues/6315) , COQBUG(https://github.com/coq/coq/issues/6559) , COQBUG(https://github.com/coq/coq/issues/6534) , https://github.com/mit-plv/fiat-crypto/issues/320 *)
      Ltac require_same_var n1 n2 :=
        (*idtac n1 n2;*)
        let c1 := constr:(fun n1 n2 : Set => ltac:(exact n1)) in
        let c2 := constr:(fun n1 n2 : Set => ltac:(exact n2)) in
        (*idtac c1 c2;*)
        first [ constr_eq c1 c2 | fail 1 "Not the same var:" n1 "and" n2 "(via constr_eq" c1 c2 ")" ].
      Ltac is_same_var n1 n2 :=
        match goal with
        | _ => let check := match goal with _ => require_same_var n1 n2 end in
               true
        | _ => false
        end.
      Ltac is_underscore v :=
        let v' := fresh v in
        let v' := fresh v' in
        is_same_var v v'.
      Ltac refresh n fresh_tac :=
        let n_is_underscore := is_underscore n in
        let n' := lazymatch n_is_underscore with
                  | true => fresh
                  | false => fresh_tac n
                  end in
        let n' := fresh_tac n' in
        n'.

      Ltac type_of_first_argument_of f :=
        let f_ty := type of f in
        lazymatch eval hnf in f_ty with
        | forall x : ?T, _ => T
        end.

      (** Forms of abstraction in Gallina that our reflective language
      cannot handle get handled by specializing the code "template" to
      each particular application of that abstraction. In particular,
      type arguments (nat, Z, (λ _, nat), etc) get substituted into
      lambdas and treated as a integral part of primitive operations
      (such as [@List.app T], [@list_rect (λ _, nat)]).  During
      reification, we accumulate them in a right-associated tuple,
      using [tt] as the "nil" base case.  When we hit a λ or an
      identifier, we plug in the template parameters as necessary. *)
      Ltac require_template_parameter parameter_type :=
        first [ unify parameter_type Prop
              | unify parameter_type Set
              | unify parameter_type Type
              | lazymatch eval hnf in parameter_type with
                | forall x : ?T, @?P x
                  => let check := constr:(fun x : T
                                          => ltac:(require_template_parameter (P x);
                                                   exact I)) in
                     idtac
                end ].
      Ltac is_template_parameter parameter_type :=
        is_success_run_tactic ltac:(fun _ => require_template_parameter parameter_type).
      Ltac plug_template_ctx f template_ctx :=
        lazymatch template_ctx with
        | tt => f
        | (?arg, ?template_ctx')
          =>
          let T := type_of_first_argument_of f in
          let x_is_template_parameter := is_template_parameter T in
          lazymatch x_is_template_parameter with
          | true
            => plug_template_ctx (f arg) template_ctx'
          | false
            => constr:(fun x : T
                       => ltac:(let v := plug_template_ctx (f x) template_ctx in
                                exact v))
          end
        end.

      Ltac reify_in_context ident reify_ident var term value_ctx template_ctx :=
        let reify_rec_gen term value_ctx template_ctx := reify_in_context ident reify_ident var term value_ctx template_ctx in
        let reify_rec term := reify_rec_gen term value_ctx template_ctx in
        let reify_rec_not_head term := reify_rec_gen term value_ctx tt in
        let mkAppIdent idc args
            := let rargs := reify_rec_not_head args in
               constr:(@AppIdent ident var _ _ idc rargs) in
        let do_reify_ident term else_tac
            := let term_is_primitive_const := is_primitive_const term in
               reify_ident
                 mkAppIdent
                 term_is_primitive_const
                 term
                 else_tac in
        (*let dummy := match goal with _ => idtac "reify_in_context: attempting to reify:" term end in*)
        lazymatch value_ctx with
        | context[@var_context.cons _ ?rT term ?v _]
          => constr:(@Var ident var rT v)
        | _
          =>
          lazymatch term with
          | match ?b with true => ?t | false => ?f end
            => let T := type of t in
               reify_rec (@bool_rect (fun _ => T) t f b)
          | match ?x with Datatypes.pair a b => ?f end
            => reify_rec (match Datatypes.fst x, Datatypes.snd x return _ with
                          | a, b => f
                          end)
          | match ?x with nil => ?N | cons a b => @?C a b end
            => let T := type of term in
               reify_rec (@list_case _ (fun _ => T) N C x)
          | let x := ?a in @?b x
            => let A := type of a in
               let B := lazymatch type of b with forall x, @?B x => B end in
               reify_rec (b a) (*(@Let_In A B a b)*)
          | Datatypes.pair ?x ?y
            => let rx := reify_rec x in
               let ry := reify_rec y in
               constr:(Pair (ident:=ident) (var:=var) rx ry)
          | tt
            => constr:(@TT ident var)
          | (fun x : ?T => ?f)
            =>
            let x_is_template_parameter := is_template_parameter T in
            lazymatch x_is_template_parameter with
            | true
              =>
              lazymatch template_ctx with
              | (?arg, ?template_ctx)
                => (* we pull a trick with [match] to plug in [arg] without running cbv β *)
                lazymatch type of term with
                | forall y, ?P
                  => reify_rec_gen (match arg as y return P with x => f end) value_ctx template_ctx
                end
              end
            | false
              =>
              let rT := type.reify T in
              let not_x := fresh (* could be [refresh x ltac:(fun n => fresh n)] in 8.8; c.f. https://github.com/mit-plv/fiat-crypto/issues/320 and probably COQBUG(https://github.com/coq/coq/issues/6534) *) in
              let not_x2 := fresh (* could be [refresh not_x ltac:(fun n => fresh n)] in 8.8; c.f. https://github.com/mit-plv/fiat-crypto/issues/320 and probably COQBUG(https://github.com/coq/coq/issues/6534) *) in
              let not_x3 := fresh (* could be [refresh not_x2 ltac:(fun n => fresh n)] in 8.8; c.f. https://github.com/mit-plv/fiat-crypto/issues/320 and probably COQBUG(https://github.com/coq/coq/issues/6534) *) in
              (*let dummy := match goal with _ => idtac "reify_in_context: λ case:" term "using vars:" not_x not_x2 not_x3 end in*)
              let rf0 :=
                  constr:(
                    fun (x : T) (not_x : var rT)
                    => match f, @var_context.cons var rT x not_x value_ctx return _ with (* c.f. COQBUG(https://github.com/coq/coq/issues/6252#issuecomment-347041995) for [return _] *)
                       | not_x2, not_x3
                         => ltac:(
                              let f := (eval cbv delta [not_x2] in not_x2) in
                              let var_ctx := (eval cbv delta [not_x3] in not_x3) in
                              (*idtac "rec call" f "was" term;*)
                              let rf := reify_rec_gen f var_ctx template_ctx in
                              exact rf)
                       end) in
              lazymatch rf0 with
              | (fun _ => ?rf)
                => constr:(@Abs ident var rT _ rf)
              | _
                => (* This will happen if the reified term still
              mentions the non-var variable.  By chance, [cbv delta]
              strips type casts, which are only places that I can
              think of where such dependency might remain.  However,
              if this does come up, having a distinctive error message
              is much more useful for debugging than the generic "no
              matching clause" *)
                let dummy := match goal with
                             | _ => fail 1 "Failure to eliminate functional dependencies of" rf0
                             end in
                constr:(I : I)
              end
            end
          | _
            =>
            do_reify_ident
              term
              ltac:(
              fun _
              =>
                lazymatch term with
                | ?f ?x
                  =>
                  let ty := type_of_first_argument_of f in
                  let x_is_template_parameter := is_template_parameter ty in
                  lazymatch x_is_template_parameter with
                  | true
                    => (* we can't reify things of type [Type], so we save it for later to plug in *)
                    reify_rec_gen f value_ctx (x, template_ctx)
                  | false
                    => let rx := reify_rec_gen x value_ctx tt in
                       let rf := reify_rec_gen f value_ctx template_ctx in
                       constr:(App (ident:=ident) (var:=var) rf rx)
                  end
                | _
                  => let term' := plug_template_ctx term template_ctx in
                     do_reify_ident
                       term'
                       ltac:(fun _
                             =>
                               (*let __ := match goal with _ => idtac "Attempting to unfold" term end in*)
                               let term
                                   := match constr:(Set) with
                                      | _ => (eval cbv delta [term] in term) (* might fail, so we wrap it in a match to give better error messages *)
                                      | _
                                        => let dummy := match goal with
                                                        | _ => fail 2 "Unrecognized term:" term'
                                                        end in
                                           constr:(I : I)
                                      end in
                               reify_rec term)
                end)
          end
        end.
      Ltac reify ident reify_ident var term :=
        reify_in_context ident reify_ident var term (@var_context.nil var) tt.
      Ltac Reify ident reify_ident term :=
        constr:(fun var : type -> Type
                => ltac:(let r := reify ident reify_ident var term in
                         exact r)).
      Ltac Reify_rhs ident reify_ident interp_ident _ :=
        let RHS := lazymatch goal with |- _ = ?RHS => RHS end in
        let R := Reify ident reify_ident RHS in
        transitivity (@Interp ident interp_ident _ R);
        [ | cbv beta iota delta [Interp interp interp_ident Let_In type.interp bool_rect];
            reflexivity ].

      Module for_reification.
        Module ident.
          Import type.
          Inductive ident : type -> type -> Set :=
          | primitive {t:type.primitive} (v : interp t) : ident () t
          | Let_In {tx tC} : ident (tx * (tx -> tC)) tC
          | Nat_succ : ident nat nat
          | Nat_max : ident (nat * nat) nat
          | Nat_mul : ident (nat * nat) nat
          | Nat_add : ident (nat * nat) nat
          | Nat_sub : ident (nat * nat) nat
          | nil {t} : ident () (list t)
          | cons {t} : ident (t * list t) (list t)
          | fst {A B} : ident (A * B) A
          | snd {A B} : ident (A * B) B
          | bool_rect {T} : ident ((unit -> T) * (unit -> T) * bool) T
          | nat_rect {P} : ident ((unit -> P) * (nat * P -> P) * nat) P
          | list_rect {A P} : ident ((unit -> P) * (A * list A * P -> P) * list A) P
          | list_case {A P} : ident ((unit -> P) * (A * list A -> P) * list A) P
          | pred : ident nat nat
          | List_length {T} : ident (list T) nat
          | List_seq : ident (nat * nat) (list nat)
          | List_repeat {A} : ident (A * nat) (list A)
          | List_combine {A B} : ident (list A * list B) (list (A * B))
          | List_map {A B} : ident ((A -> B) * list A) (list B)
          | List_flat_map {A B} : ident ((A -> list B) * list A) (list B)
          | List_partition {A} : ident ((A -> bool) * list A) (list A * list A)
          | List_app {A} : ident (list A * list A) (list A)
          | List_rev {A} : ident (list A) (list A)
          | List_fold_right {A B} : ident ((B * A -> A) * A * list B) A
          | List_update_nth {T} : ident (nat * (T -> T) * list T) (list T)
          | List_nth_default {T} : ident (T * list T * nat) T
          | Z_add : ident (Z * Z) Z
          | Z_mul : ident (Z * Z) Z
          | Z_pow : ident (Z * Z) Z
          | Z_sub : ident (Z * Z) Z
          | Z_opp : ident Z Z
          | Z_div : ident (Z * Z) Z
          | Z_modulo : ident (Z * Z) Z
          | Z_eqb : ident (Z * Z) bool
          | Z_leb : ident (Z * Z) bool
          | Z_of_nat : ident nat Z
          | Z_mul_split : ident (Z * Z * Z) (Z * Z)
          | Z_add_get_carry : ident (Z * Z * Z) (Z * Z)
          | Z_add_with_carry : ident (Z * Z * Z) Z
          | Z_add_with_get_carry : ident (Z * Z * Z * Z) (Z * Z)
          | Z_sub_get_borrow : ident (Z * Z * Z) (Z * Z)
          | Z_sub_with_get_borrow : ident (Z * Z * Z * Z) (Z * Z)
          | Z_zselect : ident (Z * Z * Z) Z
          | Z_add_modulo : ident (Z * Z * Z) Z
          | Z_rshi : ident (Z * Z * Z * Z) Z
          | Z_cc_m : ident (Z * Z) Z
          .

          Notation curry0 f
            := (fun 'tt => f).
          Notation curry2 f
            := (fun '(a, b) => f a b).
          Notation curry3 f
            := (fun '(a, b, c) => f a b c).
          Notation curry4 f
            := (fun '(a, b, c, d) => f a b c d).
          Notation uncurry2 f
            := (fun a b => f (a, b)).
          Notation uncurry3 f
            := (fun a b c => f (a, b, c)).
          Notation curry3_1 f
            := (fun '(a, b, c) => f (uncurry2 a) b c).
          Notation curry3_2 f
            := (fun '(a, b, c) => f a (uncurry2 b) c).
          Notation curry3_3 f
            := (fun '(a, b, c) => f a (uncurry3 b) c).

          (** Denote identifiers *)
          Definition interp {s d} (idc : ident s d) : type.interp s -> type.interp d
            := match idc in ident s d return type.interp s -> type.interp d with
               | primitive _ v => curry0 v
               | Let_In tx tC => curry2 (@LetIn.Let_In (type.interp tx) (fun _ => type.interp tC))
               | Nat_succ => Nat.succ
               | Nat_add => curry2 Nat.add
               | Nat_sub => curry2 Nat.sub
               | Nat_mul => curry2 Nat.mul
               | Nat_max => curry2 Nat.max
               | nil t => curry0 (@Datatypes.nil (type.interp t))
               | cons t => curry2 (@Datatypes.cons (type.interp t))
               | fst A B => @Datatypes.fst (type.interp A) (type.interp B)
               | snd A B => @Datatypes.snd (type.interp A) (type.interp B)
               | bool_rect T => curry3 (fun t f => @Datatypes.bool_rect (fun _ => type.interp T) (t tt) (f tt))
               | nat_rect P => curry3_2 (fun O_case => @Datatypes.nat_rect (fun _ => type.interp P) (O_case tt))
               | list_rect A P => curry3_3 (fun N_case => @Datatypes.list_rect (type.interp A) (fun _ => type.interp P) (N_case tt))
               | list_case A P => curry3_2 (fun N_case => @ListUtil.list_case (type.interp A) (fun _ => type.interp P) (N_case tt))
               | pred => Nat.pred
               | List_length T => @List.length (type.interp T)
               | List_seq => curry2 List.seq
               | List_combine A B => curry2 (@List.combine (type.interp A) (type.interp B))
               | List_map A B => curry2 (@List.map (type.interp A) (type.interp B))
               | List_repeat A => curry2 (@repeat (type.interp A))
               | List_flat_map A B => curry2 (@List.flat_map (type.interp A) (type.interp B))
               | List_partition A => curry2 (@List.partition (type.interp A))
               | List_app A => curry2 (@List.app (type.interp A))
               | List_rev A => @List.rev (type.interp A)
               | List_fold_right A B => curry3_1 (@List.fold_right (type.interp A) (type.interp B))
               | List_update_nth T => curry3 (@update_nth (type.interp T))
               | List_nth_default T => curry3 (@List.nth_default (type.interp T))
               | Z_add => curry2 Z.add
               | Z_mul => curry2 Z.mul
               | Z_pow => curry2 Z.pow
               | Z_modulo => curry2 Z.modulo
               | Z_opp => Z.opp
               | Z_sub => curry2 Z.sub
               | Z_div => curry2 Z.div
               | Z_eqb => curry2 Z.eqb
               | Z_leb => curry2 Z.leb
               | Z_of_nat => Z.of_nat
               | Z_mul_split => curry3 Z.mul_split
               | Z_add_get_carry => curry3 Z.add_get_carry_full
               | Z_add_with_carry => curry3 Z.add_with_carry
               | Z_add_with_get_carry => curry4 Z.add_with_get_carry_full
               | Z_sub_get_borrow => curry3 Z.sub_get_borrow_full
               | Z_sub_with_get_borrow => curry4 Z.sub_with_get_borrow_full
               | Z_zselect => curry3 Z.zselect
               | Z_add_modulo => curry3 Z.add_modulo
               | Z_rshi => curry4 Z.rshi
               | Z_cc_m => curry2 Z.cc_m
               end.

          Ltac reify
               mkAppIdent
               term_is_primitive_const
               term
               else_tac :=
            (*let dummy := match goal with _ => idtac "attempting to reify_op" term end in*)
            lazymatch term with
            | Nat.succ ?x => mkAppIdent Nat_succ x
            | Nat.add ?x ?y => mkAppIdent Nat_add (x, y)
            | Nat.sub ?x ?y => mkAppIdent Nat_sub (x, y)
            | Nat.mul ?x ?y => mkAppIdent Nat_mul (x, y)
            | Nat.max ?x ?y => mkAppIdent Nat_max (x, y)
            | S ?x => mkAppIdent Nat_succ x
            | @Datatypes.nil ?T
              => let rT := type.reify T in
                 mkAppIdent (@ident.nil rT) tt
            | @Datatypes.cons ?T ?x ?xs
              => let rT := type.reify T in
                 mkAppIdent (@ident.cons rT) (x, xs)
            | @Datatypes.fst ?A ?B ?x
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.fst rA rB) x
            | @Datatypes.snd ?A ?B ?x
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.snd rA rB) x
            | @Datatypes.bool_rect (fun _ => ?T) ?Ptrue ?Pfalse ?b
              => let rT := type.reify T in
                 mkAppIdent (@ident.bool_rect rT)
                            ((fun _ : Datatypes.unit => Ptrue), (fun _ : Datatypes.unit => Pfalse), b)
            | @Datatypes.nat_rect (fun _ => ?T) ?P0 (fun (n' : Datatypes.nat) Pn => ?PS) ?n
              => let rT := type.reify T in
                 let pat := fresh "pat" in (* fresh for COQBUG(https://github.com/coq/coq/issues/6562) *)
                 mkAppIdent (@ident.nat_rect rT) ((fun _ : Datatypes.unit => P0),
                                                  (fun pat : Datatypes.nat * T
                                                   => let '(n', Pn) := pat in PS),
                                                  n)
            | @Datatypes.nat_rect (fun _ => ?T) ?P0 ?PS ?n
              => let dummy := match goal with _ => fail 1 "nat_rect successor case is not syntactically a function of two arguments:" PS end in
                 constr:(I : I)
            | @Datatypes.list_rect ?A (fun _ => ?T) ?Pnil (fun a tl Ptl => ?PS) ?ls
              => let rA := type.reify A in
                 let rT := type.reify T in
                 let pat := fresh "pat" in (* fresh for COQBUG(https://github.com/coq/coq/issues/6562) *)
                 mkAppIdent (@ident.list_rect rA rT)
                            ((fun _ : Datatypes.unit => Pnil),
                             (fun pat : A * Datatypes.list A * T
                              => let '(a, tl, Ptl) := pat in PS),
                             ls)
            | @Datatypes.list_rect ?A (fun _ => ?T) ?Pnil ?PS ?ls
              => let dummy := match goal with _ => fail 1 "list_rect successor case is not syntactically a function of three arguments:" PS end in
                 constr:(I : I)
            | @ListUtil.list_case ?A (fun _ => ?T) ?Pnil (fun a tl => ?PS) ?ls
              => let rA := type.reify A in
                 let rT := type.reify T in
                 let pat := fresh "pat" in (* fresh for COQBUG(https://github.com/coq/coq/issues/6562) *)
                 mkAppIdent (@ident.list_case rA rT)
                            ((fun _ : Datatypes.unit => Pnil),
                             (fun pat : A * Datatypes.list A
                              => let '(a, tl) := pat in PS),
                             ls)
            | @ListUtil.list_case ?A (fun _ => ?T) ?Pnil ?PS ?ls
              => let dummy := match goal with _ => fail 1 "list_case successor case is not syntactically a function of two arguments:" PS end in
                 constr:(I : I)
            | Nat.pred ?x => mkAppIdent ident.pred x
            | @List.length ?A ?x =>
              let rA := type.reify A in
              mkAppIdent (@ident.List_length rA) x
            | List.seq ?x ?y  => mkAppIdent ident.List_seq (x, y)
            | @repeat ?A ?x ?y
              => let rA := type.reify A in
                 mkAppIdent (@ident.List_repeat rA) (x, y)
            | @LetIn.Let_In ?A (fun _ => ?B) ?x ?f
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.Let_In rA rB) (x, f)
            | @LetIn.Let_In ?A ?B ?x ?f
              => let dummy := match goal with _ => fail 1 "Let_In contains a dependent type λ as its second argument:" B end in
                 constr:(I : I)
            | @combine ?A ?B ?ls1 ?ls2
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.List_combine rA rB) (ls1, ls2)
            | @List.map ?A ?B ?f ?ls
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.List_map rA rB) (f, ls)
            | @List.flat_map ?A ?B ?f ?ls
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.List_flat_map rA rB) (f, ls)
            | @List.partition ?A ?f ?ls
              => let rA := type.reify A in
                 mkAppIdent (@ident.List_partition rA) (f, ls)
            | @List.app ?A ?ls1 ?ls2
              => let rA := type.reify A in
                 mkAppIdent (@ident.List_app rA) (ls1, ls2)
            | @List.rev ?A ?ls
              => let rA := type.reify A in
                 mkAppIdent (@ident.List_rev rA) ls
            | @List.fold_right ?A ?B (fun b a => ?f) ?a0 ?ls
              => let rA := type.reify A in
                 let rB := type.reify B in
                 let pat := fresh "pat" in (* fresh for COQBUG(https://github.com/coq/coq/issues/6562) *)
                 mkAppIdent (@ident.List_fold_right rA rB) ((fun pat : B * A => let '(b, a) := pat in f), a0, ls)
            | @List.fold_right ?A ?B ?f ?a0 ?ls
              => let dummy := match goal with _ => fail 1 "List.fold_right function argument is not syntactically a function of two arguments:" f end in
                 constr:(I : I)
            | @update_nth ?T ?n ?f ?ls
              => let rT := type.reify T in
                 mkAppIdent (@ident.List_update_nth rT) (n, f, ls)
            | @List.nth_default ?T ?d ?ls ?n
              => let rT := type.reify T in
                 mkAppIdent (@ident.List_nth_default rT) (d, ls, n)
            | Z.add ?x ?y => mkAppIdent ident.Z_add (x, y)
            | Z.mul ?x ?y => mkAppIdent ident.Z_mul (x, y)
            | Z.pow ?x ?y => mkAppIdent ident.Z_pow (x, y)
            | Z.sub ?x ?y => mkAppIdent ident.Z_sub (x, y)
            | Z.opp ?x => mkAppIdent ident.Z_opp x
            | Z.div ?x ?y => mkAppIdent ident.Z_div (x, y)
            | Z.modulo ?x ?y => mkAppIdent ident.Z_modulo (x, y)
            | Z.eqb ?x ?y => mkAppIdent ident.Z_eqb (x, y)
            | Z.leb ?x ?y => mkAppIdent ident.Z_leb (x, y)
            | Z.of_nat ?x => mkAppIdent ident.Z_of_nat x
            | Z.mul_split ?x ?y ?z => mkAppIdent ident.Z_mul_split (x, y, z)
            | Z.add_get_carry_full ?x ?y ?z => mkAppIdent ident.Z_add_get_carry (x, y, z)
            | Z.add_with_carry ?x ?y ?z => mkAppIdent ident.Z_add_with_carry (x, y, z)
            | Z.add_with_get_carry_full ?x ?y ?z ?a => mkAppIdent ident.Z_add_with_get_carry (x, y, z, a)
            | Z.sub_get_borrow_full ?x ?y ?z => mkAppIdent ident.Z_sub_get_borrow (x, y, z)
            | Z.sub_with_get_borrow_full ?x ?y ?z ?a => mkAppIdent ident.Z_sub_with_get_borrow (x, y, z, a)
            | Z.zselect ?x ?y ?z => mkAppIdent ident.Z_zselect (x, y, z)
            | Z.add_modulo ?x ?y ?z => mkAppIdent ident.Z_add_modulo (x,y,z)
            | Z.rshi ?x ?y ?z ?a => mkAppIdent ident.Z_rshi (x,y,z,a)
            | Z.cc_m ?x ?y => mkAppIdent ident.Z_cc_m (x,y)
            | _
              => lazymatch term_is_primitive_const with
                 | true
                   =>
                   let assert_const := match goal with
                                       | _ => require_primitive_const term
                                       end in
                   let T := type of term in
                   let rT := type.reify_primitive T in
                   mkAppIdent (@ident.primitive rT term) tt
                 | false => else_tac ()
                 end
            end.

          Module List.
            Notation length := List_length.
            Notation seq := List_seq.
            Notation repeat := List_repeat.
            Notation combine := List_combine.
            Notation map := List_map.
            Notation flat_map := List_flat_map.
            Notation partition := List_partition.
            Notation app := List_app.
            Notation rev := List_rev.
            Notation fold_right := List_fold_right.
            Notation update_nth := List_update_nth.
            Notation nth_default := List_nth_default.
          End List.

          Module Z.
            Notation add := Z_add.
            Notation mul := Z_mul.
            Notation pow := Z_pow.
            Notation sub := Z_sub.
            Notation opp := Z_opp.
            Notation div := Z_div.
            Notation modulo := Z_modulo.
            Notation eqb := Z_eqb.
            Notation leb := Z_leb.
            Notation of_nat := Z_of_nat.
            Notation mul_split := Z_mul_split.
            Notation add_get_carry := Z_add_get_carry.
            Notation add_with_carry := Z_add_with_carry.
            Notation add_with_get_carry := Z_add_with_get_carry.
            Notation sub_get_borrow := Z_sub_get_borrow.
            Notation sub_with_get_borrow := Z_sub_with_get_borrow.
            Notation zselect := Z_zselect.
            Notation add_modulo := Z_add_modulo.
            Notation rshi := Z_rshi.
            Notation cc_m := Z_cc_m.
          End Z.

          Module Nat.
            Notation succ := Nat_succ.
            Notation add := Nat_add.
            Notation sub := Nat_sub.
            Notation mul := Nat_mul.
            Notation max := Nat_max.
          End Nat.

          Module Export Notations.
            Notation ident := ident.
          End Notations.
        End ident.

        Module Notations.
          Include ident.Notations.
          Notation expr := (@expr ident).
          Notation Expr := (@Expr ident).
          Notation interp := (@interp ident (@ident.interp)).
          Notation Interp := (@Interp ident (@ident.interp)).

          (*Notation "( x , y , .. , z )" := (Pair .. (Pair x%expr y%expr) .. z%expr) : expr_scope.*)
          Notation "'expr_let' x := A 'in' b" := (AppIdent ident.Let_In (Pair A%expr (Abs (fun x => b%expr)))) : expr_scope.
          Notation "[ ]" := (AppIdent ident.nil _) : expr_scope.
          Notation "x :: xs" := (AppIdent ident.cons (Pair x%expr xs%expr)) : expr_scope.
          Notation "x" := (AppIdent (ident.primitive x) _) (only printing, at level 9) : expr_scope.
          Notation "ls [[ n ]]"
            := (AppIdent ident.List.nth_default (_, ls, AppIdent (ident.primitive n%nat) _)%expr)
               : expr_scope.

          Module Reification.
            Ltac reify var term := expr.reify ident ident.reify var term.
            Ltac Reify term := expr.Reify ident ident.reify term.
            Ltac Reify_rhs _ :=
              expr.Reify_rhs ident ident.reify ident.interp ().
          End Reification.
          Include Reification.
        End Notations.
        Include Notations.
      End for_reification.

      Module Export default.
        Module ident.
          Import type.
          Inductive ident : type -> type -> Set :=
          | primitive {t : type.primitive} (v : interp t) : ident () t
          | Let_In {tx tC} : ident (tx * (tx -> tC)) tC
          | Nat_succ : ident nat nat
          | Nat_add : ident (nat * nat) nat
          | Nat_sub : ident (nat * nat) nat
          | Nat_mul : ident (nat * nat) nat
          | Nat_max : ident (nat * nat) nat
          | nil {t} : ident () (list t)
          | cons {t} : ident (t * list t) (list t)
          | fst {A B} : ident (A * B) A
          | snd {A B} : ident (A * B) B
          | bool_rect {T} : ident ((unit -> T) * (unit -> T) * bool) T
          | nat_rect {P} : ident ((unit -> P) * (nat * P -> P) * nat) P
          | pred : ident nat nat
          | list_rect {A P} : ident ((unit -> P) * (A * list A * P -> P) * list A) P
          | List_nth_default {T} : ident (T * list T * nat) T
          | List_nth_default_concrete {T : type.primitive} (d : interp T) (n : Datatypes.nat) : ident (list T) T
          | Z_shiftr (offset : BinInt.Z) : ident Z Z
          | Z_shiftl (offset : BinInt.Z) : ident Z Z
          | Z_land (mask : BinInt.Z) : ident Z Z
          | Z_add : ident (Z * Z) Z
          | Z_mul : ident (Z * Z) Z
          | Z_pow : ident (Z * Z) Z
          | Z_sub : ident (Z * Z) Z
          | Z_opp : ident Z Z
          | Z_div : ident (Z * Z) Z
          | Z_modulo : ident (Z * Z) Z
          | Z_eqb : ident (Z * Z) bool
          | Z_leb : ident (Z * Z) bool
          | Z_of_nat : ident nat Z
          | Z_mul_split : ident (Z * Z * Z) (Z * Z)
          | Z_mul_split_concrete (s:BinInt.Z) : ident (Z * Z) (Z * Z)
          | Z_add_get_carry : ident (Z * Z * Z) (Z * Z)
          | Z_add_get_carry_concrete (s:BinInt.Z) : ident (Z * Z) (Z * Z)
          | Z_add_with_carry : ident (Z * Z * Z) Z
          | Z_add_with_get_carry : ident (Z * Z * Z * Z) (Z * Z)
          | Z_add_with_get_carry_concrete (s:BinInt.Z) : ident (Z * Z * Z) (Z * Z)
          | Z_sub_get_borrow : ident (Z * Z * Z) (Z * Z)
          | Z_sub_get_borrow_concrete (s:BinInt.Z) : ident (Z * Z) (Z * Z)
          | Z_sub_with_get_borrow : ident (Z * Z * Z * Z) (Z * Z)
          | Z_sub_with_get_borrow_concrete (s:BinInt.Z) : ident (Z * Z * Z) (Z * Z)
          | Z_zselect : ident (Z * Z * Z) Z
          | Z_add_modulo : ident (Z * Z * Z) Z
          | Z_rshi : ident (Z * Z * Z * Z) Z
          | Z_rshi_concrete (s offset:BinInt.Z) : ident (Z * Z) Z
          | Z_cc_m : ident (Z * Z) Z
          | Z_cc_m_concrete (s:BinInt.Z) : ident Z Z
          | Z_cast (range : zrange) : ident Z Z
          | Z_cast2 (range : zrange * zrange) : ident (Z * Z) (Z * Z)
          .

          Notation curry0 f
            := (fun 'tt => f).
          Notation curry2 f
            := (fun '(a, b) => f a b).
          Notation curry3 f
            := (fun '(a, b, c) => f a b c).
          Notation curry4 f
            := (fun '(a, b, c, d) => f a b c d).
          Notation uncurry2 f
            := (fun a b => f (a, b)).
          Notation uncurry3 f
            := (fun a b c => f (a, b, c)).
          Notation curry3_23 f
            := (fun '(a, b, c) => f a (uncurry3 b) c).
          Notation curry3_2 f
            := (fun '(a, b, c) => f a (uncurry2 b) c).

          Section gen.
            Context (cast_outside_of_range : zrange -> BinInt.Z -> BinInt.Z).

            Definition cast (r : zrange) (x : BinInt.Z)
              := if (lower r <=? x) && (x <=? upper r)
                 then x
                 else cast_outside_of_range r x.

            (** Interpret identifiers where the behavior of [Z_cast]
                on a value that does not fit in the range is given by
                a context variable.  (This allows us to treat [Z_cast]
                as "undefined behavior" when the value doesn't fit in
                the range by quantifying over all possible
                interpretations. *)
            Definition gen_interp {s d} (idc : ident s d) : type.interp s -> type.interp d
              := match idc in ident s d return type.interp s -> type.interp d with
                 | primitive _ v => curry0 v
                 | Let_In tx tC => curry2 (@LetIn.Let_In (type.interp tx) (fun _ => type.interp tC))
                 | Nat_succ => Nat.succ
                 | Nat_add => curry2 Nat.add
                 | Nat_sub => curry2 Nat.sub
                 | Nat_mul => curry2 Nat.mul
                 | Nat_max => curry2 Nat.max
                 | nil t => curry0 (@Datatypes.nil (type.interp t))
                 | cons t => curry2 (@Datatypes.cons (type.interp t))
                 | fst A B => @Datatypes.fst (type.interp A) (type.interp B)
                 | snd A B => @Datatypes.snd (type.interp A) (type.interp B)
                 | bool_rect T => curry3 (fun t f => @Datatypes.bool_rect (fun _ => type.interp T) (t tt) (f tt))
                 | nat_rect P => curry3_2 (fun O_case => @Datatypes.nat_rect (fun _ => type.interp P) (O_case tt))
                 | pred => Nat.pred
                 | list_rect A P => curry3_23 (fun N_case => @Datatypes.list_rect (type.interp A) (fun _ => type.interp P) (N_case tt))
                 | List_nth_default T => curry3 (@List.nth_default (type.interp T))
                 | List_nth_default_concrete T d n => fun ls => @List.nth_default (type.interp T) d ls n
                 | Z_shiftr n => fun v => Z.shiftr v n
                 | Z_shiftl n => fun v => Z.shiftl v n
                 | Z_land mask => fun v => Z.land v mask
                 | Z_add => curry2 Z.add
                 | Z_mul => curry2 Z.mul
                 | Z_pow => curry2 Z.pow
                 | Z_modulo => curry2 Z.modulo
                 | Z_sub => curry2 Z.sub
                 | Z_opp => Z.opp
                 | Z_div => curry2 Z.div
                 | Z_eqb => curry2 Z.eqb
                 | Z_leb => curry2 Z.leb
                 | Z_of_nat => Z.of_nat
                 | Z_mul_split => curry3 Z.mul_split
                 | Z_mul_split_concrete s => curry2 (Z.mul_split s)
                 | Z_add_get_carry => curry3 Z.add_get_carry_full
                 | Z_add_get_carry_concrete s => curry2 (Z.add_get_carry_full s)
                 | Z_add_with_carry => curry3 Z.add_with_carry
                 | Z_add_with_get_carry => curry4 Z.add_with_get_carry_full
                 | Z_add_with_get_carry_concrete s => curry3 (Z.add_with_get_carry_full s)
                 | Z_sub_get_borrow => curry3 Z.sub_get_borrow_full
                 | Z_sub_get_borrow_concrete s => curry2 (Z.sub_get_borrow_full s)
                 | Z_sub_with_get_borrow => curry4 Z.sub_with_get_borrow_full
                 | Z_sub_with_get_borrow_concrete s => curry3 (Z.sub_with_get_borrow_full s)
                 | Z_zselect => curry3 Z.zselect
                 | Z_add_modulo => curry3 Z.add_modulo
                 | Z_rshi => curry4 Z.rshi
                 | Z_rshi_concrete s n => curry2 (fun x y => Z.rshi s x y n)
                 | Z_cc_m => curry2 Z.cc_m
                 | Z_cc_m_concrete s => Z.cc_m s
                 | Z_cast r => cast r
                 | Z_cast2 (r1, r2) => fun '(x1, x2) => (cast r1 x1, cast r2 x2)
                 end.
          End gen.

          Definition cast_outside_of_range (r : zrange) (v : BinInt.Z) : BinInt.Z.
          Proof using Type. exact v. Qed.

          (** Interpret identifiers where [Z_cast] is an opaque
              identity function when the value is not inside the range
              *)
          Definition interp {s d} (idc : ident s d) : type.interp s -> type.interp d
            := @gen_interp cast_outside_of_range s d idc.
          Global Arguments interp _ _ !_ _ / .

          Ltac reify
               mkAppIdent
               term_is_primitive_const
               term
               else_tac :=
            (*let dummy := match goal with _ => idtac "attempting to reify_op" term end in*)
            lazymatch term with
            | Nat.succ ?x => mkAppIdent Nat_succ x
            | Nat.add ?x ?y => mkAppIdent Nat_add (x, y)
            | Nat.sub ?x ?y => mkAppIdent Nat_sub (x, y)
            | Nat.mul ?x ?y => mkAppIdent Nat_mul (x, y)
            | Nat.max ?x ?y => mkAppIdent Nat_max (x, y)
            | S ?x => mkAppIdent Nat_succ x
            | @Datatypes.nil ?T
              => let rT := type.reify T in
                 mkAppIdent (@ident.nil rT) tt
            | @Datatypes.cons ?T ?x ?xs
              => let rT := type.reify T in
                 mkAppIdent (@ident.cons rT) (x, xs)
            | @Datatypes.fst ?A ?B ?x
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.fst rA rB) x
            | @Datatypes.snd ?A ?B ?x
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.snd rA rB) x
            | @Datatypes.bool_rect (fun _ => ?T) ?Ptrue ?Pfalse ?b
              => let rT := type.reify T in
                 mkAppIdent (@ident.bool_rect rT)
                            ((fun _ : Datatypes.unit => Ptrue), (fun _ : Datatypes.unit => Pfalse), b)
            | @Datatypes.nat_rect (fun _ => ?T) ?P0 (fun (n' : Datatypes.nat) Pn => ?PS) ?n
              => let rT := type.reify T in
                 let pat := fresh "pat" in (* fresh for COQBUG(https://github.com/coq/coq/issues/6562) *)
                 mkAppIdent (@ident.nat_rect rT)
                            ((fun _ : Datatypes.unit => P0),
                             (fun pat : Datatypes.nat * T
                              => let '(n', Pn) := pat in PS),
                             n)
            | @Datatypes.nat_rect (fun _ => ?T) ?P0 ?PS ?n
              => let dummy := match goal with _ => fail 1 "nat_rect successor case is not syntactically a function of two arguments:" PS end in
                 constr:(I : I)
            | Nat.pred ?x => mkAppIdent ident.pred x
            | @LetIn.Let_In ?A (fun _ => ?B) ?x ?f
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.Let_In rA rB) (x, f)
            | @LetIn.Let_In ?A ?B ?x ?f
              => let dummy := match goal with _ => fail 1 "Let_In contains a dependent type λ as its second argument:" B end in
                 constr:(I : I)
            | @Datatypes.list_rect ?A (fun _ => ?B) ?Pnil (fun x xs rec => ?Pcons) ?ls
              => let rA := type.reify A in
                 let rB := type.reify B in
                 let pat := fresh "pat" in (* fresh for COQBUG(https://github.com/coq/coq/issues/6562) *)
                 let pat' := fresh "pat" in (* fresh for COQBUG(https://github.com/coq/coq/issues/6562) (must also not overlap with [rec], but I think [fresh] handles that correctly, at least) *)
                 mkAppIdent (@ident.list_rect rA rB)
                            ((fun _ : Datatypes.unit => Pnil),
                             (fun pat : A * Datatypes.list A * B
                              => let '(pat', rec) := pat in
                                 let '(x, xs) := pat' in
                                 Pcons),
                             ls)
            | @Datatypes.list_rect ?A (fun _ => ?B) ?Pnil ?Pcons ?ls
              => let dummy := match goal with _ => fail 1 "list_rect cons case is not syntactically a function of three arguments:" Pcons end in
                 constr:(I : I)
            | @List.nth_default ?T ?d ?ls ?n
              => let rT := type.reify T in
                 mkAppIdent (@ident.List_nth_default rT) (d, ls, n)
            | Z.add ?x ?y => mkAppIdent ident.Z_add (x, y)
            | Z.mul ?x ?y => mkAppIdent ident.Z_mul (x, y)
            | Z.pow ?x ?y => mkAppIdent ident.Z_pow (x, y)
            | Z.sub ?x ?y => mkAppIdent ident.Z_sub (x, y)
            | Z.opp ?x => mkAppIdent ident.Z_opp x
            | Z.div ?x ?y => mkAppIdent ident.Z_div (x, y)
            | Z.modulo ?x ?y => mkAppIdent ident.Z_modulo (x, y)
            | Z.eqb ?x ?y => mkAppIdent ident.Z_eqb (x, y)
            | Z.leb ?x ?y => mkAppIdent ident.Z_leb (x, y)
            | Z.of_nat ?x => mkAppIdent ident.Z_of_nat x
            | Z.mul_split ?x ?y ?z => mkAppIdent ident.Z_mul_split (x, y, z)
            | Z.add_get_carry_full ?x ?y ?z => mkAppIdent ident.Z_add_get_carry (x, y, z)
            | Z.add_with_carry ?x ?y ?z => mkAppIdent ident.Z_add_with_carry (x, y, z)
            | Z.add_with_get_carry_full ?x ?y ?z ?a => mkAppIdent ident.Z_add_with_get_carry (x, y, z, a)
            | Z.sub_get_borrow_full ?x ?y ?z => mkAppIdent ident.Z_sub_get_borrow (x, y, z)
            | Z.sub_with_get_borrow_full ?x ?y ?z ?a => mkAppIdent ident.Z_sub_with_get_borrow (x, y, z, a)
            | Z.zselect ?x ?y ?z => mkAppIdent ident.Z_zselect (x, y, z)
            | Z.add_modulo ?x ?y ?z => mkAppIdent ident.Z_add_modulo (x,y,z)
            | Z.rshi ?x ?y ?z ?a => mkAppIdent ident.Z_rshi (x,y,z,a)
            | Z.cc_m ?x ?y => mkAppIdent ident.Z_cc_m (x,y)
            | _
              => lazymatch term_is_primitive_const with
                 | true
                   =>
                   let assert_const := match goal with
                                       | _ => require_primitive_const term
                                       end in
                   let T := type of term in
                   let rT := type.reify_primitive T in
                   mkAppIdent (@ident.primitive rT term) tt
                 | _ => else_tac ()
                 end
            end.

          Module List.
            Notation nth_default := List_nth_default.
            Notation nth_default_concrete := List_nth_default_concrete.
          End List.

          Module Z.
            Notation shiftr := Z_shiftr.
            Notation shiftl := Z_shiftl.
            Notation land := Z_land.
            Notation add := Z_add.
            Notation mul := Z_mul.
            Notation pow := Z_pow.
            Notation sub := Z_sub.
            Notation opp := Z_opp.
            Notation div := Z_div.
            Notation modulo := Z_modulo.
            Notation eqb := Z_eqb.
            Notation leb := Z_leb.
            Notation of_nat := Z_of_nat.
            Notation mul_split := Z_mul_split.
            Notation mul_split_concrete := Z_mul_split_concrete.
            Notation add_get_carry := Z_add_get_carry.
            Notation add_get_carry_concrete := Z_add_get_carry_concrete.
            Notation add_with_carry := Z_add_with_carry.
            Notation add_with_get_carry := Z_add_with_get_carry.
            Notation add_with_get_carry_concrete := Z_add_with_get_carry_concrete.
            Notation sub_get_borrow := Z_sub_get_borrow.
            Notation sub_get_borrow_concrete := Z_sub_get_borrow_concrete.
            Notation sub_with_get_borrow := Z_sub_with_get_borrow.
            Notation sub_with_get_borrow_concrete := Z_sub_with_get_borrow_concrete.
            Notation zselect := Z_zselect.
            Notation add_modulo := Z_add_modulo.
            Notation rshi := Z_rshi.
            Notation rshi_concrete := Z_rshi_concrete.
            Notation cc_m := Z_cc_m.
            Notation cc_m_concrete := Z_cc_m_concrete.
            Notation cast := Z_cast.
            Notation cast2 := Z_cast2.
          End Z.

          Module Nat.
            Notation succ := Nat_succ.
            Notation add := Nat_add.
            Notation sub := Nat_sub.
            Notation mul := Nat_mul.
            Notation max := Nat_max.
          End Nat.

          Module Export Notations.
            Notation ident := ident.
          End Notations.
        End ident.

        Module Notations.
          Include ident.Notations.
          Notation expr := (@expr ident).
          Notation Expr := (@Expr ident).
          Notation interp := (@interp ident (@ident.interp)).
          Notation Interp := (@Interp ident (@ident.interp)).
          Notation gen_interp cast_outside_of_range := (@interp ident (@ident.gen_interp cast_outside_of_range)).
          Notation GenInterp cast_outside_of_range := (@Interp ident (@ident.gen_interp cast_outside_of_range)).

          (*Notation "( x , y , .. , z )" := (Pair .. (Pair x%expr y%expr) .. z%expr) : expr_scope.*)
          Notation "'expr_let' x := A 'in' b" := (AppIdent ident.Let_In (Pair A%expr (Abs (fun x => b%expr)))) : expr_scope.
          Notation "[ ]" := (AppIdent ident.nil _) : expr_scope.
          Notation "x :: xs" := (AppIdent ident.cons (Pair x%expr xs%expr)) : expr_scope.
          Notation "x" := (AppIdent (ident.primitive x) _) (only printing, at level 9) : expr_scope.
          Notation "ls [[ n ]]"
            := (AppIdent ident.List.nth_default (_, ls, AppIdent (ident.primitive n%nat) _)%expr)
               : expr_scope.
          Notation "ls [[ n ]]"
            := (AppIdent (ident.List.nth_default_concrete n) ls%expr)
               : expr_scope.

          Ltac reify var term := expr.reify ident ident.reify var term.
          Ltac Reify term := expr.Reify ident ident.reify term.
          Ltac Reify_rhs _ :=
            expr.Reify_rhs ident ident.reify ident.interp ().
        End Notations.
        Include Notations.
      End default.
    End expr.

    Module canonicalize_list_recursion.
      Import expr.
      Import expr.default.
      Module ident.
        Local Ltac app_and_maybe_cancel term :=
          lazymatch term with
          | Abs (fun x : @expr ?var ?T => ?f)
            => eval cbv [unexpr] in (fun x : @expr var T => @unexpr ident.ident var _ f)
          | Abs (fun x : ?T => ?f)
            => let dummy := match goal with _ => fail 1 "Invalid var type:" T end in
               constr:(I : I)
          end.

        Definition transfer {var} {s d} (idc : for_reification.ident s d) : @expr var s -> @expr var d
          := let List_app A :=
                 list_rect
                   (fun _ => list (type.interp A) -> list (type.interp A))
                   (fun m => m)
                   (fun a l1 app_l1 m => a :: app_l1 m) in
             match idc in for_reification.ident s d return @expr var s -> @expr var d with
             | for_reification.ident.Let_In tx tC
               => AppIdent ident.Let_In
             | for_reification.ident.Nat_succ
               => AppIdent ident.Nat_succ
             | for_reification.ident.Nat_add
               => AppIdent ident.Nat_add
             | for_reification.ident.Nat_sub
               => AppIdent ident.Nat_sub
             | for_reification.ident.Nat_mul
               => AppIdent ident.Nat_mul
             | for_reification.ident.Nat_max
               => AppIdent ident.Nat_max
             | for_reification.ident.nil t
               => AppIdent ident.nil
             | for_reification.ident.cons t
               => AppIdent ident.cons
             | for_reification.ident.fst A B
               => AppIdent ident.fst
             | for_reification.ident.snd A B
               => AppIdent ident.snd
             | for_reification.ident.bool_rect T
               => AppIdent ident.bool_rect
             | for_reification.ident.nat_rect P
               => AppIdent ident.nat_rect
             | for_reification.ident.list_rect A P
               => AppIdent ident.list_rect
             | for_reification.ident.pred
               => AppIdent ident.pred
             | for_reification.ident.primitive t v
               => AppIdent (ident.primitive v)
             | for_reification.ident.Z_add
               => AppIdent ident.Z.add
             | for_reification.ident.Z_mul
               => AppIdent ident.Z.mul
             | for_reification.ident.Z_pow
               => AppIdent ident.Z.pow
             | for_reification.ident.Z_sub
               => AppIdent ident.Z.sub
             | for_reification.ident.Z_opp
               => AppIdent ident.Z.opp
             | for_reification.ident.Z_div
               => AppIdent ident.Z.div
             | for_reification.ident.Z_modulo
               => AppIdent ident.Z.modulo
             | for_reification.ident.Z_eqb
               => AppIdent ident.Z.eqb
             | for_reification.ident.Z_leb
               => AppIdent ident.Z.leb
             | for_reification.ident.Z_of_nat
               => AppIdent ident.Z.of_nat
             | for_reification.ident.Z_mul_split
               => AppIdent ident.Z.mul_split
             | for_reification.ident.Z_add_get_carry
               => AppIdent ident.Z.add_get_carry
             | for_reification.ident.Z_add_with_carry
               => AppIdent ident.Z.add_with_carry
             | for_reification.ident.Z_add_with_get_carry
               => AppIdent ident.Z.add_with_get_carry
             | for_reification.ident.Z_sub_get_borrow
               => AppIdent ident.Z.sub_get_borrow
             | for_reification.ident.Z_sub_with_get_borrow
               => AppIdent ident.Z.sub_with_get_borrow
             | for_reification.ident.Z_zselect
               => AppIdent ident.Z.zselect
             | for_reification.ident.Z_add_modulo
               => AppIdent ident.Z.add_modulo
             | for_reification.ident.Z_rshi
               => AppIdent ident.Z.rshi
             | for_reification.ident.Z_cc_m
               => AppIdent ident.Z.cc_m
             | for_reification.ident.list_case A P
               => ltac:(
                    let v := reify
                               (@expr var)
                               (fun '((Pnil, Pcons, ls)
                                      : (unit -> type.interp P)
                                        * (type.interp A * list (type.interp A) -> type.interp P)
                                        * (list (type.interp A)))
                                => list_rect
                                     (fun _ => type.interp P)
                                     (Pnil tt)
                                     (fun x xs _ => Pcons (x, xs))
                                     ls) in
                    let v := app_and_maybe_cancel v in exact v)
             | for_reification.ident.List_length A
               => ltac:(
                    let v := reify
                               (@expr var)
                               (fun (ls : list (type.interp A))
                                => list_rect
                                     (fun _ => nat)
                                     0%nat
                                     (fun a t len_t => S len_t)
                                     ls) in
                    let v := app_and_maybe_cancel v in exact v)
             | for_reification.ident.List_seq
               => ltac:(
                    let v
                        :=
                        reify
                          (@expr var)
                          (fun start_len : nat * nat
                           => nat_rect
                                (fun _ => nat -> list nat)
                                (fun _ => nil)
                                (fun len seq_len start => cons start (seq_len (S start)))
                                (snd start_len) (fst start_len)) in
                    let v := app_and_maybe_cancel v in exact v)
             | for_reification.ident.List_repeat A
               => ltac:(
                    let v := reify
                               (@expr var)
                               (fun (xn : type.interp A * nat)
                                => nat_rect
                                     (fun _ => list (type.interp A))
                                     nil
                                     (fun k repeat_k => cons (fst xn) repeat_k)
                                     (snd xn)) in
                    let v := app_and_maybe_cancel v in exact v)
             | for_reification.ident.List_combine A B
               => ltac:(
                    let v := reify
                               (@expr var)
                               (fun '((ls1, ls2) : list (type.interp A) * list (type.interp B))
                                => list_rect
                                     (fun _ => list (type.interp B) -> list (type.interp A * type.interp B))
                                     (fun l' => nil)
                                     (fun x tl combine_tl rest
                                      => list_rect
                                           (fun _ => list (type.interp A * type.interp B))
                                           nil
                                           (fun y tl' _
                                            => (x, y) :: combine_tl tl')
                                           rest)
                                     ls1
                                     ls2) in
                    let v := app_and_maybe_cancel v in exact v)
             | for_reification.ident.List_map A B
               => ltac:(
                    let v := reify
                               (@expr var)
                               (fun '((f, ls) : (type.interp A -> type.interp B) * Datatypes.list (type.interp A))
                                => list_rect
                                     (fun _ => list (type.interp B))
                                     nil
                                     (fun a t map_t => f a :: map_t)
                                     ls) in
                    let v := app_and_maybe_cancel v in exact v)
             | for_reification.ident.List_flat_map A B
               => ltac:(
                    let List_app := (eval cbv [List_app] in (List_app B)) in
                    let v := reify
                               (@expr var)
                               (fun '((f, ls) : (type.interp A -> list (type.interp B)) * list (type.interp A))
                                => list_rect
                                     (fun _ => list (type.interp B))
                                     nil
                                     (fun x t flat_map_t => List_app (f x) flat_map_t)
                                     ls) in
                    let v := app_and_maybe_cancel v in exact v)
             | for_reification.ident.List_partition A
               => ltac:(
                    let v := reify
                               (@expr var)
                               (fun '((f, ls) : (type.interp A -> bool) * list (type.interp A))
                                => list_rect
                                     (fun _ => list (type.interp A) * list (type.interp A))%type
                                     (nil, nil)
                                     (fun x tl partition_tl
                                      => let g := fst partition_tl in
                                         let d := snd partition_tl in
                                         if f x then (x :: g, d) else (g, x :: d))
                                     ls) in
                    let v := app_and_maybe_cancel v in exact v)
             | for_reification.ident.List_app A
               => ltac:(
                    let List_app := (eval cbv [List_app] in (List_app A)) in
                    let v := reify (@expr var) (fun '(ls1, ls2) => List_app ls1 ls2) in
                    let v := app_and_maybe_cancel v in exact v)
             | for_reification.ident.List_rev A
               => ltac:(
                    let List_app := (eval cbv [List_app] in (List_app A)) in
                    let v := reify
                               (@expr var)
                               (fun ls
                                => list_rect
                                     (fun _ => list (type.interp A))
                                     nil
                                     (fun x l' rev_l' => List_app rev_l' [x])
                                     ls) in
                    let v := app_and_maybe_cancel v in exact v)
             | for_reification.ident.List_fold_right A B
               => ltac:(
                    let v := reify
                               (@expr var)
                               (fun '((f, a0, ls)
                                      : (type.interp B * type.interp A -> type.interp A) * type.interp A * list (type.interp B))
                                => list_rect
                                     (fun _ => type.interp A)
                                     a0
                                     (fun b t fold_right_t => f (b, fold_right_t))
                                     ls) in
                    let v := app_and_maybe_cancel v in exact v)
             | for_reification.ident.List_update_nth T
               => ltac:(
                    let v := reify
                               (@expr var)
                               (fun '((n, f, ls) : nat * (type.interp T -> type.interp T) * list (type.interp T))
                                => nat_rect
                                     (fun _ => list (type.interp T) -> list (type.interp T))
                                     (fun ls
                                      => list_rect
                                           (fun _ => list (type.interp T))
                                           nil
                                           (fun x' xs' __ => f x' :: xs')
                                           ls)
                                     (fun n' update_nth_n' ls
                                      => list_rect
                                           (fun _ => list (type.interp T))
                                           nil
                                           (fun x' xs' __ => x' :: update_nth_n' xs')
                                           ls)
                                     n
                                     ls) in
                    let v := app_and_maybe_cancel v in exact v)
             | for_reification.ident.List_nth_default T
               => AppIdent ident.List_nth_default
             (*ltac:(
                  let v := reify
                             var
                             (fun (default : type.interp T) (l : list (type.interp T)) (n : nat)
                              => nat_rect
                                   (fun _ => list (type.interp T) -> type.interp T)
                                   (list_rect
                                      (fun _ => type.interp T)
                                      default
                                      (fun x __ __ => x))
                                   (fun n nth_error_n
                                    => list_rect
                                         (fun _ => type.interp T)
                                         default
                                         (fun __ l __ => nth_error_n l))
                                   n
                                   l) in
                  exact v)*)
             end%expr.
      End ident.

      Module expr.
        Section with_var.
          Context {var : type -> Type}.

          Fixpoint transfer {t} (e : @for_reification.Notations.expr var t)
            : @expr var t
            := match e  with
               | Var t v => Var v
               | TT => TT
               | Pair A B a b => Pair (@transfer A a) (@transfer B b)
               | AppIdent s d idc args => @ident.transfer var s d idc (@transfer _ args)
               | App s d f x => App (@transfer _ f) (@transfer _ x)
               | Abs s d f => Abs (fun x => @transfer d (f x))
               end.
        End with_var.

        Definition Transfer {t} (e : for_reification.Notations.Expr t) : Expr t
          := fun var => transfer (e _).
      End expr.
    End canonicalize_list_recursion.
    Notation canonicalize_list_recursion := canonicalize_list_recursion.expr.Transfer.
    Export expr.
    Export expr.default.
  End Uncurried.

  Import Uncurried.
  Section invert.
    Context {var : type -> Type}.

    Definition invert_Var {t} (e : @expr var t) : option (var t)
      := match e with
         | Var t v => Some v
         | _ => None
         end.

    Local Notation if_arrow f
      := (fun t => match t return Type with
                   | type.arrow s d => f s d
                   | _ => True
                   end) (only parsing).
    Local Notation if_arrow_s f := (if_arrow (fun s d => f s)) (only parsing).
    Local Notation if_arrow_d f := (if_arrow (fun s d => f d)) (only parsing).
    Local Notation if_prod f
      := (fun t => match t return Type with
                   | type.prod A B => f A B
                   | _ => True
                   end).

    Definition invert_Abs {s d} (e : @expr var (type.arrow s d)) : option (var s -> @expr var d)
      := match e in expr.expr t return option (if_arrow (fun _ _ => _) t) with
         | Abs s d f => Some f
         | _ => None
         end.

    Definition invert_App {d} (e : @expr var d) : option { s : _ & @expr var (s -> d) * @expr var s }%type
      := match e with
         | App s d f x => Some (existT _ s (f, x))
         | _ => None
         end.

    Definition invert_AppIdent {d} (e : @expr var d) : option { s : _ & @ident s d * @expr var s }%type
      := match e with
         | AppIdent s d idc args
           => Some (existT _ s (idc, args))
         | _ => None
         end.

    Definition invert_App2 {d} (e : @expr var d) : option { s1s2 : _ * _ & @expr var (fst s1s2 -> snd s1s2 -> d) * @expr var (fst s1s2) * @expr var (snd s1s2) }%type
      := match invert_App e with
         | Some (existT s (f, y))
           => match invert_App f with
              | Some (existT s' (f', x))
                => Some (existT _ (s', s) (f', x, y))
              | None => None
              end
         | None => None
         end.

    Local Notation expr_prod
      := (fun t => match t return Type with
                   | type.prod A B => prod (expr A) (expr B)
                   | _ => True
                   end) (only parsing).

    Definition invert_Pair {A B} (e : @expr var (type.prod A B)) : option (@expr var A * @expr var B)
      := match e in expr.expr t return option (if_prod (fun A B => expr A * expr B)%type t) with
         | Pair A B a b
           => Some (a, b)
         | _ => None
         end.

    Definition invert_or_expand_Pair {A B} (e : @expr var (type.prod A B)) : @expr var A * @expr var B
      := match invert_Pair e with
         | Some p => p
         | None => (ident.fst @@ e, ident.snd @@ e)
         end%core%expr.

    (* if we want more code for the below, I would suggest [reify_base_type] and [reflect_base_type] *)
    Definition reify_primitive {t} (v : type.interp (type.type_primitive t)) : @expr var (type.type_primitive t)
      := AppIdent (ident.primitive v) TT.
    Definition reflect_primitive {t} (e : @expr var (type.type_primitive t)) : option (type.interp (type.type_primitive t))
      := match invert_AppIdent e with
         | Some (existT s (idc, args))
           => match idc in ident _ t return option (type.interp t) with
              | ident.primitive _ v => Some v
              | _ => None
              end
         | None => None
         end.
    Definition invert_Z_opp (e : @expr var type.Z) : option (@expr var type.Z)
      := match invert_AppIdent e with
         | Some (existT s (idc, args))
           => match idc in ident s t return expr s -> option (expr type.Z) with
              | ident.Z_opp => fun v => Some v
              | _ => fun _ => None
              end args
         | None => None
         end.

    Definition invert_Z_cast (e : @expr var type.Z) : option (zrange * @expr var type.Z)
      := match invert_AppIdent e with
         | Some (existT s (idc, args))
           => match idc in ident s t return expr s -> option (zrange * expr type.Z) with
              | ident.Z_cast r => fun v => Some (r, v)
              | _ => fun _ => None
              end args
         | None => None
         end.

    Definition invert_Z_cast2 (e : @expr var (type.Z * type.Z)) : option ((zrange * zrange) * @expr var (type.Z * type.Z))
      := match invert_AppIdent e with
         | Some (existT s (idc, args))
           => match idc in ident s t return expr s -> option ((zrange * zrange) * expr (type.Z * type.Z)) with
              | ident.Z_cast2 r => fun v => Some (r, v)
              | _ => fun _ => None
              end args
         | None => None
         end.

    Local Notation list_expr
      := (fun t => match t return Type with
                   | type.list T => list (expr T)
                   | _ => True
                   end) (only parsing).

    (* oh, the horrors of not being able to use non-linear deep pattern matches.  c.f. COQBUG(https://github.com/coq/coq/issues/6320) *)
    Fixpoint reflect_list {t} (e : @expr var (type.list t))
      : option (list (@expr var t))
      := match e in expr.expr t return option (list_expr t) with
         | AppIdent s (type.list t) idc x_xs
           => match x_xs in expr.expr s return ident s (type.list t) -> option (list (expr t)) with
              | Pair A (type.list B) x xs
                => match @reflect_list B xs with
                   | Some xs
                     => fun idc
                        => match idc in ident s d
                                 return if_prod (fun A B => expr A) s
                                        -> if_prod (fun A B => list_expr B) s
                                        -> option (list_expr d)
                           with
                           | ident.cons A
                             => fun x xs => Some (cons x xs)
                           | _ => fun _ _ => None
                           end x xs
                   | None => fun _ => None
                   end
              | _
                => fun idc
                   => match idc in ident _ t return option (list_expr t) with
                      | ident.nil _ => Some nil
                      | _ => None
                      end
              end idc
         | _ => None
         end.
  End invert.

  Section gallina_reify.
    Context {var : type -> Type}.
    Definition reify_list {t} (ls : list (@expr var t)) : @expr var (type.list t)
      := list_rect
           (fun _ => _)
           (ident.nil @@ TT)%expr
           (fun x _ xs => ident.cons @@ (x, xs))%expr
           ls.
  End gallina_reify.

  Lemma interp_reify_list {t} ls
    : interp (@reify_list _ t ls) = List.map interp ls.
  Proof using Type.
    unfold reify_list.
    induction ls as [|x xs IHxs]; cbn in *; [ reflexivity | ].
    rewrite IHxs; reflexivity.
  Qed.

  Module GallinaReify.
    Section value.
      Context (var : type -> Type).
      Fixpoint value (t : type)
        := match t return Type with
           | type.prod A B as t => value A * value B
           | type.arrow s d => var s -> value d
           | type.list A => list (value A)
           | type.type_primitive _ as t
             => type.interp t
           end%type.
    End value.

    Section reify.
      Context {var : type -> Type}.
      Fixpoint reify {t : type} {struct t}
        : value var t -> @expr var t
        := match t return value var t -> expr t with
           | type.prod A B as t
             => fun '((a, b) : value var A * value var B)
                => (@reify A a, @reify B b)%expr
           | type.arrow s d
             => fun (f : var s -> value var d)
                => Abs (fun x
                        => @reify d (f x))
           | type.list A as t
             => fun x : list (value var A)
                => reify_list (List.map (@reify A) x)
           | type.type_primitive _ as t
             => fun x : type.interp t
                => (ident.primitive x @@ TT)%expr
           end.
    End reify.

    Definition Reify_as (t : type) (v : forall var, value var t) : Expr t
      := fun var => reify (v _).

    (** [Reify] does Ltac type inference to get the type *)
    Notation Reify v
      := (Reify_as (type.reify_type_of v) (fun _ => v)) (only parsing).
  End GallinaReify.

  Module Uncurry.
    Module type.
      Fixpoint uncurried_domain (t : type) : type
        := match t with
           | type.arrow s d
             => match d with
                | type.arrow _ _
                  => s * uncurried_domain d
                | _ => s
                end
           | _ => type.type_primitive type.unit
           end%ctype.

      Definition uncurry (t : type) : type
        := type.arrow (uncurried_domain t) (type.final_codomain t).
    End type.

    Fixpoint app_curried {t : type}
      : type.interp t -> type.interp (type.uncurried_domain t) -> type.interp (type.final_codomain t)
      := match t return type.interp t -> type.interp (type.uncurried_domain t) -> type.interp (type.final_codomain t) with
         | type.arrow s d
           => match d
                    return (type.interp d -> type.interp (type.uncurried_domain d) -> type.interp (type.final_codomain d))
                           -> type.interp (type.arrow s d)
                           -> type.interp (type.uncurried_domain (type.arrow s d))
                           -> type.interp (type.final_codomain d)
              with
              | type.arrow _ _ as d
                => fun app_curried_d
                       (f : type.interp s -> type.interp d)
                       (x : type.interp s * type.interp (type.uncurried_domain d))
                   => app_curried_d (f (fst x)) (snd x)
              | d
                => fun _
                       (f : type.interp s -> type.interp d)
                       (x : type.interp s)
                   => f x
              end (@app_curried d)
         | _ => fun f _ => f
         end.

    Module expr.
      Section with_var.
        Context {var : type -> Type}.

        Fixpoint uncurry' {t}
          : @expr (@expr var) t -> @expr var (type.uncurried_domain t) -> @expr var (type.final_codomain t)
          := match t return expr t -> expr (type.uncurried_domain t) -> expr (type.final_codomain t) with
             | type.arrow s d
               => fun e
                  => let f := fun v
                              => @uncurry'
                                   d
                                   match invert_Abs e with
                                   | Some f => f v
                                   | None => e @ Var v
                                   end%expr in
                     match d return (expr s -> expr (type.uncurried_domain d) -> expr (type.final_codomain d)) -> expr (type.uncurried_domain (s -> d)) -> expr (type.final_codomain d) with
                     | type.arrow _ _ as d
                       => fun f sdv
                          => f (ident.fst @@ sdv) (ident.snd @@ sdv)
                     | _
                       => fun f sv => f sv TT
                     end f
             | type.type_primitive _
             | type.prod _ _
             | type.list _
               => fun e _ => unexpr e
             end%expr.

        Definition uncurry {t} (e : @expr (@expr var) t)
          : @expr var (type.uncurry t)
          := Abs (fun v => @uncurry' t e (Var v)).
      End with_var.

      Definition Uncurry {t} (e : Expr t) : Expr (type.uncurry t)
        := fun var => uncurry (e _).
    End expr.
  End Uncurry.

  Module CPS.
    Import Uncurried.
    Module Import Output.
      Module type.
        Import Compilers.type.
        Inductive type := type_primitive (_:primitive) | prod (A B : type) | continuation (A : type) | list (A : type).
        Module Export Coercions.
          Global Coercion type_primitive : primitive >-> type.
        End Coercions.

        Module Export Notations.
          Export Coercions.
          Delimit Scope cpstype_scope with cpstype.
          Bind Scope cpstype_scope with type.
          Notation "()" := unit : cpstype_scope.
          Notation "A * B" := (prod A B) : cpstype_scope.
          Notation "A --->" := (continuation A) : cpstype_scope.
          Notation type := type.
        End Notations.

        Section interp.
          Context (R : Type).
          (** denote CPS types *)
          Fixpoint interp (t : type)
            := match t return Type with
               | type_primitive t => Compilers.type.interp t
               | prod A B => interp A * interp B
               | continuation A => interp A -> R
               | list A => Datatypes.list (interp A)
               end%type.
        End interp.
      End type.
      Export type.Notations.

      Module expr.
        Section expr.
          Context {ident : type -> Type} {var : type -> Type} {R : type}.

          Inductive expr :=
          | Halt (v : var R)
          | App {A} (f : var (A --->)) (x : var A)
          | Bind {A} (x : primop A) (f : var A -> expr)
          with
          primop : type -> Type :=
          | Var {t} (v : var t) : primop t
          | Abs {t} (f : var t -> expr) : primop (t --->)
          | Pair {A B} (x : var A) (y : var B) : primop (A * B)
          | Fst {A B} (x : var (A * B)) : primop A
          | Snd {A B} (x : var (A * B)) : primop B
          | TT : primop ()
          | Ident {t} (idc : ident t) : primop t.
        End expr.
        Global Arguments expr {ident var} R.
        Global Arguments primop {ident var} R _.

        Definition Expr {ident : type -> Type} R := forall var, @expr ident var R.

        Section with_ident.
          Context {ident : type -> Type}
                  (r : type)
                  (R : Type)
                  (interp_ident
                   : forall t, ident t -> type.interp R t).

          (** denote CPS exprs *)
          Fixpoint interp (e : @expr ident (type.interp R) r) (k : type.interp R r -> R)
                   {struct e}
            : R
            := match e with
               | Halt v => k v
               | App A f x => f x
               | Bind A x f => interp (f (@interp_primop _ x k)) k
               end
          with interp_primop {t} (e : @primop ident (type.interp R) r t) (k : type.interp R r -> R)
                             {struct e}
               : type.interp R t
               := match e with
                  | Var t v => v
                  | Abs t f => fun x : type.interp _ t => interp (f x) k
                  | Pair A B x y => (x, y)
                  | Fst A B x => fst x
                  | Snd A B x => snd x
                  | TT => tt
                  | Ident t idc => interp_ident t idc
                  end.

          Definition Interp (e : Expr r) (k : type.interp R r -> R) : R := interp (e _) k.
        End with_ident.

        Module Export Notations.
          Delimit Scope cpsexpr_scope with cpsexpr.
          Bind Scope cpsexpr_scope with expr.
          Bind Scope cpsexpr_scope with primop.

          Infix "@" := App : cpsexpr_scope.
          Notation "v <- x ; f" := (Bind x (fun v => f)) : cpsexpr_scope.
          Notation "'λ'  x .. y , t" := (Abs (fun x => .. (Abs (fun y => t%cpsexpr)) ..)) : cpsexpr_scope.
          Notation "( x , y , .. , z )" := (Pair .. (Pair x%cpsexpr y%cpsexpr) .. z%cpsexpr) : cpsexpr_scope.
        Notation "( )" := TT : cpsexpr_scope.
        Notation "()" := TT : cpsexpr_scope.
        End Notations.
      End expr.
      Export expr.Notations.
    End Output.

    Module type.
      Section translate.
        Fixpoint translate (t : Compilers.type.type) : type
          := match t with
             | A * B => (translate A * translate B)%cpstype
             | s -> d => (translate s * (translate d --->) --->)%cpstype
             | Compilers.type.list A => type.list (translate A)
             | Compilers.type.type_primitive t
               => t
             end%ctype.
        Fixpoint untranslate (R : Compilers.type.type) (t : type)
          : Compilers.type.type
          := match t with
             | type.type_primitive t => t
             | A * B => (untranslate R A * untranslate R B)%ctype
             | (t --->)
               => (untranslate R t -> R)%ctype
             | type.list A => Compilers.type.list (untranslate R A)
             end%cpstype.
      End translate.
    End type.

    Module expr.
      Import Output.expr.
      Import Output.expr.Notations.
      Import Compilers.type.
      Import Compilers.Uncurried.expr.
      Section with_ident.
        Context {ident : Output.type.type -> Type}
                {ident' : type -> type -> Type}
                {var : Output.type.type -> Type}
                (translate_ident : forall s d, ident' s d -> ident (type.translate (s -> d))).
        Notation var' := (fun t => var (type.translate t)).
        Local Notation oexpr := (@Output.expr.expr ident var).

        Section splice.
          Context {r1 r2 : Output.type.type}.
          Fixpoint splice  (e1 : oexpr r1) (e2 : var r1 -> oexpr r2)
                   {struct e1}
            : oexpr r2
            := match e1 with
               | Halt v => e2 v
               | f @ x => f @ x
               | Bind A x f => v <- @splice_primop _ x e2; @splice (f v) e2
               end%cpsexpr
          with
          splice_primop {t} (f : @primop ident var r1 t) (e2 : var r1 -> oexpr r2)
                        {struct f}
          : @primop ident var r2 t
          := match f with
             | Output.expr.Var t v => Output.expr.Var v
             | Output.expr.Pair A B x y as e => Output.expr.Pair x y
             | Output.expr.Fst A B x => Output.expr.Fst x
             | Output.expr.Snd A B x => Output.expr.Snd x
             | Output.expr.TT => Output.expr.TT
             | Output.expr.Ident t idc => Output.expr.Ident idc
             | Output.expr.Abs t f
               => Output.expr.Abs (fun x => @splice (f x) e2)
             end.
        End splice.

        Local Notation "x <-- e1 ; e2" := (splice e1 (fun x => e2%cpsexpr)) : cpsexpr_scope.

        (** Note: We used to special-case [bool_rect] because
            reduction of the bodies of eliminators should block on the
            branching.  We would like to just write:

<<
| AppIdent (A * A * type.bool) A ident.bool_rect (Ptrue, Pfalse, b)
  => b' <-- @translate _ b;
     App_bool_rect (@translate _ Ptrue) (@translate _ Pfalse) b'
| AppIdent s d idc args
  => args' <-- @translate _ args;
     k <- Output.expr.Abs (fun r => Halt r);
     p <- (args', k);
     f <- Output.expr.Ident (translate_ident s d idc);
     f @ p
>>
            but due do deficiencies in non-linear deep pattern
            matching (and the fact that we're generic over the type of
            identifiers), we cannot, and must write something
            significantly more verbose.  Because this is so painful,
            we do not special-case [nat_rect] nor [list_rect], which
            anyway do not need special casing except in cases where
            they never hit the base case; it is already the case that
            functions get a sort of "free pass" and do get evaluated
            until applied to arguments, and the base case ought to be
            hit exactly once.

            However, now that [bool_rect]'s arguments are thunked, we
            no longer need to do this. *)
        Fixpoint translate {t}
                 (e : @Compilers.Uncurried.expr.expr ident' var' t)
          : @Output.expr.expr ident var (type.translate t)
          := match e with
             | Var t v => Halt v
             | TT => x <- () ; Halt x
             | AppIdent s d idc args
               => (args' <-- @translate _ args;
                     k <- Output.expr.Abs (fun r => Halt r);
                     p <- (args', k);
                     f <- Output.expr.Ident (translate_ident s d idc);
                     f @ p)
             | Pair A B a b
               => (a' <-- @translate _ a;
                     b' <-- @translate _ b;
                     p <- (a', b');
                     Halt p)
             | App s d e1 e2
               => (f <-- @translate _ e1;
                     x <-- @translate _ e2;
                     k <- Output.expr.Abs (fun r => Halt r);
                     p <- (x, k);
                     f @ p)
             | Abs s d f
               => f <- (Output.expr.Abs
                          (fun p
                           => x <- Fst p;
                                k <- Snd p;
                                r <-- @translate _ (f x);
                                k @ r));
                    Halt f
             end%cpsexpr.
      End with_ident.

      Definition Translate
                 {ident : Output.type.type -> Type}
                 {ident' : type -> type -> Type}
                 (translate_ident : forall s d, ident' s d -> ident (type.translate (s -> d)))
                 {t} (e : @Compilers.Uncurried.expr.Expr ident' t)
        : @Output.expr.Expr ident (type.translate t)
        := fun var => translate translate_ident (e _).

      Section call_with_cont.
        Context {ident' : Output.type.type -> Type}
                {ident : type -> type -> Type}
                {var : type -> Type}
                {r : Output.type.type}
                {R : type}.
        Notation ucexpr := (@Compilers.Uncurried.expr.expr ident var).
        Notation ucexprut t := (ucexpr (type.untranslate R t)) (only parsing).
        Notation var' := (fun t => ucexprut t).
        Context (untranslate_ident : forall t, ident' t -> ucexprut t)
                (ifst : forall A B, ident (A * B)%ctype A)
                (isnd : forall A B, ident (A * B)%ctype B).

        Fixpoint call_with_continuation
                 (e : @Output.expr.expr ident' var' r)
                 (k : ucexprut r -> ucexpr R)
                 {struct e}
          : ucexpr R
          := match e with
             | Halt v => k v
             | expr.App A f x
               => @App _ _ (type.untranslate R A) R
                       f x
             | Bind A x f
               => @call_with_continuation
                    (f (@call_primop_with_continuation A x k))
                    k
             end%expr
        with
        call_primop_with_continuation
          {t}
          (e : @Output.expr.primop ident' var' r t)
          (k : ucexprut r -> ucexpr R)
          {struct e}
        : ucexprut t
        := match e in Output.expr.primop _ t return ucexprut t with
           | expr.Var t v => v
           | expr.Abs t f => Abs (fun x : var (type.untranslate _ _)
                                  => @call_with_continuation
                                       (f (Var x)) k)
           | expr.Pair A B x y => (x, y)
           | Fst A B x => ifst (type.untranslate _ A) (type.untranslate _ B)
                               @@ x
           | Snd A B x => isnd (type.untranslate _ A) (type.untranslate _ B)
                               @@ x
           | expr.TT => TT
           | Ident t idc => untranslate_ident t idc
           end%expr.
      End call_with_cont.

      Definition CallWithContinuation
                 {ident' : Output.type.type -> Type}
                 {ident : type -> type -> Type}
                 {R : type}
                 (untranslate_ident : forall t, ident' t -> @Compilers.Uncurried.expr.Expr ident (type.untranslate R t))
                 (ifst : forall A B, ident (A * B)%ctype A)
                 (isnd : forall A B, ident (A * B)%ctype B)
                 {t} (e : @Output.expr.Expr ident' t)
                 (k : forall var, @Uncurried.expr.expr ident var (type.untranslate R t) -> @Uncurried.expr.expr ident var R)
        : @Compilers.Uncurried.expr.Expr ident R
        := fun var => call_with_continuation
                        (fun t idc => untranslate_ident t idc _) ifst isnd (e _) (k _).
    End expr.

    Module ident.
      Import CPS.Output.type.

      Inductive ident : type -> Set :=
      | wrap {s d} (idc : Uncurried.expr.default.ident s d) : ident (type.translate (s -> d)).

      Notation cps_of f
        := (fun x k => k (f x)).
      Notation curry0 f
        := (fun 'tt => f).
      Notation curry2 f
        := (fun '(a, b) => f a b).
      Notation curry3 f
        := (fun '(a, b, c) => f a b c).
      Notation uncurry2 f
        := (fun a b => f (a, b)).
      Notation uncurry3 f
        := (fun a b c => f (a, b, c)).
      Notation curry3_23 f
        := (fun '(a, b, c) => f a (uncurry3 b) c).
      Notation curry3_2 f
        := (fun '(a, b, c) => f a (uncurry2 b) c).

      (** denote CPS identifiers *)
      Definition interp {R} {t} (idc : ident t) : type.interp R t
        := match idc in ident t return type.interp R t with
           | wrap s d idc
             => fun '((x, k) : type.interp R (type.translate s) * (type.interp R (type.translate d) -> R))
                =>
                  match idc in Uncurried.expr.default.ident s d return type.interp R (type.translate s) -> (type.interp R (type.translate d) -> R) -> R with
                  | ident.primitive _ _ as idc
                  | ident.Nat_succ as idc
                  | ident.Nat_add as idc
                  | ident.Nat_sub as idc
                  | ident.Nat_mul as idc
                  | ident.Nat_max as idc
                  | ident.pred as idc
                  | ident.Z_shiftr _ as idc
                  | ident.Z_shiftl _ as idc
                  | ident.Z_land _ as idc
                  | ident.Z_add as idc
                  | ident.Z_mul as idc
                  | ident.Z_pow as idc
                  | ident.Z_sub as idc
                  | ident.Z_opp as idc
                  | ident.Z_div as idc
                  | ident.Z_modulo as idc
                  | ident.Z_eqb as idc
                  | ident.Z_leb as idc
                  | ident.Z_of_nat as idc
                  | ident.Z_mul_split as idc
                  | ident.Z_add_get_carry as idc
                  | ident.Z_add_with_carry as idc
                  | ident.Z_add_with_get_carry as idc
                  | ident.Z_sub_with_get_borrow as idc
                  | ident.Z_sub_get_borrow as idc
                  | ident.Z_zselect as idc
                  | ident.Z_add_modulo as idc
                  | ident.Z_rshi as idc
                  | ident.Z_cc_m as idc
                  | ident.Z_cast _ as idc
                  | ident.Z_cast2 _ as idc
                    => cps_of (Uncurried.expr.default.ident.interp idc)
                  | ident.Z_mul_split_concrete s
                    => cps_of (curry2 (Z.mul_split s))
                  | ident.Z_add_get_carry_concrete s
                    => cps_of (curry2 (Z.add_get_carry_full s))
                  | ident.Z_add_with_get_carry_concrete s
                    => cps_of (curry3 (Z.add_with_get_carry_full s))
                  | ident.Z_sub_get_borrow_concrete s
                    => cps_of (curry2 (Z.sub_get_borrow_full s))
                  | ident.Z_sub_with_get_borrow_concrete s
                    => cps_of (curry3 (Z.sub_with_get_borrow_full s))
                  | ident.Z_rshi_concrete s n
                    => cps_of (curry2 (fun x y => Z.rshi s x y n))
                  | ident.Z_cc_m_concrete s
                    => cps_of (Z.cc_m s)
                  | ident.Let_In tx tC
                    => fun '((x, f) : (interp R (type.translate tx)
                                       * (interp R (type.translate tx) * (interp R (type.translate tC) -> R) -> R)))
                           (k : interp R (type.translate tC) -> R)
                       => @LetIn.Let_In
                            (type.interp R (type.translate tx)) (fun _ => R)
                            x
                            (fun v => f (v, k))
                  | ident.nil t
                    => cps_of (curry0 (@Datatypes.nil (interp R (type.translate t))))
                  | ident.cons t
                    => cps_of (curry2 (@Datatypes.cons (interp R (type.translate t))))
                  | ident.fst A B
                    => cps_of (@Datatypes.fst (interp R (type.translate A)) (interp R (type.translate B)))
                  | ident.snd A B
                    => cps_of (@Datatypes.snd (interp R (type.translate A)) (interp R (type.translate B)))
                  | ident.bool_rect T
                    => fun '((tc, fc, b) :
                               (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) ((unit * (type.interp R (type.translate T) -> R) -> R) * (unit * (type.interp R (type.translate T) -> R) -> R) * bool))
                           k
                       => @Datatypes.bool_rect
                            (fun _ => R)
                            (tc (tt, k))
                            (fc (tt, k))
                            b
                  | ident.nat_rect P
                    => fun '((PO, PS, n) :
                               (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) ((unit * (interp R (type.translate P) -> R) -> R) * (nat * interp R (type.translate P) * (interp R (type.translate P) -> R) -> R) * nat))
                           k
                       => @Datatypes.nat_rect
                            (fun _ => (interp R (type.translate P) -> R) -> R)
                            (fun k => PO (tt, k))
                            (fun n' rec k
                             => rec (fun rec => PS (n', rec, k)))
                            n
                            k
                  | ident.list_rect A P
                    => fun '((Pnil, Pcons, ls) :
                               (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) ((unit * (interp R (type.translate P) -> R) -> R) * (interp R (type.translate A) * Datatypes.list (interp R (type.translate A)) * interp R (type.translate P) * (interp R (type.translate P) -> R) -> R) * Datatypes.list (interp R (type.translate A))))
                           k
                       => @Datatypes.list_rect
                            (interp R (type.translate A))
                            (fun _ => (interp R (type.translate P) -> R) -> R)
                            (fun k => Pnil (tt, k))
                            (fun x xs rec k
                             => rec (fun rec => Pcons (x, xs, rec, k)))
                            ls
                            k
                  | ident.List_nth_default T
                    => cps_of (curry3 (@List.nth_default (interp R (type.translate T))))
                  | ident.List_nth_default_concrete T d n
                    => cps_of (fun ls => @List.nth_default (interp R (type.translate T)) d ls n)
                  end x k
           end.

      Local Notation var_eta x := (ident.fst @@ x, ident.snd @@ x)%core%expr.

      Definition untranslate {R} {t} (idc : ident t)
        : @Compilers.Uncurried.expr.Expr Uncurried.expr.default.ident (type.untranslate R t)
        := fun var
           => match idc in ident t return @Compilers.Uncurried.expr.expr Uncurried.expr.default.ident var (type.untranslate R t) with
              | wrap s d idc
                =>
                match idc in default.ident s d return @Compilers.Uncurried.expr.expr Uncurried.expr.default.ident var (type.untranslate R (type.translate (s -> d))) with
                | ident.primitive t v
                  => λ (_k :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (() * (t -> R))%ctype) ,
                     (ident.snd @@ (Var _k))
                       @ (ident.primitive v @@ TT)
                | ident.Let_In tx tC
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate tx) * (type.untranslate _ (type.translate tx) * (type.untranslate _ (type.translate tC) -> R) -> R) * (type.untranslate _ (type.translate tC) -> R))%ctype) ,
                     ident.Let_In
                       @@ (ident.fst @@ (ident.fst @@ (Var xyk)),
                           (λ (x :
                                 (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate tx))) ,
                            (ident.snd @@ (ident.fst @@ (Var xyk)))
                              @ (Var x, ident.snd @@ Var xyk)))
                | ident.nat_rect P
                  => λ (PO_PS_n_k :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var ((Compilers.type.type_primitive ()%cpstype * (type.untranslate R (type.translate P) -> R) -> R) * (Compilers.type.type_primitive type.nat * type.untranslate R (type.translate P) * (type.untranslate R (type.translate P) -> R) -> R) * Compilers.type.type_primitive type.nat * (type.untranslate R (type.translate P) -> R))%ctype) ,
                     let (PO_PS_n, k) := var_eta (Var PO_PS_n_k) in
                     let (PO_PS, n) := var_eta PO_PS_n in
                     let (PO, PS) := var_eta PO_PS in
                     ((@ident.nat_rect ((type.untranslate _ (type.translate P) -> R) -> R))
                        @@ ((λ tt k , PO @ (Var tt, Var k)),
                            (λ n'rec k ,
                             let (n', rec) := var_eta (Var n'rec) in
                             rec @ (λ rec , PS @ (n', Var rec, Var k))),
                            n))
                       @ k
                | ident.list_rect A P
                  => λ (Pnil_Pcons_ls_k :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var ((Compilers.type.type_primitive ()%cpstype * (type.untranslate R (type.translate P) -> R) -> R) * (type.untranslate R (type.translate A) * Compilers.type.list (type.untranslate R (type.translate A)) * type.untranslate R (type.translate P) * (type.untranslate R (type.translate P) -> R) -> R) * Compilers.type.list (type.untranslate R (type.translate A)) * (type.untranslate R (type.translate P) -> R))%ctype) ,
                     let (Pnil_Pcons_ls, k) := var_eta (Var Pnil_Pcons_ls_k) in
                     let (Pnil_Pcons, ls) := var_eta Pnil_Pcons_ls in
                     let (Pnil, Pcons) := var_eta Pnil_Pcons in
                     ((@ident.list_rect
                         (type.untranslate _ (type.translate A))
                         ((type.untranslate _ (type.translate P) -> R) -> R))
                        @@ ((λ tt k, Pnil @ (Var tt, Var k)),
                            (λ x_xs_rec k,
                             let (x_xs, rec) := var_eta (Var x_xs_rec) in
                             let (x, xs) := var_eta x_xs in
                             rec @ (λ rec , Pcons @ (x, xs, Var rec, Var k))),
                            ls))
                       @ k
                | ident.List_nth_default T
                  => λ (xyzk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate T) * Compilers.type.list (type.untranslate _ (type.translate T)) * type.nat * (type.untranslate _ (type.translate T) -> R))%ctype) ,
                     (ident.snd @@ Var xyzk)
                       @ (ident.List_nth_default @@ (ident.fst @@ Var xyzk))
                | ident.List_nth_default_concrete T d n
                  => λ (xk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (Compilers.type.list (type.untranslate R (type.translate T)) * (type.untranslate R (type.translate T) -> R))%ctype) ,
                     (ident.snd @@ Var xk)
                       @ (ident.List_nth_default_concrete d n @@ (ident.fst @@ Var xk))
                | ident.bool_rect T
                  => λ (xyzk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var ((Compilers.type.type_primitive ()%cpstype * (type.untranslate R (type.translate T) -> R) -> R) * (Compilers.type.type_primitive ()%cpstype * (type.untranslate R (type.translate T) -> R) -> R) * Compilers.type.type_primitive type.bool * (type.untranslate R (type.translate T) -> R))%ctype) ,
                     ident.bool_rect
                       @@ ((λ tt,
                            (ident.fst @@ (ident.fst @@ (ident.fst @@ (Var xyzk))))
                              @ (Var tt, (ident.snd @@ (Var xyzk)))),
                           (λ tt,
                            (ident.snd @@ (ident.fst @@ (ident.fst @@ (Var xyzk))))
                              @ (Var tt, (ident.snd @@ (Var xyzk)))),
                           ident.snd @@ (ident.fst @@ (Var xyzk)))
                | ident.nil t
                  => λ (_k :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (() * (Compilers.type.list (type.untranslate _ (type.translate t)) -> R))%ctype) ,
                     (ident.snd @@ (Var _k))
                       @ (ident.nil @@ TT)
                | ident.cons t
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate t) * Compilers.type.list (type.untranslate _ (type.translate t)) * (Compilers.type.list (type.untranslate _ (type.translate t)) -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ (ident.cons
                            @@ (ident.fst @@ (Var xyk)))
                | ident.fst A B
                  => λ (xk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate A) * type.untranslate _ (type.translate B) * (type.untranslate _ (type.translate A) -> R))%ctype) ,
                     (ident.snd @@ (Var xk))
                       @ (ident.fst
                            @@ (ident.fst @@ (Var xk)))
                | ident.snd A B
                  => λ (xk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate A) * type.untranslate _ (type.translate B) * (type.untranslate _ (type.translate B) -> R))%ctype) ,
                     (ident.snd @@ (Var xk))
                       @ (ident.snd
                            @@ (ident.fst @@ (Var xk)))
                | ident.Nat_succ as idc
                | ident.pred as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.nat * (type.nat -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ type.nat)
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Nat_add as idc
                | ident.Nat_sub as idc
                | ident.Nat_mul as idc
                | ident.Nat_max as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.nat * type.nat * (type.nat -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ type.nat)
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Z_shiftr _ as idc
                | ident.Z_shiftl _ as idc
                | ident.Z_land _ as idc
                | ident.Z_opp as idc
                | ident.Z_cast _ as idc
                | ident.Z.cc_m_concrete _ as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.Z * (type.Z -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ type.Z)
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Z_add as idc
                | ident.Z_mul as idc
                | ident.Z_sub as idc
                | ident.Z_pow as idc
                | ident.Z_div as idc
                | ident.Z_modulo as idc
                | ident.Z.cc_m as idc
                | ident.Z_rshi_concrete _ _ as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.Z * type.Z * (type.Z -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ type.Z)
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Z_eqb as idc
                | ident.Z_leb as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.Z * type.Z * (type.bool -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ type.bool)
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Z_of_nat as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.nat * (type.Z -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ type.Z)
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Z_mul_split as idc
                | ident.Z_add_get_carry as idc
                | ident.Z_sub_get_borrow as idc
                | ident.Z_add_with_get_carry_concrete _ as idc
                | ident.Z_sub_with_get_borrow_concrete _ as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.Z * type.Z * type.Z * ((type.Z * type.Z) -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ (type.Z * type.Z))
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Z_cast2 _ as idc
                | ident.Z_mul_split_concrete _ as idc
                | ident.Z_add_get_carry_concrete _ as idc
                | ident.Z_sub_get_borrow_concrete _ as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.Z * type.Z * ((type.Z * type.Z) -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ (type.Z * type.Z))
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Z_add_with_carry as idc
                | ident.Z_zselect as idc
                | ident.Z_add_modulo as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.Z * type.Z * type.Z * (type.Z -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ type.Z)
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Z_add_with_get_carry as idc
                | ident.Z_sub_with_get_borrow as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.Z * type.Z * type.Z * type.Z * ((type.Z * type.Z) -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ (type.Z * type.Z))
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Z_rshi as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.Z * type.Z * type.Z * type.Z * (type.Z -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ type.Z)
                            @@ (ident.fst @@ (Var xyk)))
                end%expr
              end.
    End ident.
    Notation ident := ident.ident.

    Module default.
      Notation expr := (@Output.expr.expr ident).
      Notation Expr := (@Output.expr.Expr ident).

      Definition Translate
                 {t} (e : @Compilers.Uncurried.expr.default.Expr t)
        : Expr (type.translate t)
        := expr.Translate (@ident.wrap) e.

      Definition call_with_continuation
                 {var}
                 {R : Compilers.type.type}
                 {t} (e : @expr _ t)
                 (k : @Uncurried.expr.default.expr var (type.untranslate R t) -> @Uncurried.expr.default.expr var R)
        : @Compilers.Uncurried.expr.default.expr var R
        := expr.call_with_continuation (fun t idc => @ident.untranslate _ t idc _) (@ident.fst) (@ident.snd) e k.

      Definition CallWithContinuation
                 {R : Compilers.type.type}
                 {t} (e : Expr t)
                 (k : forall var, @Uncurried.expr.default.expr var (type.untranslate R t) -> @Uncurried.expr.default.expr var R)
        : @Compilers.Uncurried.expr.default.Expr R
        := expr.CallWithContinuation (@ident.untranslate _) (@ident.fst) (@ident.snd) e k.

      Local Notation iffT A B := ((A -> B) * (B -> A))%type.
      (** We can only "plug in the identity continuation" for flat
          (arrow-free) types.  (Actually, we know how to do it in a
          very ad-hoc way for types of at-most second-order functions;
          see git history.  This is much simpler.) *)
      Fixpoint try_untranslate_translate {R} {t}
        : option (forall (P : Compilers.type.type -> Type),
                     iffT (P (type.untranslate R (type.translate t))) (P t))
        := match t return option (forall (P : Compilers.type.type -> Type),
                                     iffT (P (type.untranslate R (type.translate t))) (P t)) with
           | Compilers.type.type_primitive x
             => Some (fun P => ((fun v => v), (fun v => v)))
           | type.arrow s d => None
           | Compilers.type.prod A B
             => (fA <- (@try_untranslate_translate _ A);
                   fB <- (@try_untranslate_translate _ B);
                   Some
                     (fun P
                      => let fA := fA (fun A => P (Compilers.type.prod A (type.untranslate R (type.translate B)))) in
                         let fB := fB (fun B => P (Compilers.type.prod A B)) in
                         ((fun v => fst fB (fst fA v)),
                          (fun v => snd fA (snd fB v)))))%option
           | Compilers.type.list A
             => (fA <- (@try_untranslate_translate R A);
                   Some (fun P => fA (fun A => P (Compilers.type.list A))))%option
           end.

      Local Notation "x <-- e1 ; e2" := (expr.splice e1 (fun x => e2%cpsexpr)) : cpsexpr_scope.

      Definition call_fun_with_id_continuation'
                 {s d}
        : option (forall var
                         (e : @expr _ (type.translate (s -> d))),
                     @Compilers.Uncurried.expr.default.expr var (s -> d))
        := (fs <- (@try_untranslate_translate _ s);
              fd <- (@try_untranslate_translate _ d);
              Some
                (fun var e
                 => let P := @Compilers.Uncurried.expr.default.expr var in
                    Abs
                      (fun v : var s
                       => call_with_continuation
                            ((f <-- e;
                                k <- (λ r, expr.Halt r);
                                p <- (snd (fs P) (Var v), k);
                                f @ p)%cpsexpr)
                            (fst (fd P)))))%option.

      Definition call_fun_with_id_continuation
                 {var}
                 {s d} (e : @expr _ (type.translate (s -> d)))
        : option (@Compilers.Uncurried.expr.default.expr var (s -> d))
        := option_map
             (fun f => f _ e)
             (@call_fun_with_id_continuation' s d).

      Definition CallFunWithIdContinuation
                 {s d}
                 (e : Expr (type.translate (s -> d)))
        : option (@Compilers.Uncurried.expr.default.Expr (s -> d))
        := option_map
             (fun f var => f _ (e _))
             (@call_fun_with_id_continuation' s d).
    End default.
    Include default.
  End CPS.

  Module ZRange.
    Module type.
      Module primitive.
        (** turn a [type.primitive] into a [Set] describing the type
            of bounds on that primitive *)
        Definition interp (t : type.primitive) : Set
          := match t with
             | type.unit => unit
             | type.Z => zrange
             | type.nat => unit
             | type.bool => unit
             end.
        Definition is_neg {t} : interp t -> bool
          := match t with
             | type.Z => fun r => (lower r <? 0) && (upper r <=? 0)
             | _ => fun _ => false
             end.
        Definition is_tighter_than {t} : interp t -> interp t -> bool
          := match t with
             | type.Z => is_tighter_than_bool
             | type.unit
             | type.nat
             | type.bool
               => fun _ _ => true
             end.
        Definition is_bounded_by {t} : interp t -> type.interp t -> bool
          := match t with
             | type.Z => fun r z => (lower r <=? z) && (z <=? upper r)
             | type.unit
             | type.nat
             | type.bool
               => fun _ _ => true
             end.
        Module option.
          (** turn a [type.primitive] into a [Set] describing the type
              of optional bounds on that primitive; bounds on a [Z]
              may be either a range, or [None], generally indicating
              that the [Z] is unbounded. *)
          Definition interp (t : type.primitive) : Set
            := match t with
               | type.unit => unit
               | type.Z => option zrange
               | type.nat => unit
               | type.bool => unit
               end.
          Definition None {t} : interp t
            := match t with
               | type.Z => None
               | _ => tt
               end.
          Definition Some {t} : primitive.interp t -> interp t
            := match t with
               | type.Z => Some
               | _ => id
               end.
          Definition is_neg {t} : interp t -> bool
            := match t with
               | type.Z => fun v => match v with
                                    | Datatypes.Some v => @is_neg type.Z v
                                    | Datatypes.None => false
                                    end
               | t => @primitive.is_neg t
               end.
        Definition is_tighter_than {t} : interp t -> interp t -> bool
          := match t with
             | type.Z
               => fun r1 r2
                  => match r1, r2 with
                     | _, Datatypes.None => true
                     | Datatypes.None, Datatypes.Some _ => false
                     | Datatypes.Some r1, Datatypes.Some r2 => is_tighter_than (t:=type.Z) r1 r2
                     end
             | t => @is_tighter_than t
             end.
        Definition is_bounded_by {t} : interp t -> type.interp t -> bool
          := match t with
             | type.Z
               => fun r
                  => match r with
                     | Datatypes.Some r => @is_bounded_by type.Z r
                     | Datatypes.None => fun _ => true
                     end
             | t => @is_bounded_by t
             end.
        End option.
      End primitive.
      (** turn a [type] into a [Set] describing the type of bounds on
          that type; this lifts [primitive.interp] from
          [type.primitive] to [type] *)
      Fixpoint interp (t : type) : Set
        := match t with
           | type.type_primitive x => primitive.interp x
           | type.prod A B => interp A * interp B
           | type.arrow s d => interp s -> interp d
           | type.list A => list (interp A)
           end.
      Fixpoint is_tighter_than {t} : interp t -> interp t -> bool
        := match t with
           | type.type_primitive x => @primitive.is_tighter_than x
           | type.prod A B
             => fun '((ra, rb) : interp A * interp B)
                    '((ra', rb') : interp A * interp B)
                => @is_tighter_than A ra ra' && @is_tighter_than B rb rb'
           | type.arrow s d => fun _ _ => false
           | type.list A
             => fold_andb_map (@is_tighter_than A)
           end.
      Fixpoint is_bounded_by {t} : interp t -> Compilers.type.interp t -> bool
        := match t return interp t -> Compilers.type.interp t -> bool with
           | type.type_primitive x => @primitive.is_bounded_by x
           | type.prod A B
             => fun '((ra, rb) : interp A * interp B)
                    '((ra', rb') : Compilers.type.interp A * Compilers.type.interp B)
                => @is_bounded_by A ra ra' && @is_bounded_by B rb rb'
           | type.arrow s d => fun _ _ => false
           | type.list A
             => fold_andb_map (@is_bounded_by A)
           end.
      Module option.
        (** turn a [type] into a [Set] describing the type of optional
            bounds on that primitive; bounds on a [Z] may be either a
            range, or [None], generally indicating that the [Z] is
            unbounded.  This lifts [primitive.option.interp] from
            [type.primitive] to [type] *)
        Fixpoint interp (t : type) : Set
          := match t with
             | type.type_primitive x => primitive.option.interp x
             | type.prod A B => interp A * interp B
             | type.arrow s d => interp s -> interp d
             | type.list A => option (list (interp A))
             end.
        Fixpoint None {t : type} : interp t
          := match t with
             | type.type_primitive x => @primitive.option.None x
             | type.prod A B => (@None A, @None B)
             | type.arrow s d => fun _ => @None d
             | type.list A => Datatypes.None
             end.
        Fixpoint Some {t : type} : type.interp t -> interp t
          := match t with
             | type.type_primitive x => @primitive.option.Some x
             | type.prod A B
               => fun x : type.interp A * type.interp B
                  => (@Some A (fst x), @Some B (snd x))
             | type.arrow s d => fun _ _ => @None d
             | type.list A => fun ls => Datatypes.Some (List.map (@Some A) ls)
             end.
        Fixpoint is_tighter_than {t} : interp t -> interp t -> bool
          := match t with
             | type.type_primitive x => @primitive.option.is_tighter_than x
             | type.prod A B
               => fun '((ra, rb) : interp A * interp B)
                      '((ra', rb') : interp A * interp B)
                  => @is_tighter_than A ra ra' && @is_tighter_than B rb rb'
             | type.arrow s d => fun _ _ => false
             | type.list A
               => fun ls1 ls2
                  => match ls1, ls2 with
                     | Datatypes.None, Datatypes.None => true
                     | Datatypes.Some _, Datatypes.None => true
                     | Datatypes.None, Datatypes.Some _ => false
                     | Datatypes.Some ls1, Datatypes.Some ls2 => fold_andb_map (@is_tighter_than A) ls1 ls2
                     end
             end.
        Fixpoint is_bounded_by {t} : interp t -> Compilers.type.interp t -> bool
          := match t return interp t -> Compilers.type.interp t -> bool with
             | type.type_primitive x => @primitive.option.is_bounded_by x
             | type.prod A B
               => fun '((ra, rb) : interp A * interp B)
                      '((ra', rb') : Compilers.type.interp A * Compilers.type.interp B)
                  => @is_bounded_by A ra ra' && @is_bounded_by B rb rb'
             | type.arrow s d => fun _ _ => false
             | type.list A
               => fun ls1 ls2
                  => match ls1 with
                     | Datatypes.None => true
                     | Datatypes.Some ls1 => fold_andb_map (@is_bounded_by A) ls1 ls2
                     end
             end.

        Lemma is_bounded_by_Some {t} r val
          : is_bounded_by (@Some t r) val = type.is_bounded_by r val.
        Proof using Type.
          induction t;
            repeat first [ reflexivity
                         | progress cbn in *
                         | progress destruct_head'_prod
                         | progress destruct_head' type.primitive
                         | match goal with H : _ |- _ => rewrite H end ].
          { lazymatch goal with
            | [ r : list (type.interp t), val : list (Compilers.type.interp t) |- _ ]
              => revert r val IHt
            end; intros r val; revert r val.
            induction r, val; cbn; auto with nocore; try congruence; [].
            intro H'; rewrite H', IHr by auto.
            reflexivity. }
        Qed.

        Lemma is_tighter_than_is_bounded_by {t} r1 r2 val
              (Htight : @is_tighter_than t r1 r2 = true)
              (Hbounds : is_bounded_by r1 val = true)
          : is_bounded_by r2 val = true.
        Proof using Type.
          induction t;
            repeat first [ progress destruct_head'_prod
                         | progress destruct_head'_and
                         | progress destruct_head' type.primitive
                         | progress cbn in *
                         | progress destruct_head' option
                         | solve [ eauto with nocore ]
                         | progress cbv [is_tighter_than_bool] in *
                         | progress rewrite ?Bool.andb_true_iff in *
                         | discriminate
                         | apply conj
                         | Z.ltb_to_lt; lia
                         | rewrite @fold_andb_map_map in * ].
          { lazymatch goal with
            | [ r1 : list (interp t), r2 : list (interp t), val : list (Compilers.type.interp t) |- _ ]
              => revert r1 r2 val Htight Hbounds IHt
            end; intros r1 r2 val; revert r1 r2 val.
            induction r1, r2, val; cbn; auto with nocore; try congruence; [].
            rewrite !Bool.andb_true_iff; intros; destruct_head'_and; split; eauto with nocore. }
        Qed.

        Lemma is_tighter_than_Some_is_bounded_by {t} r1 r2 val
              (Htight : @is_tighter_than t r1 (Some r2) = true)
              (Hbounds : is_bounded_by r1 val = true)
          : type.is_bounded_by r2 val = true.
        Proof using Type.
          rewrite <- is_bounded_by_Some.
          eapply is_tighter_than_is_bounded_by; eassumption.
        Qed.
      End option.
    End type.

    Module ident.
      Module option.
        Local Open Scope zrange_scope.

        Notation curry0 f
          := (fun 'tt => f).
        Notation curry2 f
          := (fun '(a, b) => f a b).
        Notation uncurry2 f
          := (fun a b => f (a, b)).
        Notation curry3 f
          := (fun '(a, b, c) => f a b c).

        (** do bounds analysis on identifiers; take in optional bounds
            on arguments, return optional bounds on outputs. *)
        Definition interp {s d} (idc : ident s d) : type.option.interp s -> type.option.interp d
          := match idc in ident.ident s d return type.option.interp s -> type.option.interp d with
             | ident.primitive type.Z v => fun _ => Some r[v ~> v]
             | ident.Let_In tx tC => fun '(x, C) => C x
             | ident.primitive _ _
             | ident.Nat_succ
             | ident.Nat_add
             | ident.Nat_sub
             | ident.Nat_mul
             | ident.Nat_max
             | ident.bool_rect _
             | ident.nat_rect _
             | ident.pred
             | ident.list_rect _ _
             | ident.List_nth_default _
             | ident.Z_pow
             | ident.Z_div
             | ident.Z_eqb
             | ident.Z_leb
             | ident.Z_of_nat
             | ident.Z_mul_split
             | ident.Z_add_get_carry
             | ident.Z_add_with_get_carry
             | ident.Z_sub_get_borrow
             | ident.Z_sub_with_get_borrow
             | ident.Z_modulo
             | ident.Z_rshi
             | ident.Z_cc_m
               => fun _ => type.option.None
             | ident.nil t => curry0 (Some (@nil (type.option.interp t)))
             | ident.cons t => curry2 (fun a => option_map (@Datatypes.cons (type.option.interp t) a))
             | ident.fst A B => @Datatypes.fst (type.option.interp A) (type.option.interp B)
             | ident.snd A B => @Datatypes.snd (type.option.interp A) (type.option.interp B)
             | ident.List_nth_default_concrete T d n
               => fun ls
                  => match ls with
                     | Datatypes.Some ls
                       => @nth_default (type.option.interp T) type.option.None ls n
                     | Datatypes.None
                       => type.option.None
                     end
             | ident.Z_shiftr _ as idc
             | ident.Z_shiftl _ as idc
             | ident.Z_opp as idc
             | ident.Z_cc_m_concrete _ as idc
               => option_map (ZRange.two_corners (ident.interp idc))
             | ident.Z_land mask
               => option_map
                    (fun r : zrange
                     => ZRange.land_bounds r r[mask~>mask])
             | ident.Z_add as idc
             | ident.Z_mul as idc
             | ident.Z_sub as idc
             | ident.Z.rshi_concrete _ _ as idc
               => fun '((x, y) : option zrange * option zrange)
                  => match x, y with
                     | Some x, Some y
                       => Some (ZRange.four_corners (uncurry2 (ident.interp idc)) x y)
                     | Some _, None | None, Some _ | None, None => None
                     end
             | ident.Z_cast range
               => fun r : option zrange
                  => Some match r with
                          | Some r => ZRange.intersection r range
                          | None => range
                          end
             | ident.Z_cast2 (r1, r2)
               => fun '((r1', r2') : option zrange * option zrange)
                  => (Some match r1' with
                           | Some r => ZRange.intersection r r1
                           | None => r1
                           end,
                      Some match r2' with
                           | Some r => ZRange.intersection r r2
                           | None => r2
                           end)
             | ident.Z_mul_split_concrete split_at
               => fun '((x, y) : option zrange * option zrange)
                  => match x, y with
                     | Some x, Some y
                       => type.option.Some
                            (t:=(type.Z*type.Z)%ctype)
                            (ZRange.split_bounds (ZRange.four_corners BinInt.Z.mul x y) split_at)
                     | Some _, None | None, Some _ | None, None => type.option.None
                     end
             | ident.Z_add_get_carry_concrete split_at
               => fun '((x, y) : option zrange * option zrange)
                  => match x, y with
                     | Some x, Some y
                       => type.option.Some
                            (t:=(type.Z*type.Z)%ctype)
                            (ZRange.split_bounds (ZRange.four_corners BinInt.Z.add x y) split_at)
                     | Some _, None | None, Some _ | None, None => type.option.None
                     end
             | ident.Z_add_with_carry
               => fun '((x, y, z) : option zrange * option zrange * option zrange)
                  => match x, y, z with
                     | Some x, Some y, Some z
                       => type.option.Some
                            (t:=type.Z)
                            (ZRange.eight_corners (fun x y z => (x + y + z)%Z) x y z)
                     | _, _, _ => type.option.None
                     end
             | ident.Z_add_with_get_carry_concrete split_at
               => fun '((x, y, z) : option zrange * option zrange * option zrange)
                  => match x, y, z with
                     | Some x, Some y, Some z
                       => type.option.Some
                            (t:=(type.Z*type.Z)%ctype)
                            (ZRange.split_bounds
                               (ZRange.eight_corners (fun x y z => (x + y + z)%Z) x y z)
                               split_at)
                     | _, _, _ => type.option.None
                     end
             | ident.Z_sub_get_borrow_concrete split_at
               => fun '((x, y) : option zrange * option zrange)
                  => match x, y with
                     | Some x, Some y
                       => type.option.Some
                            (t:=(type.Z*type.Z)%ctype)
                            (let b := ZRange.split_bounds (ZRange.four_corners BinInt.Z.sub x y) split_at in
                             (* N.B. sub_get_borrow returns - ((x - y) / split_at) as the borrow, so we need to negate *)
                             (fst b, ZRange.opp (snd b)))
                     | Some _, None | None, Some _ | None, None => type.option.None
                     end
             | ident.Z_sub_with_get_borrow_concrete split_at
               => fun '((x, y, z) : option zrange * option zrange * option zrange)
                  => match x, y, z with
                     | Some x, Some y, Some z
                       => type.option.Some
                            (t:=(type.Z*type.Z)%ctype)
                            (let b := ZRange.split_bounds (ZRange.eight_corners (fun x y z => (y - z - x)%Z) x y z) split_at in
                             (* N.B. sub_get_borrow returns - ((x - y) / split_at) as the borrow, so we need to negate *)
                               (fst b, ZRange.opp (snd b)))
                     | _, _, _ => type.option.None
                     end
             | ident.Z_zselect
               => fun '((x, y, z) : option zrange * option zrange * option zrange)
                  => match y, z with
                     | Some y, Some z => Some (ZRange.union y z)
                     | Some _, None | None, Some _ | None, None => None
                     end
             | ident.Z_add_modulo
               => fun '((x, y, z) : option zrange * option zrange * option zrange)
                  => match x, y, z with
                     | Some x, Some y, Some m
                       => Some (ZRange.union
                                  (ZRange.four_corners BinInt.Z.add x y)
                                  (ZRange.eight_corners (fun x y m => Z.max 0 (x + y - m))
                                                        x y m))
                     | _, _, _ => None
                     end
             end.
      End option.
    End ident.
  End ZRange.

  Module DefaultValue.
    (** This module provides "default" inhabitants for the
        interpretation of PHOAS types and for the PHOAS [expr] type.
        These values are used for things like [nth_default] and in
        other places where we need to provide a dummy value in cases
        that will never actually be reached in correctly used code. *)
    Module type.
      Module primitive.
        Definition default {t : type.primitive} : type.interp t
          := match t with
             | type.unit => tt
             | type.Z => (-1)%Z
             | type.nat => 0%nat
             | type.bool => true
             end.
      End primitive.
      Fixpoint default {t} : type.interp t
        := match t with
           | type.type_primitive x => @primitive.default x
           | type.prod A B => (@default A, @default B)
           | type.arrow s d => fun _ => @default d
           | type.list A => @nil (type.interp A)
           end.
    End type.

    Module expr.
      Section with_var.
        Context {var : type -> Type}.
        Fixpoint default {t : type} : @expr var t
          := match t with
             | type.type_primitive x
               => AppIdent (ident.primitive type.primitive.default) TT
             | type.prod A B
               => (@default A, @default B)
             | type.arrow s d => Abs (fun _ => @default d)
             | type.list A => AppIdent ident.nil TT
             end.
      End with_var.

      Definition Default {t} : Expr t := fun _ => default.
    End expr.
  End DefaultValue.

  Module GeneralizeVar.
    (** In both lazy and cbv evaluation strategies, reduction under
        lambdas is only done at the very end.  This means that if we
        have a computation which returns a PHOAS syntax tree, and we
        plug in two different values for [var], the computation is run
        twice.  This module provides a way of computing a
        representation of terms which does not suffer from this issue.
        By computing a flat representation, and then going back to
        PHOAS, the cbv strategy will fully compute the preceeding
        PHOAS passes only once, and the lazy strategy will share
        computation among the various uses of [var] (because there are
        no lambdas to get blocked on) and thus will also compute the
        preceeding PHOAS passes only once. *)
    Module Flat.
      Inductive expr : type -> Set :=
      | Var (t : type) (n : positive) : expr t
      | TT : expr type.unit
      | AppIdent {s d} (idc : ident s d) (arg : expr s) : expr d
      | App {s d} (f : expr (s -> d)) (x : expr s) : expr d
      | Pair {A B} (a : expr A) (b : expr B) : expr (A * B)
      | Abs (s : type) (n : positive) {d} (f : expr d) : expr (s -> d).
    End Flat.

    Definition ERROR {T} (v : T) : T. exact v. Qed.

    Fixpoint to_flat' {t} (e : @expr (fun _ => PositiveMap.key) t)
             (cur_idx : PositiveMap.key)
      : Flat.expr t
      := match e in expr.expr t return Flat.expr t with
         | Var t v => Flat.Var t v
         | TT => Flat.TT
         | AppIdent s d idc args
           => Flat.AppIdent idc (@to_flat' _ args cur_idx)
         | App s d f x => Flat.App
                            (@to_flat' _ f cur_idx)
                            (@to_flat' _ x cur_idx)
         | Pair A B a b => Flat.Pair
                             (@to_flat' _ a cur_idx)
                             (@to_flat' _ b cur_idx)
         | Abs s d f
           => Flat.Abs s cur_idx
                       (@to_flat'
                          d (f cur_idx)
                          (Pos.succ cur_idx))
         end.

    Fixpoint from_flat {t} (e : Flat.expr t)
      : forall var, PositiveMap.t { t : type & var t } -> @expr var t
      := match e in Flat.expr t return forall var, _ -> expr t with
         | Flat.Var t v
           => fun var ctx
              => match (tv <- PositiveMap.find v ctx;
                          type.try_transport var _ _ (projT2 tv))%option with
                 | Some v => Var v
                 | None => ERROR DefaultValue.expr.default
                 end
         | Flat.TT => fun _ _ => TT
         | Flat.AppIdent s d idc args
           => let args' := @from_flat _ args in
              fun var ctx => AppIdent idc (args' var ctx)
         | Flat.App s d f x
           => let f' := @from_flat _ f in
              let x' := @from_flat _ x in
              fun var ctx => App (f' var ctx) (x' var ctx)
         | Flat.Pair A B a b
           => let a' := @from_flat _ a in
              let b' := @from_flat _ b in
              fun var ctx => Pair (a' var ctx) (b' var ctx)
         | Flat.Abs s cur_idx d f
           => let f' := @from_flat d f in
              fun var ctx
              => Abs (fun v => f' var (PositiveMap.add cur_idx (existT _ s v) ctx))
         end.

    Definition to_flat {t} (e : expr t) : Flat.expr t
      := to_flat' e 1%positive.
    Definition ToFlat {t} (E : Expr t) : Flat.expr t
      := to_flat (E _).
    Definition FromFlat {t} (e : Flat.expr t) : Expr t
      := let e' := @from_flat t e in
         fun var => e' var (PositiveMap.empty _).
    Definition GeneralizeVar {t} (e : @expr (fun _ => PositiveMap.key) t) : Expr t
      := FromFlat (to_flat e).
  End GeneralizeVar.

  Module partial.
    Notation data := ZRange.type.option.interp.
    Section value.
      Context (var : type -> Type).
      Definition value_prestep (value : type -> Type) (t : type)
        := match t return Type with
           | type.prod A B as t => value A * value B
           | type.arrow s d => value s -> value d
           | type.list A => list (value A)
           | type.type_primitive _ as t
             => type.interp t
           end%type.
      Definition value_step (value : type -> Type) (t : type)
        := match t return Type with
           | type.arrow _ _ as t
             => value_prestep value t
           | type.prod _ _ as t
           | type.list _ as t
           | type.type_primitive _ as t
             => data t * @expr var t + value_prestep value t
           end%type.
      Fixpoint value (t : type)
        := value_step value t.

      Fixpoint value_default {t} : value t
        := match t return value t with
           | type.type_primitive type.Z
           | type.type_primitive _
             => inr DefaultValue.type.primitive.default
           | type.prod A B
             => inr (@value_default A, @value_default B)
           | type.arrow s d => fun _ => @value_default d
           | type.list A => inr (@nil (value A))
           end.

      Fixpoint data_from_value {t} : value t -> data t
        := match t return value t -> data t with
           | type.arrow _ _ as t
             => fun _ => ZRange.type.option.None
           | type.prod A B as t
             => fun v
                => match v with
                   | inl (data, _) => data
                   | inr (a, b)
                     => (@data_from_value A a, @data_from_value B b)
                   end
           | type.list A as t
             => fun v
                => match v with
                   | inl (data, _) => data
                   | inr ls
                     => Some (List.map (@data_from_value A) ls)
                   end
           | type.type_primitive type.Z as t
             => fun v
                => match v with
                   | inl (data, _) => data
                   | inr v => Some r[v~>v]%zrange
                   end
           | type.type_primitive _ as t
             => fun v
                => match v with
                   | inl (data, _) => data
                   | inr _ => ZRange.type.option.None
                   end
           end.
    End value.

    Module expr.
      Section reify.
        Context {var : type -> Type}.
        Fixpoint reify {t : type} {struct t}
          : value var t -> @expr var t
          := match t return value var t -> expr t with
             | type.prod A B as t
               => fun x : (data A * data B) * expr t + value var A * value var B
                  => match x with
                     | inl ((da, db), v)
                       => match A, B return data A -> data B -> expr (A * B) -> expr (A * B) with
                          | type.Z, type.Z
                            => fun da db v
                               => match da, db with
                                  | Some r1, Some r2
                                    => (ident.Z.cast2 (r1, r2)%core @@ v)%expr
                                  | _, _ => v
                                  end
                          | _, _ => fun _ _ v => v
                          end da db v
                     | inr (a, b) => (@reify A a, @reify B b)%expr
                     end
             | type.arrow s d
               => fun (f : value var s -> value var d)
                  => Abs (fun x
                          => @reify d (f (@reflect s (Var x))))
             | type.list A as t
               => fun x : _ * expr t + list (value var A)
                  => match x with
                     | inl (_, v) => v
                     | inr v => reify_list (List.map (@reify A) v)
                     end
             | type.type_primitive type.Z as t
               => fun x : _ * expr t + type.interp t
                  => match x with
                     | inl (Some r, v) => ident.Z.cast r @@ v
                     | inl (None, v) => v
                     | inr v => ident.primitive v @@ TT
                     end%core%expr
             | type.type_primitive _ as t
               => fun x : _ * expr t + type.interp t
                  => match x with
                     | inl (_, v) => v
                     | inr v => ident.primitive v @@ TT
                     end%core%expr
             end
        with reflect {t : type}
             : @expr var t -> value var t
             := match t return expr t -> value var t with
                | type.arrow s d
                  => fun (f : expr (s -> d)) (x : value var s)
                     => @reflect d (App f (@reify s x))
                | type.prod A B as t
                  => fun v : expr t
                     => let inr := @inr (data t * expr t) (value_prestep (value var) t) in
                        let inl := @inl (data t * expr t) (value_prestep (value var) t) in
                        match invert_Pair v with
                        | Some (a, b)
                          => inr (@reflect A a, @reflect B b)
                        | None
                          => inl
                               (match A, B return expr (A * B) -> data (A * B) * expr (A * B) with
                                | type.Z, type.Z
                                  => fun v
                                     => match invert_Z_cast2 v with
                                        | Some (r, v)
                                          => (ZRange.type.option.Some (t:=type.Z*type.Z) r, v)
                                        | None
                                          => (ZRange.type.option.None, v)
                                        end
                                | _, _ => fun v => (ZRange.type.option.None, v)
                                end v)
                        end
                | type.list A as t
                  => fun v : expr t
                     => let inr := @inr (data t * expr t) (value_prestep (value var) t) in
                        let inl := @inl (data t * expr t) (value_prestep (value var) t) in
                        match reflect_list v with
                        | Some ls
                          => inr (List.map (@reflect A) ls)
                        | None
                          => inl (None, v)
                        end
                | type.type_primitive type.Z as t
                  => fun v : expr t
                     => let inr' := @inr (data t * expr t) (value_prestep (value var) t) in
                        let inl' := @inl (data t * expr t) (value_prestep (value var) t) in
                        match reflect_primitive v, invert_Z_cast v with
                        | Some v, _ => inr' v
                        | None, Some (r, v) => inl' (Some r, v)
                        | None, None => inl' (None, v)
                        end
                | type.type_primitive _ as t
                  => fun v : expr t
                     => let inr := @inr (data t * expr t) (value_prestep (value var) t) in
                        let inl := @inl (data t * expr t) (value_prestep (value var) t) in
                        match reflect_primitive v with
                        | Some v => inr v
                        | None => inl (tt, v)
                        end
                end.
      End reify.
    End expr.

    Module ident.
      Section interp.
        Context (inline_var_nodes : bool)
                {var : type -> Type}.
        Fixpoint is_var_like {t} (e : @expr var t) : bool
          := match e with
             | Var t v => true
             | TT => true
             | AppIdent _ _ (ident.fst _ _) args => @is_var_like _ args
             | AppIdent _ _ (ident.snd _ _) args => @is_var_like _ args
             | AppIdent _ _ (ident.Z.cast _) args => @is_var_like _ args
             | AppIdent _ _ (ident.Z.cast2 _) args => @is_var_like _ args
             | Pair A B a b => @is_var_like A a && @is_var_like B b
             | AppIdent _ _ _ _ => false
             | App _ _ _ _
             | Abs _ _ _
               => false
             end.
        (** do partial evaluation on let-in, controlling what gets
            inlined and what doesn't *)
        Fixpoint interp_let_in {tC tx : type} {struct tx} : value var tx -> (value var tx -> value var tC) -> value var tC
          := match tx return value var tx -> (value var tx -> value var tC) -> value var tC with
             | type.arrow _ _
               => fun x f => f x
             | type.list T as t
               => fun (x : data t * expr t + list (value var T)) (f : data t * expr t + list (value var T) -> value var tC)
                  => match x with
                     | inr ls
                       => list_rect
                            (fun _ => (list (value var T) -> value var tC) -> value var tC)
                            (fun f => f nil)
                            (fun x _ rec f
                             => rec (fun ls => @interp_let_in
                                                 _ T x
                                                 (fun x => f (cons x ls))))
                            ls
                            (fun ls => f (inr ls))
                     | inl e => f (inl e)
                     end
             | type.prod A B as t
               => fun (x : data t * expr t + value var A * value var B) (f : data t * expr t + value var A * value var B -> value var tC)
                  => match x with
                     | inr (a, b)
                       => @interp_let_in
                            _ A a
                            (fun a
                             => @interp_let_in
                                  _ B b
                                  (fun b => f (inr (a, b))))
                     | inl (data, e)
                       => if inline_var_nodes && is_var_like e
                          then f x
                          else partial.expr.reflect
                                 (expr_let y := partial.expr.reify (t:=t) x in
                                      partial.expr.reify (f (inl (data, Var y)%core)))%expr
                     end
             | type.type_primitive _ as t
               => fun (x : data t * expr t + type.interp t) (f : data t * expr t + type.interp t -> value var tC)
                  => match x with
                     | inl (data, e)
                       => if inline_var_nodes && is_var_like e
                          then f x
                          else partial.expr.reflect
                                 (expr_let y := (partial.expr.reify (t:=t) x) in
                                      partial.expr.reify (f (inl (data, Var y)%core)))%expr
                     | inr v => f (inr v) (* FIXME: do not substitute [S (big stuck term)] *)
                     end
             end.

        Let default_interp
            {s d}
          : ident s d -> value var s -> value var d
          := match d return ident s d -> value var s -> value var d with
             | type.arrow _ _
               => fun idc args => expr.reflect (AppIdent idc (expr.reify args))
             | _
               => fun idc args
                  => inl (ZRange.ident.option.interp idc (data_from_value var args),
                          AppIdent idc (expr.reify args))
             end.

        (** do partial evaluation on identifiers *)
        Definition interp {s d} (idc : ident s d) : value var (s -> d)
          := match idc in ident s d return value var (s -> d) with
             | ident.Let_In tx tC as idc
               => fun (xf : data (tx * (tx -> tC)) * expr (tx * (tx -> tC)) + value var tx * value var (tx -> tC))
                  => match xf with
                     | inr (x, f) => interp_let_in x f
                     | _ => expr.reflect (AppIdent idc (expr.reify (t:=tx * (tx -> tC)) xf))
                     end
             | ident.nil t
               => fun _ => inr (@nil (value var t))
             | ident.primitive t v
               => fun _ => inr v
             | ident.cons t as idc
               => fun (x_xs : data (t * type.list t) * expr (t * type.list t) + value var t * (data (type.list t) * expr (type.list t) + list (value var t)))
                  => match x_xs return data (type.list t) * expr (type.list t) + list (value var t) with
                     | inr (x, inr xs) => inr (cons x xs)
                     | _
                       => default_interp idc x_xs
                     end
             | ident.fst A B as idc
               => fun x : data (A * B) * expr (A * B) + value var A * value var B
                  => match x with
                     | inr x => fst x
                     | _ => default_interp idc x
                     end
             | ident.snd A B as idc
               => fun x : data (A * B) * expr (A * B) + value var A * value var B
                  => match x with
                     | inr x => snd x
                     | _ => default_interp idc x
                     end
             | ident.bool_rect T as idc
               => fun (true_case_false_case_b : data ((type.unit -> T) * (type.unit -> T) * type.bool) * expr ((type.unit -> T) * (type.unit -> T) * type.bool) + (data ((type.unit -> T) * (type.unit -> T)) * expr ((type.unit -> T) * (type.unit -> T)) + (_ + Datatypes.unit -> value var T) * (_ + Datatypes.unit -> value var T)) * (data type.bool * expr type.bool + bool))
                  => match true_case_false_case_b with
                     | inr (inr (true_case, false_case), inr b)
                       => if b then true_case (inr tt) else false_case (inr tt)
                     | _ => default_interp idc true_case_false_case_b
                     end
             | ident.nat_rect P as idc
               => fun (O_case_S_case_n : _ * expr ((type.unit -> P) * (type.nat * P -> P) * type.nat) + (_ * expr ((type.unit -> P) * (type.nat * P -> P)) + (_ + Datatypes.unit -> value var P) * value var (type.nat * P -> P)) * (_ * expr type.nat + nat))
                  => match O_case_S_case_n with
                     | inr (inr (O_case, S_case), inr n)
                       => @nat_rect (fun _ => value var P)
                                    (O_case (inr tt))
                                    (fun n' rec => S_case (inr (inr n', rec)))
                                    n
                     | _ => default_interp idc O_case_S_case_n
                     end
             | ident.list_rect A P as idc
               => fun (nil_case_cons_case_ls : _ * expr ((type.unit -> P) * (A * type.list A * P -> P) * type.list A) + (_ * expr ((type.unit -> P) * (A * type.list A * P -> P)) + (_ + Datatypes.unit -> value var P) * value var (A * type.list A * P -> P)) * (_ * expr (type.list A) + list (value var A)))
                  => match nil_case_cons_case_ls with
                     | inr (inr (nil_case, cons_case), inr ls)
                       => @list_rect
                            (value var A)
                            (fun _ => value var P)
                            (nil_case (inr tt))
                            (fun x xs rec => cons_case (inr (inr (x, inr xs), rec)))
                            ls
                     | _ => default_interp idc nil_case_cons_case_ls
                     end
             | ident.List.nth_default type.Z as idc
               => fun (default_ls_idx : _ * expr (type.Z * type.list type.Z * type.nat) + (_ * expr (type.Z * type.list type.Z) + (_ * expr type.Z + type.interp type.Z) * (_ * expr (type.list type.Z) + list (value var type.Z))) * (_ * expr type.nat + nat))
                  => match default_ls_idx with
                     | inr (inr (default, inr ls), inr idx)
                       => List.nth_default default ls idx
                     | inr (inr (inr default, ls), inr idx)
                       => default_interp (ident.List.nth_default_concrete default idx) ls
                     | _ => default_interp idc default_ls_idx
                     end
             | ident.List.nth_default (type.type_primitive A) as idc
               => fun (default_ls_idx : _ * expr (A * type.list A * type.nat) + (_ * expr (A * type.list A) + (_ * expr A + type.interp A) * (_ * expr (type.list A) + list (value var A))) * (_ * expr type.nat + nat))
                  => match default_ls_idx with
                     | inr (inr (default, inr ls), inr idx)
                       => List.nth_default default ls idx
                     | inr (inr (inr default, ls), inr idx)
                       => default_interp (ident.List.nth_default_concrete default idx) ls
                     | _ => default_interp idc default_ls_idx
                     end
             | ident.List.nth_default A as idc
               => fun (default_ls_idx : _ * expr (A * type.list A * type.nat) + (_ * expr (A * type.list A) + value var A * (_ * expr (type.list A) + list (value var A))) * (_ * expr type.nat + nat))
                  => match default_ls_idx with
                     | inr (inr (default, inr ls), inr idx)
                       => List.nth_default default ls idx
                     | _ => default_interp idc default_ls_idx
                     end
             | ident.List.nth_default_concrete A default idx as idc
               => fun (ls : _ * expr (type.list A) + list (value var A))
                  => match ls with
                     | inr ls
                       => List.nth_default (expr.reflect (t:=A) (AppIdent (ident.primitive default) TT)) ls idx
                     | _ => default_interp idc ls
                     end
             | ident.Z_mul_split as idc
               => fun (x_y_z :  (_ * expr (type.Z * type.Z * type.Z) +
                                 (_ * expr (type.Z * type.Z) + (_ * expr type.Z + Z) * (_ * expr type.Z + Z)) * (_ * expr type.Z + Z))%type)
                  => match x_y_z return (_ * expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) with
                     | inr (inr (inr x, inr y), inr z) =>
                       let result := ident.interp idc (x, y, z) in
                       inr (inr (fst result), inr (snd result))
                     | inr (inr (inr x, y), z)
                       => let default _ := default_interp (ident.Z.mul_split_concrete x) (inr (y, z)) in
                          match (y, z) with
                          | (inr xx, inl (data, e) as y)
                          | (inl (data, e) as y, inr xx)
                            => if Z.eqb xx 0
                               then inr (inr 0%Z, inr 0%Z)
                               else if Z.eqb xx 1
                                    then inr (y, inr 0%Z)
                                    else if Z.eqb xx (-1)
                                         then inr (inl (data, AppIdent ident.Z.opp (expr.reify (t:=type.Z) y)), inr 0%Z)
                                         else default tt
                          | _ => default tt
                          end
                     | _ => default_interp idc x_y_z
                     end
             | ident.Z_rshi as idc
               => fun (x_y_z_a :
                         (_ * expr (_ * _ * _ * _) + (_ * expr (_ * _ * _) + (_ * expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) *  (_ * expr _ + type.interp _)) * (_ * expr _ + type.interp _))%type)
                  => match x_y_z_a return _ * expr _ + type.interp _ with
                     | inr (inr (inr (inr x, inr y), inr z), inr a) => inr (ident.interp idc (x, y, z, a))
                     | inr (inr (inr (inr x, y), z), inr a)
                       => default_interp (ident.Z.rshi_concrete x a) (inr (y, z))
                     | _ => default_interp idc x_y_z_a
                     end
             | ident.Z_cc_m as idc
               => fun (x_y : data (_ * _) * expr (_ * _) + (_ + type.interp _) * (_ + type.interp _))
                  => match x_y return _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | inr (inr x, y)
                       => default_interp (ident.Z.cc_m_concrete x) y
                     | _ => default_interp idc x_y
                     end
             | ident.Z_add_get_carry as idc
               => fun (x_y_z :  (_ * expr (type.Z * type.Z * type.Z) +
                                 (_ * expr (type.Z * type.Z) + (_ * expr type.Z + Z) * (_ * expr type.Z + Z)) * (_ * expr type.Z + Z))%type)
                  => match x_y_z return (_ * expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) with
                     | inr (inr (inr x, inr y), inr z) =>
                       let result := ident.interp idc (x, y, z) in
                       inr (inr (fst result), inr (snd result))
                     | inr (inr (inr x, y), z)
                       => let default _ := default_interp (ident.Z.add_get_carry_concrete x) (inr (y, z)) in
                          match (y, z) with
                          | (inr xx, inl e)
                          | (inl e, inr xx)
                            => if Z.eqb xx 0
                               then inr (inl e, inr 0%Z)
                               else default tt
                          | _ => default tt
                          end
                     | _ => default_interp idc x_y_z
                     end
             | ident.Z_add_with_carry as idc
               => fun (x_y_z :  (_ * expr (type.Z * type.Z * type.Z) +
                                 (_ * expr (type.Z * type.Z) + (_ * expr type.Z + Z) * (_ * expr type.Z + Z)) * (_ * expr type.Z + Z))%type)
                  => match x_y_z return ( _ * expr _ + type.interp _) with
                     | inr (inr (inr x, inr y), inr z) => inr (ident.interp idc (x, y, z))
                     | inr (inr (inr x, y), z)
                       => if Z.eqb x 0 then default_interp (ident.Z.add) (inr (y,z)) else default_interp idc x_y_z
                     | _ => default_interp idc x_y_z
                     end
             | ident.Z_add_with_get_carry as idc
               => fun (x_y_z_a : (_ * expr (_ * _ * _ * _) +
                                  (_ * expr (_ * _ * _) +
                                   (_ * expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) *
                                   (_ * expr _ + type.interp _)) * (_ * expr _ + type.interp _))%type)
                  => match x_y_z_a return (_ * expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) with
                     | inr (inr (inr (inr x, inr y), inr z), inr a) =>
                       let result := ident.interp idc (x, y, z, a) in
                       inr (inr (fst result), inr (snd result))
                     | inr (inr (inr (inr x, y), z), a)
                       =>
                       let default _ := default_interp (ident.Z.add_with_get_carry_concrete x) (inr (inr (y, z), a)) in
                       let default_add _ := default_interp (ident.Z.add_get_carry_concrete x) (inr (z,a)) in
                       let default_adx _ := default_interp (ident.Z.add_with_carry) (inr (inr (y, z), a)) in
                       match y, z, a with
                       | inr cc, inr xx, inl e
                       | inr cc, inl e, inr xx
                         => if Z.eqb cc 0
                            then if Z.eqb xx 0
                                 then inr (inl e, inr 0%Z)
                                 else default_add tt (* carry = 0: ADC x y -> ADD x y *)
                            else default tt
                       | inr cc, inl xx, inl yy
                         => if Z.eqb cc 0
                            then default_add tt (* carry = 0: ADC x y -> ADD x y *)
                            else default tt
                       | inl _, inr xx, inr yy
                         => if Z.eqb xx 0
                            then if Z.eqb yy 0
                                 then inr (default_adx tt, inr 0%Z) (* ADC 0 0 -> (ADX 0 0, 0) *)
                                 else default tt
                            else default tt
                        | _, _, _ => default tt
                       end
                     | _ => default_interp idc x_y_z_a
                     end
             | ident.Z_sub_get_borrow as idc
               => fun (x_y_z :  (_ * expr (type.Z * type.Z * type.Z) +
                                 (_ * expr (type.Z * type.Z) + (_ * expr type.Z + Z) * (_ * expr type.Z + Z)) * (_ * expr type.Z + Z))%type)
                  => match x_y_z return (_ * expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) with
                     | inr (inr (inr x, inr y), inr z) =>
                       let result := ident.interp idc (x, y, z) in
                       inr (inr (fst result), inr (snd result))
                     | inr (inr (inr x, y), z)
                       => default_interp (ident.Z.sub_get_borrow_concrete x) (inr (y, z))
                     | _ => default_interp idc x_y_z
                     end
             | ident.Z_sub_with_get_borrow as idc
               => fun (x_y_z_a : (_ * expr (_ * _ * _ * _) + (_ * expr (_ * _ * _) + (_ * expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) * (_ * expr _ + type.interp _)) * (_ * expr _ + type.interp _))%type)
                  => match x_y_z_a return (_ * expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) with
                     | inr (inr (inr (inr x, inr y), inr z), inr a) =>
                       let '(r, b) := ident.interp idc (x, y, z, a) in
                       inr (inr r, inr b)
                     | inr (inr (inr (inr x, y), z), a)
                       => default_interp (ident.Z.sub_with_get_borrow_concrete x) (inr (inr (y, z), a))
                     | _ => default_interp idc x_y_z_a
                     end
             | ident.Z_mul_split_concrete _ as idc
             | ident.Z.sub_get_borrow_concrete _ as idc
               => fun (x_y : _ * expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => let default _ := default_interp idc x_y in
                     match x_y return (_ * expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) with
                     | inr (inr x, inr y) =>
                       let result := ident.interp idc (x, y) in
                       inr (inr (fst result), inr (snd result))
                     | _ => default tt
                     end
             | ident.Z.add_get_carry_concrete _ as idc
               => fun (x_y : _ * expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => let default _ := default_interp idc x_y in
                     match x_y return (_ * expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) with
                     | inr (inr x, inr y) =>
                       let result := ident.interp idc (x, y) in
                       inr (inr (fst result), inr (snd result))
                     | inr (inr x, inl e)
                     | inr (inl e, inr x) =>
                       if Z.eqb x 0%Z
                       then inr (inl e, inr 0%Z)
                       else default tt
                     | _ => default tt
                     end
             | ident.Z.add_with_get_carry_concrete _ as idc
             | ident.Z.sub_with_get_borrow_concrete _ as idc
               => fun (x_y_z :
                         (_ * expr (type.Z * type.Z * type.Z) + (_ * expr (type.Z * type.Z) + (_ * expr type.Z + Z) * (_ * expr type.Z + Z)) * (_ * expr type.Z + Z))%type)
                  => match x_y_z return (_ * expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) with
                     | inr (inr (inr x, inr y), inr z) =>
                       let result := ident.interp idc (x, y, z) in
                       inr (inr (fst result), inr (snd result))
                     | _ => default_interp idc x_y_z
                     end
             | ident.pred as idc
             | ident.Nat_succ as idc
               => fun x : _ * expr _ + type.interp _
                  => match x return _ * expr _ + type.interp _ with
                     | inr x => inr (ident.interp idc x)
                     | _ => default_interp idc x
                     end
             | ident.Z_of_nat as idc
               => fun x : _ * expr _ + type.interp _
                  => match x return _ * expr _ + type.interp _ with
                     | inr x => inr (ident.interp idc x)
                     | _ => default_interp idc x
                     end
             | ident.Z_opp as idc
               => fun x : _ * expr _ + type.interp _
                  => match x return _ * expr _ + type.interp _ with
                     | inr x => inr (ident.interp idc x)
                     | inl (r, x)
                       => match invert_Z_opp x with
                          | Some x => inl (r, x)
                          | None => inl (ZRange.ident.option.interp idc r, AppIdent idc x)
                          end
                     end
             | ident.Z_shiftr _ as idc
             | ident.Z_shiftl _ as idc
             | ident.Z_land _ as idc
             | ident.Z_cc_m_concrete _ as idc
               => fun x : _ * expr _ + type.interp _
                  => match x return _ * expr _ + type.interp _ with
                     | inr x => inr (ident.interp idc x)
                     | inl (data, e)
                       => inl (ZRange.ident.option.interp idc data,
                               AppIdent idc (expr.reify (t:=type.Z) x))
                     end
             | ident.Nat_add as idc
             | ident.Nat_sub as idc
             | ident.Nat_mul as idc
             | ident.Nat_max as idc
             | ident.Z_eqb as idc
             | ident.Z_leb as idc
             | ident.Z_pow as idc
             | ident.Z_rshi_concrete _ _ as idc
               => fun (x_y : data (_ * _) * expr (_ * _) + (_ + type.interp _) * (_ + type.interp _))
                  => match x_y return _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | _ => default_interp idc x_y
                     end
             | ident.Z_div as idc
               => fun (x_y : _ * expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => let default _ := default_interp idc x_y in
                     match x_y return _ * expr _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | inr (x, inr y)
                       => if Z.eqb y (2^Z.log2 y)
                          then default_interp (ident.Z.shiftr (Z.log2 y)) x
                          else default tt
                     | _ => default tt
                     end
             | ident.Z_modulo as idc
               => fun (x_y : _ * expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => let default _ := default_interp idc x_y in
                     match x_y return _ * expr _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | inr (x, inr y)
                       => if Z.eqb y (2^Z.log2 y)
                          then default_interp (ident.Z.land (y-1)) x
                          else default tt
                     | _ => default tt
                     end
             | ident.Z_mul as idc
               => fun (x_y : _ * expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => let default _ := default_interp idc x_y in
                     match x_y return _ * expr _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | inr (inr x, inl (data, e) as y)
                     | inr (inl (data, e) as y, inr x)
                       => let data' _ := ZRange.ident.option.interp idc (data, Some r[x~>x]%zrange) in
                          if Z.eqb x 0
                          then inr 0%Z
                          else if Z.eqb x 1
                               then y
                               else if Z.eqb x (-1)
                                    then inl (data' tt, AppIdent ident.Z.opp (expr.reify (t:=type.Z) y))
                                    else if Z.eqb x (2^Z.log2 x)
                                         then inl (data' tt,
                                                   AppIdent (ident.Z.shiftl (Z.log2 x)) (expr.reify (t:=type.Z) y))
                                         else inl (data' tt,
                                                   AppIdent idc (ident.primitive (t:=type.Z) x @@ TT, expr.reify (t:=type.Z) y))
                     | inr (inl (dataa, a), inl (datab, b))
                       => inl (ZRange.ident.option.interp idc (dataa, datab),
                               AppIdent idc (a, b))
                     | inl _ => default tt
                     end
             | ident.Z_add as idc
               => fun (x_y : _ * expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => let default0 _ := AppIdent idc (expr.reify (t:=_*_) x_y) in
                     let default _ := expr.reflect (default0 tt) in
                     match x_y return _ * expr _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | inr (inr x, inl (data, e) as y)
                     | inr (inl (data, e) as y, inr x)
                       => let data' _ := ZRange.ident.option.interp idc (data, Some r[x~>x]%zrange) in
                          if Z.eqb x 0
                          then y
                          else inl (data' tt,
                                    match invert_Z_opp e with
                                    | Some e => AppIdent
                                                  ident.Z.sub
                                                  (ident.primitive (t:=type.Z) x @@ TT,
                                                   e)
                                    | None => default0 tt
                                    end)
                     | inr (inl (dataa, a), inl (datab, b))
                       => inl (ZRange.ident.option.interp idc (dataa, datab),
                               match invert_Z_opp a, invert_Z_opp b with
                               | Some a, Some b
                                 => AppIdent
                                      ident.Z.opp
                                      (idc @@ (a, b))
                               | Some a, None
                                 => AppIdent ident.Z.sub (b, a)
                               | None, Some b
                                 => AppIdent ident.Z.sub (a, b)
                               | None, None => default0 tt
                               end)
                     | inl _ => default tt
                     end
             | ident.Z_sub as idc
               => fun (x_y : _ * expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => let default0 _ := AppIdent idc (expr.reify (t:=_*_) x_y) in
                     let default _ := expr.reflect (default0 tt) in
                     match x_y return _ * expr _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | inr (inr x, inl (data, e))
                       => let data' _ := ZRange.ident.option.interp idc (Some r[x~>x]%zrange, data) in
                          if Z.eqb x 0
                          then inl (data' tt, AppIdent ident.Z.opp e)
                          else inl (data' tt, default0 tt)
                     | inr (inl (data, e), inr x)
                       => let data' _ := ZRange.ident.option.interp idc (data, Some r[x~>x]%zrange) in
                          if Z.eqb x 0
                          then inl (data' tt, e)
                          else inl (data' tt, default0 tt)
                     | inr (inl (dataa, a), inl (datab, b))
                       => inl (ZRange.ident.option.interp idc (dataa, datab),
                               match invert_Z_opp a, invert_Z_opp b with
                               | Some a, Some b
                                 => AppIdent
                                      ident.Z.opp
                                      (idc @@ (a, b))
                               | Some a, None
                                 => AppIdent ident.Z.add (b, a)
                               | None, Some b
                                 => AppIdent ident.Z.add (a, b)
                               | None, None => default0 tt
                               end)
                     | inl _ => default tt
                     end
             | ident.Z_zselect as idc
             | ident.Z_add_modulo as idc
               => fun (x_y_z :  (_ * expr (_ * _ * _) +
                                 (_ * expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) * (_ * expr _ + type.interp _))%type)
                  => match x_y_z return _ * expr _ + type.interp _ with
                     | inr (inr (inr x, inr y), inr z) => inr (ident.interp idc (x, y, z))
                     | _ => default_interp idc x_y_z
                     end
             | ident.Z_cast r as idc
               => fun (x : _ * expr _ + type.interp _)
                  => match x with
                     | inr x => inr (ident.interp idc x)
                     | inl (data, e)
                       => inl (ZRange.ident.option.interp idc data, e)
                     end
             | ident.Z_cast2 (r1, r2) as idc
               => fun (x : _ * expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => match x with
                     | inr (inr a, inr b)
                       => inr (inr (ident.interp (ident.Z.cast r1) a),
                               inr (ident.interp (ident.Z.cast r2) b))
                     | inr (inr a, inl (r2', b))
                       => inr (inr (ident.interp (ident.Z.cast r1) a),
                               inl (ZRange.ident.option.interp (ident.Z.cast r2) r2', b))
                     | inr (inl (r1', a), inr b)
                       => inr (inl (ZRange.ident.option.interp (ident.Z.cast r1) r1', a),
                               inr (ident.interp (ident.Z.cast r2) b))
                     | inr (inl (r1', a), inl (r2', b))
                       => inr (inl (ZRange.ident.option.interp (ident.Z.cast r1) r1', a),
                               inl (ZRange.ident.option.interp (ident.Z.cast r2) r2', b))
                     | inl (data, e)
                       => inl (ZRange.ident.option.interp idc data, e)
                     end
           end.
      End interp.
    End ident.

    Module bounds.
      Section with_var.
        Context {var : type -> Type}.

        Fixpoint extend_concrete_list_with_obounds {t}
                 (extend_with_obounds : ZRange.type.option.interp t -> partial.value var t -> partial.value var t )
                 (ls : list (ZRange.type.option.interp t))
                 (e : list (partial.value var t))
                 {struct ls}
          : list (partial.value var t)
          := match ls with
             | nil => nil
             | cons b bs
               => cons (extend_with_obounds
                          b
                          (hd (partial.value_default _) e))
                       (@extend_concrete_list_with_obounds
                          t extend_with_obounds bs (tl e))
             end.

        Fixpoint extend_list_expr_with_obounds {t}
                 (extend_with_obounds : ZRange.type.primitive.option.interp t -> partial.value var t -> partial.value var t )
                 (starting_index : nat)
                 (ls : list (ZRange.type.option.interp t))
                 (e : @expr var (type.list t))
                 {struct ls}
          : list (partial.value var t)
          := match ls with
             | nil => nil
             | cons b bs
               => cons (extend_with_obounds
                          b
                          (partial.expr.reflect
                             (AppIdent
                                (ident.List_nth_default_concrete
                                   DefaultValue.type.default starting_index)
                                e)))
                       (@extend_list_expr_with_obounds
                          t extend_with_obounds (S starting_index) bs e)
             end.

        Fixpoint extend_with_obounds {t} : ZRange.type.option.interp t -> partial.value var t -> partial.value var t
          := match t return ZRange.type.option.interp t -> partial.value var t -> partial.value var t with
             | type.type_primitive type.Z
               => fun (r : option zrange) (e : option zrange * expr _ + type.interp _)
                  => match r, e with
                     | Some r, inr v => inr (default.ident.interp (ident.Z.cast r) v)
                     | Some r, inl (data, e)
                       => inl (ZRange.ident.option.interp (ident.Z.cast r) data, e)
                     | None, e => e
                     end
             | type.type_primitive _t => fun _ => id
             | type.prod A B
               => fun '((ra, rb) : ZRange.type.option.interp A * ZRange.type.option.interp B)
                      (e : _ * expr _ + partial.value var A * partial.value var B)
                  => match e with
                     | inr (a, b)
                       => inr (@extend_with_obounds A ra a,
                               @extend_with_obounds B rb b)
                     | inl ((dataa, datab), e)
                       => if partial.ident.is_var_like e
                          then inr (@extend_with_obounds A ra (partial.expr.reflect (AppIdent ident.fst e)),
                                    @extend_with_obounds B rb (partial.expr.reflect (AppIdent ident.snd e)))
                          else inl
                                 (match A, B return ZRange.type.option.interp A  -> ZRange.type.option.interp B -> data A -> data B -> expr (A * B) -> data (A * B) * expr (A * B) with
                                  | type.Z, type.Z
                                    => fun ra rb da db e
                                       => let da'
                                              := match ra with
                                                 | Some ra
                                                   => ZRange.ident.option.interp
                                                        (ident.Z.cast ra) da
                                                 | None => da
                                                 end in
                                          let db'
                                              := match rb with
                                                 | Some rb
                                                   => ZRange.ident.option.interp
                                                        (ident.Z.cast rb) db
                                                 | None => db
                                                 end in
                                          ((da', db'), e)
                                  | _, _
                                    => fun _ _ da db e => ((da, db), e)
                                  end ra rb dataa datab e)
                     end
             | type.arrow s d => fun _ => id
             | type.list A
               => fun (ls : option (Datatypes.list (ZRange.type.option.interp A)))
                      (e : data _ * expr _ + list (partial.value var A))
                  => match ls with
                     | None => e
                     | Some ls
                       =>
                       match e with
                       | inl (data, e)
                         => match A return (ZRange.type.option.interp A -> partial.value var A -> partial.value var A)
                                           -> Datatypes.list (ZRange.type.option.interp A)
                                           -> option (Datatypes.list (ZRange.type.option.interp A))
                                           -> expr (type.list A)
                                           -> partial.value var (type.list A)
                            with
                            | type.type_primitive A
                              => fun extend_with_obounds ls data e
                                 => match data with
                                    | Some data
                                      => inr
                                           (extend_concrete_list_with_obounds
                                              extend_with_obounds ls
                                              (extend_list_expr_with_obounds
                                                 extend_with_obounds 0 data e))
                                    | None
                                      => inr (extend_list_expr_with_obounds
                                                extend_with_obounds 0 ls e)
                                    end
                            | _A'
                                (* N.B. We clobber the existing bounds here, rather than fusing them *)
                              => fun _ ls data e => inl (Some ls, e)
                            end (@extend_with_obounds A) ls data e
                       | inr e => inr (extend_concrete_list_with_obounds
                                         (@extend_with_obounds A) ls e)
                       end
                     end
             end.
        Definition extend_with_bounds {t}
                   (b : ZRange.type.interp t)
                   (e : partial.value var t)
          : partial.value var t
          := @extend_with_obounds t (ZRange.type.option.Some b) e.
      End with_var.

      Module ident.
        Definition extract {s d} (idc : ident s d) : ZRange.type.option.interp s -> ZRange.type.option.interp d
          := match idc in ident s d return ZRange.type.option.interp s -> ZRange.type.option.interp d with
             | ident.Let_In tx tC
               => fun '((x, f) : ZRange.type.option.interp tx * (ZRange.type.option.interp tx -> ZRange.type.option.interp tC))
                  => f x
             | ident.Z_cast range => fun _ => Some range
             | ident.Z_cast2 (r1, r2) => fun _ => (Some r1, Some r2)
             | ident.primitive type.Z v
               => fun _ => Some r[v~>v]%zrange
             | ident.nil _ => fun _ => Some nil
             | ident.cons t
               => fun '((x, xs) : ZRange.type.option.interp t * option (list (ZRange.type.option.interp t)))
                  => option_map (cons x) xs
             | _ => fun _ => ZRange.type.option.None
             end.
      End ident.

      Module expr.
        Section with_var.
          Context {var : type -> Type}
                  (fill_var : forall t, ZRange.type.option.interp t -> var t).
          Fixpoint extract' {t} (e : @expr var t) : ZRange.type.option.interp t
            := match e in expr.expr t return ZRange.type.option.interp t with
               | Var _ _
               | TT
                 => ZRange.type.option.None
               | AppIdent s d idc args => ident.extract idc (@extract' s args)
               | App s d f x => @extract' _ f (@extract' s x)
               | Pair A B a b => (@extract' A a, @extract' B b)
               | Abs s d f => fun bs : ZRange.type.option.interp s
                              => @extract' d (f (fill_var s bs))
               end.
        End with_var.

        Definition extract {t} (e : expr t) : ZRange.type.option.interp t
          := extract' (fun _ => id) e.

        Definition Extract {t} (e : Expr t) : ZRange.type.option.interp t
          := extract (e _).
      End expr.
    End bounds.
  End partial.

  Section partial_evaluate.
    Context (inline_var_nodes : bool)
            {var : type -> Type}.

    Definition partial_evaluate'_step
               (partial_evaluate' : forall {t} (e : @expr (partial.value var) t),
                   partial.value var t)
               {t} (e : @expr (partial.value var) t)
      : partial.value var t
      := match e in expr.expr t return partial.value var t with
         | Var t v => v
         | TT => inr tt
         | AppIdent s d idc args => partial.ident.interp inline_var_nodes idc (@partial_evaluate' _ args)
         | Pair A B a b => inr (@partial_evaluate' A a, @partial_evaluate' B b)
         | App s d f x => @partial_evaluate' _ f (@partial_evaluate' _ x)
         | Abs s d f => fun x => @partial_evaluate' d (f x)
         end.
    Fixpoint partial_evaluate' {t} (e : @expr (partial.value var) t)
      : partial.value var t
      := @partial_evaluate'_step (@partial_evaluate') t e.

    Definition partial_evaluate {t} (e : @expr (partial.value var) t) : @expr var t
      := partial.expr.reify (@partial_evaluate' t e).

    Definition partial_evaluate_with_bounds1' {s d} (e : @expr (partial.value var) (s -> d))
               (b : ZRange.type.option.interp s)
      : partial.value var (s -> d)
      := fun x : partial.value var s
         => partial_evaluate' e (partial.bounds.extend_with_obounds b x).

    Definition partial_evaluate_with_bounds1 {s d} (e : @expr (partial.value var) (s -> d))
               (b : ZRange.type.option.interp s)
      := partial.expr.reify (@partial_evaluate_with_bounds1' s d e b).

  End partial_evaluate.

  Definition PartialEvaluate (inline_var_nodes : bool) {t} (e : Expr t) : Expr t
    := fun var => @partial_evaluate inline_var_nodes var t (e _).

  Module RelaxZRange.
    Module ident.
      Section relax.
        Context (relax_zrange : zrange -> option zrange)
                {var : type -> Type}.

        Definition relax {s d} (idc : ident s d) : @expr var s -> @expr var d
          := match idc in ident s d return expr s -> expr d with
             | ident.Z_cast range
               => match relax_zrange range with
                  | Some r => AppIdent (ident.Z.cast r)
                  | None => id
                  end
             | ident.Z_cast2 (r1, r2)
               => match relax_zrange r1, relax_zrange r2 with
                  | Some r1, Some r2
                    => AppIdent (ident.Z.cast2 (r1, r2))
                  | Some _, None | None, Some _ | None, None => id
                  end
             | idc => AppIdent idc
             end.
      End relax.
    End ident.

    Module expr.
      Section relax.
        Context (relax_zrange : zrange -> option zrange).
        Section with_var.
          Context {var : type -> Type}.

          Fixpoint relax {t} (e : @expr var t) : @expr var t
            := match e with
               | Var t v => Var v
               | TT => TT
               | AppIdent s d idc args => @ident.relax relax_zrange var s d idc
                                                       (@relax s args)
               | App s d f x => App (@relax _ f) (@relax _ x)
               | Pair A B a b => Pair (@relax A a) (@relax B b)
               | Abs s d f => Abs (fun v => @relax d (f v))
               end.
        End with_var.

        Definition Relax {t} (e : Expr t) : Expr t
          := fun var => relax (e _).
      End relax.
    End expr.
  End RelaxZRange.

  Definition PartialEvaluateWithBounds1
             {s d} (e : Expr (s -> d)) (b : ZRange.type.option.interp s)
    : Expr (s -> d)
    := fun var => @partial_evaluate_with_bounds1 true var s d (e _) b.

  Definition CheckPartialEvaluateWithBounds1
             (relax_zrange : zrange -> option zrange)
             {s d} (E : Expr (s -> d))
             (b_in : ZRange.type.option.interp s)
             (b_out : ZRange.type.option.interp d)
    : Expr (s -> d) + (ZRange.type.option.interp d * Expr (s -> d))
    := let b_computed := partial.bounds.expr.Extract E b_in in
       if ZRange.type.option.is_tighter_than b_computed b_out
       then @inl (Expr (s -> d)) _ (RelaxZRange.expr.Relax relax_zrange E)
       else @inr _ (ZRange.type.option.interp d * Expr (s -> d)) (b_computed, E).

  Definition CheckPartialEvaluateWithBounds0
             (relax_zrange : zrange -> option zrange)
             {t} (E : Expr t)
             (b_out : ZRange.type.option.interp t)
    : Expr t + (ZRange.type.option.interp t * Expr t)
    := let b_computed := partial.bounds.expr.Extract E in
       if ZRange.type.option.is_tighter_than b_computed b_out
       then @inl (Expr t) _ (RelaxZRange.expr.Relax relax_zrange E)
       else @inr _ (ZRange.type.option.interp t * Expr t) (b_computed, E).

  Definition CheckedPartialEvaluateWithBounds1
             (relax_zrange : zrange -> option zrange)
             {s d} (e : Expr (s -> d))
             (b_in : ZRange.type.option.interp s)
             (b_out : ZRange.type.option.interp d)
    : Expr (s -> d) + (ZRange.type.option.interp d * Expr (s -> d))
    := let E := PartialEvaluateWithBounds1 e b_in in
       dlet_nd e := GeneralizeVar.ToFlat E in
             let E := GeneralizeVar.FromFlat e in
             CheckPartialEvaluateWithBounds1 relax_zrange E b_in b_out.

  Definition CheckedPartialEvaluateWithBounds0
             (relax_zrange : zrange -> option zrange)
             {t} (e : Expr t)
             (b_out : ZRange.type.option.interp t)
    : Expr t + (ZRange.type.option.interp t * Expr t)
    := let E := PartialEvaluate true e in
       dlet_nd e := GeneralizeVar.ToFlat E in
             let E := GeneralizeVar.FromFlat e in
             CheckPartialEvaluateWithBounds0 relax_zrange E b_out.

  Axiom admit_pf : False.
  Local Notation admit := (match admit_pf with end).

  Theorem CheckedPartialEvaluateWithBounds1_Correct
          (relax_zrange : zrange -> option zrange)
          (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                   -> relax_zrange r = Some r'
                                   -> is_tighter_than_bool z r' = true)
          {s d} (e : Expr (s -> d))
          (b_in : ZRange.type.option.interp s)
          (b_out : ZRange.type.option.interp d)
          rv (Hrv : CheckedPartialEvaluateWithBounds1 relax_zrange e b_in b_out = inl rv)
    : forall arg
             (Harg : ZRange.type.option.is_bounded_by b_in arg = true),
      Interp rv arg = Interp e arg
      /\ ZRange.type.option.is_bounded_by b_out (Interp rv arg) = true.
  Proof using Type.
    cbv [CheckedPartialEvaluateWithBounds1 CheckPartialEvaluateWithBounds1 Let_In] in *;
      break_innermost_match_hyps; inversion_sum; subst.
    intros arg Harg.
    split.
    { exact admit. (* correctness of interp *) }
    { eapply ZRange.type.option.is_tighter_than_is_bounded_by; [ eassumption | ].
      cbv [expr.Interp].
      revert Harg.
      exact admit. (* boundedness *) }
  Qed.

  Theorem CheckedPartialEvaluateWithBounds0_Correct
          (relax_zrange : zrange -> option zrange)
          (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                   -> relax_zrange r = Some r'
                                   -> is_tighter_than_bool z r' = true)
          {t} (e : Expr t)
          (b_out : ZRange.type.option.interp t)
          rv (Hrv : CheckedPartialEvaluateWithBounds0 relax_zrange e b_out = inl rv)
    : Interp rv = Interp e
      /\ ZRange.type.option.is_bounded_by b_out (Interp rv) = true.
  Proof using Type.
    cbv [CheckedPartialEvaluateWithBounds0 CheckPartialEvaluateWithBounds0 Let_In] in *;
      break_innermost_match_hyps; inversion_sum; subst.
    split.
    { exact admit. (* correctness of interp *) }
    { eapply ZRange.type.option.is_tighter_than_is_bounded_by; [ eassumption | ].
      cbv [expr.Interp].
      exact admit. (* boundedness *) }
  Qed.

  Module DeadCodeElimination.
    Fixpoint compute_live' {t} (e : @expr (fun _ => PositiveSet.t) t) (cur_idx : positive)
    : positive * PositiveSet.t
      := match e with
         | Var t v => (cur_idx, v)
         | TT => (cur_idx, PositiveSet.empty)
         | AppIdent s d idc args
           => let default _ := @compute_live' _ args cur_idx in
              match args in expr.expr t return ident.ident t d -> _ with
              | Pair A B x (Abs s d f)
                => fun idc
                   => match idc with
                      | ident.Let_In _ _
                        => let '(idx, live) := @compute_live' A x cur_idx in
                           let '(_, live) := @compute_live' _ (f (PositiveSet.add idx live)) (Pos.succ idx) in
                           (Pos.succ idx, live)
                      | _ => default tt
                      end
              | _ => fun _ => default tt
              end idc
         | App s d f x
           => let '(idx, live1) := @compute_live' _ f cur_idx in
              let '(idx, live2) := @compute_live' _ x idx in
              (idx, PositiveSet.union live1 live2)
         | Pair A B a b
           => let '(idx, live1) := @compute_live' A a cur_idx in
              let '(idx, live2) := @compute_live' B b idx in
              (idx, PositiveSet.union live1 live2)
         | Abs s d f
           => let '(_, live) := @compute_live' _ (f PositiveSet.empty) cur_idx in
              (cur_idx, live)
         end.
    Definition compute_live {t} e : PositiveSet.t := snd (@compute_live' t e 1).
    Definition ComputeLive {t} (e : Expr t) := compute_live (e _).

    Section with_var.
      Context {var : type -> Type}
              (live : PositiveSet.t).
      Definition OUGHT_TO_BE_UNUSED {T1 T2} (v : T1) (v' : T2) := v.
      Global Opaque OUGHT_TO_BE_UNUSED.
      Fixpoint eliminate_dead' {t} (e : @expr (@expr var) t) (cur_idx : positive)
        : positive * @expr var t
        := match e with
           | Var t v => (cur_idx, v)
           | TT => (cur_idx, TT)
           | AppIdent s d idc args
             => let default _
                    := let default' := @eliminate_dead' _ args cur_idx in
                       (fst default', AppIdent idc (snd default')) in
                match args in expr.expr t return ident.ident t d -> (unit -> positive * expr d) -> positive * expr d with
                | Pair A B x y
                  => match y in expr.expr Y return ident.ident (A * Y) d -> (unit -> positive * expr d) -> positive * expr d with
                     | Abs s' d' f
                       => fun idc
                          => let '(idx, x') := @eliminate_dead' A x cur_idx in
                             let f' := fun v => snd (@eliminate_dead' _ (f v) (Pos.succ idx)) in
                             match idc in ident.ident s d
                                   return (match s return Type with
                                           | A * _ => expr A
                                           | _ => unit
                                           end%ctype
                                           -> match s return Type with
                                              | _ * (s -> d) => (expr s -> expr d)%type
                                              | _ => unit
                                              end%ctype
                                           -> (unit -> positive * expr d)
                                           -> positive * expr d)
                             with
                             | ident.Let_In _ _
                               => fun x' f' _
                                  => if PositiveSet.mem idx live
                                     then (Pos.succ idx, AppIdent ident.Let_In (Pair x' (Abs (fun v => f' (Var v)))))
                                     else (Pos.succ idx, f' (OUGHT_TO_BE_UNUSED x' (Pos.succ idx, PositiveSet.elements live)))
                             | _ => fun _ _ default => default tt
                             end x' f'
                     | _ => fun _ default => default tt
                     end
                | _ => fun _ default => default tt
                end idc default
           | App s d f x
             => let '(idx, f') := @eliminate_dead' _ f cur_idx in
                let '(idx, x') := @eliminate_dead' _ x idx in
                (idx, App f' x')
           | Pair A B a b
             => let '(idx, a') := @eliminate_dead' A a cur_idx in
                let '(idx, b') := @eliminate_dead' B b idx in
                (idx, Pair a' b')
           | Abs s d f
             => (cur_idx, Abs (fun v => snd (@eliminate_dead' _ (f (Var v)) cur_idx)))
           end.

      Definition eliminate_dead {t} e : expr t
        := snd (@eliminate_dead' t e 1).
    End with_var.

    Definition EliminateDead {t} (e : Expr t) : Expr t
      := fun var => eliminate_dead (ComputeLive e) (e _).
  End DeadCodeElimination.

  Module Subst01.
    Local Notation PositiveMap_incr idx m
      := (PositiveMap.add idx (match PositiveMap.find idx m with
                               | Some n => S n
                               | None => S O
                               end) m).
    Local Notation PositiveMap_union m1 m2
      := (PositiveMap.map2
            (fun c1 c2
             => match c1, c2 with
                | Some n1, Some n2 => Some (n1 + n2)%nat
                | Some n, None
                | None, Some n
                  => Some n
                | None, None => None
                end) m1 m2).
    Fixpoint compute_live_counts' {t} (e : @expr (fun _ => positive) t) (cur_idx : positive)
      : positive * PositiveMap.t nat
      := match e with
         | Var t v => (cur_idx, PositiveMap_incr v (PositiveMap.empty _))
         | TT => (cur_idx, PositiveMap.empty _)
         | AppIdent s d idc args
           => @compute_live_counts' _ args cur_idx
         | App s d f x
           => let '(idx, live1) := @compute_live_counts' _ f cur_idx in
              let '(idx, live2) := @compute_live_counts' _ x idx in
              (idx, PositiveMap_union live1 live2)
         | Pair A B a b
           => let '(idx, live1) := @compute_live_counts' A a cur_idx in
              let '(idx, live2) := @compute_live_counts' B b idx in
              (idx, PositiveMap_union live1 live2)
         | Abs s d f
           => let '(idx, live) := @compute_live_counts' _ (f cur_idx) (Pos.succ cur_idx) in
              (cur_idx, live)
         end.
    Definition compute_live_counts {t} e : PositiveMap.t _ := snd (@compute_live_counts' t e 1).
    Definition ComputeLiveCounts {t} (e : Expr t) := compute_live_counts (e _).

    Section with_var.
      Context {var : type -> Type}
              (live : PositiveMap.t nat).
      Fixpoint subst01' {t} (e : @expr (@expr var) t) (cur_idx : positive)
        : positive * @expr var t
        := match e with
           | Var t v => (cur_idx, v)
           | TT => (cur_idx, TT)
           | AppIdent s d idc args
             => let default _
                    := let default := @subst01' _ args cur_idx in
                       (fst default, AppIdent idc (snd default)) in
                match args in expr.expr t return ident.ident t d -> (unit -> positive * expr d) -> positive * expr d with
                | Pair A B x y
                  => match y in expr.expr Y return ident.ident (A * Y) d -> (unit -> positive * expr d) -> positive * expr d with
                     | Abs s' d' f
                       => fun idc
                          => let '(idx, x') := @subst01' A x cur_idx in
                             let f' := fun v => snd (@subst01' _ (f v) (Pos.succ idx)) in
                             match idc in ident.ident s d
                                   return (match s return Type with
                                           | A * _ => expr A
                                           | _ => unit
                                           end%ctype
                                           -> match s return Type with
                                              | _ * (s -> d) => (expr s -> expr d)%type
                                              | _ => unit
                                              end%ctype
                                           -> (unit -> positive * expr d)
                                           -> positive * expr d)
                             with
                             | ident.Let_In _ _
                               => fun x' f' _
                                  => if match PositiveMap.find idx live with
                                        | Some n => (n <=? 1)%nat
                                        | None => true
                                        end
                                     then (Pos.succ idx, f' x')
                                     else (Pos.succ idx, AppIdent ident.Let_In (Pair x' (Abs (fun v => f' (Var v)))))
                             | _ => fun _ _ default => default tt
                             end x' f'
                     | _ => fun _ default => default tt
                     end
                | _ => fun _ default => default tt
                end idc default
           | App s d f x
             => let '(idx, f') := @subst01' _ f cur_idx in
                let '(idx, x') := @subst01' _ x idx in
                (idx, App f' x')
           | Pair A B a b
             => let '(idx, a') := @subst01' A a cur_idx in
                let '(idx, b') := @subst01' B b idx in
                (idx, Pair a' b')
           | Abs s d f
             => (cur_idx, Abs (fun v => snd (@subst01' _ (f (Var v)) (Pos.succ cur_idx))))
           end.

      Definition subst01 {t} e : expr t
        := snd (@subst01' t e 1).
    End with_var.

    Definition Subst01 {t} (e : Expr t) : Expr t
      := fun var => subst01 (ComputeLiveCounts e) (e _).
  End Subst01.

  Module ReassociateSmallConstants.
    Import Compilers.Uncurried.expr.default.

    Section with_var.
      Context (max_const_val : Z)
              {var : type -> Type}.

      Fixpoint to_mul_list (e : @expr var type.Z) : list (@expr var type.Z)
        := match e in expr.expr t return list (@expr var t) with
           | AppIdent s type.Z ident.Z_mul (Pair type.Z type.Z x y)
             => to_mul_list x ++ to_mul_list y
           | Var _ _ as e
           | TT as e
           | App _ _ _ _ as e
           | Abs _ _ _ as e
           | Pair _ _ _ _ as e
           | AppIdent _ _ _ _ as e
             => [e]
           end.

      Definition is_small_prim (e : @expr var type.Z) : bool
        := match e with
           | AppIdent _ _ (ident.primitive type.Z v) _
             => Z.abs v <=? Z.abs max_const_val
           | _ => false
           end.
      Definition is_not_small_prim (e : @expr var type.Z) : bool
        := negb (is_small_prim e).

      Definition reorder_mul_list (ls : list (@expr var type.Z))
        : list (@expr var type.Z)
        := filter is_not_small_prim ls ++ filter is_small_prim ls.

      Fixpoint of_mul_list (ls : list (@expr var type.Z)) : @expr var type.Z
        := match ls with
           | nil => AppIdent (ident.primitive (t:=type.Z) 1) TT
           | cons x nil
             => x
           | cons x xs
             => AppIdent ident.Z_mul (x, of_mul_list xs)
           end.

      Fixpoint reassociate {t} (e : @expr var t) : @expr var t
        := match e in expr.expr t return expr t with
           | Var _ _ as e
           | TT as e
             => e
           | Pair A B a b
             => Pair (@reassociate A a) (@reassociate B b)
           | App s d f x => App (@reassociate _ f) (@reassociate _ x)
           | Abs s d f => Abs (fun v => @reassociate _ (f v))
           | AppIdent s type.Z idc args
             => of_mul_list (reorder_mul_list (to_mul_list (AppIdent idc (@reassociate s args))))
           | AppIdent s _d idc args
             => AppIdent idc (@reassociate s args)
           end.
    End with_var.

    Definition Reassociate (max_const_val : Z) {t} (e : Expr t) : Expr t
      := fun var => reassociate max_const_val (e _).
  End ReassociateSmallConstants.
End Compilers.
Import Associational Positional Compilers.
Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.

(** TODO: FILES:
- Uncurried expr + reification + list canonicalization
- cps
- partial evaluation + DCE
- reassociation
- indexed + bounds analysis + of phoas *)

Import Uncurried.
Import expr.
Import for_reification.Notations.Reification.

Notation "x + y"
  := (AppIdent ident.Z.add (x, y)%expr)
     : expr_scope.
Notation "x * y"
  := (AppIdent ident.Z.mul (x, y)%expr)
     : expr_scope.
Notation "x" := (Var x) (only printing, at level 9) : expr_scope.

Example test1 : True.
Proof using Type.
  let v := Reify ((fun x => 2^x) 255)%Z in
  pose v as E.
  vm_compute in E.
  pose (PartialEvaluate false (canonicalize_list_recursion E)) as E'.
  vm_compute in E'.
  lazymatch (eval cbv delta [E'] in E') with
  | (fun var => AppIdent (ident.primitive ?v) TT) => idtac
  end.
  constructor.
Qed.
Module test2.
  Example test2 : True.
  Proof using Type.
    let v := Reify (fun y : Z
                    => (fun k : Z * Z -> Z * Z
                        => dlet_nd x := (y * y) in
                            dlet_nd z := (x * x) in
                            k (z, z))
                         (fun v => v)) in
    pose v as E.
    vm_compute in E.
    pose (PartialEvaluate false (canonicalize_list_recursion E)) as E'.
    vm_compute in E'.
    lazymatch (eval cbv delta [E'] in E') with
    | (fun var : type -> Type =>
         (λ x : var (type.type_primitive type.Z),
                expr_let x0 := (Var x * Var x) in
              expr_let x1 := (Var x0 * Var x0) in
              (Var x1, Var x1))%expr) => idtac
    end.
    pose (PartialEvaluateWithBounds1 E' (Some r[0~>10]%zrange)) as E''.
    lazy in E''.
    lazymatch (eval cbv delta [E''] in E'') with
    | (fun var : type -> Type =>
         (λ x : var (type.type_primitive type.Z),
          expr_let y := ident.Z.cast r[0 ~> 100] @@ (Var x * Var x) in
          expr_let y0 := ident.Z.cast r[0 ~> 10000] @@ (Var y * Var y) in
          (ident.Z.cast r[0 ~> 10000] @@ Var y0, ident.Z.cast r[0 ~> 10000] @@ Var y0))%expr)
      => idtac
    end.
    constructor.
  Qed.
End test2.
Module test3.
  Example test3 : True.
  Proof using Type.
    let v := Reify (fun y : Z
                    => dlet_nd x := dlet_nd x := (y * y) in
                        (x * x) in
                        dlet_nd z := dlet_nd z := (x * x) in
                        (z * z) in
                        (z * z)) in
    pose v as E.
    vm_compute in E.
    pose (option_map (PartialEvaluate false) (CPS.CallFunWithIdContinuation (CPS.Translate (canonicalize_list_recursion E)))) as E'.
    vm_compute in E'.
    lazymatch (eval cbv delta [E'] in E') with
    | (Some
         (fun var : type -> Type =>
            (λ x : var (type.type_primitive type.Z),
                   expr_let x0 := Var x * Var x in
                 expr_let x1 := Var x0 * Var x0 in
                 expr_let x2 := Var x1 * Var x1 in
                 expr_let x3 := Var x2 * Var x2 in
                 Var x3 * Var x3)%expr))
      => idtac
    end.
    pose (PartialEvaluateWithBounds1 (invert_Some E') (Some r[0~>10]%zrange)) as E'''.
    lazy in E'''.
    lazymatch (eval cbv delta [E'''] in E''') with
    | (fun var : type -> Type =>
          (λ x : var (type.type_primitive type.Z),
           expr_let y := ident.Z.cast r[0 ~> 100] @@ (Var x * Var x) in
           expr_let y0 := ident.Z.cast r[0 ~> 10000] @@ (Var y * Var y) in
           expr_let y1 := ident.Z.cast r[0 ~> 100000000] @@ (Var y0 * Var y0) in
           expr_let y2 := ident.Z.cast r[0 ~> 10000000000000000] @@ (Var y1 * Var y1) in
           ident.Z.cast r[0 ~> 100000000000000000000000000000000] @@ (Var y2 * Var y2))%expr)
      => idtac
    end.
    constructor.
  Qed.
End test3.
Module test4.
  Example test4 : True.
  Proof using Type.
    let v := Reify (fun y : (list Z * list Z)
                    => dlet_nd x := List.nth_default (-1) (fst y) 0 in
                        dlet_nd z := List.nth_default (-1) (snd y) 0 in
                        dlet_nd xz := (x * z) in
                        (xz :: xz :: nil)) in
    pose v as E.
    vm_compute in E.
    pose (option_map (PartialEvaluate false) (CPS.CallFunWithIdContinuation (CPS.Translate (canonicalize_list_recursion E)))) as E'.
    lazy in E'.
    clear E.
    pose (PartialEvaluateWithBounds1 (invert_Some E') (Some [Some r[0~>10]%zrange],Some [Some r[0~>10]%zrange])) as E''.
    lazy in E''.
    lazymatch (eval cbv delta [E''] in E'') with
    | (fun var : type -> Type =>
         (λ x : var (type.list (type.type_primitive type.Z) * type.list (type.type_primitive type.Z))%ctype,
          expr_let y := ident.Z.cast r[0 ~> 10] @@
                        (ident.List.nth_default_concrete (-1) 0 @@ (ident.fst @@ Var x)) in
          expr_let y0 := ident.Z.cast r[0 ~> 10] @@
                         (ident.List.nth_default_concrete (-1) 0 @@ (ident.snd @@ Var x)) in
          expr_let y1 := ident.Z.cast r[0 ~> 100] @@ (Var y * Var y0) in
          ident.Z.cast r[0 ~> 100] @@ Var y1 :: ident.Z.cast r[0 ~> 100] @@ Var y1 :: [])%expr)
      => idtac
    end.
    constructor.
  Qed.
End test4.
Module test5.
  Example test5 : True.
  Proof using Type.
    let v := Reify (fun y : (Z * Z)
                    => dlet_nd x := (13 * (fst y * snd y)) in
                        x) in
    pose v as E.
    vm_compute in E.
    pose (ReassociateSmallConstants.Reassociate (2^8) (PartialEvaluate false (invert_Some (CPS.CallFunWithIdContinuation (CPS.Translate (canonicalize_list_recursion E)))))) as E'.
    lazy in E'.
    clear E.
    lazymatch (eval cbv delta [E'] in E') with
    | (fun var =>
         Abs (fun v
              => (expr_let v0 := ident.Z.mul @@ (ident.fst @@ Var v, ident.Z.mul @@ (ident.snd @@ Var v, ident.primitive 13 @@ TT)) in
                      Var v0)%expr))
      => idtac
    end.
    constructor.
  Qed.
End test5.
Module test6.
  (* check for no dead code with if *)
  Example test6 : True.
  Proof using Type.
    let v := Reify (fun y : Z
                    => if 0 =? 1
                       then dlet_nd x := (y * y) in
                                x
                       else y) in
    pose v as E.
    vm_compute in E.
    pose (CPS.CallFunWithIdContinuation (CPS.Translate (canonicalize_list_recursion E))) as E'.
    lazy in E'.
    clear E.
    pose (PartialEvaluate false (invert_Some E')) as E''.
    lazy in E''.
    lazymatch eval cbv delta [E''] in E'' with
    | fun var : type -> Type => (λ x : var (type.type_primitive type.Z), Var x)%expr
      => idtac
    end.
    exact I.
  Qed.
End test6.
Module test7.
  Example test7 : True.
  Proof using Type.
    let v := Reify (fun y : Z
                    => dlet_nd x := y + y in
                        dlet_nd z := x in
                        dlet_nd z' := z in
                        dlet_nd z'' := z in
                        z'' + z'') in
    pose v as E.
    vm_compute in E.
    pose (canonicalize_list_recursion E) as E'.
    lazy in E'.
    clear E.
    pose (Subst01.Subst01 (DeadCodeElimination.EliminateDead E')) as E''.
    lazy in E''.
    lazymatch eval cbv delta [E''] in E'' with
    | fun var : type -> Type => (λ x : var (type.type_primitive type.Z), expr_let v0 := Var x + Var x in Var v0 + Var v0)%expr
      => idtac
    end.
    exact I.
  Qed.
End test7.
Module test8.
  Example test8 : True.
  Proof using Type.
    let v := Reify (fun y : Z
                    => dlet_nd x := y + y in
                        dlet_nd z := x in
                        dlet_nd z' := z in
                        dlet_nd z'' := z in
                        z'' + z'') in
    pose v as E.
    vm_compute in E.
    pose (canonicalize_list_recursion E) as E'.
    lazy in E'.
    clear E.
    pose (GeneralizeVar.GeneralizeVar (E' _)) as E''.
    lazy in E''.
    unify E' E''.
    exact I.
  Qed.
End test8.
Module test9.
  Example test9 : True.
  Proof using Type.
    let v := Reify (fun y : list Z => (hd 0%Z y, tl y)) in
    pose v as E.
    vm_compute in E.
    pose (PartialEvaluate true (canonicalize_list_recursion E)) as E'.
    lazy in E'.
    clear E.
    lazymatch (eval cbv delta [E'] in E') with
    | (fun var
       => (λ x,
           (ident.list_rect
              @@
              ((λ _, ident.primitive 0%Z @@ TT),
               (λ x0, ident.fst @@ (ident.fst @@ Var x0)),
               Var x),
            ident.list_rect
              @@
              ((λ _, ident.nil @@ TT),
               (λ x0, ident.snd @@ (ident.fst @@ Var x0)),
               Var x)))%expr)
      => idtac
    end.
    exact I.
  Qed.
End test9.
Module test10.
  Example test10 : True.
  Proof using Type.
    let v := Reify (fun (f : Z -> Z -> Z) x y => f (x + y) (x * y))%Z in
    pose v as E.
    vm_compute in E.
    pose (Uncurry.expr.Uncurry (PartialEvaluate true (canonicalize_list_recursion E))) as E'.
    lazy in E'.
    clear E.
    lazymatch (eval cbv delta [E'] in E') with
    | (fun var =>
         (λ v,
          ident.fst @@ Var v @
                    (ident.fst @@ (ident.snd @@ Var v) + ident.snd @@ (ident.snd @@ Var v)) @
                    (ident.fst @@ (ident.snd @@ Var v) * ident.snd @@ (ident.snd @@ Var v)))%expr)
      => idtac
    end.
    constructor.
  Qed.
End test10.
Module test11.
  Example test11 : True.
  Proof using Type.
    let v := Reify (fun x y => (fun f a b => f a b) (fun a b => a + b) (x + y) (x * y))%Z in
    pose v as E.
    vm_compute in E.
    pose (Uncurry.expr.Uncurry (PartialEvaluate true (canonicalize_list_recursion E))) as E'.
    lazy in E'.
    clear E.
    lazymatch (eval cbv delta [E'] in E') with
    | (fun var =>
         (λ x,
          ident.fst @@ Var x + ident.snd @@ Var x + ident.fst @@ Var x * ident.snd @@ Var x)%expr)
      => idtac
    end.
    constructor.
  Qed.
End test11.
Axiom admit_pf : False.
Notation admit := (match admit_pf with end).
Ltac cache_reify _ :=
  intros;
  etransitivity;
  [
  | repeat apply (f_equal (fun f => f _));
    Reify_rhs ();
    reflexivity ];
  cbv beta;
  let RHS := match goal with |- _ = ?RHS => RHS end in
  let e := match RHS with context[expr.Interp _ ?e] => e end in
  let E := fresh "E" in
  set (E := e);
  let E' := constr:(canonicalize_list_recursion E) in
  let LHS := match goal with |- ?LHS = _ => LHS end in
  lazymatch LHS with
  | context LHS[@expr.Interp ?ident ?interp_ident ?t ?e]
    => let LHS := context LHS[@expr.Interp ident interp_ident t E'] in
       transitivity LHS; [ | clear e ]
  end;
  [ repeat match goal with |- context[expr.Interp _ _ _] => apply (f_equal (fun f => f _)) end;
    apply f_equal;
    lazymatch goal with |- ?LHS = ?RHS => subst LHS end;
    let RHS := lazymatch goal with |- ?LHS = ?RHS => RHS end in
    time (let RHS' := (eval vm_compute in RHS) in (* [vm_compute] is much faster than [lazy] here on large things *)
          time instantiate (1:=RHS');
          vm_cast_no_check (eq_refl RHS'))
  | clearbody E ].

Create HintDb reify_gen_cache.

Derive carry_mul_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (f g : list Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (len_c : nat)
                        (idxs : list nat)
                        (len_idxs : nat),
                    Interp (t:=type.reify_type_of carry_mulmod)
                           carry_mul_gen limbwidth_num limbwidth_den s c n len_c idxs len_idxs f g
                    = carry_mulmod limbwidth_num limbwidth_den s c n len_c idxs len_idxs f g)
       As carry_mul_gen_correct.
Proof. Time cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Time Qed.
Global Hint Extern 1 (_ = carry_mulmod _ _ _ _ _ _ _ _ _ _) => simple apply carry_mul_gen_correct : reify_gen_cache.

Derive carry_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (f : list Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (len_c : nat)
                        (idxs : list nat)
                        (len_idxs : nat),
                    Interp (t:=type.reify_type_of carrymod)
                           carry_gen limbwidth_num limbwidth_den s c n len_c idxs len_idxs f
                    = carrymod limbwidth_num limbwidth_den s c n len_c idxs len_idxs f)
       As carry_gen_correct.
Proof. cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Qed.
Global Hint Extern 1 (_ = carrymod _ _ _ _ _ _ _ _ _) => simple apply carry_gen_correct : reify_gen_cache.

Derive encode_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (v : Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (len_c : nat),
                    Interp (t:=type.reify_type_of encodemod)
                           encode_gen limbwidth_num limbwidth_den s c n len_c v
                    = encodemod limbwidth_num limbwidth_den s c n len_c v)
       As encode_gen_correct.
Proof. cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Qed.
Global Hint Extern 1 (_ = encodemod _ _ _ _ _ _ _) => simple apply encode_gen_correct : reify_gen_cache.

Derive add_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (f g : list Z)
                        (n : nat),
                    Interp (t:=type.reify_type_of addmod)
                           add_gen limbwidth_num limbwidth_den n f g
                    = addmod limbwidth_num limbwidth_den n f g)
       As add_gen_correct.
Proof. cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Qed.
Global Hint Extern 1 (_ = addmod _ _ _ _ _) => simple apply add_gen_correct : reify_gen_cache.
Derive sub_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (len_c : nat)
                        (coef : Z)
                        (f g : list Z),
                    Interp (t:=type.reify_type_of submod)
                           sub_gen limbwidth_num limbwidth_den s c n len_c coef f g
                    = submod limbwidth_num limbwidth_den s c n len_c coef f g)
       As sub_gen_correct.
Proof. cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Qed.
Global Hint Extern 1 (_ = submod _ _ _ _ _ _ _ _ _) => simple apply sub_gen_correct : reify_gen_cache.

Derive opp_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (len_c : nat)
                        (coef : Z)
                        (f : list Z),
                    Interp (t:=type.reify_type_of oppmod)
                           opp_gen limbwidth_num limbwidth_den s c n len_c coef f
                    = oppmod limbwidth_num limbwidth_den s c n len_c coef f)
       As opp_gen_correct.
Proof. cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Qed.
Global Hint Extern 1 (_ = oppmod _ _ _ _ _ _ _ _) => simple apply opp_gen_correct : reify_gen_cache.

Definition zeromod limbwidth_num limbwidth_den n s c len_c := encodemod limbwidth_num limbwidth_den n s c len_c 0.
Definition onemod limbwidth_num limbwidth_den n s c len_c := encodemod limbwidth_num limbwidth_den n s c len_c 1.

Derive zero_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (len_c : nat),
                    Interp (t:=type.reify_type_of zeromod)
                           zero_gen limbwidth_num limbwidth_den s c n len_c
                    = zeromod limbwidth_num limbwidth_den s c n len_c)
       As zero_gen_correct.
Proof. cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Qed.
Global Hint Extern 1 (_ = zeromod _ _ _ _ _ _) => simple apply zero_gen_correct : reify_gen_cache.

Derive one_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (len_c : nat),
                    Interp (t:=type.reify_type_of onemod)
                           one_gen limbwidth_num limbwidth_den s c n len_c
                    = onemod limbwidth_num limbwidth_den s c n len_c)
       As one_gen_correct.
Proof. cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Qed.
Global Hint Extern 1 (_ = onemod _ _ _ _ _ _) => simple apply one_gen_correct : reify_gen_cache.

Derive id_gen
       SuchThat (forall (n : nat)
                        (ls : list Z),
                    Interp (t:=type.reify_type_of expanding_id)
                           id_gen n ls
                    = expanding_id n ls)
       As id_gen_correct.
Proof. cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Qed.
Global Hint Extern 1 (_ = expanding_id _ _) => simple apply id_gen_correct : reify_gen_cache.

Import Uncurry.
Module Pipeline.
  Import GeneralizeVar.
  Inductive ErrorMessage :=
  | Computed_bounds_are_not_tight_enough
      {t} (computed_bounds expected_bounds : ZRange.type.option.interp t)
      {s} (syntax_tree : Expr (s -> t)) (arg_bounds : ZRange.type.option.interp s)
  | Bounds_analysis_failed
  | Type_too_complicated_for_cps (t : type)
  | Value_not_le (descr : string) {T'} (lhs rhs : T')
  | Value_not_lt (descr : string) {T'} (lhs rhs : T')
  | Values_not_provably_distinct (descr : string) {T'} (lhs rhs : T')
  | Values_not_provably_equal (descr : string) {T'} (lhs rhs : T').

  Inductive ErrorT {T} :=
  | Success (v : T)
  | Error (msg : ErrorMessage).
  Global Arguments ErrorT : clear implicits.

  Definition invert_result {T} (v : ErrorT T)
    := match v return match v with Success _ => T | _ => ErrorMessage end with
       | Success v => v
       | Error msg => msg
       end.

  Definition PrePipeline
             {t}
             (E : for_reification.Expr t)
    : Expr t
    := canonicalize_list_recursion E.

  Lemma PrePipeline_correct {t} (E : for_reification.Expr t) v
    : expr.Interp (@ident.interp) v =
      expr.Interp (@for_reification.ident.interp) E.
  Admitted.

  Definition BoundsPipeline
             (with_dead_code_elimination : bool := true)
             (with_subst01 : bool)
             relax_zrange
             {t}
             (E : Expr t)
             arg_bounds
             out_bounds
  : ErrorT (Expr (type.uncurry t))
    := let E := expr.Uncurry E in
       let E := CPS.CallFunWithIdContinuation (CPS.Translate E) in
       match E with
       | Some E
         => (let E := PartialEvaluate false E in
             (* Note that DCE evaluates the expr with two different
                [var] arguments, and so results in a pipeline that is
                2x slower unless we pass through a uniformly concrete
                [var] type first *)
             dlet_nd e := ToFlat E in
             let E := FromFlat e in
             let E := if with_dead_code_elimination then DeadCodeElimination.EliminateDead E else E in
             dlet_nd e := ToFlat E in
             let E := FromFlat e in
             let E := if with_subst01 then Subst01.Subst01 E else E in
             let E := ReassociateSmallConstants.Reassociate (2^8) E in
             let E := CheckedPartialEvaluateWithBounds1 relax_zrange E arg_bounds out_bounds in
             match E with
             | inl E => Success E
             | inr (b, E)
               => Error (Computed_bounds_are_not_tight_enough b out_bounds E arg_bounds)
             end)
       | None => Error (Type_too_complicated_for_cps t)
       end.

  Lemma BoundsPipeline_correct
             (with_dead_code_elimination : bool := true)
             (with_subst01 : bool)
             relax_zrange
             (Hrelax : forall r r' z : zrange,
                 (z <=? r)%zrange = true -> relax_zrange r = Some r' -> (z <=? r')%zrange = true)
             {t}
             (e : Expr t)
             arg_bounds
             out_bounds
             rv
             (Hrv : BoundsPipeline (*with_dead_code_elimination*) with_subst01 relax_zrange e arg_bounds out_bounds = Success rv)
    : forall arg
             (Harg : ZRange.type.option.is_bounded_by arg_bounds arg = true),
      ZRange.type.option.is_bounded_by out_bounds (Interp rv arg) = true
      /\ Interp rv arg = app_curried (Interp e) arg.
  Proof using Type.
    cbv [BoundsPipeline Let_In] in *;
      repeat match goal with
             | [ H : match ?x with _ => _ end = Success _ |- _ ]
               => destruct x eqn:?; cbv beta iota in H; [ | destruct_head'_prod; congruence ];
                    let H' := fresh in
                    inversion H as [H']; clear H; rename H' into H
             end.
    { intros;
        match goal with
        | [ H : _ = _ |- _ ]
          => eapply CheckedPartialEvaluateWithBounds1_Correct in H;
               [ destruct H as [H0 H1] | .. ]
        end;
        [
        | eassumption || (try reflexivity).. ].
      refine (let H' := admit (* interp correctness *) in
              conj _ (eq_trans H' _));
        clearbody H'.
      { rewrite H'; eassumption. }
      { rewrite H0.
        exact admit. (* interp correctness *) } }
  Qed.

  Definition BoundsPipeline_correct_transT
             {t}
             arg_bounds
             out_bounds
             (InterpE : type.interp t)
             (rv : Expr (type.uncurry t))
    := forall arg
              (Harg : ZRange.type.option.is_bounded_by arg_bounds arg = true),
      ZRange.type.option.is_bounded_by out_bounds (Interp rv arg) = true
      /\ Interp rv arg = app_curried InterpE arg.

  Lemma BoundsPipeline_correct_trans
        (with_dead_code_elimination : bool := true)
        (with_subst01 : bool)
        relax_zrange
        (Hrelax
         : forall r r' z : zrange,
            (z <=? r)%zrange = true -> relax_zrange r = Some r' -> (z <=? r')%zrange = true)
        {t}
        (e : Expr t)
        arg_bounds out_bounds
        (InterpE : type.interp t)
        (InterpE_correct
         : forall arg
                  (Harg : ZRange.type.option.is_bounded_by arg_bounds arg = true),
            app_curried (Interp e) arg = app_curried InterpE arg)
        rv
        (Hrv : BoundsPipeline (*with_dead_code_elimination*) with_subst01 relax_zrange e arg_bounds out_bounds = Success rv)
    : BoundsPipeline_correct_transT arg_bounds out_bounds InterpE rv.
  Proof using Type.
    intros arg Harg; rewrite <- InterpE_correct by assumption.
    eapply @BoundsPipeline_correct; eassumption.
  Qed.

  Definition BoundsPipeline_full
             (with_dead_code_elimination : bool := true)
             (with_subst01 : bool)
             relax_zrange
             {t}
             (E : for_reification.Expr t)
             arg_bounds
             out_bounds
  : ErrorT (Expr (type.uncurry t))
    := let E := PrePipeline E in
       @BoundsPipeline
         (*with_dead_code_elimination*)
         with_subst01
         relax_zrange
         t E arg_bounds out_bounds.

  Lemma BoundsPipeline_full_correct
             (with_dead_code_elimination : bool := true)
             (with_subst01 : bool)
             relax_zrange
             (Hrelax : forall r r' z : zrange,
                 (z <=? r)%zrange = true -> relax_zrange r = Some r' -> (z <=? r')%zrange = true)
             {t}
             (E : for_reification.Expr t)
             arg_bounds
             out_bounds
             rv
             (Hrv : BoundsPipeline_full (*with_dead_code_elimination*) with_subst01 relax_zrange E arg_bounds out_bounds = Success rv)
    : forall arg
             (Harg : ZRange.type.option.is_bounded_by arg_bounds arg = true),
      ZRange.type.option.is_bounded_by out_bounds (Interp rv arg) = true
      /\ Interp rv arg = app_curried (for_reification.Interp E) arg.
  Proof using Type.
    cbv [BoundsPipeline_full] in *.
    eapply BoundsPipeline_correct_trans; [ eassumption | | eassumption.. ].
    intros; erewrite PrePipeline_correct; reflexivity.
  Qed.
End Pipeline.

Definition round_up_bitwidth_gen (possible_values : list Z) (bitwidth : Z) : option Z
  := List.fold_right
       (fun allowed cur
        => if bitwidth <=? allowed
           then Some allowed
           else cur)
       None
       possible_values.

Lemma round_up_bitwidth_gen_le possible_values bitwidth v
  : round_up_bitwidth_gen possible_values bitwidth = Some v
    -> bitwidth <= v.
Proof using Type.
  cbv [round_up_bitwidth_gen].
  induction possible_values as [|x xs IHxs]; cbn; intros; inversion_option.
  break_innermost_match_hyps; Z.ltb_to_lt; inversion_option; subst; trivial.
  specialize_by_assumption; lia.
Qed.

Definition relax_zrange_gen (possible_values : list Z) : zrange -> option zrange
  := (fun '(r[ l ~> u ])
      => if (0 <=? l)%Z
         then option_map (fun u => r[0~>2^u-1])
                         (round_up_bitwidth_gen possible_values (Z.log2_up (u+1)))
         else None)%zrange.

Lemma relax_zrange_gen_good
      (possible_values : list Z)
  : forall r r' z : zrange,
    (z <=? r)%zrange = true -> relax_zrange_gen possible_values r = Some r' -> (z <=? r')%zrange = true.
Proof using Type.
  cbv [is_tighter_than_bool relax_zrange_gen]; intros *.
  pose proof (Z.log2_up_nonneg (upper r + 1)).
  rewrite !Bool.andb_true_iff; destruct_head' zrange; cbn [ZRange.lower ZRange.upper] in *.
  cbv [fold_right option_map].
  break_innermost_match; intros; destruct_head'_and;
    try match goal with
        | [ H : _ |- _ ] => apply round_up_bitwidth_gen_le in H
        end;
    inversion_option; inversion_zrange;
      subst;
      repeat apply conj;
      Z.ltb_to_lt; try lia;
        try (rewrite <- Z.log2_up_le_pow2_full in *; lia).
Qed.

(** XXX TODO: Translate Jade's python script *)
Section rcarry_mul.
  Context (n : nat)
          (s : Z)
          (c : list (Z * Z))
          (machine_wordsize : Z).

  Let limbwidth := (Z.log2_up (s - Associational.eval c) / Z.of_nat n)%Q.
  Let idxs := (seq 0 n ++ [0; 1])%list%nat.
  Let coef := 2.
  Let tight_upperbounds : list Z
    := List.map
         (fun v : Z => Qceiling (11/10 * v))
         (encode (weight (Qnum limbwidth) (Qden limbwidth)) n s c (s-1)).
  Let prime_bound : ZRange.type.option.interp (type.Z)
    := Some r[0~>(s - Associational.eval c - 1)]%zrange.

  Definition relax_zrange_of_machine_wordsize
    := relax_zrange_gen [machine_wordsize; 2 * machine_wordsize]%Z.

  Let relax_zrange := relax_zrange_of_machine_wordsize.
  Let tight_bounds : list (ZRange.type.option.interp type.Z)
    := List.map (fun u => Some r[0~>u]%zrange) tight_upperbounds.
  Let loose_bounds : list (ZRange.type.option.interp type.Z)
    := List.map (fun u => Some r[0 ~> 3*u]%zrange) tight_upperbounds.

  Definition check_args {T} (res : Pipeline.ErrorT T)
    : Pipeline.ErrorT T
    := if negb (Qle_bool 1 limbwidth)%Q
       then Pipeline.Error (Pipeline.Value_not_le "1 ≤ limbwidth" 1%Q limbwidth)
       else if (negb (0 <? s - Associational.eval c))%Z
            then Pipeline.Error (Pipeline.Value_not_lt "s - Associational.eval c ≤ 0" 0 (s - Associational.eval c))
            else if (s =? 0)%Z
                 then Pipeline.Error (Pipeline.Values_not_provably_distinct "s ≠ 0" s 0)
                 else if (n =? 0)%nat
                      then Pipeline.Error (Pipeline.Values_not_provably_distinct "n ≠ 0" n 0%nat)
                      else if (negb (0 <? machine_wordsize))
                           then Pipeline.Error (Pipeline.Value_not_lt "0 < machine_wordsize" 0 machine_wordsize)
                           else res.

  Notation type_of_strip_3arrow := ((fun (d : Prop) (_ : forall A B C, d) => d) _).

  Notation BoundsPipeline rop in_bounds out_bounds
    := (Pipeline.BoundsPipeline
          (*false*) true
          relax_zrange
          rop%Expr in_bounds out_bounds).

  Notation BoundsPipeline_correct in_bounds out_bounds op
    := (fun rv (rop : Expr (type.reify_type_of op)) Hrop
        => @Pipeline.BoundsPipeline_correct_trans
             (*false*) true
             relax_zrange
             (relax_zrange_gen_good _)
             _
             rop
             in_bounds
             out_bounds
             op
             Hrop rv)
         (only parsing).

  (* N.B. We only need [rcarry_mul] if we want to extract the Pipeline; otherwise we can just use [rcarry_mul_correct] *)
  Definition rcarry_mul
    := BoundsPipeline
         (carry_mul_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n @ GallinaReify.Reify (length c) @ GallinaReify.Reify idxs @ GallinaReify.Reify (length idxs))
         (Some loose_bounds, Some loose_bounds)
         (Some tight_bounds).

  Definition rcarry_mul_correct
    := BoundsPipeline_correct
         (Some loose_bounds, Some loose_bounds)
         (Some tight_bounds)
         (carry_mulmod (Qnum limbwidth) (Z.pos (Qden limbwidth)) s c n (List.length c) idxs (List.length idxs)).

  Definition rcarry_correct
    := BoundsPipeline_correct
         (Some loose_bounds)
         (Some tight_bounds)
         (carrymod (Qnum limbwidth) (Z.pos (Qden limbwidth)) s c n (List.length c) idxs (List.length idxs)).

  Definition rrelax_correct
    := BoundsPipeline_correct
         (Some tight_bounds)
         (Some loose_bounds)
         (expanding_id n).

  Definition radd_correct
    := BoundsPipeline_correct
         (Some tight_bounds, Some tight_bounds)
         (Some loose_bounds)
         (addmod (Qnum limbwidth) (Z.pos (Qden limbwidth)) n).

  Definition rsub_correct
    := BoundsPipeline_correct
         (Some tight_bounds, Some tight_bounds)
         (Some loose_bounds)
         (submod (Qnum limbwidth) (Z.pos (Qden limbwidth)) s c n (List.length c) coef).

  Definition ropp_correct
    := BoundsPipeline_correct
         (Some tight_bounds)
         (Some loose_bounds)
         (oppmod (Qnum limbwidth) (Z.pos (Qden limbwidth)) s c n (List.length c) coef).

  Definition rencode_correct
    := BoundsPipeline_correct
         prime_bound
         (Some tight_bounds)
         (encodemod (Qnum limbwidth) (Z.pos (Qden limbwidth)) s c n (List.length c)).

  Definition rzero_correct
    := BoundsPipeline_correct
         tt
         (Some tight_bounds)
         (zeromod (Qnum limbwidth) (Z.pos (Qden limbwidth)) s c n (List.length c)).

  Definition rone_correct
    := BoundsPipeline_correct
         tt
         (Some tight_bounds)
         (onemod (Qnum limbwidth) (Z.pos (Qden limbwidth)) s c n (List.length c)).

  (* we need to strip off [Hrv : ... = Pipeline.Success rv] and related arguments *)
  Definition rcarry_mul_correctT rv : Prop
    := type_of_strip_3arrow (@rcarry_mul_correct rv).
  Definition rcarry_correctT rv : Prop
    := type_of_strip_3arrow (@rcarry_correct rv).
  Definition rrelax_correctT rv : Prop
    := type_of_strip_3arrow (@rrelax_correct rv).
  Definition radd_correctT rv : Prop
    := type_of_strip_3arrow (@radd_correct rv).
  Definition rsub_correctT rv : Prop
    := type_of_strip_3arrow (@rsub_correct rv).
  Definition ropp_correctT rv : Prop
    := type_of_strip_3arrow (@ropp_correct rv).
  Definition rencode_correctT rv : Prop
    := type_of_strip_3arrow (@rencode_correct rv).
  Definition rzero_correctT rv : Prop
    := type_of_strip_3arrow (@rzero_correct rv).
  Definition rone_correctT rv : Prop
    := type_of_strip_3arrow (@rone_correct rv).

  Section make_ring.
    Let m : positive := Z.to_pos (s - Associational.eval c).
    Context (curve_good : check_args (Pipeline.Success tt) = Pipeline.Success tt)
            {rcarry_mulv} (Hrmulv : rcarry_mul_correctT rcarry_mulv)
            {rcarryv} (Hrcarryv : rcarry_correctT rcarryv)
            {rrelaxv} (Hrrelaxv : rrelax_correctT rrelaxv)
            {raddv} (Hraddv : radd_correctT raddv)
            {rsubv} (Hrsubv : rsub_correctT rsubv)
            {roppv} (Hroppv : ropp_correctT roppv)
            {rzerov} (Hrzerov : rzero_correctT rzerov)
            {ronev} (Hronev : rone_correctT ronev)
            {rencodev} (Hrencodev : rencode_correctT rencodev).

    Local Ltac use_curve_good_t :=
      repeat first [ progress rewrite ?map_length, ?Z.mul_0_r, ?Pos.mul_1_r, ?Z.mul_1_r in *
                   | reflexivity
                   | lia
                   | rewrite interp_reify_list, ?map_map
                   | rewrite map_ext with (g:=id), map_id
                   | progress distr_length
                   | progress cbv [Qceiling Qfloor Qopp Qdiv Qplus inject_Z Qmult Qinv] in *
                   | progress cbv [Qle] in *
                   | progress cbn -[reify_list] in *
                   | progress intros
                   | solve [ auto ] ].

    Lemma use_curve_good
      : Z.pos m = s - Associational.eval c
        /\ Z.pos m <> 0
        /\ s - Associational.eval c <> 0
        /\ s <> 0
        /\ 0 < machine_wordsize
        /\ n <> 0%nat
        /\ List.length tight_bounds = n
        /\ List.length loose_bounds = n
        /\ 0 < Qden limbwidth <= Qnum limbwidth.
    Proof using curve_good.
      clear -curve_good.
      cbv [check_args] in curve_good.
      break_innermost_match_hyps; try discriminate.
      rewrite negb_false_iff in *.
      Z.ltb_to_lt.
      rewrite Qle_bool_iff in *.
      rewrite NPeano.Nat.eqb_neq in *.
      intros.
      cbv [Qnum Qden limbwidth Qceiling Qfloor Qopp Qdiv Qplus inject_Z Qmult Qinv] in *.
      rewrite ?map_length, ?Z.mul_0_r, ?Pos.mul_1_r, ?Z.mul_1_r in *.
      specialize_by lia.
      repeat match goal with H := _ |- _ => subst H end.
      repeat apply conj.
      { destruct (s - Associational.eval c); cbn; lia. }
      { use_curve_good_t. }
      { use_curve_good_t. }
      { use_curve_good_t. }
      { use_curve_good_t. }
      { use_curve_good_t. }
      { use_curve_good_t. }
      { use_curve_good_t. }
      { use_curve_good_t. }
      { use_curve_good_t. }
    Qed.

    Definition GoodT : Prop
      := @Ring.GoodT
           (Qnum limbwidth)
           (Z.pos (Qden limbwidth))
           n s c
           tight_bounds
           (Interp rrelaxv)
           (Interp rcarry_mulv)
           (Interp rcarryv)
           (Interp raddv)
           (Interp rsubv)
           (Interp roppv)
           (Interp rzerov tt)
           (Interp ronev tt)
           (Interp rencodev).

    Theorem Good : GoodT.
    Proof using Hraddv Hrcarryv Hrencodev Hrmulv Hronev Hroppv Hrrelaxv Hrsubv Hrzerov curve_good.
      pose proof use_curve_good; destruct_head'_and; destruct_head_hnf' ex.
      eapply Ring.Good;
        repeat first [ assumption
                     | intros; apply eval_carry_mulmod
                     | intros; apply eval_carrymod
                     | intros; apply eval_addmod
                     | intros; apply eval_submod
                     | intros; apply eval_oppmod
                     | intros; apply eval_encodemod
                     | eassumption
                     | apply conj
                     | progress intros
                     | progress cbv [onemod zeromod]
                     | eapply Hrzerov (* to handle diff with whether or not correctness asks for boundedness of tt *)
                     | eapply Hronev (* to handle diff with whether or not correctness asks for boundedness of tt *)
                     | match goal with
                       | [ |- ?x = ?x ] => reflexivity
                       | [ |- ?x = ?ev ] => is_evar ev; reflexivity
                       | [ |- ZRange.type.option.is_bounded_by tt tt = true ] => reflexivity
                       end ].
    Qed.
  End make_ring.
End rcarry_mul.

Ltac peel_interp_app _ :=
  lazymatch goal with
  | [ |- ?R' (?InterpE ?arg) (?f ?arg) ]
    => apply fg_equal_rel; [ | reflexivity ];
       try peel_interp_app ()
  | [ |- ?R' (Interp ?ev) (?f ?x) ]
    => let sv := type of x in
       let fx := constr:(f x) in
       let dv := type of fx in
       let rs := type.reify sv in
       let rd := type.reify dv in
       etransitivity;
       [ apply @Interp_APP_rel_reflexive with (s:=rs) (d:=rd) (R:=R');
         typeclasses eauto
       | apply fg_equal_rel;
         [ try peel_interp_app ()
         | try lazymatch goal with
               | [ |- ?R (Interp ?ev) (Interp _) ]
                 => reflexivity
               | [ |- ?R (Interp ?ev) ?c ]
                 => let rc := constr:(GallinaReify.Reify c) in
                    unify ev rc; reflexivity
               end ] ]
  end.
Ltac pre_cache_reify _ :=
  cbv [app_curried];
  let arg := fresh "arg" in
  intros arg _;
  peel_interp_app ();
  [ lazymatch goal with
    | [ |- ?R (Interp ?ev) _ ]
      => (tryif is_evar ev
           then let ev' := fresh "ev" in set (ev' := ev)
           else idtac)
    end;
    cbv [pointwise_relation]; intros; clear
  | .. ].
Ltac do_inline_cache_reify do_if_not_cached :=
  pre_cache_reify ();
  [ try solve [
          repeat match goal with H := ?e |- _ => is_evar e; subst H end;
          eauto with nocore reify_gen_cache;
          do_if_not_cached ()
        ];
    cache_reify (); exact admit
  | .. ].

(* TODO: MOVE ME *)
Ltac vm_compute_lhs_reflexivity :=
  lazymatch goal with
  | [ |- ?LHS = ?RHS ]
    => let x := (eval vm_compute in LHS) in
       (* we cannot use the unify tactic, which just gives "not
          unifiable" as the error message, because we want to see the
          terms that were not unifable.  See also
          COQBUG(https://github.com/coq/coq/issues/7291) *)
       let _unify := constr:(ltac:(reflexivity) : RHS = x) in
       vm_cast_no_check (eq_refl x)
  end.

Ltac solve_rop' rop_correct do_if_not_cached machine_wordsizev :=
  eapply rop_correct with (machine_wordsize:=machine_wordsizev);
  [ do_inline_cache_reify do_if_not_cached
  | subst_evars; vm_compute_lhs_reflexivity (* lazy; reflexivity *) ].
Ltac solve_rop_nocache rop_correct :=
  solve_rop' rop_correct ltac:(fun _ => idtac).
Ltac solve_rop rop_correct :=
  solve_rop'
    rop_correct
    ltac:(fun _ => let G := get_goal in fail 2 "Could not find a solution in reify_gen_cache for" G).
Ltac solve_rcarry_mul := solve_rop rcarry_mul_correct.
Ltac solve_rcarry_mul_nocache := solve_rop_nocache rcarry_mul_correct.
Ltac solve_rcarry := solve_rop rcarry_correct.
Ltac solve_radd := solve_rop radd_correct.
Ltac solve_rsub := solve_rop rsub_correct.
Ltac solve_ropp := solve_rop ropp_correct.
Ltac solve_rencode := solve_rop rencode_correct.
Ltac solve_rrelax := solve_rop rrelax_correct.
Ltac solve_rzero := solve_rop rzero_correct.
Ltac solve_rone := solve_rop rone_correct.

Module PrintingNotations.
  Export ident.
  (*Global Set Printing Width 100000.*)
  Open Scope zrange_scope.
  Notation "'uint256'"
    := (r[0 ~> 115792089237316195423570985008687907853269984665640564039457584007913129639935]%zrange) : zrange_scope.
  Notation "'uint128'"
    := (r[0 ~> 340282366920938463463374607431768211455]%zrange) : zrange_scope.
  Notation "'uint64'"
    := (r[0 ~> 18446744073709551615]) : zrange_scope.
  Notation "'uint32'"
    := (r[0 ~> 4294967295]) : zrange_scope.
  Notation "'bool'"
    := (r[0 ~> 1]%zrange) : zrange_scope.
  Notation "ls [[ n ]]"
    := ((List.nth_default_concrete _ n @@ ls)%expr)
         (at level 30, format "ls [[ n ]]") : expr_scope.
  Notation "( range )( ls [[ n ]] )"
    := ((ident.Z.cast range @@ (List.nth_default_concrete _ n @@ ls))%expr)
         (format "( range )( ls [[ n ]] )") : expr_scope.
  (*Notation "( range )( v )" := (ident.Z.cast range @@ v)%expr : expr_scope.*)
  Notation "x *₂₅₆ y"
    := (ident.Z.cast uint256 @@ (ident.Z.mul @@ (x, y)))%expr (at level 40) : expr_scope.
  Notation "x *₁₂₈ y"
    := (ident.Z.cast uint128 @@ (ident.Z.mul @@ (x, y)))%expr (at level 40) : expr_scope.
  Notation "x *₆₄ y"
    := (ident.Z.cast uint64 @@ (ident.Z.mul @@ (x, y)))%expr (at level 40) : expr_scope.
  Notation "x *₃₂ y"
    := (ident.Z.cast uint32 @@ (ident.Z.mul @@ (x, y)))%expr (at level 40) : expr_scope.
  Notation "x +₂₅₆ y"
    := (ident.Z.cast uint256 @@ (ident.Z.add @@ (x, y)))%expr (at level 50) : expr_scope.
  Notation "x +₁₂₈ y"
    := (ident.Z.cast uint128 @@ (ident.Z.add @@ (x, y)))%expr (at level 50) : expr_scope.
  Notation "x +₆₄ y"
    := (ident.Z.cast uint64 @@ (ident.Z.add @@ (x, y)))%expr (at level 50) : expr_scope.
  Notation "x +₃₂ y"
    := (ident.Z.cast uint32 @@ (ident.Z.add @@ (x, y)))%expr (at level 50) : expr_scope.
  Notation "x -₁₂₈ y"
    := (ident.Z.cast uint128 @@ (ident.Z.sub @@ (x, y)))%expr (at level 50) : expr_scope.
  Notation "x -₆₄ y"
    := (ident.Z.cast uint64 @@ (ident.Z.sub @@ (x, y)))%expr (at level 50) : expr_scope.
  Notation "x -₃₂ y"
    := (ident.Z.cast uint32 @@ (ident.Z.sub @@ (x, y)))%expr (at level 50) : expr_scope.
  Notation "( out_t )( v >> count )"
    := ((ident.Z.cast out_t @@ (ident.Z.shiftr count @@ v))%expr)
         (format "( out_t )( v  >>  count )") : expr_scope.
  Notation "( out_t )( v << count )"
    := ((ident.Z.cast out_t @@ (ident.Z.shiftl count @@ v))%expr)
         (format "( out_t )( v  <<  count )") : expr_scope.
  Notation "( range )( v )"
    := ((ident.Z.cast range @@ Var v)%expr)
         (format "( range )( v )") : expr_scope.
  Notation "( ( out_t )( v ) & mask )"
    := ((ident.Z.cast out_t @@ (ident.Z.land mask @@ v))%expr)
         (format "( ( out_t )( v )  &  mask )")
       : expr_scope.

  Notation "x" := (ident.Z.cast _ @@ Var x)%expr (only printing, at level 9) : expr_scope.
  Notation "x" := (ident.Z.cast2 _ @@ Var x)%expr (only printing, at level 9) : expr_scope.
  Notation "v ₁" := (ident.fst @@ Var v)%expr (at level 10, format "v ₁") : expr_scope.
  Notation "v ₂" := (ident.snd @@ Var v)%expr (at level 10, format "v ₂") : expr_scope.
  Notation "v ₁" := (ident.Z.cast _ @@ (ident.fst @@ Var v))%expr (at level 10, format "v ₁") : expr_scope.
  Notation "v ₂" := (ident.Z.cast _ @@ (ident.snd @@ Var v))%expr (at level 10, format "v ₂") : expr_scope.
  Notation "v ₁" := (ident.Z.cast _ @@ (ident.fst @@ (ident.Z.cast2 _ @@ Var v)))%expr (at level 10, format "v ₁") : expr_scope.
  Notation "v ₂" := (ident.Z.cast _ @@ (ident.snd @@ (ident.Z.cast2 _ @@ Var v)))%expr (at level 10, format "v ₂") : expr_scope.

  (*Notation "ls [[ n ]]" := (List.nth_default_concrete _ n @@ ls)%expr : expr_scope.
  Notation "( range )( v )" := (ident.Z.cast range @@ v)%expr : expr_scope.
  Notation "x *₁₂₈ y"
    := (ident.Z.cast uint128 @@ (ident.Z.mul (x, y)))%expr (at level 40) : expr_scope.
  Notation "( out_t )( v >> count )"
    := (ident.Z.cast out_t (ident.Z.shiftr count @@ v)%expr)
         (format "( out_t )( v  >>  count )") : expr_scope.
  Notation "( out_t )( v >> count )"
    := (ident.Z.cast out_t (ident.Z.shiftr count @@ v)%expr)
         (format "( out_t )( v  >>  count )") : expr_scope.
  Notation "v ₁" := (ident.fst @@ v)%expr (at level 10, format "v ₁") : expr_scope.
  Notation "v ₂" := (ident.snd @@ v)%expr (at level 10, format "v ₂") : expr_scope.*)
  (*
  Notation "'ℤ'"
    := BoundsAnalysis.type.Z : zrange_scope.
  Notation "ls [[ n ]]" := (List.nth n @@ ls)%nexpr : nexpr_scope.
  Notation "x *₆₄₋₆₄₋₁₂₈ y"
    := (mul uint64 uint64 uint128 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x *₆₄₋₆₄₋₆₄ y"
    := (mul uint64 uint64 uint64 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x *₃₂₋₃₂₋₃₂ y"
    := (mul uint32 uint32 uint32 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x *₃₂₋₁₂₈₋₁₂₈ y"
    := (mul uint32 uint128 uint128 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x *₃₂₋₆₄₋₆₄ y"
    := (mul uint32 uint64 uint64 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x *₃₂₋₃₂₋₆₄ y"
    := (mul uint32 uint32 uint64 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x +₁₂₈ y"
    := (add uint128 uint128 uint128 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x +₆₄₋₁₂₈₋₁₂₈ y"
    := (add uint64 uint128 uint128 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x +₃₂₋₆₄₋₆₄ y"
    := (add uint32 uint64 uint64 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x +₆₄ y"
    := (add uint64 uint64 uint64 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x +₃₂ y"
    := (add uint32 uint32 uint32 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x -₁₂₈ y"
    := (sub uint128 uint128 uint128 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x -₆₄₋₁₂₈₋₁₂₈ y"
    := (sub uint64 uint128 uint128 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x -₃₂₋₆₄₋₆₄ y"
    := (sub uint32 uint64 uint64 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x -₆₄ y"
    := (sub uint64 uint64 uint64 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x -₃₂ y"
    := (sub uint32 uint32 uint32 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x" := ({| BoundsAnalysis.type.value := x |}) (only printing) : nexpr_scope.
  Notation "( out_t )( v >> count )"
    := ((shiftr _ out_t count @@ v)%nexpr)
         (format "( out_t )( v  >>  count )")
       : nexpr_scope.
  Notation "( out_t )( v << count )"
    := ((shiftl _ out_t count @@ v)%nexpr)
         (format "( out_t )( v  <<  count )")
       : nexpr_scope.
  Notation "( ( out_t ) v & mask )"
    := ((land _ out_t mask @@ v)%nexpr)
         (format "( ( out_t ) v  &  mask )")
       : nexpr_scope.
*)
  (* TODO: come up with a better notation for arithmetic with carries
  that still distinguishes it from arithmetic without carries? *)
  Local Notation "'TwoPow256'" := 115792089237316195423570985008687907853269984665640564039457584007913129639936 (only parsing).
  Notation "'ADD_256' ( x ,  y )" := (ident.Z.cast2 (uint256, bool)%core @@ (ident.Z.add_get_carry_concrete TwoPow256 @@ (x, y)))%expr : expr_scope.
  Notation "'ADD_128' ( x ,  y )" := (ident.Z.cast2 (uint128, bool)%core @@ (ident.Z.add_get_carry_concrete TwoPow256 @@ (x, y)))%expr : expr_scope.
  Notation "'ADDC_256' ( x ,  y ,  z )" := (ident.Z.cast2 (uint256, bool)%core @@ (ident.Z.add_with_get_carry_concrete TwoPow256 @@ (x, y, z)))%expr : expr_scope.
  Notation "'ADDC_128' ( x ,  y ,  z )" := (ident.Z.cast2 (uint128, bool)%core @@ (ident.Z.add_with_get_carry_concrete TwoPow256 @@ (x, y, z)))%expr : expr_scope.
  Notation "'SUB_256' ( x ,  y )" := (ident.Z.cast2 (uint256, bool)%core @@ (ident.Z.sub_get_borrow_concrete TwoPow256 @@ (x, y)))%expr : expr_scope.
  Notation "'SUBB_256' ( x ,  y , z )" := (ident.Z.cast2 (uint256, bool)%core @@ (ident.Z.sub_with_get_borrow_concrete TwoPow256 @@ (x, y, z)))%expr : expr_scope.
  Notation "'ADDM' ( x ,  y ,  z )" := (ident.Z.cast uint256 @@ (ident.Z.add_modulo @@ (x, y, z)))%expr : expr_scope.
  Notation "'RSHI' ( x ,  y ,  z )" := (ident.Z.cast _ @@ (ident.Z.rshi_concrete _ z @@ (x, y)))%expr : expr_scope.
  Notation "'SELC' ( x ,  y ,  z )" := (ident.Z.cast uint256 @@ (ident.Z.zselect @@ (x, y, z)))%expr : expr_scope.
  Notation "'SELM' ( x ,  y ,  z )" := (ident.Z.cast uint256 @@ (ident.Z.zselect @@ (Z.cast bool @@ (Z.cc_m_concrete _ @@ x), y, z)))%expr : expr_scope.
  Notation "'SELL' ( x ,  y ,  z )" := (ident.Z.cast uint256 @@ (ident.Z.zselect @@ (Z.cast bool @@ (Z.land 1 @@ x), y, z)))%expr : expr_scope.
End PrintingNotations.

(*
Notation "a ∈ b" := (ZRange.type.is_bounded_by b%zrange a = true) (at level 10) : type_scope.
Notation Interp := (expr.Interp _).
Notation "'ℤ'" := (type.type_primitive type.Z).
Set Printing Width 70.
Goal False.
  let rop' := Reify (fun v1v2 : Z * Z => fst v1v2 + snd v1v2) in
  pose rop' as rop.
  pose (@Pipeline.BoundsPipeline_full
          false (fun v => Some v) (type.Z * type.Z) type.Z
          rop
          (r[0~>10], r[0~>10])%zrange
          r[0~>20]%zrange
       ) as E.
  simple refine (let Ev := _ in
                 let compiler_outputs_Ev : E = Pipeline.Success Ev := _ in
                 _); [ shelve | .. ]; revgoals.
  clearbody compiler_outputs_Ev.
  refine (let H' :=
              (fun H'' =>
                 @Pipeline.BoundsPipeline_full_correct
                   _ _
                   H'' _ _ _ _ _ _ compiler_outputs_Ev) _
          in _);
    clearbody H'.
  Focus 2.
  { cbv [Pipeline.BoundsPipeline_full] in E.
    remember (Pipeline.PrePipeline rop) as cache eqn:Hcache in (value of E).
    lazy in Hcache.
    subst cache.
    lazy in E.
    subst E Ev; reflexivity.
  } Unfocus.
  cbv [rop] in H'; cbn [expr.Interp expr.interp for_reification.ident.interp] in H'.
(*
  H' : forall arg : type.interp (ℤ * ℤ),
       arg ∈ (r[0 ~> 10], r[0 ~> 10]) ->
       (Interp Ev arg) ∈ r[0 ~> 20] /\
       Interp Ev arg = fst arg + snd arg
*)
Abort.
*)

Time Redirect "log" Compute
     (Pipeline.BoundsPipeline_full
        true (relax_zrange_gen [64; 128])
        ltac:(let r := Reify (to_associational (weight 51 1) 5) in
              exact r)
               ZRange.type.option.None ZRange.type.option.None).

(* N.B. When the uncurrying PR lands, we will no longer need to
   manually uncurry this function example before reification *)
Time Redirect "log" Compute
     (Pipeline.BoundsPipeline_full
        true (relax_zrange_gen [64; 128])
        ltac:(let r := Reify (fun '(x, y) => scmul (weight 51 1) 5 x y) in
              exact r)
               ZRange.type.option.None ZRange.type.option.None).

(* TODO: move to top *)
Import Coq.Classes.Equivalence.

Module X25519_64.
  Definition n := 5%nat.
  Definition s := 2^255.
  Definition c := [(1, 19)].
  Definition machine_wordsize := 64.

  Derive base_51_relax
         SuchThat (rrelax_correctT n s c machine_wordsize base_51_relax)
         As base_51_relax_correct.
  Proof. Time solve_rrelax machine_wordsize. Time Qed.
  Derive base_51_carry_mul
         SuchThat (rcarry_mul_correctT n s c machine_wordsize base_51_carry_mul)
         As base_51_carry_mul_correct.
  Proof. Time solve_rcarry_mul machine_wordsize. Time Qed.
  Derive base_51_carry
         SuchThat (rcarry_correctT n s c machine_wordsize base_51_carry)
         As base_51_carry_correct.
  Proof. Time solve_rcarry machine_wordsize. Time Qed.
  Derive base_51_add
         SuchThat (radd_correctT n s c machine_wordsize base_51_add)
         As base_51_add_correct.
  Proof. Time solve_radd machine_wordsize. Time Qed.
  Derive base_51_sub
         SuchThat (rsub_correctT n s c machine_wordsize base_51_sub)
         As base_51_sub_correct.
  Proof. Time solve_rsub machine_wordsize. Time Qed.
  Derive base_51_opp
         SuchThat (ropp_correctT n s c machine_wordsize base_51_opp)
         As base_51_opp_correct.
  Proof. Time solve_ropp machine_wordsize. Time Qed.
  Derive base_51_encode
         SuchThat (rencode_correctT n s c machine_wordsize base_51_encode)
         As base_51_encode_correct.
  Proof. Time solve_rencode machine_wordsize. Time Qed.
  Derive base_51_zero
         SuchThat (rzero_correctT n s c machine_wordsize base_51_zero)
         As base_51_zero_correct.
  Proof. Time solve_rzero machine_wordsize. Time Qed.
  Derive base_51_one
         SuchThat (rone_correctT n s c machine_wordsize base_51_one)
         As base_51_one_correct.
  Proof. Time solve_rone machine_wordsize. Time Qed.
  Lemma base_51_curve_good
    : check_args n s c machine_wordsize (Pipeline.Success tt) = Pipeline.Success tt.
  Proof using Type. vm_compute; reflexivity. Qed.

  Definition base_51_good : GoodT n s c
    := Good n s c machine_wordsize
            base_51_curve_good
            base_51_carry_mul_correct
            base_51_carry_correct
            base_51_relax_correct
            base_51_add_correct
            base_51_sub_correct
            base_51_opp_correct
            base_51_zero_correct
            base_51_one_correct
            base_51_encode_correct.

  Print Assumptions base_51_good.
  Import PrintingNotations.
  Set Printing Width 80.
  Redirect "log" Print base_51_carry_mul.
(*base_51_carry_mul =
fun var : type -> Type =>
(λ x : var
         (type.list (type.type_primitive type.Z) *
          type.list (type.type_primitive type.Z))%ctype,
 expr_let x0 := x₁ [[0]] *₁₂₈ x₂ [[0]] +₁₂₈
                (x₁ [[1]] *₁₂₈ (19 * (uint64)(x₂[[4]])) +₁₂₈
                 (x₁ [[2]] *₁₂₈ (19 * (uint64)(x₂[[3]])) +₁₂₈
                  (x₁ [[3]] *₁₂₈ (19 * (uint64)(x₂[[2]])) +₁₂₈
                   x₁ [[4]] *₁₂₈ (19 * (uint64)(x₂[[1]]))))) in
 expr_let x1 := (uint64)(x0 >> 51) +₁₂₈
                (x₁ [[0]] *₁₂₈ x₂ [[1]] +₁₂₈
                 (x₁ [[1]] *₁₂₈ x₂ [[0]] +₁₂₈
                  (x₁ [[2]] *₁₂₈ (19 * (uint64)(x₂[[4]])) +₁₂₈
                   (x₁ [[3]] *₁₂₈ (19 * (uint64)(x₂[[3]])) +₁₂₈
                    x₁ [[4]] *₁₂₈ (19 * (uint64)(x₂[[2]])))))) in
 expr_let x2 := (uint64)(x1 >> 51) +₁₂₈
                (x₁ [[0]] *₁₂₈ x₂ [[2]] +₁₂₈
                 (x₁ [[1]] *₁₂₈ x₂ [[1]] +₁₂₈
                  (x₁ [[2]] *₁₂₈ x₂ [[0]] +₁₂₈
                   (x₁ [[3]] *₁₂₈ (19 * (uint64)(x₂[[4]])) +₁₂₈
                    x₁ [[4]] *₁₂₈ (19 * (uint64)(x₂[[3]])))))) in
 expr_let x3 := (uint64)(x2 >> 51) +₁₂₈
                (x₁ [[0]] *₁₂₈ x₂ [[3]] +₁₂₈
                 (x₁ [[1]] *₁₂₈ x₂ [[2]] +₁₂₈
                  (x₁ [[2]] *₁₂₈ x₂ [[1]] +₁₂₈
                   (x₁ [[3]] *₁₂₈ x₂ [[0]] +₁₂₈
                    x₁ [[4]] *₁₂₈ (19 * (uint64)(x₂[[4]])))))) in
 expr_let x4 := (uint64)(x3 >> 51) +₁₂₈
                (x₁ [[0]] *₁₂₈ x₂ [[4]] +₁₂₈
                 (x₁ [[1]] *₁₂₈ x₂ [[3]] +₁₂₈
                  (x₁ [[2]] *₁₂₈ x₂ [[2]] +₁₂₈
                   (x₁ [[3]] *₁₂₈ x₂ [[1]] +₁₂₈ x₁ [[4]] *₁₂₈ x₂ [[0]])))) in
 expr_let x5 := ((uint64)(x0) & 2251799813685247) +₆₄ 19 *₆₄ (uint64)(x4 >> 51) in
 expr_let x6 := (uint64)(x5 >> 51) +₆₄ ((uint64)(x1) & 2251799813685247) in
 ((uint64)(x5) & 2251799813685247)
 :: ((uint64)(x6) & 2251799813685247)
    :: (uint64)(x6 >> 51) +₆₄ ((uint64)(x2) & 2251799813685247)
       :: ((uint64)(x3) & 2251799813685247)
          :: ((uint64)(x4) & 2251799813685247) :: [])%expr
     : Expr
         (type.uncurry
            (type.list (type.type_primitive type.Z) ->
             type.list (type.type_primitive type.Z) ->
             type.list (type.type_primitive type.Z)))
*)
  Redirect "log" Print base_51_sub.
  (*
base_51_sub =
fun var : type -> Type =>
(λ x : var
         (type.list (type.type_primitive type.Z) *
          type.list (type.type_primitive type.Z))%ctype,
 (4503599627370458 + (uint64)(x₁[[0]])) -₆₄ x₂ [[0]]
 :: (4503599627370494 + (uint64)(x₁[[1]])) -₆₄ x₂ [[1]]
    :: (4503599627370494 + (uint64)(x₁[[2]])) -₆₄ x₂ [[2]]
       :: (4503599627370494 + (uint64)(x₁[[3]])) -₆₄ x₂ [[3]]
          :: (4503599627370494 + (uint64)(x₁[[4]])) -₆₄ x₂ [[4]] :: [])%expr
     : Expr
         (type.uncurry
            (type.list (type.type_primitive type.Z) ->
             type.list (type.type_primitive type.Z) ->
             type.list (type.type_primitive type.Z)))
*)
End X25519_64.

(** TODO: factor out bounds analysis pipeline as a single definition / proof *)
(** TODO: factor out apply one argument in the fst of a pair *)
(** TODO: write a definition that specializes the PHOAS thing and composes with bounds analysis, + proof *)
(** TODO: write wrappers for (string) prime -> reified arguments *)
(** TODO: write indexed AST interp that returns default value, prove that given correctness for specialized thing, the defaulting interp is totally equal to the original operation *)
(** TODO: write a lemma that for things equal to all operations using defaulting interp, we get a ring isomorphic to F m *)
(** TODO: compose with stringification + wrappers for prime, extract to OCaml/Haskell *)
(** TODO: proofs *)
(*
Module X25519_32.
  Definition n := 10%nat.
  Definition s := 2^255.
  Definition c := [(1, 19)].
  Definition machine_wordsize := 32.

  Derive base_25p5_sub
         SuchThat (rsub_correctT n s c machine_wordsize base_25p5_sub)
         As base_25p5_sub_correct.
  Proof. Time solve_rsub machine_wordsize. Time Qed.

  Derive base_25p5_carry_mul
         SuchThat (rcarry_mul_correctT n s c machine_wordsize base_25p5_carry_mul)
         As base_25p5_carry_mul_correct.
  Proof. Time solve_rcarry_mul machine_wordsize. Time Qed.

  Import PrintingNotations.
  Print base_25p5_carry_mul.
(*
base_25p5_carry_mul =
fun var : type -> Type =>
(λ x : var (type.list (type.type_primitive type.Z) * type.list (type.type_primitive type.Z))%ctype,
 expr_let x0 := x₁ [[0]] *₆₄ x₂ [[0]] +₆₄
                ((uint64)(x₁ [[1]] *₆₄ (19 * (uint32)(x₂[[9]])) << 1) +₆₄
                 (x₁ [[2]] *₆₄ (19 * (uint32)(x₂[[8]])) +₆₄
                  ((uint64)(x₁ [[3]] *₆₄ (19 * (uint32)(x₂[[7]])) << 1) +₆₄
                   (x₁ [[4]] *₆₄ (19 * (uint32)(x₂[[6]])) +₆₄
                    ((uint64)(x₁ [[5]] *₆₄ (19 * (uint32)(x₂[[5]])) << 1) +₆₄
                     (x₁ [[6]] *₆₄ (19 * (uint32)(x₂[[4]])) +₆₄
                      ((uint64)(x₁ [[7]] *₆₄ (19 * (uint32)(x₂[[3]])) << 1) +₆₄
                       (x₁ [[8]] *₆₄ (19 * (uint32)(x₂[[2]])) +₆₄ (uint64)(x₁ [[9]] *₆₄ (19 * (uint32)(x₂[[1]])) << 1))))))))) in
 expr_let x1 := (uint64)(x0 >> 26) +₆₄
                (x₁ [[0]] *₆₄ x₂ [[1]] +₆₄
                 (x₁ [[1]] *₆₄ x₂ [[0]] +₆₄
                  (x₁ [[2]] *₆₄ (19 * (uint32)(x₂[[9]])) +₆₄
                   (x₁ [[3]] *₆₄ (19 * (uint32)(x₂[[8]])) +₆₄
                    (x₁ [[4]] *₆₄ (19 * (uint32)(x₂[[7]])) +₆₄
                     (x₁ [[5]] *₆₄ (19 * (uint32)(x₂[[6]])) +₆₄
                      (x₁ [[6]] *₆₄ (19 * (uint32)(x₂[[5]])) +₆₄
                       (x₁ [[7]] *₆₄ (19 * (uint32)(x₂[[4]])) +₆₄
                        (x₁ [[8]] *₆₄ (19 * (uint32)(x₂[[3]])) +₆₄ x₁ [[9]] *₆₄ (19 * (uint32)(x₂[[2]]))))))))))) in
 expr_let x2 := (uint64)(x1 >> 25) +₆₄
                (x₁ [[0]] *₆₄ x₂ [[2]] +₆₄
                 ((uint64)(x₁ [[1]] *₆₄ x₂ [[1]] << 1) +₆₄
                  (x₁ [[2]] *₆₄ x₂ [[0]] +₆₄
                   ((uint64)(x₁ [[3]] *₆₄ (19 * (uint32)(x₂[[9]])) << 1) +₆₄
                    (x₁ [[4]] *₆₄ (19 * (uint32)(x₂[[8]])) +₆₄
                     ((uint64)(x₁ [[5]] *₆₄ (19 * (uint32)(x₂[[7]])) << 1) +₆₄
                      (x₁ [[6]] *₆₄ (19 * (uint32)(x₂[[6]])) +₆₄
                       ((uint64)(x₁ [[7]] *₆₄ (19 * (uint32)(x₂[[5]])) << 1) +₆₄
                        (x₁ [[8]] *₆₄ (19 * (uint32)(x₂[[4]])) +₆₄ (uint64)(x₁ [[9]] *₆₄ (19 * (uint32)(x₂[[3]])) << 1)))))))))) in
 expr_let x3 := (uint64)(x2 >> 26) +₆₄
                (x₁ [[0]] *₆₄ x₂ [[3]] +₆₄
                 (x₁ [[1]] *₆₄ x₂ [[2]] +₆₄
                  (x₁ [[2]] *₆₄ x₂ [[1]] +₆₄
                   (x₁ [[3]] *₆₄ x₂ [[0]] +₆₄
                    (x₁ [[4]] *₆₄ (19 * (uint32)(x₂[[9]])) +₆₄
                     (x₁ [[5]] *₆₄ (19 * (uint32)(x₂[[8]])) +₆₄
                      (x₁ [[6]] *₆₄ (19 * (uint32)(x₂[[7]])) +₆₄
                       (x₁ [[7]] *₆₄ (19 * (uint32)(x₂[[6]])) +₆₄
                        (x₁ [[8]] *₆₄ (19 * (uint32)(x₂[[5]])) +₆₄ x₁ [[9]] *₆₄ (19 * (uint32)(x₂[[4]]))))))))))) in
 expr_let x4 := (uint64)(x3 >> 25) +₆₄
                (x₁ [[0]] *₆₄ x₂ [[4]] +₆₄
                 ((uint64)(x₁ [[1]] *₆₄ x₂ [[3]] << 1) +₆₄
                  (x₁ [[2]] *₆₄ x₂ [[2]] +₆₄
                   ((uint64)(x₁ [[3]] *₆₄ x₂ [[1]] << 1) +₆₄
                    (x₁ [[4]] *₆₄ x₂ [[0]] +₆₄
                     ((uint64)(x₁ [[5]] *₆₄ (19 * (uint32)(x₂[[9]])) << 1) +₆₄
                      (x₁ [[6]] *₆₄ (19 * (uint32)(x₂[[8]])) +₆₄
                       ((uint64)(x₁ [[7]] *₆₄ (19 * (uint32)(x₂[[7]])) << 1) +₆₄
                        (x₁ [[8]] *₆₄ (19 * (uint32)(x₂[[6]])) +₆₄ (uint64)(x₁ [[9]] *₆₄ (19 * (uint32)(x₂[[5]])) << 1)))))))))) in
 expr_let x5 := (uint64)(x4 >> 26) +₆₄
                (x₁ [[0]] *₆₄ x₂ [[5]] +₆₄
                 (x₁ [[1]] *₆₄ x₂ [[4]] +₆₄
                  (x₁ [[2]] *₆₄ x₂ [[3]] +₆₄
                   (x₁ [[3]] *₆₄ x₂ [[2]] +₆₄
                    (x₁ [[4]] *₆₄ x₂ [[1]] +₆₄
                     (x₁ [[5]] *₆₄ x₂ [[0]] +₆₄
                      (x₁ [[6]] *₆₄ (19 * (uint32)(x₂[[9]])) +₆₄
                       (x₁ [[7]] *₆₄ (19 * (uint32)(x₂[[8]])) +₆₄
                        (x₁ [[8]] *₆₄ (19 * (uint32)(x₂[[7]])) +₆₄ x₁ [[9]] *₆₄ (19 * (uint32)(x₂[[6]]))))))))))) in
 expr_let x6 := (uint64)(x5 >> 25) +₆₄
                (x₁ [[0]] *₆₄ x₂ [[6]] +₆₄
                 ((uint64)(x₁ [[1]] *₆₄ x₂ [[5]] << 1) +₆₄
                  (x₁ [[2]] *₆₄ x₂ [[4]] +₆₄
                   ((uint64)(x₁ [[3]] *₆₄ x₂ [[3]] << 1) +₆₄
                    (x₁ [[4]] *₆₄ x₂ [[2]] +₆₄
                     ((uint64)(x₁ [[5]] *₆₄ x₂ [[1]] << 1) +₆₄
                      (x₁ [[6]] *₆₄ x₂ [[0]] +₆₄
                       ((uint64)(x₁ [[7]] *₆₄ (19 * (uint32)(x₂[[9]])) << 1) +₆₄
                        (x₁ [[8]] *₆₄ (19 * (uint32)(x₂[[8]])) +₆₄ (uint64)(x₁ [[9]] *₆₄ (19 * (uint32)(x₂[[7]])) << 1)))))))))) in
 expr_let x7 := (uint64)(x6 >> 26) +₆₄
                (x₁ [[0]] *₆₄ x₂ [[7]] +₆₄
                 (x₁ [[1]] *₆₄ x₂ [[6]] +₆₄
                  (x₁ [[2]] *₆₄ x₂ [[5]] +₆₄
                   (x₁ [[3]] *₆₄ x₂ [[4]] +₆₄
                    (x₁ [[4]] *₆₄ x₂ [[3]] +₆₄
                     (x₁ [[5]] *₆₄ x₂ [[2]] +₆₄
                      (x₁ [[6]] *₆₄ x₂ [[1]] +₆₄
                       (x₁ [[7]] *₆₄ x₂ [[0]] +₆₄ (x₁ [[8]] *₆₄ (19 * (uint32)(x₂[[9]])) +₆₄ x₁ [[9]] *₆₄ (19 * (uint32)(x₂[[8]]))))))))))) in
 expr_let x8 := (uint64)(x7 >> 25) +₆₄
                (x₁ [[0]] *₆₄ x₂ [[8]] +₆₄
                 ((uint64)(x₁ [[1]] *₆₄ x₂ [[7]] << 1) +₆₄
                  (x₁ [[2]] *₆₄ x₂ [[6]] +₆₄
                   ((uint64)(x₁ [[3]] *₆₄ x₂ [[5]] << 1) +₆₄
                    (x₁ [[4]] *₆₄ x₂ [[4]] +₆₄
                     ((uint64)(x₁ [[5]] *₆₄ x₂ [[3]] << 1) +₆₄
                      (x₁ [[6]] *₆₄ x₂ [[2]] +₆₄
                       ((uint64)(x₁ [[7]] *₆₄ x₂ [[1]] << 1) +₆₄
                        (x₁ [[8]] *₆₄ x₂ [[0]] +₆₄ (uint64)(x₁ [[9]] *₆₄ (19 * (uint32)(x₂[[9]])) << 1)))))))))) in
 expr_let x9 := (uint64)(x8 >> 26) +₆₄
                (x₁ [[0]] *₆₄ x₂ [[9]] +₆₄
                 (x₁ [[1]] *₆₄ x₂ [[8]] +₆₄
                  (x₁ [[2]] *₆₄ x₂ [[7]] +₆₄
                   (x₁ [[3]] *₆₄ x₂ [[6]] +₆₄
                    (x₁ [[4]] *₆₄ x₂ [[5]] +₆₄
                     (x₁ [[5]] *₆₄ x₂ [[4]] +₆₄
                      (x₁ [[6]] *₆₄ x₂ [[3]] +₆₄ (x₁ [[7]] *₆₄ x₂ [[2]] +₆₄ (x₁ [[8]] *₆₄ x₂ [[1]] +₆₄ x₁ [[9]] *₆₄ x₂ [[0]]))))))))) in
 expr_let x10 := ((uint32)(x0) & 67108863) +₆₄ 19 *₆₄ (uint64)(x9 >> 25) in
 expr_let x11 := (uint32)(x10 >> 26) +₃₂ ((uint32)(x1) & 33554431) in
 ((uint32)(x10) & 67108863)
 :: ((uint32)(x11) & 33554431)
    :: (uint32)(x11 >> 25) +₃₂ ((uint32)(x2) & 67108863)
       :: ((uint32)(x3) & 33554431)
          :: ((uint32)(x4) & 67108863)
             :: ((uint32)(x5) & 33554431)
                :: ((uint32)(x6) & 67108863)
                   :: ((uint32)(x7) & 33554431) :: ((uint32)(x8) & 67108863) :: ((uint32)(x9) & 33554431) :: [])%expr
     : Expr
         (type.uncurry
            (type.list (type.type_primitive type.Z) ->
             type.list (type.type_primitive type.Z) ->
             type.list (type.type_primitive type.Z)))
 *)
  Print base_25p5_sub.
  (*
base_25p5_sub =
fun var : type -> Type =>
(λ x : var
         (type.list (type.type_primitive type.Z) *
          type.list (type.type_primitive type.Z))%ctype,
 (134217690 + (uint32)(x₁[[0]])) -₃₂ x₂ [[0]]
 :: (67108862 + (uint32)(x₁[[1]])) -₃₂ x₂ [[1]]
    :: (134217726 + (uint32)(x₁[[2]])) -₃₂ x₂ [[2]]
       :: (67108862 + (uint32)(x₁[[3]])) -₃₂ x₂ [[3]]
          :: (134217726 + (uint32)(x₁[[4]])) -₃₂ x₂ [[4]]
             :: (67108862 + (uint32)(x₁[[5]])) -₃₂ x₂ [[5]]
                :: (134217726 + (uint32)(x₁[[6]])) -₃₂ x₂ [[6]]
                   :: (67108862 + (uint32)(x₁[[7]])) -₃₂ x₂ [[7]]
                      :: (134217726 + (uint32)(x₁[[8]])) -₃₂ x₂ [[8]]
                         :: (67108862 + (uint32)(x₁[[9]])) -₃₂ x₂ [[9]] :: [])%expr
     : Expr
         (type.uncurry
            (type.list (type.type_primitive type.Z) ->
             type.list (type.type_primitive type.Z) ->
             type.list (type.type_primitive type.Z)))
*)
End X25519_32.
 *)

Module Straightline.
  Module expr.
    (* TODO: move these to a better location *)
    Module type.
      Definition primitive_eq_dec (a b : type.primitive) : {a = b} + {a <> b}.
      Proof. destruct a,b; auto; right; congruence. Defined.
      Fixpoint type_eq_dec (a b : type) : {a = b} + {a <> b}.
      Proof.
        destruct a, b; try solve [right; congruence]; [ | | | ].
        { destruct (primitive_eq_dec p p0); subst; [left | right]; congruence. }
        { destruct (type_eq_dec a1 b1); destruct (type_eq_dec a2 b2); subst; try solve [right; congruence].
          left; congruence. }
        { destruct (type_eq_dec a1 b1); destruct (type_eq_dec a2 b2); subst; try solve [right; congruence].
          left; congruence. }
        { destruct (type_eq_dec a b); [left | right]; congruence. }
      Defined.
    End type.

    Section with_var.
      Context {var : type.type -> Type}.
      Context {dummy_arrow : forall s d, var (s -> d)}. (* TODO: remove once arrow-containing pairs are removed at type level *)

      Let uexpr t := @Uncurried.expr.expr ident.ident var t.

      Section with_ident.
        Context {ident : type.type -> type.type -> Type}.
        Inductive scalar : type.type -> Type :=
        | Var t : var t -> scalar t
        | TT : scalar (type.type_primitive type.unit)
        | Nil t : scalar (type.list t)
        | Pair {a b} : scalar a -> scalar b -> scalar (a * b)
        | Cast : zrange -> scalar type.Z -> scalar type.Z
        | Cast2 : zrange * zrange -> scalar (type.Z*type.Z) -> scalar (type.Z*type.Z)
        | Fst {a b} : scalar (a * b) -> scalar a
        | Snd {a b} : scalar (a * b) -> scalar b
        | Shiftr : Z -> scalar type.Z -> scalar type.Z
        | Shiftl : Z -> scalar type.Z -> scalar type.Z
        | Land : Z -> scalar type.Z -> scalar type.Z
        | CC_m : Z -> scalar type.Z -> scalar type.Z
        | Primitive {t} : type.interp (type.type_primitive t) -> scalar t
        .

        Inductive expr : type.type -> Type :=
        | Scalar {t} : scalar t -> expr t
        | LetInAppIdentZ {s d} : zrange -> ident s (type.Z) -> scalar s -> (var (type.Z) -> expr d) -> expr d
        | LetInAppIdentZZ {s d} : zrange * zrange -> ident s (type.Z*type.Z) -> scalar s -> (var (type.Z*type.Z) -> expr d) -> expr d
        .

        Fixpoint dummy_scalar t : scalar t :=
          match t with
          | type.type_primitive p => Primitive (@DefaultValue.type.primitive.default p)
          | type.prod A B => Pair (dummy_scalar A) (dummy_scalar B)
          | type.arrow A B => Var _ (dummy_arrow A B)
          | type.list A => Nil A
          end.

        Definition dummy t : expr t := Scalar (dummy_scalar t).
      End with_ident.

      Definition of_uncurried_scalar_ident {s d} (idc : ident.ident s d)
        : scalar s -> option (scalar d) :=
        match idc in ident.ident s d return scalar s -> option (scalar d) with
        | ident.Z.cast r => fun args => Some (Cast r args)
        | ident.Z.cast2 r => fun args => Some (Cast2 r args)
        | @ident.fst A B => fun args => Some (Fst args)
        | @ident.snd A B => fun args => Some (Snd args)
        | ident.Z.shiftr n => fun args => Some (Shiftr n args)
        | ident.Z.shiftl n => fun args => Some (Shiftl n args)
        | ident.Z.land n => fun args => Some (Land n args)
        | ident.Z.cc_m_concrete s => fun args => Some (CC_m s args)
        | @ident.primitive p x => fun _ => Some (Primitive x)
        | _ => fun _ => None
        end.

      Fixpoint of_uncurried_scalar {t} (e : uexpr t) : option (scalar t) :=
          match e in Uncurried.expr.expr t return option (scalar t) with
          | expr.Var t v as e => Some (Var t v)
          | expr.TT as e => Some TT
          | expr.Pair A B a b
            => match of_uncurried_scalar a, of_uncurried_scalar b with
               | Some x, Some y => Some (Pair x y)
               | _, _ => None
               end
          | expr.AppIdent _ _ idc args
            => match of_uncurried_scalar args with
               | Some x => of_uncurried_scalar_ident idc x
               | None => None
               end
          | _ => None
          end.

      Fixpoint range_type t : Type :=
        match t with
        | type.type_primitive type.Z => zrange
        | type.prod x y => range_type x * range_type y
        | _ => unit
        end.

      Definition invert_cast {t} (e : uexpr t)
        : option (range_type t * uexpr t) :=
        match invert_AppIdent e with
        | Some (existT s (idc, x)) =>
          (match idc in ident.ident s t return uexpr s -> option (range_type t * uexpr t) with
           | ident.Z.cast r => fun x => Some (r, x)
           | ident.Z.cast2 r => fun x => Some (r, x)
           | _ => fun _ => None
           end) x
        | None => None
        end.

      (* ident.Let_In @@ (cast r x) => r, x *)
      Definition invert_LetInCast {tx tC} (args : uexpr (tx * (tx -> tC)))
        : option (range_type tx * uexpr tx * uexpr (tx -> tC)) :=
        match invert_Pair args with
        | Some (x, e) =>
          match invert_cast x with
          | Some (r, x') => Some (r, x', e)
          | None => None
          end
        | None => None
        end.

      Definition invert_LetInAppIdent {tx tC} (args : uexpr (tx * (tx -> tC)))
        : option { s : type.type & (range_type tx * ident.ident s tx * scalar s * (var tx -> uexpr tC))%type } :=
        match invert_LetInCast args with
        | Some (r, x, e) =>
          match invert_AppIdent x with
          | Some (existT s idc_x') =>
            match of_uncurried_scalar (snd idc_x') with
            | Some x'' =>
              match invert_Abs e with
              | Some k => Some (existT _ s (r, fst idc_x', x'', k))
              | None => None
              end
            | None => None
            end
          | None => None
          end
        | None => None
        end.

      Definition mk_LetInAppIdent {s d t} (default : expr t)
        : range_type d -> ident.ident s d -> scalar s -> (var d -> expr t) -> expr t :=
        match d as d0 return range_type d0 -> ident.ident s d0 -> scalar s -> (var d0 -> expr t) -> expr t with
        | type.type_primitive type.Z =>
          fun r idc x k => @LetInAppIdentZ ident.ident s t r idc x k
        | type.prod type.Z type.Z =>
          fun r idc x k => @LetInAppIdentZZ ident.ident s t r idc x k
        | _ => fun _ _ _ _ => default
        end.

      Definition of_uncurried_ident
                 (of_uncurried : forall t, uexpr t -> expr t)
                 {s d} (idc : ident.ident s d)
        : uexpr s -> expr d -> expr d :=
        match idc in ident.ident s d return uexpr s -> expr d -> expr d with
        | ident.Let_In tx tC =>
          fun args default =>
            match invert_LetInAppIdent args return expr tC with
            | Some (existT s (r, idc, x, k)) =>
              @mk_LetInAppIdent s tx tC default r idc x (fun y : var tx => of_uncurried _ (k y))
            | None => default
            end
        | ident.Z.cast r =>
          fun (args : uexpr _) default =>
            match invert_AppIdent args with
            | Some (existT s idc_x') =>
              match of_uncurried_scalar (snd idc_x') with
              | Some x'' =>
                @mk_LetInAppIdent s type.Z type.Z default r (fst idc_x') x'' (fun y => Scalar (Var _ y))
              | None => default
              end
            | None => default
            end
        | ident.Z.cast2 r =>
          fun (args : uexpr _) default =>
            match invert_AppIdent args with
            | Some (existT s idc_x') =>
              match of_uncurried_scalar (snd idc_x') with
              | Some x'' =>
                @mk_LetInAppIdent s (type.Z*type.Z) (type.Z*type.Z) default r (fst idc_x') x'' (fun y => Scalar (Var _ y))
              | None => default
              end
            | None => default
            end
        | _ => fun _ default => default
        end.

      Definition of_uncurried_step {t} (e : uexpr t)
                 (of_uncurried : forall t, uexpr t -> expr t)
                 : expr t -> expr t :=
        match e in Uncurried.expr.expr t return expr t -> expr t with
        | AppIdent s d idc args =>
          fun default =>
            of_uncurried_ident of_uncurried idc args
                               (match of_uncurried_scalar (AppIdent idc args) with
                                | Some s => Scalar s
                                | None => default
                                end)
         | _ as e  =>
           (fun default =>
              match of_uncurried_scalar e with
              | Some s => Scalar s
              | None => default
              end)
        end.

      (* TODO : uses fuel; ideally want a cleaner termination proof *)
      Fixpoint of_uncurried (fuel : nat) {t} (e : uexpr t)
        : expr t :=
        match fuel with
        | S fuel' => of_uncurried_step e (@of_uncurried fuel') (dummy t)
        | O => dummy t
        end.
    End with_var.

    Section depth.
      Context (var : type -> Type) (dummy_var : forall t, var t).
      Fixpoint depth {t} (e : @Uncurried.expr.expr ident var t) : nat :=
        match e with
        | Uncurried.expr.Var _ _ => 1
        | Uncurried.expr.TT => 1
        | Uncurried.expr.AppIdent _ _ idc args => S (depth args)
        | Uncurried.expr.App _ _ f x => S (Nat.max (depth f) (depth x))
        | Uncurried.expr.Pair _ _ x y => S (Nat.max (depth x) (depth y))
        | Uncurried.expr.Abs _ _ f => S (depth (f (dummy_var _)))
        end.

      Definition Expr_depth {t} (e : Expr t) : nat := depth (e _).
    End depth.

    Section interp.
      Context {ident : type -> type -> Type} {interp_ident : forall s d, ident s d -> type.interp s -> type.interp d}.
      Context {interp_cast : zrange -> Z -> Z}.

      Definition interp_cast2 (r : zrange * zrange) (x : Z * Z) : Z * Z :=
        (interp_cast (fst r) (fst x), interp_cast (snd r) (snd x)).

      Fixpoint interp_scalar {t} (s : @scalar type.interp t) : type.interp t :=
        match s with
        | Var t v => v
        | TT => tt
        | Nil _ => []
        | Pair _ _ x y => (interp_scalar x, interp_scalar y)
        | Cast r x => interp_cast r (interp_scalar x)
        | Cast2 r x => interp_cast2 r (interp_scalar x)
        | Fst _ _ p => fst (interp_scalar p)
        | Snd _ _ p => snd (interp_scalar p)
        | Shiftr n x => Z.shiftr (interp_scalar x) n
        | Shiftl n x => Z.shiftl (interp_scalar x) n
        | Land n x => Z.land (interp_scalar x) n
        | CC_m n x => Z.cc_m n (interp_scalar x)
        | Primitive _ x => x
        end.

      Fixpoint interp {t} (e : @expr type.interp ident t) : type.interp t :=
        match e with
        | Scalar _ s => interp_scalar s
        | LetInAppIdentZ _ _ r idc x f =>
          interp (f (interp_cast r (interp_ident _ _ idc (interp_scalar x))))
        | LetInAppIdentZZ _ _ r idc x f =>
          interp (f (interp_cast2 r (interp_ident _ _ idc (interp_scalar x))))
        end.
    End interp.

    Section proofs.
      Local Notation straightline_interp := (expr.interp (ident:=default.ident) (interp_ident:=@ident.interp) (interp_cast:=ident.cast (@ident.cast_outside_of_range))).
      Local Notation uinterp := (Uncurried.expr.interp (@ident.interp)).
      Local Notation uexpr := (@Uncurried.expr.expr ident type.interp).
      Local Notation interp_scalar := (interp_scalar (interp_cast:=ident.cast (@ident.cast_outside_of_range))).

      Inductive ok_scalar_ident : forall {s d}, ident.ident s d -> Prop :=
      | ok_si_cast : forall r, ok_scalar_ident (ident.Z.cast r)
      | ok_si_cast2 : forall r, ok_scalar_ident (ident.Z.cast2 r)
      | ok_si_fst : forall A B, ok_scalar_ident (@ident.fst A B)
      | ok_si_snd : forall A B, ok_scalar_ident (@ident.snd A B)
      | ok_si_shiftr : forall n, ok_scalar_ident (@ident.Z.shiftr n)
      | ok_si_shiftl : forall n, ok_scalar_ident (@ident.Z.shiftl n)
      | ok_si_land : forall n, ok_scalar_ident (@ident.Z.land n)
      | ok_si_cc_m : forall n, ok_scalar_ident (@ident.Z.cc_m_concrete n)
      | ok_prim : forall p x, ok_scalar_ident (@ident.primitive p x)
      .

      Inductive ok_scalar: forall {t}, uexpr t -> Prop :=
      | ok_Var : forall t v, @ok_scalar t (Uncurried.expr.Var v)
      | ok_TT : ok_scalar Uncurried.expr.TT
      | ok_AppIdent :
          forall s d idc args,
            ok_scalar args ->
            @ok_scalar_ident s d idc ->
            ok_scalar (AppIdent idc args)
      | ok_Pair :
          forall A B a b,
            @ok_scalar A a ->
            @ok_scalar B b ->
            ok_scalar (Uncurried.expr.Pair a b)
      .

      Inductive ok_expr : forall {t}, uexpr t -> Prop :=
      | ok_LetInAppIdentZ :
          forall tC r s (idc : ident s type.Z) x k,
            ok_scalar x -> (forall y, @ok_expr tC (k y)) ->
            @ok_expr tC (AppIdent (@ident.Let_In _ tC) (Uncurried.expr.Pair (AppIdent (ident.Z.cast r) (AppIdent idc x)) (Abs k)))
      | ok_LetInAppIdentZZ :
          forall tC r s (idc : ident s (type.prod type.Z type.Z)) x k,
            ok_scalar x -> (forall y, @ok_expr tC (k y)) ->
            @ok_expr tC (AppIdent (@ident.Let_In _ tC) (Uncurried.expr.Pair (AppIdent (ident.Z.cast2 r) (AppIdent idc x)) (Abs k)))
      | ok_scalar_cast :
          forall r s (idc : ident s  _) x,
            ok_scalar x ->
            @ok_expr type.Z (AppIdent (ident.Z.cast r) (AppIdent idc x))
      | ok_scalar_cast2 :
          forall r s (idc : ident s _) x,
            ok_scalar x ->
            @ok_expr (type.prod type.Z type.Z) (AppIdent (ident.Z.cast2 r) (AppIdent idc x))
      | ok_scalar_nocast :
          forall t x, @ok_scalar t x -> @ok_expr t x
      .

      Lemma interp_cast_correct r (x : uexpr type.Z) :
        ident.cast ident.cast_outside_of_range r (uinterp x) = uinterp (AppIdent (ident.Z.cast r) x).
      Proof using Type. reflexivity. Qed.

      Lemma interp_cast2_correct r (x : uexpr (type.prod type.Z type.Z)) :
        @interp_cast2 (ident.cast ident.cast_outside_of_range) r (uinterp x) = uinterp (AppIdent (ident.Z.cast2 r) x).
      Proof using Type. cbn; break_match; reflexivity. Qed.

      Ltac invert H :=
        inversion H; subst;
        repeat match goal with
               | H : existT _ _ _ = existT _ _ _ |- _ => apply (Eqdep_dec.inj_pair2_eq_dec _ type.type_eq_dec) in H; subst
               end.

      Ltac invert_ok_expr :=
        match goal with H : ok_expr _ |- _ => invert H end.
      Ltac invert_ok_scalar :=
        match goal with H : ok_scalar _ |- _ => invert H end.
      Ltac invert_ok_scalar_ident :=
        match goal with H : ok_scalar_ident _ |- _ => invert H end.
      Ltac simpl_inversions :=
        cbn [invert_LetInAppIdent invert_LetInCast invert_Pair invert_cast invert_AppIdent invert_Abs].

      Lemma invert_AppIdent_correct {d} (e : uexpr d) x p :
        invert_AppIdent e = Some (existT (fun s : type => (ident s d * default.expr s)%type) x p) ->
        e = AppIdent (fst p) (snd p).
      Proof using Type.
        cbv [invert_AppIdent].
        break_match; try discriminate.
        intro H; invert H. reflexivity.
      Qed.

      Lemma depth_positive {var t} dummy_var (e : Uncurried.expr.expr t) : 0 < depth var dummy_var e.
      Proof using Type. destruct e; cbn [depth]; rewrite Nat2Z.inj_succ; lia. Qed.

      Lemma of_uncurried_scalar_ident_correct {s d} (idc : ident s d) args args':
        ok_scalar_ident idc ->
        of_uncurried_scalar args = Some args' ->
        interp_scalar args' = uinterp args ->
        exists s,
          of_uncurried_scalar_ident idc args' = Some s
          /\ interp_scalar s = uinterp (AppIdent idc args).
      Proof using Type.
        destruct 1; intros;
          repeat match goal with
                 | _ => eexists; split; [ reflexivity | cbn [interp_scalar] ]
                 | H : interp_scalar _ = _ |- _ => rewrite H
                 | _ => reflexivity
                 | _ => solve [auto using interp_cast2_correct]
                 | |- context [@Uncurried.expr.interp _ _ (type.type_primitive _)] =>
                   cbn; break_match; reflexivity
                 end.
      Qed.

      Lemma of_uncurried_scalar_correct {t} (e : uexpr t) :
        ok_scalar e ->
        exists s,
          of_uncurried_scalar e = Some s
          /\ interp_scalar s = uinterp  e.
      Proof using Type.
        induction 1; cbn [of_uncurried_scalar]; intros;
          repeat match goal with
                 | _ => progress cbn [interp_scalar]
                 | IH : exists _, _ /\ _ |- _ => destruct IH as [? [? ?] ]
                 | H : of_uncurried_scalar _ = _ |- _ => rewrite H
                 | H : interp_scalar _ = _ |- _ => rewrite H
                 | _ => apply of_uncurried_scalar_ident_correct; solve [auto]
                 | _ => eexists; split; [ reflexivity | ]
                 | _ => reflexivity
                 end.
      Qed.

      Ltac rewrite_ok_scalar :=
        match goal with H : ok_scalar _ |- _ =>
                        let P := fresh in destruct (of_uncurried_scalar_correct _ H) as [? [P ?] ]; rewrite P in *
        end;
        repeat match goal with
               | H : Some _ = Some _ |- _ => inversion H; progress subst
               | _ => progress break_match;
                      match goal with | H: Some _ = Some _ |- _ => inversion H; progress subst end
               end.

      Lemma of_uncurried_correct dummy_arrow fuel dummy_var :
        forall {t} (e : uexpr t),
        (depth _ dummy_var e <= fuel)%nat ->
        ok_expr e ->
        uinterp e = straightline_interp (@of_uncurried _ dummy_arrow fuel _ e).
      Proof.
        induction fuel; intros; [ pose proof (depth_positive dummy_var e); lia | ].
        destruct e; cbn [depth of_uncurried expr.interp interp]; intros; invert_ok_expr;
          repeat match goal with
                 | |- context [of_uncurried_scalar _ ] => progress rewrite_ok_scalar
                 | _ => progress (cbn [of_uncurried_step of_uncurried_ident fst snd mk_LetInAppIdent expr.interp interp depth] in * )
                 | _ => progress simpl_inversions
                 | _ => congruence
                 end; [ | | | | ].
        {
          match goal with H : interp_scalar _ = _ |- _ => rewrite H end.
          rewrite <-IHfuel.
          { reflexivity. }
          { cbn [depth] in *.
            (* here we have to reason about the depth calculation for arrows; this will probably be unnecessary with new compilers setup *)
            admit. }
          { auto. } }
        {
          match goal with H : interp_scalar _ = _ |- _ => rewrite H end.
          rewrite <-IHfuel.
          { cbn; break_match; reflexivity. }
          { cbn [depth] in *.
            (* here we have to reason about the depth calculation for arrows; this will probably be unnecessary with new compilers setup *)
            admit. }
          { auto. } }
        {
          match goal with H : interp_scalar _ = _ |- _ => rewrite H end.
          rewrite <-interp_cast_correct.
          reflexivity. }
        {
          match goal with H : interp_scalar _ = _ |- _ => rewrite H end.
          rewrite <-interp_cast2_correct.
          cbn; break_match; reflexivity. }
        { invert_ok_scalar.
          rewrite <-H2.
          invert_ok_scalar_ident; try reflexivity.
          { match goal with H : context [of_uncurried_scalar _ = Some _ ] |- _ => cbn in H end.
            rewrite_ok_scalar.
            cbn [of_uncurried_ident].
            cbn [interp_scalar].
            cbn.
            break_match; cbn; auto.
            match goal with H : _ |- _ => apply invert_AppIdent_correct in H end.
            subst.
            invert_ok_scalar.
            rewrite_ok_scalar.
            repeat match goal with H : interp_scalar _ = _ |- _ => rewrite H end.
            reflexivity. }
          { match goal with H : context [of_uncurried_scalar _ = Some _ ] |- _ => cbn in H end.
            rewrite_ok_scalar.
            cbn [of_uncurried_ident].
            break_match; cbn; auto.
            match goal with H : _ |- _ => apply invert_AppIdent_correct in H end.
            subst.
            invert_ok_scalar.
            rewrite_ok_scalar.
            repeat match goal with H : interp_scalar _ = _ |- _ => rewrite H end.
            destruct r; reflexivity. }
        Admitted.
    End proofs.
  End expr.

  Definition of_Expr {s d} (e : Expr (s->d)) (var : type -> Type) (x:var s) dummy_arrow: expr.expr d
    :=
      match invert_Abs (e var) with
      | Some f =>
        expr.of_uncurried (dummy_arrow:=dummy_arrow) (expr.depth (fun _ => unit) (fun _ => tt) (e (fun _ => unit))) (f x)
      | None => expr.dummy (dummy_arrow:=dummy_arrow) d
      end.

End Straightline.

Module StraightlineTest.
  Definition test : Expr (type.Z -> type.Z) :=
    fun var =>
      Abs
        (fun (x : var type.Z) =>
           AppIdent (var:=var) ident.Let_In
               (Pair (AppIdent (var:=var) (ident.Z.cast r[0~>4294967295]%zrange) (AppIdent (var:=var) (ident.Z.shiftr 8) (Var x)))
                     (Abs (fun x : var type.Z => expr.Var x)))).

  Redirect "log" Check eq_refl :
    Straightline.of_Expr test =
    fun var x _ =>
       Straightline.expr.LetInAppIdentZ r[0 ~> 4294967295] (ident.Z.shiftr 8) (Straightline.expr.Var _ x)
         (fun x0 => Straightline.expr.Scalar (Straightline.expr.Var _ x0)).

  Definition test_mul : Expr (type.Z -> type.Z) :=
    fun var =>
      Abs
        (fun (x : var type.Z) =>
           AppIdent (var:=var) ident.Let_In
               (Pair (AppIdent (var:=var) (ident.Z.cast r[0~>4294967295]%zrange) (AppIdent (var:=var) (ident.Z.shiftr 8) (Var x)))
                     (Abs (fun y : var type.Z =>
                             AppIdent ident.Let_In
                                      (Pair (AppIdent (ident.Z.cast r[0~>4294967295]%zrange) (AppIdent ident.Z.mul (Pair (AppIdent (@ident.primitive type.Z 12) TT) (Var y))))
                                            (Abs (fun z : var type.Z => (AppIdent (ident.Z.cast r[0~>4294967295]%zrange) (AppIdent (ident.Z.shiftr 3) (Var z)))))
        ))))).

  Redirect "log" Check eq_refl :
    Straightline.of_Expr test_mul =
    fun var x _ =>
       Straightline.expr.LetInAppIdentZ r[0 ~> 4294967295] (ident.Z.shiftr 8) (Straightline.expr.Var _ x)
         (fun x0 =>
          Straightline.expr.LetInAppIdentZ r[0 ~> 4294967295] ident.Z.mul
            (Straightline.expr.Pair (Straightline.expr.Primitive (t:=type.Z) 12) (Straightline.expr.Var _ x0))
            (fun x1 =>
             Straightline.expr.LetInAppIdentZ r[0 ~> 4294967295] (ident.Z.shiftr 3)
               (Straightline.expr.Var _ x1)
               (fun x2 => Straightline.expr.Scalar (Straightline.expr.Var _ x2)))).

  Definition test_selm : Expr (type.Z -> type.Z) :=
    fun var =>
      Abs (fun x : var type.Z =>
             AppIdent (var:=var) ident.Let_In
                      (Pair (AppIdent (var:=var) (ident.Z.cast r[0~>4294967295]%zrange)
                                      (AppIdent (var:=var) ident.Z.zselect
                                                (Pair
                                                   (Pair
                                                      (AppIdent (var:=var) (ident.Z.cast r[0~>1]%zrange)
                                                                (AppIdent (var:=var) (ident.Z.cc_m_concrete 4294967296)
                                                                          (AppIdent (ident.Z.cast r[0~>4294967295]%zrange) (Var x))))
                                                      (AppIdent (@ident.primitive type.Z 0) TT))
                                                   (AppIdent (@ident.primitive type.Z 100) TT))))
                            (Abs (fun z : var type.Z => Var z)))).

  Redirect "log" Check eq_refl :
    Straightline.of_Expr test_selm =
    fun var x _ =>
      Straightline.expr.LetInAppIdentZ r[0 ~> 4294967295] ident.Z.zselect
        (Straightline.expr.Pair
           (Straightline.expr.Pair
              (Straightline.expr.Cast r[0 ~> 1]
                 (Straightline.expr.CC_m 4294967296
                    (Straightline.expr.Cast r[0 ~> 4294967295] (Straightline.expr.Var _ x))))
              (Straightline.expr.Primitive (t:=type.Z) 0)) (Straightline.expr.Primitive (t:=type.Z) 100))
        (fun x0 => Straightline.expr.Scalar (Straightline.expr.Var _ x0)).
End StraightlineTest.

(* Convert straightline code to code that uses only a certain set of identifiers *)
Module PreFancy.
  Import Straightline.expr.
  Section with_wordmax.
    Context (log2wordmax : Z) (log2wordmax_pos : 1 < log2wordmax) (log2wordmax_even : log2wordmax mod 2 = 0).
    Let wordmax := 2 ^ log2wordmax.
    Lemma wordmax_gt_2 : 2 < wordmax.
    Proof using log2wordmax_pos.
      apply Z.le_lt_trans with (m:=2 ^ 1); [ reflexivity | ].
      apply Z.pow_lt_mono_r; lia.
    Qed.

    Lemma wordmax_even : wordmax mod 2 = 0.
    Proof using log2wordmax_pos.
      replace 2 with (2 ^ 1) by reflexivity.
      subst wordmax. apply Z.mod_same_pow; lia.
    Qed.

    Let half_bits := log2wordmax / 2.

    Lemma half_bits_nonneg : 0 <= half_bits.
    Proof using log2wordmax_pos wordmax. subst half_bits; Z.zero_bounds. Qed.

    Let wordmax_half_bits := 2 ^ half_bits.

    Lemma wordmax_half_bits_pos : 0 < wordmax_half_bits.
    Proof using half_bits log2wordmax_pos wordmax. subst wordmax_half_bits half_bits. Z.zero_bounds. Qed.

    Lemma half_bits_squared : (wordmax_half_bits - 1) * (wordmax_half_bits - 1) <= wordmax - 1.
    Proof using half_bits log2wordmax_pos.
      pose proof wordmax_half_bits_pos.
      subst wordmax_half_bits.
      transitivity (2 ^ (half_bits + half_bits) - 2 * 2 ^ half_bits + 1).
      { rewrite Z.pow_add_r by (subst half_bits; Z.zero_bounds).
        autorewrite with push_Zmul; lia. }
      { transitivity (wordmax - 2 * 2 ^ half_bits + 1); [ | lia].
        subst wordmax.
        apply Z.add_le_mono_r.
        apply Z.sub_le_mono_r.
        apply Z.pow_le_mono_r; [ lia | ].
        rewrite Z.add_diag; subst half_bits.
        apply BinInt.Z.mul_div_le; lia. }
    Qed.

    Lemma wordmax_half_bits_le_wordmax : wordmax_half_bits <= wordmax.
    Proof using half_bits log2wordmax_pos.
      subst wordmax half_bits wordmax_half_bits.
      apply Z.pow_le_mono_r; [lia|].
      apply Z.div_le_upper_bound; lia.
    Qed.

    Lemma ones_half_bits : wordmax_half_bits - 1 = Z.ones half_bits.
    Proof using log2wordmax_pos wordmax.
      subst wordmax_half_bits. cbv [Z.ones].
      rewrite Z.shiftl_mul_pow2, <-Z.sub_1_r by auto using half_bits_nonneg.
      lia.
    Qed.

    Lemma wordmax_half_bits_squared : wordmax_half_bits * wordmax_half_bits = wordmax.
    Proof using half_bits log2wordmax_even log2wordmax_pos.
      subst wordmax half_bits wordmax_half_bits.
      rewrite <-Z.pow_add_r by Z.zero_bounds.
      rewrite Z.add_diag, Z.mul_div_eq by lia.
      f_equal; lia.
    Qed.

    Section with_var.
      Context {var : type -> Type} (dummy_arrow : forall s d, var (type.arrow s d)) (consts : list Z).
      Local Notation Z := (type.type_primitive type.Z).

      Inductive ident : type -> type -> Type :=
      | add (imm : BinInt.Z) : ident (Z * Z) (Z * Z)
      | addc (imm : BinInt.Z) : ident (Z * Z * Z) (Z * Z)
      | sub (imm : BinInt.Z) : ident (Z * Z) (Z * Z)
      | subb (imm : BinInt.Z) : ident (Z * Z * Z) (Z * Z)
      | mulll : ident (Z * Z) Z
      | mullh : ident (Z * Z) Z
      | mulhl : ident (Z * Z) Z
      | mulhh : ident (Z * Z) Z
      | rshi : BinInt.Z -> ident (Z * Z) Z
      | selc : ident (Z * Z * Z) Z
      | selm : ident (Z * Z * Z) Z
      | sell : ident (Z * Z * Z) Z
      | addm : ident (Z * Z * Z) Z
      .
      Definition dummy t : @expr var ident t := Scalar (dummy_scalar (dummy_arrow:=dummy_arrow) t).

      Definition constant_to_scalar_single (const x : BinInt.Z) : option (@scalar var Z) :=
        if x =? (BinInt.Z.shiftr const half_bits)
        then Some (Cast {|lower := 0; upper:=wordmax_half_bits-1|} (Shiftr half_bits (Primitive (t:=type.Z) const)))
        else if x =? (BinInt.Z.land const (wordmax_half_bits - 1))
             then Some (Cast {|lower := 0; upper:=wordmax_half_bits-1|} (Land (wordmax_half_bits-1) (Primitive (t:=type.Z) const)))
             else None.

      Definition constant_to_scalar (x : BinInt.Z)
        : option (Straightline.expr.scalar Z) :=
        fold_right (fun c res => match res with
                                 | Some s => Some s
                                 | None => constant_to_scalar_single c x
                                 end) None consts.

      Definition invert_lower' {t} (e : @scalar var t) :
        option (@scalar var Z) :=
        match e in scalar t return option (@scalar var Z) with
        | Cast r (Land n x) =>
          if (lower r =? 0) && (upper r =? (wordmax_half_bits - 1)) && (n =? wordmax_half_bits-1)
          then Some x
          else None
        | _ => None
        end.

      Definition invert_upper' {t} (e : @scalar var t) :
        option (@scalar var Z) :=
        match e in scalar t return option (@scalar var Z) with
        | Cast r (Shiftr n x) =>
          if (lower r =? 0) && (upper r =? (wordmax_half_bits - 1)) && (n =? half_bits)
          then Some x
          else None
        | _ => None
        end.

      Definition invert_lower {t} (e : @scalar var t) :
        option (@scalar var Z) :=
        match e in scalar t return option (@scalar var Z) with
        | Primitive type.Z x =>
          match constant_to_scalar x with
          | Some y => invert_lower' y
          | None => None
          end
        | _ => invert_lower' e
        end.

      Definition invert_upper {t} (e : @scalar var t) :
        option (@scalar var Z) :=
        match e in scalar t return option (@scalar var Z) with
        | Primitive type.Z x =>
          match constant_to_scalar x with
          | Some y => invert_upper' y
          | None => None
          end
        | _ => invert_upper' e
        end.

      Definition invert_sell {t} (e : @scalar var t) :
        option (@scalar var Z * @scalar var Z *  @scalar var Z) :=
        match e return _ with
        | Pair _ Z (Pair Z Z x y) z =>
          match x return option (@scalar var Z * @scalar var Z *  @scalar var Z) with
          | Cast r (Land n x') =>
            if (lower r =? 0) && (upper r =? 1) && (n =? 1)
            then Some (x', y, z)
            else None
          | _ => (@None _)
          end
        | _ => None
        end.

      Definition invert_selm {t} (e : @scalar var t) :
        option (@scalar var Z * @scalar var Z *  @scalar var Z) :=
        match e return _ with
        | Pair _ Z (Pair Z Z x y) z =>
          match x return option (@scalar var Z * @scalar var Z *  @scalar var Z) with
          | Cast r (CC_m n x') =>
            if (lower r =? 0) && (upper r =? 1) && (n =? wordmax)
            then Some (x', y, z)
            else None
          | _ => (@None _)
          end
        | _ => None
        end.

      Definition invert_shift {t} (s : @scalar var t)
        : option (@scalar var Z * BinInt.Z) :=
          match s return option (@scalar var Z * BinInt.Z) with
          | Cast r (Shiftl n x) =>
            match invert_lower x return option (@scalar var Z * BinInt.Z) with
            | Some x' =>
              if (lower r =? 0) && (upper r =? wordmax-1) && (n =? half_bits)
              then Some (x', half_bits)
              else None
            | None => None
            end
          | _ =>
            match invert_upper s return _ with
            | Some x => Some (x, -half_bits)
            | None => None
            end
          end.

      Definition of_straightline_ident {s d} (idc : ident.ident s d)
        : forall t, range_type d -> @scalar var s -> (var d -> @expr var ident t) -> @expr var ident t :=
        match idc in ident.ident s d return forall t, range_type d -> scalar s -> (var d -> @expr var ident t) -> @expr var ident t with
        | ident.Z.add_get_carry_concrete w =>
          fun t r x f =>
            if w =? wordmax
            then
              match x with
              | Pair Z Z xl xr =>
                match invert_shift xl, invert_shift xr with
                | _, Some (xr', imm) => LetInAppIdentZZ r (add imm) (Pair xl xr') f
                | Some (xl', imm), None => LetInAppIdentZZ r (add imm) (Pair xr xl') f

                | None, None => LetInAppIdentZZ r (add 0) (Pair xl xr) f
                end
              | _ => dummy _
              end
            else dummy _
        | ident.Z.add_with_get_carry_concrete w =>
          fun t r x f =>
            if w =? wordmax
            then
              match x with
              | Pair (type.prod Z Z) Z (Pair Z Z xc xl) xr =>
                match invert_shift xl, invert_shift xr with
                | _, Some (xr', imm) => LetInAppIdentZZ r (addc imm) (Pair (Pair xc xl) xr') f
                | Some (xl', imm), None => LetInAppIdentZZ r (addc imm) (Pair (Pair xc xr) xl') f

                | None, None => LetInAppIdentZZ r (addc 0) (Pair (Pair xc xl) xr) f
                end
              | _ => dummy _
              end
            else dummy _
        | ident.Z.sub_get_borrow_concrete w =>
          fun t r x f =>
            if w =? wordmax
            then
              match x with
              | Pair Z Z xl xr =>
                match invert_shift xr with
                | Some (xr', imm) => LetInAppIdentZZ r (sub imm) (Pair xl xr') f
                | None => LetInAppIdentZZ r (sub 0) (Pair xl xr) f
                end
              | _ => dummy _
              end
            else dummy _
        | ident.Z.sub_with_get_borrow_concrete w =>
          fun t r x f =>
            if w =? wordmax
            then
              match x with
              | Pair (type.prod Z Z) Z (Pair Z Z xb xl) xr =>
                match invert_shift xr with
                | Some (xr', imm) => LetInAppIdentZZ r (subb imm) (Pair (Pair xb xl) xr') f
                | None => LetInAppIdentZZ r (subb 0) (Pair (Pair xb xl) xr) f
                end
              | _ => dummy _
              end
            else dummy _
        | ident.Z.rshi_concrete w n =>
          fun _ r x f =>
            if w =? wordmax
            then LetInAppIdentZ r (rshi n) x f
            else dummy _
        | ident.Z.zselect =>
          fun t r x f =>
            match invert_selm x with
            | Some (x, y, z) => LetInAppIdentZ r selm (Pair (Pair x y) z) f
            | None => match invert_sell x with
                      | Some (x, y, z) => LetInAppIdentZ r sell (Pair (Pair x y) z) f
                      | None => LetInAppIdentZ r selc x f
                      end
            end
        | ident.Z.add_modulo => fun _ r => LetInAppIdentZ r addm
        | ident.Z.mul =>
          fun t r x f =>
            match x return expr t with
            | Pair _ _ x0 x1 =>
              match invert_lower x0, invert_lower x1 with
              | Some y0, Some y1 => LetInAppIdentZ r mulll (Pair y0 y1) f
              | Some y0, None =>
                match invert_upper x1 with
                | Some y1 => LetInAppIdentZ r mullh (Pair y0 y1) f
                | None => dummy _
                end
              | None, Some y1 =>
                match invert_upper x0 with
                | Some y0 => LetInAppIdentZ r mulhl (Pair y0 y1) f
                | None => dummy _
                end
              | None, None =>
                match invert_upper x0, invert_upper x1 with
                | Some y0, Some y1 => LetInAppIdentZ r mulhh (Pair y0 y1) f
                | _,_ => dummy _
                end
              end
            | _ => dummy _
            end
        | _ => fun t _ _ _ => dummy t
        end.

      Fixpoint of_straightline {t} (e : @expr var ident.ident t)
        : @expr var ident t :=
        match e with
        | Scalar _ s => Scalar s
        | LetInAppIdentZ _ t r idc x f =>
          of_straightline_ident idc t r[0~>wordmax-1]%zrange x (fun y => of_straightline (f y))
        | LetInAppIdentZZ _ t r idc x f =>
          of_straightline_ident idc t (r[0~>wordmax-1], r[0~>1])%zrange x (fun y => of_straightline (f y))
        end.
    End with_var.

    Section interp.
      Context {interp_cast : zrange -> Z -> Z}.
      Local Notation interp_scalar := (interp_scalar (interp_cast:=interp_cast)).
      Local Notation interp_cast2 := (interp_cast2 (interp_cast:=interp_cast)).
      Local Notation low x := (Z.land x (wordmax_half_bits - 1)).
      Local Notation high x := (x >> half_bits).
      Local Notation shift x imm := ((x << imm) mod wordmax).

      Definition interp_ident {s d} (idc : ident s d) : type.interp s -> type.interp d :=
        match idc with
        | add imm => fun x => Z.add_get_carry_full wordmax (fst x) (shift (snd x) imm)
        | addc imm => fun x => Z.add_with_get_carry_full wordmax (fst (fst x)) (snd (fst x)) (shift (snd x) imm)
        | sub imm => fun x => Z.sub_get_borrow_full wordmax (fst x) (shift (snd x) imm)
        | subb imm => fun x => Z.sub_with_get_borrow_full wordmax (fst (fst x)) (snd (fst x)) (shift (snd x) imm)
        | mulll => fun x => low (fst x) * low (snd x)
        | mullh => fun x => low (fst x) * high (snd x)
        | mulhl => fun x => high (fst x) * low (snd x)
        | mulhh => fun x => high (fst x) * high (snd x)
        | rshi n => fun x => Z.rshi wordmax (fst x) (snd x) n
        | selc => fun x => Z.zselect (fst (fst x)) (snd (fst x)) (snd x)
        | selm => fun x => Z.zselect (Z.cc_m wordmax (fst (fst x))) (snd (fst x)) (snd x)
        | sell => fun x => Z.zselect (Z.land (fst (fst x)) 1) (snd (fst x)) (snd x)
        | addm => fun x => Z.add_modulo (fst (fst x)) (snd (fst x)) (snd x)
        end.

      Fixpoint interp {t} (e : @expr type.interp ident t) : type.interp t :=
        match e with
        | Scalar t s => interp_scalar s
        | LetInAppIdentZ s d r idc x f =>
          interp (f (interp_cast r (interp_ident idc (interp_scalar x))))
        | LetInAppIdentZZ s d r idc x f =>
          interp (f (interp_cast2 r (interp_ident idc (interp_scalar x))))
        end.
    End interp.

    Section proofs.
      Context (dummy_arrow : forall s d, type.interp (s -> d)%ctype) (consts : list Z)
              (consts_ok : forall x, In x consts -> 0 <= x <= wordmax - 1).
      Context {interp_cast : zrange -> Z -> Z} {interp_cast_correct : forall r x, lower r <= x <= upper r -> interp_cast r x = x}.
      Local Notation interp_scalar := (interp_scalar (interp_cast:=interp_cast)).
      Local Notation interp_cast2 := (interp_cast2 (interp_cast:=interp_cast)).

      Local Notation word_range := (r[0~>wordmax-1])%zrange.
      Local Notation half_word_range := (r[0~>wordmax_half_bits-1])%zrange.
      Local Notation flag_range := (r[0~>1])%zrange.

      Definition in_word_range (r : zrange) := is_tighter_than_bool r word_range = true.
      Definition in_flag_range (r : zrange) := is_tighter_than_bool r flag_range = true.

      Fixpoint get_range_var (t : type) : type.interp t -> range_type t :=
        match t with
        | type.type_primitive type.Z =>
          fun x => {| lower := x; upper := x |}
        | type.prod a b =>
          fun x => (get_range_var a (fst x), get_range_var b (snd x))
        | _ => fun _ => tt
        end.

      Fixpoint get_range {t} (x : @scalar type.interp t) : range_type t :=
        match x with
        | Var t v => get_range_var t v
        | TT => tt
        | Nil _ => tt
        | Pair _ _ x y => (get_range x, get_range y)
        | Cast r _ => r
        | Cast2 r _ => r
        | Fst _ _ p => fst (get_range p)
        | Snd _ _ p => snd (get_range p)
        | Shiftr n x => ZRange.map (fun y => Z.shiftr y n) (get_range x)
        | Shiftl n x => ZRange.map (fun y => Z.shiftl y n) (get_range x)
        | Land n x => r[0~>n]%zrange
        | CC_m n x => ZRange.map (Z.cc_m n) (get_range x)
        | Primitive type.Z x => {| lower := x; upper := x |}
        | Primitive _p x => tt
        end.

      Fixpoint has_range {t} : range_type t -> type.interp t -> Prop :=
        match t with
        | type.type_primitive type.Z =>
          fun r x =>
            lower r <= x <= upper r
        | type.prod a b =>
          fun r x =>
            has_range (fst r) (fst x) /\ has_range (snd r) (snd x)
        | _ => fun _ _ => True
        end.

      Inductive ok_scalar : forall {t}, @scalar type.interp t -> Prop :=
      | sc_ok_var : forall t v, ok_scalar (Var t v)
      | sc_ok_unit : ok_scalar TT
      | sc_ok_nil : forall t, ok_scalar (Nil t)
      | sc_ok_pair : forall A B x y,
          @ok_scalar A x ->
          @ok_scalar B y ->
          ok_scalar (Pair x y)
      | sc_ok_cast : forall r (x : scalar type.Z),
          ok_scalar x ->
          is_tighter_than_bool (get_range x) r = true ->
          ok_scalar (Cast r x)
      | sc_ok_cast2 : forall r (x : scalar (type.prod type.Z type.Z)),
          ok_scalar x ->
          is_tighter_than_bool (fst (get_range x)) (fst r) = true ->
          is_tighter_than_bool (snd (get_range x)) (snd r) = true ->
          ok_scalar (Cast2 r x)
      | sc_ok_fst :
          forall A B p, @ok_scalar (A * B) p -> ok_scalar (Fst p)
      | sc_ok_snd :
          forall A B p, @ok_scalar (A * B) p -> ok_scalar (Snd p)
      | sc_ok_shiftr :
          forall n x, 0 <= n -> ok_scalar x -> ok_scalar (Shiftr n x)
      | sc_ok_shiftl :
          forall n x, 0 <= n -> 0 <= lower (@get_range type.Z x) -> ok_scalar x -> ok_scalar (Shiftl n x)
      | sc_ok_land :
          forall n x, 0 <= n -> 0 <= lower (@get_range type.Z x) -> ok_scalar x -> ok_scalar (Land n x)
      | sc_ok_cc_m :
          forall x, ok_scalar x -> ok_scalar (CC_m wordmax x)
      | sc_ok_prim : forall p x, ok_scalar (@Primitive _ p x)
      .

      Inductive is_halved : scalar type.Z -> Prop :=
      | is_halved_lower :
          forall x : scalar type.Z,
            in_word_range (get_range x) ->
            is_halved (Cast half_word_range (Land (wordmax_half_bits - 1) x))
      | is_halved_upper :
          forall x : scalar type.Z,
            in_word_range (get_range x) ->
            is_halved (Cast half_word_range (Shiftr half_bits x))
      | is_halved_constant :
          forall y z,
            constant_to_scalar consts z = Some y ->
            is_halved y ->
            is_halved (Primitive (t:=type.Z) z)
      .

      Inductive ok_ident : forall s d, scalar s -> range_type d -> ident.ident s d -> Prop :=
      | ok_add :
          forall x y : scalar type.Z,
            in_word_range (get_range x) ->
            in_word_range (get_range y) ->
            ok_ident _
                     (type.prod type.Z type.Z)
                     (Pair x y)
                     (word_range, flag_range)
                     (ident.Z.add_get_carry_concrete wordmax)
      | ok_addc :
          forall (c x y : scalar type.Z) outr,
            in_flag_range (get_range c) ->
            in_word_range (get_range x) ->
            in_word_range (get_range y) ->
            lower outr = 0 ->
            (0 <= upper (get_range c) + upper (get_range x) + upper (get_range y) <= upper outr \/ outr = word_range) ->
            ok_ident _
                     (type.prod type.Z type.Z)
                     (Pair (Pair c x) y)
                     (outr, flag_range)
                     (ident.Z.add_with_get_carry_concrete wordmax)
      | ok_sub :
          forall x y : scalar type.Z,
            in_word_range (get_range x) ->
            in_word_range (get_range y) ->
            ok_ident _
                     (type.prod type.Z type.Z)
                     (Pair x y)
                     (word_range, flag_range)
                     (ident.Z.sub_get_borrow_concrete wordmax)
      | ok_subb :
          forall b x y : scalar type.Z,
            in_flag_range (get_range b) ->
            in_word_range (get_range x) ->
            in_word_range (get_range y) ->
            ok_ident _
                     (type.prod type.Z type.Z)
                     (Pair (Pair b x) y)
                     (word_range, flag_range)
                     (ident.Z.sub_with_get_borrow_concrete wordmax)
      | ok_rshi :
          forall (x : scalar (type.prod type.Z type.Z)) n outr,
            in_word_range (fst (get_range x)) ->
            in_word_range (snd (get_range x)) ->
            (* note : using [outr] rather than [word_range] allows for cases where the result has been put in a smaller word size. *)
            lower outr = 0 ->
            0 <= n ->
            ((0 <= (upper (snd (get_range x)) + upper (fst (get_range x)) * wordmax) / 2^n <= upper outr)
              \/ outr = word_range) ->
            ok_ident (type.prod type.Z type.Z) type.Z x outr (ident.Z.rshi_concrete wordmax n)
      | ok_selc :
          forall (x : scalar (type.prod type.Z type.Z)) (y z : scalar type.Z),
            in_flag_range (snd (get_range x)) ->
            in_word_range (get_range y) ->
            in_word_range (get_range z) ->
            ok_ident _
                     type.Z
                     (Pair (Pair (Cast flag_range (Snd x)) y) z)
                     word_range
                     ident.Z.zselect
      | ok_selm :
          forall x y z : scalar type.Z,
            in_word_range (get_range x) ->
            in_word_range (get_range y) ->
            in_word_range (get_range z) ->
            ok_ident _
                     type.Z
                     (Pair (Pair (Cast flag_range (CC_m wordmax x)) y) z)
                     word_range
                     ident.Z.zselect
      | ok_sell :
          forall x y z : scalar type.Z,
            in_word_range (get_range x) ->
            in_word_range (get_range y) ->
            in_word_range (get_range z) ->
            ok_ident _
                     type.Z
                     (Pair (Pair (Cast flag_range (Land 1 x)) y) z)
                     word_range
                     ident.Z.zselect
      | ok_addm :
          forall (x : scalar (type.prod (type.prod type.Z type.Z) type.Z)),
            in_word_range (fst (fst (get_range x))) ->
            in_word_range (snd (fst (get_range x))) ->
            in_word_range (snd (get_range x)) ->
            upper (fst (fst (get_range x))) + upper (snd (fst (get_range x))) - lower (snd (get_range x)) < wordmax ->
            ok_ident _
                     type.Z
                     x
                     word_range
                     ident.Z.add_modulo
      | ok_mul :
          forall x y : scalar type.Z,
            is_halved x ->
            is_halved y ->
            ok_ident (type.prod type.Z type.Z)
                     type.Z
                     (Pair x y)
                     word_range
                     ident.Z.mul
      .

      Inductive ok_expr : forall {t}, @expr type.interp ident.ident t -> Prop :=
      | ok_of_scalar : forall t s, ok_scalar s -> @ok_expr t (Scalar s)
      | ok_letin_z : forall s d r idc x f,
          ok_ident _ type.Z x r idc ->
          (r <=? word_range)%zrange = true ->
          ok_scalar x ->
          (forall y, has_range (t:=type.Z) r y -> ok_expr (f y)) ->
          ok_expr (@LetInAppIdentZ _ _ s d r idc x f)
      | ok_letin_zz : forall s d r idc x f,
          ok_ident _ (type.prod type.Z type.Z) x (r, flag_range) idc ->
          (r <=? word_range)%zrange = true ->
          ok_scalar x ->
          (forall y, has_range (t:=type.Z * type.Z) (r, flag_range) y -> ok_expr (f y)) ->
          ok_expr (@LetInAppIdentZZ _ _ s d (r, flag_range) idc x f)
      .

      Ltac invert H :=
        inversion H; subst;
        repeat match goal with
               | H : existT _ _ _ = existT _ _ _ |- _ => apply (Eqdep_dec.inj_pair2_eq_dec _ type.type_eq_dec) in H; subst
               end.

      Lemma has_range_get_range_var {t} (v : type.interp t) :
        has_range (get_range_var _ v) v.
      Proof using wordmax wordmax_half_bits.
        induction t; cbn [get_range_var has_range fst snd]; auto.
        destruct p; auto; cbn [upper lower]; lia.
      Qed.

      Lemma has_range_loosen r1 r2 (x : Z) :
        @has_range type.Z r1 x ->
        is_tighter_than_bool r1 r2 = true ->
        @has_range type.Z r2 x.
      Proof using log2wordmax_pos wordmax wordmax_half_bits.
        cbv [is_tighter_than_bool has_range]; intros;
          match goal with H : _ && _ = true |- _ => rewrite andb_true_iff in H; destruct H end;
          Z.ltb_to_lt; lia.
      Qed.

      Lemma interp_cast_noop x r :
        @has_range type.Z r x ->
        interp_cast r x = x.
      Proof using interp_cast_correct. cbv [has_range]; intros; auto. Qed.

      Lemma interp_cast2_noop x r :
        @has_range (type.prod type.Z type.Z) r x ->
        interp_cast2 r x = x.
      Proof using interp_cast_correct.
        cbv [has_range interp_cast2]; intros.
        rewrite !interp_cast_correct by tauto.
        destruct x; reflexivity.
      Qed.

      Lemma has_range_shiftr n (x : scalar type.Z) :
        0 <= n ->
        has_range (get_range x) (interp_scalar x) ->
        @has_range type.Z (ZRange.map (fun y : Z => y >> n) (get_range x)) (interp_scalar x >> n).
      Proof using wordmax wordmax_half_bits. cbv [has_range]; intros; cbn. auto using Z.shiftr_le with lia. Qed.
      Local Hint Resolve has_range_shiftr : has_range.

      Lemma has_range_shiftl n r x :
        0 <= n -> 0 <= lower r ->
        @has_range type.Z r x ->
        @has_range type.Z (ZRange.map (fun y : Z => y << n) r) (x << n).
      Proof using log2wordmax_pos wordmax wordmax_half_bits. cbv [has_range]; intros; cbn. auto using Z.shiftl_le_mono with lia. Qed.
      Local Hint Resolve has_range_shiftl : has_range.

      Lemma has_range_land n (x : scalar type.Z) :
        0 <= n -> 0 <= lower (get_range x) ->
        has_range (get_range x) (interp_scalar x) ->
        @has_range type.Z (r[0~>n])%zrange (Z.land (interp_scalar x) n).
      Proof using log2wordmax_pos wordmax wordmax_half_bits.
        cbv [has_range]; intros; cbn.
        split; [ apply Z.land_nonneg | apply Z.land_upper_bound_r ]; lia.
      Qed.
      Local Hint Resolve has_range_land : has_range.

      Lemma has_range_interp_scalar {t} (x : scalar t) :
        ok_scalar x ->
        has_range (get_range x) (interp_scalar x).
      Proof using interp_cast_correct log2wordmax_pos.
        induction 1; cbn [interp_scalar get_range];
          auto with has_range;
          try solve [try inversion IHok_scalar; cbn [has_range];
                     auto using has_range_get_range_var]; [ | | | ].
        { rewrite interp_cast_noop by eauto using has_range_loosen.
          eapply has_range_loosen; eauto. }
        { inversion IHok_scalar.
          rewrite interp_cast2_noop;
            cbn [has_range]; split; eapply has_range_loosen; eauto. }
        { cbn. cbv [has_range] in *.
          pose proof wordmax_gt_2.
          rewrite !Z.cc_m_eq by lia.
          split; apply Z.div_le_mono; Z.zero_bounds; lia. }
        { destruct p; cbn [has_range upper lower]; auto; lia. }
      Qed.
      Local Hint Resolve has_range_interp_scalar : has_range.

      Lemma has_word_range_interp_scalar (x : scalar type.Z) :
        ok_scalar x ->
        in_word_range (get_range x) ->
        @has_range type.Z word_range (interp_scalar x).
      Proof using interp_cast_correct log2wordmax_pos. eauto using has_range_loosen, has_range_interp_scalar. Qed.

      Lemma in_word_range_nonneg r : in_word_range r -> 0 <= lower r.
      Proof using Type.
        cbv [in_word_range is_tighter_than_bool].
        rewrite andb_true_iff; intuition.
      Qed.

      Lemma in_word_range_upper_nonneg r x : @has_range type.Z r x -> in_word_range r -> 0 <= upper r.
      Proof using log2wordmax_pos.
        cbv [in_word_range is_tighter_than_bool]; cbn.
        rewrite andb_true_iff; intuition.
        Z.ltb_to_lt. lia.
      Qed.

      Lemma has_word_range_shiftl n r x :
        0 <= n -> upper r * 2 ^ n <= wordmax - 1 ->
        @has_range type.Z r x ->
        in_word_range r ->
        @has_range type.Z word_range (x << n).
      Proof using log2wordmax_pos.
        intros.
        eapply has_range_loosen;
          [ apply has_range_shiftl; eauto using in_word_range_nonneg with has_range; lia | ].
        cbv [is_tighter_than_bool]. cbn.
        apply andb_true_iff; split; apply Z.leb_le;
          [ apply Z.shiftl_nonneg; solve [auto using in_word_range_nonneg] | ].
        rewrite Z.shiftl_mul_pow2 by lia.
        auto.
      Qed.

      Lemma has_range_rshi r n x y :
        0 <= n ->
        0 <= x ->
        0 <= y ->
        lower r = 0 ->
        (0 <= (y + x * wordmax) / 2^n <= upper r \/ r = word_range) ->
        @has_range type.Z r (Z.rshi wordmax x y n).
      Proof using log2wordmax_pos wordmax_half_bits.
        pose proof wordmax_gt_2.
        intros. cbv [has_range].
        rewrite Z.rshi_correct by lia.
        match goal with |- context [?x mod ?m] =>
                        pose proof (Z.mod_pos_bound x m ltac:(lia)) end.
        split; [lia|].
        intuition.
        { destruct (Z_lt_dec (upper r) wordmax); [ | lia].
          rewrite Z.mod_small by (split; Z.zero_bounds; lia).
          lia. }
        { subst r. cbn [upper]. lia. }
      Qed.

      Lemma in_word_range_spec r :
        (0 <= lower r /\ upper r <= wordmax - 1)
        <-> in_word_range r.
      Proof using Type.
        intros; cbv [in_word_range is_tighter_than_bool].
        rewrite andb_true_iff.
        intuition; apply Z.leb_le; cbn [upper lower]; try lia.
      Qed.

      Ltac destruct_scalar :=
        match goal with
        | x : scalar (type.prod (type.prod _ _) _) |- _ =>
          match goal with |- context [interp_scalar x] =>
            destruct (interp_scalar x) as [ [? ?] ?];
            destruct (get_range x) as [ [? ?] ?]
          end
        | x : scalar (type.prod _ _) |- _ =>
          match goal with |- context [interp_scalar x] =>
            destruct (interp_scalar x) as [? ?]; destruct (get_range x) as [? ?]
          end
        end.

      Ltac extract_ok_scalar' level x :=
        match goal with
        | H : ok_scalar (Pair (Pair (?f (?g x)) _) _) |- _ =>
          match (eval compute in (4 <=? level)) with
          | true => invert H; extract_ok_scalar' 3 x
          | _ => fail
          end
        | H : ok_scalar (Pair (?f (?g x)) _) |- _ =>
          match (eval compute in (3 <=? level)) with
          | true => invert H; extract_ok_scalar' 2 x
          | _ => fail
          end
        | H : ok_scalar (Pair _ (?f (?g x))) |- _ =>
          match (eval compute in (3 <=? level)) with
          | true => invert H; extract_ok_scalar' 2 x
          | _ => fail
          end
        | H : ok_scalar (?f (?g x)) |- _ =>
          match (eval compute in (2 <=? level)) with
          | true => invert H; extract_ok_scalar' 1 x
          | _ => fail
          end
        | H : ok_scalar (Pair (Pair x _) _) |- _ =>
          match (eval compute in (2 <=? level)) with
          | true => invert H; extract_ok_scalar' 1 x
          | _ => fail
          end
        | H : ok_scalar (Pair (Pair _ x) _) |- _ =>
          match (eval compute in (2 <=? level)) with
          | true => invert H; extract_ok_scalar' 1 x
          | _ => fail
          end
        | H : ok_scalar (?g x) |- _ => invert H
        | H : ok_scalar (Pair x _) |- _ => invert H
        | H : ok_scalar (Pair _ x) |- _ => invert H
        end.

      Ltac extract_ok_scalar :=
        match goal with |- ok_scalar ?x => extract_ok_scalar' 4 x; assumption end.

      Lemma has_half_word_range_shiftr r x :
        in_word_range r ->
        @has_range type.Z r x ->
        @has_range type.Z half_word_range (x >> half_bits).
      Proof using log2wordmax_even log2wordmax_pos.
        cbv [in_word_range is_tighter_than_bool].
        rewrite andb_true_iff.
        cbn [has_range upper lower]; intros; intuition; Z.ltb_to_lt.
        { apply Z.shiftr_nonneg. lia. }
        { pose proof half_bits_nonneg.
          pose proof half_bits_squared.
          assert (x >> half_bits < wordmax_half_bits); [|lia].
          rewrite Z.shiftr_div_pow2 by auto.
          apply Z.div_lt_upper_bound; Z.zero_bounds.
          subst wordmax_half_bits half_bits.
          rewrite <-Z.pow_add_r by lia.
          rewrite Z.add_diag, Z.mul_div_eq, log2wordmax_even by lia.
          autorewrite with zsimplify_fast. subst wordmax. lia. }
      Qed.

      Lemma has_half_word_range_land r x :
        in_word_range r ->
        @has_range type.Z r x ->
        @has_range type.Z half_word_range (x &' (wordmax_half_bits - 1)).
      Proof using log2wordmax_pos.
        pose proof wordmax_half_bits_pos.
        cbv [in_word_range is_tighter_than_bool].
        rewrite andb_true_iff.
        cbn [has_range upper lower]; intros; intuition; Z.ltb_to_lt.
        { apply Z.land_nonneg; lia. }
        { apply Z.land_upper_bound_r; lia. }
      Qed.

      Section constant_to_scalar.
        Lemma constant_to_scalar_single_correct s x z :
            0 <= x <= wordmax - 1 ->
            constant_to_scalar_single x z = Some s -> interp_scalar s = z.
        Proof using interp_cast_correct log2wordmax_even log2wordmax_pos.
          cbv [constant_to_scalar_single].
          break_match; try discriminate; intros; Z.ltb_to_lt; subst;
            try match goal with H : Some _ = Some _ |- _ => inversion H; subst end;
            cbn [interp_scalar]; apply interp_cast_noop.
          { apply has_half_word_range_shiftr with (r:=r[x~>x]%zrange);
            cbv [in_word_range is_tighter_than_bool upper lower has_range]; try lia;
            apply andb_true_iff; split; apply Z.leb_le; lia. }
          { apply has_half_word_range_land with (r:=r[x~>x]%zrange);
            cbv [in_word_range is_tighter_than_bool upper lower has_range]; try lia;
            apply andb_true_iff; split; apply Z.leb_le; lia. }
        Qed.

        Lemma constant_to_scalar_correct s z :
          constant_to_scalar consts z = Some s -> interp_scalar s = z.
        Proof using consts_ok interp_cast_correct log2wordmax_even log2wordmax_pos.
          cbv [constant_to_scalar].
          apply fold_right_invariant; try discriminate.
          intros until 2; break_match; eauto using constant_to_scalar_single_correct.
        Qed.

        Lemma constant_to_scalar_single_cases x y z :
          @constant_to_scalar_single type.interp x z = Some y ->
          (y = Cast half_word_range (Land (wordmax_half_bits - 1) (Primitive (t:=type.Z) x)))
          \/ (y = Cast half_word_range (Shiftr half_bits (Primitive (t:=type.Z) x))).
        Proof using Type.
          cbv [constant_to_scalar_single].
          break_match; try discriminate; intros; Z.ltb_to_lt; subst;
            try match goal with H : Some _ = Some _ |- _ => inversion H; subst end;
            tauto.
        Qed.

        Lemma constant_to_scalar_cases y z :
          @constant_to_scalar type.interp consts z = Some y ->
          (exists x,
              @has_range type.Z word_range x
              /\ y = Cast half_word_range (Land (wordmax_half_bits - 1) (Primitive x)))
          \/ (exists x,
                 @has_range type.Z word_range x
                 /\ y = Cast half_word_range (Shiftr half_bits (Primitive x))).
        Proof using consts_ok.
          cbv [constant_to_scalar].
          apply fold_right_invariant; try discriminate.
          intros until 2; break_match; eauto; intros.
          match goal with H : constant_to_scalar_single _ _ = _ |- _ =>
                          destruct (constant_to_scalar_single_cases _ _ _ H); subst end.
          { left; eexists; split; eauto.
            apply consts_ok; auto. }
          { right; eexists; split; eauto.
            apply consts_ok; auto. }
        Qed.

        Lemma ok_scalar_constant_to_scalar y z : constant_to_scalar consts z = Some y -> ok_scalar y.
        Proof using consts_ok log2wordmax_even log2wordmax_pos.
          pose proof wordmax_half_bits_pos. pose proof half_bits_nonneg.
          let H := fresh in
          intro H; apply constant_to_scalar_cases in H; destruct H as [ [? ?] | [? ?] ]; intuition; subst;
            cbn [has_range lower upper] in *; repeat constructor; cbn [lower get_range]; try apply Z.leb_refl; try lia.
          assert (in_word_range r[x~>x]) by (apply in_word_range_spec; cbn [lower upper]; lia).
          pose proof (has_half_word_range_shiftr r[x~>x] x ltac:(assumption) ltac:(cbv [has_range lower upper]; lia)).
          cbn [has_range ZRange.map is_tighter_than_bool lower upper] in *.
          apply andb_true_iff; cbn [lower upper]; split; apply Z.leb_le; lia.
        Qed.
      End constant_to_scalar.
      Local Hint Resolve ok_scalar_constant_to_scalar.

      Lemma is_halved_has_range x :
        ok_scalar x ->
        is_halved x ->
        @has_range type.Z half_word_range (interp_scalar x).
      Proof using consts_ok interp_cast_correct log2wordmax_even log2wordmax_pos.
        intro; pose proof (has_range_interp_scalar x ltac:(assumption)).
        induction 1; cbn [interp_scalar] in *; intros; try assumption; [ ].
        rewrite <-(constant_to_scalar_correct y z) by assumption.
        eauto using has_range_interp_scalar.
      Qed.

      Lemma ident_interp_has_range s d x r idc:
        ok_scalar x ->
        ok_ident s d x r idc ->
        has_range r (ident.interp idc (interp_scalar x)).
      Proof using consts_ok interp_cast_correct log2wordmax_even log2wordmax_pos.
        intro.
        pose proof (has_range_interp_scalar x ltac:(assumption)).
        pose proof wordmax_gt_2.
        induction 1; cbn [ident.interp ident.gen_interp]; intros; try destruct_scalar;
          repeat match goal with
                 | H : _ && _ = true |- _ => rewrite andb_true_iff in H; destruct H; Z.ltb_to_lt
                 |  H : _ /\ _ |- _ => destruct H
                 | H : is_halved _ |- _ => apply is_halved_has_range in H; [ | extract_ok_scalar ]
                 | _ => progress subst
                 | _ => progress (cbv [in_word_range in_flag_range is_tighter_than_bool] in * )
                 | _ => progress (cbn [interp_scalar get_range has_range upper lower fst snd] in * )
                 end.
        {
          autorewrite with to_div_mod.
          match goal with |- context[?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)) end.
          rewrite Z.div_between_0_if by lia.
          split; break_match; lia. }
        {
          autorewrite with to_div_mod.
          match goal with |- context[?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)) end.
          rewrite Z.div_between_0_if by lia.
          match goal with H : _ \/ _ |- _ => destruct H; subst end.
          { split; break_match; try lia.
            destruct (Z_lt_dec (upper outr) wordmax).
            { match goal with |- _ <= ?y mod _ <= ?u =>
                              assert (y <= u) by nia end.
              rewrite Z.mod_small by lia. lia. }
            { match goal with|- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)) end.
              lia. } }
          { split; break_match; cbn; lia. } }
        {
          autorewrite with to_div_mod.
          match goal with |- context[?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)) end.
          rewrite Z.div_sub_small by lia.
          split; break_match; lia. }
        {
          autorewrite with to_div_mod.
          match goal with |- context [?a - ?b - ?c] => replace (a - b - c) with (a - (b + c)) by ring end.
          match goal with |- context[?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)) end.
          rewrite Z.div_sub_small by lia.
          split; break_match; lia. }
        { apply has_range_rshi; try nia; [ ].
          match goal with H : context [upper ?ra + upper ?rb * wordmax] |- context [?a + ?b * wordmax] =>
                          assert ((a + b * wordmax) / 2^n <= (upper ra + upper rb * wordmax) / 2^n) by (apply Z.div_le_mono; Z.zero_bounds; nia)
          end.
          match goal with H : _ \/ ?P |- _ \/ ?P => destruct H; [left|tauto] end.
          split; Z.zero_bounds; nia. }
        { rewrite Z.zselect_correct. break_match; lia. }
        { cbn [interp_scalar fst snd get_range] in *.
          rewrite Z.zselect_correct. break_match; lia. }
        { cbn [interp_scalar fst snd get_range] in *.
          rewrite Z.zselect_correct. break_match; lia. }
        { rewrite Z.add_modulo_correct.
          break_match; Z.ltb_to_lt; lia. }
        { cbn [interp_scalar has_range fst snd get_range upper lower] in *.
          pose proof half_bits_squared. nia. }
      Qed.

      Lemma has_flag_range_cc_m r x :
        @has_range type.Z r x ->
        in_word_range r ->
        @has_range type.Z flag_range (Z.cc_m wordmax x).
      Proof using log2wordmax_pos.
        cbv [has_range in_word_range is_tighter_than_bool].
        cbn [upper lower]; rewrite andb_true_iff; intros.
        match goal with H : _ /\ _ |- _ => destruct H; Z.ltb_to_lt end.
        pose proof wordmax_gt_2. pose proof wordmax_even.
        pose proof (Z.cc_m_small wordmax x). lia.
      Qed.

      Lemma has_flag_range_cc_m' (x : scalar type.Z) :
        ok_scalar x ->
        in_word_range (get_range x) ->
        @has_range type.Z flag_range (Z.cc_m wordmax (interp_scalar x)).
      Proof using interp_cast_correct log2wordmax_pos. eauto using has_flag_range_cc_m with has_range. Qed.

      Lemma has_flag_range_land r x :
        @has_range type.Z r x ->
        in_word_range r ->
        @has_range type.Z flag_range (Z.land x 1).
      Proof using log2wordmax_pos.
        cbv [has_range in_word_range is_tighter_than_bool].
        cbn [upper lower]; rewrite andb_true_iff; intuition; Z.ltb_to_lt.
        { apply Z.land_nonneg. left; lia. }
        { apply Z.land_upper_bound_r; lia. }
      Qed.

      Lemma has_flag_range_land' (x : scalar type.Z) :
        ok_scalar x ->
        in_word_range (get_range x) ->
        @has_range type.Z flag_range (Z.land (interp_scalar x) 1).
      Proof using interp_cast_correct log2wordmax_pos. eauto using has_flag_range_land with has_range. Qed.

      Ltac rewrite_cast_noop_in_mul :=
        repeat match goal with
               | _ => rewrite interp_cast_noop with (r:=half_word_range) in *
                   by (eapply has_range_loosen; auto using has_range_land, has_range_interp_scalar)
               | _ => rewrite interp_cast_noop with (r:=half_word_range) in *
                   by (eapply has_range_loosen; try apply has_range_shiftr; auto using has_range_interp_scalar;
                       cbn [ZRange.map get_range] in *; auto)
               | _ => rewrite interp_cast_noop by assumption
               end.

      Lemma is_halved_cases x :
        is_halved x ->
        ok_scalar x ->
        (exists y,
            invert_lower consts x = Some y
            /\ invert_upper consts x = None
            /\ interp_scalar y &' (wordmax_half_bits - 1) = interp_scalar x)
        \/ (exists y,
               invert_lower consts x = None
               /\ invert_upper consts x = Some y
               /\ interp_scalar y >> half_bits = interp_scalar x).
      Proof using consts_ok interp_cast_correct log2wordmax_even log2wordmax_pos.
        induction 1; intros; cbn; rewrite ?Z.eqb_refl; cbn.
        { left. eexists; repeat split; auto.
          rewrite interp_cast_noop; [ reflexivity | ].
          apply has_half_word_range_land with (r:=get_range x); auto.
          apply has_range_interp_scalar; extract_ok_scalar. }
        { right. eexists; repeat split; auto.
          rewrite interp_cast_noop; [ reflexivity | ].
          apply has_half_word_range_shiftr with (r:=get_range x); auto.
          apply has_range_interp_scalar; extract_ok_scalar. }
        { match goal with H : constant_to_scalar _ _ = Some _ |- _ =>
                          rewrite H;
                            let P := fresh in
                            destruct (constant_to_scalar_cases _ _ H) as [ [? [? ?] ] | [? [? ?] ] ];
                              subst; cbn; rewrite ?Z.eqb_refl; cbn
          end.
          { left; eexists; repeat split; auto.
            erewrite <-constant_to_scalar_correct by eassumption.
            subst. cbn.
            rewrite interp_cast_noop; [ reflexivity | ].
            eapply has_half_word_range_land with (r:=word_range); auto.
            cbv [in_word_range is_tighter_than_bool].
            rewrite !Z.leb_refl; reflexivity. }
          { right; eexists; repeat split; auto.
            erewrite <-constant_to_scalar_correct by eassumption.
            subst. cbn.
            rewrite interp_cast_noop; [ reflexivity | ].
            eapply has_half_word_range_shiftr with (r:=word_range); auto.
            cbv [in_word_range is_tighter_than_bool].
            rewrite !Z.leb_refl; reflexivity. } }
      Qed.

      Lemma halved_mul_range x y :
        ok_scalar (Pair x y) ->
        is_halved x ->
        is_halved y ->
        0 <= interp_scalar x * interp_scalar y < wordmax.
      Proof using consts_ok interp_cast_correct log2wordmax_even log2wordmax_pos.
        intro Hok; invert Hok. intros.
        repeat match goal with H : _ |- _ => apply is_halved_has_range in H; [|assumption] end.
        cbv [has_range lower upper] in *.
        pose proof half_bits_squared. nia.
      Qed.

      Lemma of_straightline_ident_mul_correct r t x y g :
        is_halved x ->
        is_halved y ->
        ok_scalar (Pair x y) ->
        (word_range <=? r)%zrange = true ->
        @has_range type.Z word_range (ident.interp ident.Z.mul (interp_scalar (Pair x y))) ->
        @interp interp_cast _ (of_straightline_ident dummy_arrow consts ident.Z.mul t r (Pair x y) g) =
        @interp interp_cast _ (g (ident.interp ident.Z.mul (interp_scalar (Pair x y)))).
      Proof using consts_ok interp_cast_correct log2wordmax_even log2wordmax_pos.
        intros Hx Hy Hok ? ?; invert Hok; cbn [interp_scalar of_straightline_ident];
        destruct (is_halved_cases x Hx ltac:(assumption)) as [ [? [Pxlow [Pxhigh Pxi] ] ] | [? [Pxlow [Pxhigh Pxi] ] ] ];
          rewrite ?Pxlow, ?Pxhigh;
          destruct (is_halved_cases y Hy ltac:(assumption)) as [ [? [Pylow [Pyhigh Pyi] ] ] | [? [Pylow [Pyhigh Pyi] ] ] ];
          rewrite ?Pylow, ?Pyhigh;
          cbn; rewrite Pxi, Pyi; assert (0 <= interp_scalar x * interp_scalar y < wordmax) by (auto using halved_mul_range);
            rewrite interp_cast_noop by (cbv [is_tighter_than_bool] in *; cbn [has_range upper lower] in *; rewrite andb_true_iff in *; intuition; Z.ltb_to_lt; lia); reflexivity.
      Qed.

      Lemma has_word_range_mod_small x:
        @has_range type.Z word_range x ->
        x mod wordmax = x.
      Proof using wordmax_half_bits.
        cbv [has_range upper lower].
        intros. apply Z.mod_small; lia.
      Qed.

      Lemma half_word_range_le_word_range r :
        upper r = wordmax_half_bits - 1 ->
        lower r = 0 ->
        (r <=? word_range)%zrange = true.
      Proof using half_bits log2wordmax_pos.
        pose proof wordmax_half_bits_le_wordmax.
        destruct r; cbv [is_tighter_than_bool ZRange.lower ZRange.upper].
        intros; subst.
        apply andb_true_iff; split; Z.ltb_to_lt; lia.
      Qed.

      Lemma and_shiftl_half_bits_eq x :
        (x &' (wordmax_half_bits - 1)) << half_bits = x << half_bits mod wordmax.
      Proof using log2wordmax_even log2wordmax_pos.
        rewrite ones_half_bits.
        rewrite Z.land_ones, !Z.shiftl_mul_pow2 by auto using half_bits_nonneg.
        rewrite <-wordmax_half_bits_squared.
        subst wordmax_half_bits.
        rewrite Z.mul_mod_distr_r_full.
        reflexivity.
      Qed.

      Lemma in_word_range_word_range : in_word_range word_range.
      Proof using Type.
        cbv [in_word_range is_tighter_than_bool].
        rewrite !Z.leb_refl; reflexivity.
      Qed.

      Lemma invert_shift_correct (s : scalar type.Z) x imm :
        ok_scalar s ->
        invert_shift consts s = Some (x, imm) ->
        interp_scalar s = (interp_scalar x << imm) mod wordmax.
      Proof using consts_ok interp_cast_correct log2wordmax_even log2wordmax_pos.
        intros Hok ?; invert Hok;
          try match goal with H : ok_scalar ?x, H' : context[Cast _ ?x] |- _ =>
                          invert H end;
          try match goal with H : ok_scalar ?x, H' : context[Shiftl _ ?x] |- _ =>
                          invert H end;
          try match goal with H : ok_scalar ?x, H' : context[Shiftl _ (Cast _ ?x)] |- _ =>
                          invert H end;
          try (cbn [invert_shift invert_upper invert_upper'] in *; discriminate);
          repeat match goal with
                 | _ => progress (cbn [invert_shift invert_lower invert_lower' invert_upper invert_upper' interp_scalar fst snd] in * )
                 | _ => rewrite interp_cast_noop by eauto using has_half_word_range_land, has_half_word_range_shiftr, in_word_range_word_range, has_range_loosen
                 | H : ok_scalar (Shiftr _ _) |- _ => apply has_range_interp_scalar in H
                 | H : ok_scalar (Shiftl _ _) |- _ => apply has_range_interp_scalar in H
                 | H : ok_scalar (Land _ _) |- _ => apply has_range_interp_scalar in H
                 | H : context [if ?x then _ else _] |- _ =>
                   let Heq := fresh in case_eq x; intro Heq; rewrite Heq in H
                 | H : context [match @constant_to_scalar ?v ?consts ?x with _ => _ end] |- _ =>
                   let Heq := fresh in
                   case_eq (@constant_to_scalar v consts x); intros until 0; intro Heq; rewrite Heq in *; [|discriminate];
                     destruct (constant_to_scalar_cases _ _ Heq) as [ [? [? ?] ] | [? [? ?] ] ]; subst;
                       pose proof (ok_scalar_constant_to_scalar _ _ Heq)
                 | H : constant_to_scalar _ _ = Some _ |- _ => erewrite <-(constant_to_scalar_correct _ _ H)
                 | H : _ |- _ => rewrite andb_true_iff in H; destruct H; Z.ltb_to_lt
                 | H : Some _ = Some _ |- _ => progress (invert H)
                 | _ => rewrite has_word_range_mod_small by eauto using has_range_loosen, half_word_range_le_word_range
                 | _ => rewrite has_word_range_mod_small by
                       (eapply has_range_loosen with (r1:=half_word_range);
                        [ eapply has_half_word_range_shiftr with (r:=word_range) | ];
                        eauto using in_word_range_word_range, half_word_range_le_word_range)
                 | _ => rewrite and_shiftl_half_bits_eq
                 | _ => progress subst
                 | _ => reflexivity
                 | _ => discriminate
                 end.
      Qed.

      Local Ltac solve_commutative_replace :=
        match goal with
               | |- @eq (_ * _) ?x ?y =>
                 replace x with (fst x, snd x) by (destruct x; reflexivity);
                 replace y with (fst y, snd y) by (destruct y; reflexivity)
        end; autorewrite with to_div_mod; solve [repeat (f_equal; try ring)].

      Fixpoint is_tighter_than_bool_range_type t : range_type t -> range_type t -> bool :=
        match t with
        | type.type_primitive type.Z => (fun r1 r2 => (r1 <=? r2)%zrange)
        | type.prod a b => fun r1 r2 =>
                             (is_tighter_than_bool_range_type a (fst r1) (fst r2))
                               && (is_tighter_than_bool_range_type b (snd r1) (snd r2))
        | _ => fun _ _ => true
        end.

      Definition range_ok {t} : range_type t -> Prop :=
        match t with
        | type.type_primitive type.Z => fun r => in_word_range r
        | type.prod type.Z type.Z => fun r => in_word_range (fst r) /\ snd r = flag_range
        | _ => fun _ => False
        end.

      Lemma of_straightline_ident_correct s d t x r r' (idc : ident.ident s d) g :
        ok_ident s d x r idc ->
        range_ok r' ->
        is_tighter_than_bool_range_type d r r' = true ->
        ok_scalar x ->
        @interp interp_cast _ (of_straightline_ident dummy_arrow consts idc t r' x g) =
        @interp interp_cast _ (g (ident.interp idc (interp_scalar x))).
      Proof using consts_ok interp_cast_correct log2wordmax_even log2wordmax_pos.
        intros.
        pose proof wordmax_half_bits_pos.
        pose proof (ident_interp_has_range _ _ x r idc ltac:(assumption) ltac:(assumption)).
        match goal with H : ok_ident _ _ _ _ _ |- _ => induction H end;
          try solve [auto using of_straightline_ident_mul_correct];
          cbv [is_tighter_than_bool_range_type is_tighter_than_bool range_ok] in *;
          cbn [of_straightline_ident ident.interp ident.gen_interp
                                     invert_selm invert_sell] in *;
            intros; rewrite ?Z.eqb_refl; cbn [andb];
            try match goal with |- context [invert_shift] => break_match end;
            cbn [interp interp_ident]; try destruct_scalar;
          repeat match goal with
                   | _ => progress (cbn [fst snd interp_scalar] in * )
                   | _ => progress break_match; [ ]
                   | _ => progress autorewrite with zsimplify_fast
                   | _ => progress Z.ltb_to_lt
                   | H : _ /\ _ |- _ => destruct H
                   | _ => rewrite andb_true_iff in *
                   | _ => rewrite interp_cast_noop with (r:=flag_range) in *
                       by (apply has_flag_range_cc_m'; auto; extract_ok_scalar)
                   | _ => rewrite interp_cast_noop with (r:=flag_range) in *
                       by (apply has_flag_range_land'; auto; extract_ok_scalar)
                   | H : _ = (_,_) |- _ => progress (inversion H; subst)
                   | H : invert_shift _ _ = Some _ |- _ =>
                     apply invert_shift_correct in H; [|extract_ok_scalar];
                       rewrite <-H
                   | H : has_range ?r  (?f ?x ?y) |- context [?f ?y ?x] =>
                     replace (f y x) with (f x y) by solve_commutative_replace
                   | _ => rewrite has_word_range_mod_small
                       by (eapply has_range_loosen;
                           [apply has_range_interp_scalar; extract_ok_scalar|];
                           assumption)
                   | _ => rewrite interp_cast_noop by (cbn [has_range fst snd] in *; split; lia)
                   | _ => rewrite interp_cast2_noop by (cbn [has_range fst snd] in *; split; lia)
                   | _ => reflexivity
                 end.
      Qed.

      Lemma of_straightline_correct {t} (e : expr t) :
        ok_expr e ->
        @interp interp_cast _ (of_straightline dummy_arrow consts e)
        = Straightline.expr.interp (interp_ident:=@ident.interp) (interp_cast:=interp_cast) e.
      Proof using consts_ok interp_cast_correct log2wordmax_even log2wordmax_pos.
        induction 1; cbn [of_straightline]; intros;
          repeat match goal with
                 | _ => progress cbn [Straightline.expr.interp]
                 | _ => erewrite of_straightline_ident_correct
                     by (cbv [range_ok is_tighter_than_bool_range_type];
                         eauto using in_word_range_word_range;
                         try apply andb_true_iff; auto)
                 | _ => rewrite interp_cast_noop by eauto using has_range_loosen, ident_interp_has_range
                 | _ => rewrite interp_cast2_noop by eauto using has_range_loosen, ident_interp_has_range
                 | H : forall y, has_range _ y -> interp _ = _ |- _ => rewrite H by eauto using has_range_loosen, ident_interp_has_range
                 | _ => reflexivity
        end.
      Qed.
    End proofs.

   Section no_interp_cast.
      Context (dummy_arrow : forall s d, type.interp (s -> d)%ctype) (consts : list Z)
              (consts_ok : forall x, In x consts -> 0 <= x <= wordmax - 1).

      Local Arguments interp _ {_} _.
      Local Arguments interp_scalar _ {_} _.

      Local Ltac tighter_than_to_le :=
        repeat match goal with
               | _ => progress (cbv [is_tighter_than_bool] in * )
               | _ => rewrite andb_true_iff in *
               | H : _ /\ _ |- _ => destruct H
               end; Z.ltb_to_lt.

      Lemma replace_interp_cast_scalar {t} (x : scalar t) interp_cast interp_cast'
        (interp_cast_correct : forall r x, lower r <= x <= upper r -> interp_cast r x = x)
        (interp_cast'_correct : forall r x, lower r <= x <= upper r -> interp_cast' r x = x) :
        ok_scalar x ->
        interp_scalar interp_cast x = interp_scalar interp_cast' x.
      Proof using log2wordmax_pos.
        induction 1; cbn [interp_scalar Straightline.expr.interp_scalar];
          repeat match goal with
                 | _ => progress (cbv [has_range interp_cast2] in * )
                 | _ => progress tighter_than_to_le
                 | H : ok_scalar _ |- _ => apply (has_range_interp_scalar (interp_cast_correct:=interp_cast_correct)) in H
                 | _ => rewrite <-IHok_scalar
                 | _ => rewrite interp_cast_correct by lia
                 | _ => rewrite interp_cast'_correct by lia
                 | _ => congruence
                 end.
      Qed.

      Lemma replace_interp_cast {t} (e : expr t) interp_cast interp_cast'
        (interp_cast_correct : forall r x, lower r <= x <= upper r -> interp_cast r x = x)
        (interp_cast'_correct : forall r x, lower r <= x <= upper r -> interp_cast' r x = x) :
        ok_expr consts e ->
        interp interp_cast (of_straightline dummy_arrow consts e) =
        interp interp_cast' (of_straightline dummy_arrow consts e).
      Proof using consts_ok log2wordmax_even log2wordmax_pos.
        induction 1; intros; cbn [of_straightline interp].
        { apply replace_interp_cast_scalar; auto. }
        { erewrite !of_straightline_ident_correct by (eauto; cbv [range_ok]; apply in_word_range_word_range).
          rewrite @replace_interp_cast_scalar with (interp_cast':=interp_cast') by auto.
          eauto using ident_interp_has_range. }
        { erewrite !of_straightline_ident_correct by
              (eauto; try solve [cbv [range_ok]; split; auto using in_word_range_word_range];
               cbv [is_tighter_than_bool_range_type]; apply andb_true_iff; split; auto).
          rewrite @replace_interp_cast_scalar with (interp_cast':=interp_cast') by auto.
          eauto using ident_interp_has_range. }
      Qed.
    End no_interp_cast.
  End with_wordmax.

  Definition of_Expr {s d} (log2wordmax : Z) (consts : list Z) (e : Expr (s -> d))
             (var : type -> Type) (x : var s) dummy_arrow : @Straightline.expr.expr var ident d :=
    @of_straightline log2wordmax var dummy_arrow consts _ (Straightline.of_Expr e var x dummy_arrow).

  Definition interp_cast_mod w r x := if (lower r =? 0)
                                      then if (upper r =? 2^w - 1)
                                           then x mod (2^w)
                                           else if (upper r =? 1)
                                                then x mod 2
                                                else x
                                      else x.

  Lemma interp_cast_mod_correct w r x :
    lower r <= x <= upper r ->
    interp_cast_mod w r x = x.
  Proof using Type.
    cbv [interp_cast_mod].
    intros; break_match; rewrite ?andb_true_iff in *; intuition; Z.ltb_to_lt;
      apply Z.mod_small; lia.
  Qed.

  Lemma of_Expr_correct {s d} (log2wordmax : Z) (consts : list Z) (e : Expr (s -> d))
        (e' : (type.interp s -> Uncurried.expr.expr d))
        (x : type.interp s) dummy_arrow :
    e type.interp = Abs e' ->
    1 < log2wordmax ->
    log2wordmax mod 2 = 0 ->
    Straightline.expr.ok_expr (e' x) ->
    (forall x0 : Z, In x0 consts -> 0 <= x0 <= 2 ^ log2wordmax - 1) ->
    ok_expr log2wordmax consts
            (of_uncurried (dummy_arrow:=dummy_arrow) (depth (fun _ : type => unit) (fun _ : type => tt) (e _)) (e' x)) ->
    (depth type.interp (@DefaultValue.type.default) (e' x) <= depth (fun _ : type => unit) (fun _ : type => tt) (e _))%nat ->
    @interp log2wordmax (interp_cast_mod log2wordmax) _ (of_Expr log2wordmax consts e type.interp x dummy_arrow) = @Uncurried.expr.interp _ (@ident.interp) _ (e type.interp) x.
  Proof using Type.
    intro He'; intros; cbv [of_Expr Straightline.of_Expr].
    rewrite He'; cbn [invert_Abs expr.interp].
    assert (forall r z, lower r <= z <= upper r -> ident.cast ident.cast_outside_of_range r z = z) as interp_cast_correct.
    { cbv [ident.cast]; intros; break_match; rewrite ?andb_true_iff, ?andb_false_iff in *; intuition; Z.ltb_to_lt; lia. }
    erewrite replace_interp_cast with (interp_cast':=ident.cast ident.cast_outside_of_range) by auto using interp_cast_mod_correct.
    rewrite of_straightline_correct by auto.
    erewrite Straightline.expr.of_uncurried_correct by eassumption.
    reflexivity.
  Qed.

  Module Notations.
    Import PrintingNotations.
    Import Straightline.expr.

    Local Notation "'tZ'" := (type.type_primitive type.Z).
    Notation "'RegZero'" := (Primitive (t:=type.Z) 0).
    Notation "$ x" := (Cast uint256 (Fst (Cast2 (uint256,bool)%core (Var (tZ * tZ) x)))) (at level 10, format "$ x").
    Notation "$ x" := (Cast uint128 (Fst (Cast2 (uint128,bool)%core (Var (tZ * tZ) x)))) (at level 10, format "$ x").
    Notation "$ x ₁" := (Cast uint256 (Fst (Var (tZ * tZ) x))) (at level 10, format "$ x ₁").
    Notation "$ x ₂" := (Cast uint256 (Snd (Var (tZ * tZ) x))) (at level 10, format "$ x ₂").
    Notation "$ x" := (Cast uint256 (Var tZ x)) (at level 10, format "$ x").
    Notation "$ x" := (Cast uint128 (Var tZ x)) (at level 10, format "$ x").
    Notation "$ x" := (Cast bool (Var tZ x)) (at level 10, format "$ x").
    Notation "carry{ $ x }" := (Cast bool (Snd (Cast2 (uint256, bool)%core (Var (tZ * tZ) x))))
                                 (at level 10, format "carry{ $ x }").
    Notation "Lower{ x }" := (Cast uint128 (Land 340282366920938463463374607431768211455 x))
                               (at level 10, format "Lower{ x }").
    Notation "f @( y , x1 , x2 ); g "
      := (LetInAppIdentZZ (uint256, bool)%core f (Pair x1 x2) (fun y => g))
           (at level 10, g at level 200, format "f @( y ,  x1 ,  x2 ); '//' g ").
    Notation "f @( y , x1 , x2 , x3 ); g "
      := (LetInAppIdentZZ (uint256, bool)%core f (Pair (Pair x1 x2) x3) (fun y => g))
           (at level 10, g at level 200, format "f @( y ,  x1 ,  x2 ,  x3 ); '//' g ").
    Notation "f @( y , x1 , x2 , x3 ); '#128' g "
      := (LetInAppIdentZZ (uint128, bool)%core f (Pair (Pair x1 x2) x3) (fun y => g))
           (at level 10, g at level 200, format "f @( y ,  x1 ,  x2 ,  x3 );  '#128' '//' g ").
    Notation "f @( y , x1 , x2 ); g "
      := (LetInAppIdentZ uint256 f (Pair x1 x2) (fun y => g))
           (at level 10, g at level 200, format "f @( y ,  x1 ,  x2 ); '//' g ").
    Notation "f @( y , x1 , x2 , x3 ); g "
      := (LetInAppIdentZ uint256 f (Pair (Pair x1 x2) x3) (fun y => g))
           (at level 10, g at level 200, format "f @( y ,  x1 ,  x2 ,  x3 ); '//' g ").
    (* special cases for when the ident constructor takes a constant argument *)
    Notation "add@( y , x1 , x2 , n ); g"
      := (LetInAppIdentZZ (uint256, bool) (add n) (Pair x1 x2) (fun y => g))
           (at level 10, g at level 200, format "add@( y ,  x1 ,  x2 ,  n ); '//' g").
    Notation "addc@( y , x1 , x2 , x3 , n ); g"
      := (LetInAppIdentZZ (uint256, bool) (addc n) (Pair (Pair x1 x2) x3) (fun y => g))
           (at level 10, g at level 200, format "addc@( y ,  x1 ,  x2 ,  x3 ,  n ); '//' g").
    Notation "addc@( y , x1 , x2 , x3 , n ); '#128' g"
      := (LetInAppIdentZZ (uint128, bool) (addc n) (Pair (Pair x1 x2) x3) (fun y => g))
           (at level 10, g at level 200, format "addc@( y ,  x1 ,  x2 ,  x3 ,  n );  '#128' '//' g").
    Notation "sub@( y , x1 , x2 , n ); g"
      := (LetInAppIdentZZ (uint256, bool) (sub n) (Pair x1 x2) (fun y => g))
           (at level 10, g at level 200, format "sub@( y ,  x1 ,  x2 ,  n ); '//' g").
    Notation "subb@( y , x1 , x2 , x3 , n ); g"
      := (LetInAppIdentZZ (uint256, bool) (subb n) (Pair (Pair x1 x2) x3) (fun y => g))
           (at level 10, g at level 200, format "subb@( y ,  x1 ,  x2 ,  x3 ,  n ); '//' g").
    Notation "rshi@( y , x1 , x2 , n ); g"
      := (LetInAppIdentZ _ (rshi n) (Pair x1 x2) (fun y => g))
           (at level 10, g at level 200, format "rshi@( y ,  x1 ,  x2 , n ); '//' g ").
    Notation "'ret' $ x" := (Scalar (Var tZ x)) (at level 10, format "'ret'  $ x").
    Notation "( x , y )" := (Pair x y) (at level 10, left associativity).
  End Notations.

  Module Tactics.
    Ltac ok_expr_step' :=
      match goal with
      | _ => assumption
      | |- _ <= _ <= _ \/ @eq zrange _ _ =>
        right; lazy; try split; congruence
      | |- _ <= _ <= _ \/ @eq zrange _ _ =>
        left; lazy; try split; congruence
      | |- context [PreFancy.ok_ident] => constructor
      | |- context [PreFancy.ok_scalar] => constructor; try lia
      | |- context [PreFancy.is_halved] => eapply PreFancy.is_halved_constant; [lazy; reflexivity | ]
      | |- context [PreFancy.is_halved] => constructor
      | |- context [PreFancy.in_word_range] => lazy; reflexivity
      | |- context [PreFancy.in_flag_range] => lazy; reflexivity
      | |- context [PreFancy.get_range] =>
        cbn [PreFancy.get_range lower upper fst snd ZRange.map]
      | x : type.interp (type.prod _ _) |- _ => destruct x
      | |- (_ <=? _)%zrange = true =>
        match goal with
        | |- context [PreFancy.get_range_var] =>
          cbv [is_tighter_than_bool PreFancy.has_range fst snd upper lower] in *; cbn;
          apply andb_true_iff; split; apply Z.leb_le
        | _ => lazy
        end; lia || reflexivity
      | |- @eq zrange _ _ => lazy; reflexivity
      | |- _ <= _ => lia
      | |- _ <= _ <= _ => lia
      end; intros.

    Ltac ok_expr_step :=
      match goal with
      | |- context [PreFancy.ok_expr] => constructor; cbn [fst snd]; repeat ok_expr_step'
      end; intros; cbn [Nat.max].
  End Tactics.
End PreFancy.

Module Fancy.
  Import Straightline.expr.

  Module CC.
    Inductive code : Type :=
    | C : code
    | M : code
    | L : code
    | Z : code
    .

    Record state :=
      { cc_c : bool; cc_m : bool; cc_l : bool; cc_z : bool }.

    Definition code_dec (x y : code) : {x = y} + {x <> y}.
    Proof. destruct x, y; try apply (left eq_refl); right; congruence. Defined.

    Definition update (to_write : list code) (result : BinInt.Z) (cc_spec : code -> BinInt.Z -> bool) (old_state : state)
      : state :=
      {|
        cc_c := if (In_dec code_dec C to_write)
                then cc_spec C result
                else old_state.(cc_c);
        cc_m := if (In_dec code_dec M to_write)
                then cc_spec M result
                else old_state.(cc_m);
        cc_l := if (In_dec code_dec L to_write)
                then cc_spec L result
                else old_state.(cc_l);
        cc_z := if (In_dec code_dec Z to_write)
                then cc_spec Z result
                else old_state.(cc_z)
      |}.

  End CC.

  Record instruction :=
    {
      num_source_regs : nat;
      writes_conditions : list CC.code;
      spec : tuple Z num_source_regs -> CC.state -> Z
    }.

  Section expr.
    Context {name : Type} (name_eqb : name -> name -> bool) (wordmax : Z) (cc_spec : CC.code -> Z -> bool).

    Inductive expr :=
    | Ret : name -> expr
    | Instr (i : instruction)
            (rd : name) (* destination register *)
            (args : tuple name i.(num_source_regs)) (* source registers *)
            (cont : expr) (* next line *)
      : expr
    .

    Fixpoint interp (e : expr) (cc : CC.state) (ctx : name -> Z) : Z :=
      match e with
      | Ret n => ctx n
      | Instr i rd args cont =>
        let result := i.(spec) (Tuple.map ctx args) cc in
        let new_cc := CC.update i.(writes_conditions) result cc_spec cc in
        let new_ctx := (fun n : name => if name_eqb n rd then result mod wordmax else ctx n) in
        interp cont new_cc new_ctx
      end.
  End expr.

  Section ISA.
    Import CC.

    (* For the C flag, we have to consider cases with a negative result (like the one returned by an underflowing borrow).
       In these cases, we want to set the C flag to true. *)
    Definition cc_spec (x : CC.code) (result : BinInt.Z) : bool :=
      match x with
      | CC.C => if result <? 0 then true else Z.testbit result 256
      | CC.M => Z.testbit result 255
      | CC.L => Z.testbit result 0
      | CC.Z => result =? 0
      end.

    Local Definition lower128 x := (Z.land x (Z.ones 128)).
    Local Definition upper128 x := (Z.shiftr x 128).
    Local Notation "x '[C]'" := (if x.(cc_c) then 1 else 0) (at level 20).
    Local Notation "x '[M]'" := (if x.(cc_m) then 1 else 0) (at level 20).
    Local Notation "x '[L]'" := (if x.(cc_l) then 1 else 0) (at level 20).
    Local Notation "x '[Z]'" := (if x.(cc_z) then 1 else 0) (at level 20).
    Local Notation "'int'" := (BinInt.Z).
    Local Notation "x << y" := ((x << y) mod (2^256)) : Z_scope. (* truncating left shift *)


    (* Note: In the specification document, argument order gets a bit
    confusing. Like here, r0 is always the first argument "source 0"
    and r1 the second. But the specification of MUL128LU is:
            (R[RS1][127:0] * R[RS0][255:128])

    while the specification of SUB is:
          (R[RS0] - shift(R[RS1], imm))

    In the SUB case, r0 is really treated the first argument, but in
    MUL128LU the order seems to be reversed; rather than low-high, we
    take the high part of the first argument r0 and the low parts of
    r1. This is also true for MUL128UL. *)

    Definition ADD (imm : int) : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [C; M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   r0 + (r1 << imm))
      |}.

    Definition ADDC (imm : int) : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [C; M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   r0 + (r1 << imm) + cc[C])
      |}.

    Definition SUB (imm : int) : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [C; M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   r0 - (r1 << imm))
      |}.

    Definition SUBC (imm : int) : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [C; M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   r0 - (r1 << imm) - cc[C])
      |}.


    Definition MUL128LL : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   (lower128 r0) * (lower128 r1))
      |}.

    Definition MUL128LU : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   (lower128 r1) * (upper128 r0)) (* see note *)
      |}.

    Definition MUL128UL : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   (upper128 r1) * (lower128 r0)) (* see note *)
      |}.

    Definition MUL128UU : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   (upper128 r0) * (upper128 r1))
      |}.

    (* Note : Unlike the other operations, the output of RSHI is
    truncated in the specification. This is not strictly necessary,
    since the interpretation function truncates the output
    anyway. However, it is useful to make the definition line up
    exactly with Z.rshi. *)
    Definition RSHI (imm : int) : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   (((2^256 * r0) + r1) >> imm) mod (2^256))
      |}.

    Definition SELC : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [];
        spec := (fun '(r0, r1) cc =>
                   if cc[C] =? 1 then r0 else r1)
      |}.

    Definition SELM : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [];
        spec := (fun '(r0, r1) cc =>
                   if cc[M] =? 1 then r0 else r1)
      |}.

    Definition SELL : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [];
        spec := (fun '(r0, r1) cc =>
                   if cc[L] =? 1 then r0 else r1)
      |}.

    (* TODO : treat the MOD register specially, like CC *)
    Definition ADDM : instruction :=
      {|
        num_source_regs := 3;
        writes_conditions := [M; L; Z];
        spec := (fun '(r0, r1, MOD) cc =>
                   let ra := r0 + r1 in
                   if ra >=? MOD
                   then ra - MOD
                   else ra)
      |}.

  End ISA.

  Module Registers.
    Inductive register : Type :=
    | r0 : register
    | r1 : register
    | r2 : register
    | r3 : register
    | r4 : register
    | r5 : register
    | r6 : register
    | r7 : register
    | r8 : register
    | r9 : register
    | r10 : register
    | r11 : register
    | r12 : register
    | r13 : register
    | r14 : register
    | r15 : register
    | r16 : register
    | r17 : register
    | r18 : register
    | r19 : register
    | r20 : register
    | r21 : register
    | r22 : register
    | r23 : register
    | r24 : register
    | r25 : register
    | r26 : register
    | r27 : register
    | r28 : register
    | r29 : register
    | r30 : register
    | RegZero : register (* r31 *)
    | RegMod : register
    .

    Definition reg_dec (x y : register) : {x = y} + {x <> y}.
    Proof. destruct x, y; try (apply left; congruence); right; congruence. Defined.
    Definition reg_eqb x y := if reg_dec x y then true else false.

    Lemma reg_eqb_neq x y : x <> y -> reg_eqb x y = false.
    Proof using Type. cbv [reg_eqb]; break_match; congruence. Qed.
    Lemma reg_eqb_refl x : reg_eqb x x = true.
    Proof using Type. cbv [reg_eqb]; break_match; congruence. Qed.
  End Registers.

  Section of_prefancy.
    Context (name : Type) (name_succ : name -> name) (error : name) (consts : Z -> option name).

    Fixpoint var (t : type) : Type :=
      match t with
      | type.type_primitive type.Z => name
      | type.prod a b => var a * var b
      | _ => unit
      end.

    Fixpoint of_prefancy_scalar {t} (s : @scalar var t) : var t :=
      match s with
      | Var t v => v
      | Pair a b x y => (of_prefancy_scalar x, of_prefancy_scalar y)
      | Cast r x => of_prefancy_scalar x
      | Cast2 r x => of_prefancy_scalar x
      | Fst a b x => fst (of_prefancy_scalar x)
      | Snd a b x => snd (of_prefancy_scalar x)
      | Shiftr n x => error
      | Shiftl n x => error
      | Land n x => error
      | CC_m n x => error
      | @Primitive _ type.Z x => match consts x with
                                 | Some n => n
                                 | None => error
                                 end
      | @Primitive _ _ x => tt
      | TT => tt
      | Nil _ => tt
      end.

    (* Note : some argument orders are reversed for MUL128LU, MUL128UL, SELC, SELM, and SELL *)
    Definition of_prefancy_ident {s d} (idc : PreFancy.ident s d)
      : @scalar var s -> {i : instruction & tuple name i.(num_source_regs) } :=
      match idc in PreFancy.ident s d return _ with
      | PreFancy.add imm => fun args : @scalar var (type.Z * type.Z) =>
                              existT _ (ADD imm) (of_prefancy_scalar args)
      | PreFancy.addc imm => fun args : @scalar var (type.Z * type.Z * type.Z) =>
                               existT _ (ADDC imm) (of_prefancy_scalar (Pair (Snd (Fst args)) (Snd args)))
      | PreFancy.sub imm => fun args : @scalar var (type.Z * type.Z) =>
                              existT _ (SUB imm) (of_prefancy_scalar args)
      | PreFancy.subb imm => fun args : @scalar var (type.Z * type.Z * type.Z) =>
                               existT _ (SUBC imm) (of_prefancy_scalar (Pair (Snd (Fst args)) (Snd args)))
      | PreFancy.mulll => fun args : @scalar var (type.Z * type.Z) =>
                            existT _ MUL128LL (of_prefancy_scalar args)
      | PreFancy.mullh => fun args : @scalar var (type.Z * type.Z) =>
                            existT _ MUL128LU (of_prefancy_scalar (Pair (Snd args) (Fst args)))
      | PreFancy.mulhl => fun args : @scalar var (type.Z * type.Z) =>
                            existT _ MUL128UL (of_prefancy_scalar (Pair (Snd args) (Fst args)))
      | PreFancy.mulhh => fun args : @scalar var (type.Z * type.Z) =>
                            existT _ MUL128UU (of_prefancy_scalar args)
      | PreFancy.rshi imm => fun args : @scalar var (type.Z * type.Z) =>
                               existT _ (RSHI imm) (of_prefancy_scalar args)
      | PreFancy.selc => fun args : @scalar var (type.Z * type.Z * type.Z) =>
                           existT _ SELC (of_prefancy_scalar (Pair (Snd args) (Snd (Fst args))))
      | PreFancy.selm => fun args : @scalar var (type.Z * type.Z * type.Z) =>
                           existT _ SELM (of_prefancy_scalar (Pair (Snd args) (Snd (Fst args))))
      | PreFancy.sell => fun args : @scalar var (type.Z * type.Z * type.Z) =>
                           existT _ SELL (of_prefancy_scalar (Pair (Snd args) (Snd (Fst args))))
      | PreFancy.addm => fun args : @scalar var (type.Z * type.Z * type.Z) =>
                           existT _ ADDM (of_prefancy_scalar args)
      end.

    Fixpoint of_prefancy (next_name : name) {t} (e : @Straightline.expr.expr var PreFancy.ident t) : expr :=
      match e with
      | LetInAppIdentZ s d r idc x f =>
        let instr_args := @of_prefancy_ident s type.Z idc x in
        let i : instruction := projT1 instr_args in
        let args : tuple name i.(num_source_regs) := projT2 instr_args in
        Instr i next_name args (of_prefancy (name_succ next_name) (f next_name))
      | LetInAppIdentZZ s d r idc x f =>
        let instr_args := @of_prefancy_ident s (type.Z * type.Z) idc x in
        let i : instruction := projT1 instr_args in
        let args : tuple name i.(num_source_regs) := projT2 instr_args in
        Instr i next_name args (of_prefancy (name_succ next_name) (f (next_name, error))) (* we pass the error code as the carry register, because it cannot be read from directly. *)
      | Scalar type.Z s => Ret (of_prefancy_scalar s)
      | _ => Ret error
      end.
  End of_prefancy.

  Section allocate_registers.
    Context (reg name : Type) (name_eqb : name -> name -> bool) (error : reg).
    Fixpoint allocate (e : @expr name) (reg_list : list reg) (name_to_reg : name -> reg) : @expr reg :=
      match e with
      | Ret n => Ret (name_to_reg n)
      | Instr i rd args cont =>
        match reg_list with
        | r :: reg_list' => Instr i r (Tuple.map name_to_reg args) (allocate cont reg_list' (fun n => if name_eqb n rd then r else name_to_reg n))
        | nil => Ret error
        end
      end.
  End allocate_registers.

  Definition test_prog : @expr positive :=
    Instr (ADD (128)) 3%positive (1, 2)%positive
          (Instr (ADDC 0) 4%positive (3,1)%positive
                 (Ret 4%positive)).

  Definition x1 := 2^256 - 1.
  Definition x2 := 2^128 - 1.
  Definition wordmax := 2^256.
  Definition expected :=
    let r3' := (x1 + (x2 << 128)) in
    let r3 := r3' mod wordmax in
    let c := r3' / wordmax in
    let r4' := (r3 + x1 + c) in
    r4' mod wordmax.
  Definition actual :=
    interp Pos.eqb
           (2^256) cc_spec test_prog {|CC.cc_c:=false; CC.cc_m:=false; CC.cc_l:=false; CC.cc_z:=false|}
           (fun n => if n =? 1%positive
                     then x1
                     else if n =? 2%positive
                          then x2
                          else 0).
  Lemma test_prog_ok : expected = actual.
  Proof using Type. reflexivity. Qed.

  Definition of_Expr {s d} next_name (consts : Z -> option positive) (consts_list : list Z) (e : Expr (s -> d)) (x : var positive s) dummy_arrow : positive -> @expr positive :=
    fun error =>
      @of_prefancy positive Pos.succ error consts next_name _ (PreFancy.of_Expr 256 consts_list e (var positive) x dummy_arrow).

End Fancy.

Module Prod.
  Import Fancy. Import Registers.

  Definition Mul256 (out src1 src2 tmp : register) (cont : Fancy.expr) : Fancy.expr :=
    Instr MUL128LL out (src1, src2)
          (Instr MUL128UL tmp (src1, src2)
                 (Instr (ADD 128) out (out, tmp)
                        (Instr MUL128LU tmp (src1, src2)
                               (Instr (ADD 128) out (out, tmp) cont)))).
  Definition Mul256x256 (out outHigh src1 src2 tmp : register) (cont : Fancy.expr) : Fancy.expr :=
    Instr MUL128LL out (src1, src2)
          (Instr MUL128UU outHigh (src1, src2)
                 (Instr MUL128UL tmp (src1, src2)
                        (Instr (ADD 128) out (out, tmp)
                               (Instr (ADDC (-128)) outHigh (outHigh, tmp)
                                      (Instr MUL128LU tmp (src1, src2)
                                             (Instr (ADD 128) out (out, tmp)
                                                    (Instr (ADDC (-128)) outHigh (outHigh, tmp) cont))))))).

  Definition MontRed256 lo hi y t1 t2 scratch RegPInv : @Fancy.expr register :=
    Mul256 y lo RegPInv t1
           (Mul256x256 t1 t2 y RegMod scratch
                       (Instr (ADD 0) lo (lo, t1)
                              (Instr (ADDC 0) hi (hi, t2)
                                     (Instr SELC y (RegMod, RegZero)
                                            (Instr (SUB 0) lo (hi, y)
                                                   (Instr ADDM lo (lo, RegZero, RegMod)
                                                          (Ret lo))))))).

  (* Barrett reduction -- this is only the "reduce" part, excluding the initial multiplication. *)
  Definition MulMod x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5 : @Fancy.expr register :=
    let q1Bottom256 := scratchp1 in
    let muSelect := scratchp2 in
    let q2 := scratchp3 in
    let q2High := scratchp4 in
    let q2High2 := scratchp5 in
    let q3 := scratchp1 in
    let r2 := scratchp2 in
    let r2High := scratchp3 in
    let maybeM := scratchp1 in
    Instr SELM muSelect (RegMuLow, RegZero)
          (Instr (RSHI 255) q1Bottom256 (xHigh, x)
                 (Mul256x256 q2 q2High q1Bottom256 RegMuLow scratchp5
                             (Instr (RSHI 255) q2High2 (RegZero, xHigh)
                                    (Instr (ADD 0) q2High (q2High, q1Bottom256)
                                           (Instr (ADDC 0) q2High2 (q2High2, RegZero)
                                                  (Instr (ADD 0) q2High (q2High, muSelect)
                                                         (Instr (ADDC 0) q2High2 (q2High2, RegZero)
                                                                (Instr (RSHI 1) q3 (q2High2, q2High)
                                                                       (Mul256x256 r2 r2High RegMod q3 scratchp4
                                                                                   (Instr (SUB 0) muSelect (x, r2)
                                                                                          (Instr (SUBC 0) xHigh (xHigh, r2High)
                                                                                                 (Instr SELL maybeM (RegMod, RegZero)
                                                                                                        (Instr (SUB 0) q3 (muSelect, maybeM)
                                                                                                               (Instr ADDM x (q3, RegZero, RegMod)
                                                                                                                      (Ret x))))))))))))))).
End Prod.

Module ProdEquiv.
  Import Fancy. Import Registers.

  Definition interp256 := Fancy.interp reg_eqb (2^256) cc_spec.
  Lemma interp_step i rd args cont cc ctx :
    interp256 (Instr i rd args cont) cc ctx =
      let result := spec i (Tuple.map ctx args) cc in
      let new_cc := CC.update (writes_conditions i) result cc_spec cc in
      let new_ctx := fun n => if reg_eqb n rd then result mod wordmax else ctx n in interp256 cont new_cc new_ctx.
  Proof using Type. reflexivity. Qed.

  Lemma interp_state_equiv e :
    forall cc ctx cc' ctx',
    cc = cc' -> (forall r, ctx r = ctx' r) ->
    interp256 e cc ctx = interp256 e cc' ctx'.
  Proof using Type.
    induction e; intros; subst; cbn; [solve[auto]|].
    apply IHe; rewrite Tuple.map_ext with (g:=ctx') by auto;
      [reflexivity|].
    intros; break_match; auto.
  Qed.
  Lemma cc_overwrite_full x1 x2 l1 cc :
    CC.update [CC.C; CC.M; CC.L; CC.Z] x2 cc_spec (CC.update l1 x1 cc_spec cc) = CC.update [CC.C; CC.M; CC.L; CC.Z] x2 cc_spec cc.
  Proof using Type.
    cbv [CC.update]. cbn [CC.cc_c CC.cc_m CC.cc_l CC.cc_z].
    break_match; try match goal with H : ~ In _ _ |- _ => cbv [In] in H; tauto end.
    reflexivity.
  Qed.

  Definition value_unused r e : Prop :=
    forall x cc ctx, interp256 e cc ctx = interp256 e cc (fun r' => if reg_eqb r' r then x else ctx r').

  Lemma value_unused_skip r i rd args cont (Hcont: value_unused r cont) :
    r <> rd ->
    (~ In r (Tuple.to_list _ args)) ->
    value_unused r (Instr i rd args cont).
  Proof using Type.
    cbv [value_unused] in *; intros.
    rewrite !interp_step; cbv zeta.
    rewrite Hcont with (x:=x).
    match goal with |- ?lhs = ?rhs =>
                    match lhs with context [Tuple.map ?f ?t] =>
                                   match rhs with context [Tuple.map ?g ?t] =>
                                                  rewrite (Tuple.map_ext_In f g) by (intros; cbv [reg_eqb]; break_match; congruence)
                                   end end end.
    apply interp_state_equiv; [ congruence | ].
    { intros; cbv [reg_eqb] in *; break_match; congruence. }
  Qed.

  Lemma value_unused_overwrite r i args cont :
    (~ In r (Tuple.to_list _ args)) ->
    value_unused r (Instr i r args cont).
  Proof using Type.
    cbv [value_unused]; intros; rewrite !interp_step; cbv zeta.
    match goal with |- ?lhs = ?rhs =>
                    match lhs with context [Tuple.map ?f ?t] =>
                                   match rhs with context [Tuple.map ?g ?t] =>
                                                  rewrite (Tuple.map_ext_In f g) by (intros; cbv [reg_eqb]; break_match; congruence)
                                   end end end.
    apply interp_state_equiv; [ congruence | ].
    { intros; cbv [reg_eqb] in *; break_match; congruence. }
  Qed.

  Lemma value_unused_ret r r' :
    r <> r' ->
    value_unused r (Ret r').
  Proof using Type.
    cbv - [reg_dec]; intros.
    break_match; congruence.
  Qed.

  Ltac remember_results :=
    repeat match goal with |- context [(spec ?i ?args ?flags) mod ?w] =>
                    let x := fresh "x" in
                    let y := fresh "y" in
                    let Heqx := fresh "Heqx" in
                    remember (spec i args flags) as x eqn:Heqx;
                    remember (x mod w) as y
           end.

  Ltac do_interp_step :=
    rewrite interp_step; cbn - [interp spec];
    repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl by congruence;
    remember_results.

  Lemma interp_Mul256 out src1 src2 tmp tmp2 cont cc ctx:
    out <> src1 ->
    out <> src2 ->
    out <> tmp ->
    out <> tmp2 ->
    src1 <> src2 ->
    src1 <> tmp ->
    src1 <> tmp2 ->
    src2 <> tmp ->
    src2 <> tmp2 ->
    tmp <> tmp2 ->
    value_unused tmp cont ->
    value_unused tmp2 cont ->
    interp256 (Prod.Mul256 out src1 src2 tmp cont) cc ctx =
    interp256 (
        Instr MUL128LU tmp (src1, src2)
              (Instr MUL128UL tmp2 (src1, src2)
                     (Instr MUL128LL out (src1, src2)
                                 (Instr (ADD 128) out (out, tmp2)
                                        (Instr (ADD 128) out (out, tmp) cont))))) cc ctx.
  Proof using Type.
    intros; cbv [Prod.Mul256].
    repeat (do_interp_step; cbn [spec MUL128LL MUL128UL MUL128LU ADD] in * ).

    match goal with H : value_unused tmp _ |- _ => erewrite H end.
    match goal with H : value_unused tmp2 _ |- _ => erewrite H end.
    apply interp_state_equiv.
    { rewrite !cc_overwrite_full.
      f_equal. subst. lia. }
    { intros; cbv [reg_eqb].
      repeat (break_match_step ltac:(fun _ => idtac); try congruence); reflexivity. }
  Qed.

  Lemma interp_Mul256x256 out outHigh src1 src2 tmp tmp2 cont cc ctx:
    out <> src1 ->
    out <> outHigh ->
    out <> src2 ->
    out <> tmp ->
    out <> tmp2 ->
    outHigh <> src1 ->
    outHigh <> src2 ->
    outHigh <> tmp ->
    outHigh <> tmp2 ->
    src1 <> src2 ->
    src1 <> tmp ->
    src1 <> tmp2 ->
    src2 <> tmp ->
    src2 <> tmp2 ->
    tmp <> tmp2 ->
    value_unused tmp cont ->
    value_unused tmp2 cont ->
    interp256 (Prod.Mul256x256 out outHigh src1 src2 tmp cont) cc ctx =
    interp256 (
        Instr MUL128LL out (src1, src2)
              (Instr MUL128LU tmp (src1, src2)
                     (Instr MUL128UL tmp2 (src1, src2)
                            (Instr MUL128UU outHigh (src1, src2)
                                   (Instr (ADD 128) out (out, tmp2)
                                          (Instr (ADDC (-128)) outHigh (outHigh, tmp2)
                                                 (Instr (ADD 128) out (out, tmp)
                                                        (Instr (ADDC (-128)) outHigh (outHigh, tmp) cont)))))))) cc ctx.
  Proof using Type.
    intros; cbv [Prod.Mul256x256].
    repeat (do_interp_step; cbn [spec MUL128LL MUL128UL MUL128LU MUL128UU ADD ADDC] in * ).

    match goal with H : value_unused tmp _ |- _ => erewrite H end.
    match goal with H : value_unused tmp2 _ |- _ => erewrite H end.
    apply interp_state_equiv.
    { rewrite !cc_overwrite_full.
      f_equal.
      subst. cbn - [Z.add Z.modulo Z.testbit Z.mul Z.shiftl Fancy.lower128 Fancy.upper128].
      lia. }
    { intros; cbv [reg_eqb].
      repeat (break_match_step ltac:(fun _ => idtac); try congruence); try reflexivity; [ ].
      subst. cbn - [Z.add Z.modulo Z.testbit Z.mul Z.shiftl Fancy.lower128 Fancy.upper128].
      lia. }
  Qed.

  Lemma mulll_comm rd x y cont cc ctx :
    ProdEquiv.interp256 (Fancy.Instr Fancy.MUL128LL rd (x, y) cont) cc ctx = ProdEquiv.interp256 (Fancy.Instr Fancy.MUL128LL rd (y, x) cont) cc ctx.
  Proof using Type. rewrite !ProdEquiv.interp_step. cbn - [Fancy.interp]. rewrite Z.mul_comm. reflexivity. Qed.

  Lemma mulhh_comm rd x y cont cc ctx :
    ProdEquiv.interp256 (Fancy.Instr Fancy.MUL128UU rd (x, y) cont) cc ctx = ProdEquiv.interp256 (Fancy.Instr Fancy.MUL128UU rd (y, x) cont) cc ctx.
  Proof using Type. rewrite !ProdEquiv.interp_step. cbn - [Fancy.interp]. rewrite Z.mul_comm. reflexivity. Qed.

  Lemma mullh_mulhl rd x y cont cc ctx :
    ProdEquiv.interp256 (Fancy.Instr Fancy.MUL128LU rd (x, y) cont) cc ctx = ProdEquiv.interp256 (Fancy.Instr Fancy.MUL128UL rd (y, x) cont) cc ctx.
  Proof using Type. rewrite !ProdEquiv.interp_step. cbn - [Fancy.interp]. rewrite Z.mul_comm. reflexivity. Qed.

  Lemma add_comm rd x y cont cc ctx :
    0 <= ctx x < 2^256 ->
    0 <= ctx y < 2^256 ->
    ProdEquiv.interp256 (Fancy.Instr (Fancy.ADD 0) rd (x, y) cont) cc ctx = ProdEquiv.interp256 (Fancy.Instr (Fancy.ADD 0) rd (y, x) cont) cc ctx.
  Proof using Type.
    intros; rewrite !ProdEquiv.interp_step. cbn - [Fancy.interp]. rewrite Z.add_comm.
    rewrite !(Z.mod_small (ctx _)) by (cbn in *; lia). reflexivity.
  Qed.

  Lemma addc_comm rd x y cont cc ctx :
    0 <= ctx x < 2^256 ->
    0 <= ctx y < 2^256 ->
    ProdEquiv.interp256 (Fancy.Instr (Fancy.ADDC 0) rd (x, y) cont) cc ctx = ProdEquiv.interp256 (Fancy.Instr (Fancy.ADDC 0) rd (y, x) cont) cc ctx.
  Proof using Type.
    intros; rewrite !ProdEquiv.interp_step. cbn - [Fancy.interp]. rewrite (Z.add_comm (ctx x)).
    rewrite !(Z.mod_small (ctx _)) by (cbn in *; lia). reflexivity.
  Qed.

  (* Tactics to help prove that something in Fancy is line-by-line equivalent to something in PreFancy *)
  Ltac push_value_unused :=
    repeat match goal with
           | |- ~ In _ _ => cbn; intuition; congruence
           | _ => apply ProdEquiv.value_unused_overwrite
           | _ => apply ProdEquiv.value_unused_skip; [ | congruence | ]
           | _ => apply ProdEquiv.value_unused_ret; congruence
           end.

  Ltac remember_single_result :=
    match goal with |- context [(Fancy.spec ?i ?args ?cc) mod ?w] =>
                    let x := fresh "x" in
                    let y := fresh "y" in
                    let Heqx := fresh "Heqx" in
                    remember (Fancy.spec i args cc) as x eqn:Heqx;
                    remember (x mod w) as y
    end.
  Ltac step_both_sides :=
    match goal with |- ProdEquiv.interp256 (Fancy.Instr ?i ?rd1 ?args1 _) _ ?ctx1 = ProdEquiv.interp256 (Fancy.Instr ?i ?rd2 ?args2 _) _ ?ctx2 =>
                    rewrite (ProdEquiv.interp_step i rd1 args1); rewrite (ProdEquiv.interp_step i rd2 args2);
                    cbn - [Fancy.interp Fancy.spec];
                    repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl by congruence;
                    remember_single_result;
                    lazymatch goal with
                    | |- context [Fancy.spec i _ _] =>
                      let Heqa1 := fresh in
                      let Heqa2 := fresh in
                      remember (Tuple.map (n:=i.(Fancy.num_source_regs)) ctx1 args1) eqn:Heqa1;
                      remember (Tuple.map (n:=i.(Fancy.num_source_regs)) ctx2 args2) eqn:Heqa2;
                      cbn in Heqa1; cbn in Heqa2;
                      repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl in Heqa1 by congruence;
                      repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl in Heqa2 by congruence;
                      let a1 := match type of Heqa1 with _ = ?a1 => a1 end in
                      let a2 := match type of Heqa2 with _ = ?a2 => a2 end in
                      (fail 1 "arguments to " i " do not match; LHS has " a1 " and RHS has " a2)
                    | _ => idtac
                    end
    end.
End ProdEquiv.

(* Lemmas to help prove that a fancy and prefancy expression have the
same meaning -- should be replaced eventually with a proof of fancy
passes in general. *)
Module Fancy_PreFancy_Equiv.
  Import Fancy.Registers.

  Lemma interp_cast_mod_eq w u x: u = 2^w - 1 -> PreFancy.interp_cast_mod w r[0 ~> u] x = x mod 2^w.
  Proof using Type.
    cbv [PreFancy.interp_cast_mod upper lower]; intros; subst.
    rewrite !Z.eqb_refl.
    reflexivity.
  Qed.
  Lemma interp_cast_mod_flag w x: PreFancy.interp_cast_mod w r[0 ~> 1] x = x mod 2.
  Proof using Type.
    cbv [PreFancy.interp_cast_mod upper lower].
    break_match; Z.ltb_to_lt; subst; try lia.
    f_equal; lia.
  Qed.

  Lemma interp_equivZ {s} w u (Hu : u = 2^w-1) i rd regs e cc ctx idc args f :
    (Fancy.spec i (Tuple.map ctx regs) cc
     = PreFancy.interp_ident (d:=type.Z) w idc (Straightline.expr.interp_scalar (interp_cast:=PreFancy.interp_cast_mod w) args)) ->
    ( let r := Fancy.spec i (Tuple.map ctx regs) cc in
      Fancy.interp reg_eqb (2 ^ w) Fancy.cc_spec e
                 (Fancy.CC.update (Fancy.writes_conditions i) r Fancy.cc_spec cc)
                 (fun n : register => if reg_eqb n rd then r mod 2 ^ w else ctx n) =
    PreFancy.interp (t:=type.Z) (interp_cast:=PreFancy.interp_cast_mod w) w (f (r mod 2 ^ w))) ->
    Fancy.interp reg_eqb (2^w) Fancy.cc_spec (Fancy.Instr i rd regs e) cc ctx
    = PreFancy.interp (t:=type.Z) (interp_cast:=PreFancy.interp_cast_mod w) w
                      (@Straightline.expr.LetInAppIdentZ _ _ s _ (r[0~>2^w-1])%zrange idc args f).
  Proof using Type.
    cbv zeta; intros spec_eq next_eq.
    cbn [Fancy.interp PreFancy.interp].
    rewrite next_eq.
    rewrite <-spec_eq.
    rewrite interp_cast_mod_eq by lia.
    reflexivity.
  Qed.

  Lemma interp_equivZZ {s} w (Hw : 2 < 2 ^ w) u (Hu : u = 2^w - 1) i rd regs e cc ctx idc args f :
    ((Fancy.spec i (Tuple.map ctx regs) cc) mod 2 ^ w
     = fst (PreFancy.interp_ident (d:=type.Z*type.Z) w idc (Straightline.expr.interp_scalar (interp_cast:=PreFancy.interp_cast_mod w) args))) ->
    ((if Fancy.cc_spec Fancy.CC.C(Fancy.spec i (Tuple.map ctx regs) cc) then 1 else 0)
     = snd (PreFancy.interp_ident (d:=type.Z*type.Z) w idc (Straightline.expr.interp_scalar (interp_cast:=PreFancy.interp_cast_mod w) args)) mod 2) ->
    ( let r := Fancy.spec i (Tuple.map ctx regs) cc in
      Fancy.interp reg_eqb (2 ^ w) Fancy.cc_spec e
                 (Fancy.CC.update (Fancy.writes_conditions i) r Fancy.cc_spec cc)
                 (fun n : register => if reg_eqb n rd then r mod 2 ^ w else ctx n) =
     PreFancy.interp (t:=type.Z) (interp_cast:=PreFancy.interp_cast_mod w) w
                     (f (r mod 2 ^ w, if (Fancy.cc_spec Fancy.CC.C r) then 1 else 0))) ->
    Fancy.interp reg_eqb (2^w) Fancy.cc_spec (Fancy.Instr i rd regs e) cc ctx
    = PreFancy.interp (t:=type.Z) (interp_cast:=PreFancy.interp_cast_mod w) w
                      (@Straightline.expr.LetInAppIdentZZ _ _ s _ (r[0~>u], r[0~>1])%zrange idc args f).
  Proof using Type.
    cbv zeta; intros spec_eq1 spec_eq2 next_eq.
    cbn [Fancy.interp PreFancy.interp].
    cbv [Straightline.expr.interp_cast2]. cbn [fst snd].
    rewrite next_eq.
    rewrite interp_cast_mod_eq by lia.
    rewrite interp_cast_mod_flag by lia.
    rewrite <-spec_eq1, <-spec_eq2.
    rewrite Z.mod_mod by lia.
    reflexivity.
  Qed.
End Fancy_PreFancy_Equiv.

Module BarrettReduction.
  (* TODO : generalize to multi-word and operate on (list Z) instead of T; maybe stop taking ops as context variables *)
  Section Generic.
    Context {T} (rep : T -> Z -> Prop)
            (k : Z) (k_pos : 0 < k)
            (low : T -> Z)
            (low_correct : forall a x, rep a x -> low a = x mod 2 ^ k)
            (shiftr : T -> Z -> T)
            (shiftr_correct : forall a x n,
                rep a x ->
                0 <= n <= k ->
                rep (shiftr a n) (x / 2 ^ n))
            (mul_high : T -> T -> Z -> T)
            (mul_high_correct : forall a b x y x0y1,
                rep a x ->
                rep b y ->
                2 ^ k <= x < 2^(k+1) ->
                0 <= y < 2^(k+1) ->
                x0y1 = x mod 2 ^ k * (y / 2 ^ k) ->
                rep (mul_high a b x0y1) (x * y / 2 ^ k))
            (mul : Z -> Z -> T)
            (mul_correct : forall x y,
                0 <= x < 2^k ->
                0 <= y < 2^k ->
                rep (mul x y) (x * y))
            (sub : T -> T -> T)
            (sub_correct : forall a b x y,
                rep a x ->
                rep b y ->
                0 <= x - y < 2^k * 2^k ->
                rep (sub a b) (x - y))
            (cond_sub1 : T -> Z -> Z)
            (cond_sub1_correct : forall a x y,
                rep a x ->
                0 <= x < 2 * y ->
                0 <= y < 2 ^ k ->
                cond_sub1 a y = if (x <? 2 ^ k) then x else x - y)
            (cond_sub2 : Z -> Z -> Z)
            (cond_sub2_correct : forall x y, cond_sub2 x y = if (x <? y) then x else x - y).
    Context (xt mut : T) (M muSelect: Z).

    Let mu := 2 ^ (2 * k) / M.
    Context x (mu_rep : rep mut mu) (x_rep : rep xt x).
    Context (M_nz : 0 < M)
            (x_range : 0 <= x < M * 2 ^ k)
            (M_range : 2 ^ (k - 1) < M < 2 ^ k)
            (M_good : 2 * (2 ^ (2 * k) mod M) <= 2 ^ (k + 1) - mu)
            (muSelect_correct: muSelect = mu mod 2 ^ k * (x / 2 ^ (k - 1) / 2 ^ k)).

    Definition qt :=
      dlet_nd muSelect := muSelect in (* makes sure muSelect is not inlined in the output *)
      dlet_nd q1 := shiftr xt (k - 1) in
      dlet_nd twoq := mul_high mut q1 muSelect in
      shiftr twoq 1.
    Definition reduce  :=
      dlet_nd qt := qt in
      dlet_nd r2 := mul (low qt) M in
      dlet_nd r := sub xt r2 in
      let q3 := cond_sub1 r M in
      cond_sub2 q3 M.

    Lemma looser_bound : M * 2 ^ k < 2 ^ (2*k).
    Proof using M_nz M_range k_pos. clear -M_range M_nz k_pos; assert (0 < 2^k) by auto with zarith; rewrite <-Z.add_diag, Z.pow_add_r; nia. Qed.

    Lemma pow_2k_eq : 2 ^ (2*k) = 2 ^ (k - 1) * 2 ^ (k + 1).
    Proof using k_pos. clear -k_pos; rewrite <-Z.pow_add_r by lia. f_equal; ring. Qed.

    Lemma mu_bounds : 2 ^ k <= mu < 2^(k+1).
    Proof using M_nz M_range k_pos.
      clear -M_nz M_range k_pos mu.
      pose proof looser_bound.
      subst mu. split.
      { apply Z.div_le_lower_bound; lia. }
      { apply Z.div_lt_upper_bound; try lia.
        rewrite pow_2k_eq; apply Z.mul_lt_mono_pos_r; auto with zarith. }
    Qed.

    Lemma shiftr_x_bounds : 0 <= x / 2 ^ (k - 1) < 2^(k+1).
    Proof using M_nz M_range k_pos mu x_range.
      pose proof looser_bound.
      split; [ solve [Z.zero_bounds] | ].
      apply Z.div_lt_upper_bound; auto with zarith.
      rewrite <-pow_2k_eq. lia.
    Qed.
    Local Hint Resolve shiftr_x_bounds.

    Ltac solve_rep := eauto using shiftr_correct, mul_high_correct, mul_correct, sub_correct with lia.

    Let q := mu * (x / 2 ^ (k - 1)) / 2 ^ (k + 1).

    Lemma q_correct : rep qt q .
    Proof using M_nz M_range k_pos muSelect_correct mu_rep mul_high_correct shiftr_correct x_range x_rep.
      pose proof mu_bounds. cbv [qt]; subst q.
      rewrite Z.pow_add_r, <-Z.div_div by Z.zero_bounds.
      solve_rep.
    Qed.
    Local Hint Resolve q_correct.

    Lemma x_mod_small : x mod 2 ^ (k - 1) <= M.
    Proof using M_range k_pos. clear -M_range k_pos. transitivity (2 ^ (k - 1)); auto with zarith. Qed.
    Local Hint Resolve x_mod_small.

    Lemma q_bounds : 0 <= q < 2 ^ k.
    Proof using M_good M_nz M_range k_pos x_range.
      pose proof looser_bound. pose proof x_mod_small. pose proof mu_bounds.
      split; subst q; [ solve [Z.zero_bounds] | ].
      edestruct q_nice_strong with (n:=M) as [? Hqnice];
        try rewrite Hqnice; auto; try lia; [ ].
      apply Z.le_lt_trans with (m:= x / M).
      { break_match; lia. }
      { apply Z.div_lt_upper_bound; lia. }
    Qed.

    Lemma two_conditional_subtracts :
      forall a x,
      rep a x ->
      0 <= x < 2 * M ->
      cond_sub2 (cond_sub1 a M) M = cond_sub2 (cond_sub2 x M) M.
    Proof using M_nz M_range cond_sub1_correct cond_sub2_correct k_pos q.
      intros.
      erewrite !cond_sub2_correct, !cond_sub1_correct by (eassumption || lia).
      break_match; Z.ltb_to_lt; try lia; discriminate.
    Qed.

    Lemma r_bounds : 0 <= x - q * M < 2 * M.
    Proof using M_good M_nz M_range k_pos x_range.
      pose proof looser_bound. pose proof q_bounds. pose proof x_mod_small.
      subst q mu; split.
      { Z.zero_bounds. apply qn_small; lia. }
      { apply r_small_strong; rewrite ?Z.pow_1_r; auto; lia. }
    Qed.

    Lemma reduce_correct : reduce = x mod M.
    Proof using M_good M_nz M_range cond_sub1_correct cond_sub2_correct k_pos low_correct muSelect_correct mu_rep mul_correct mul_high_correct shiftr_correct sub_correct x_range x_rep.
      pose proof looser_bound. pose proof r_bounds. pose proof q_bounds.
      assert (2 * M < 2^k * 2^k) by nia.
      rewrite barrett_reduction_small with (k:=k) (m:=mu) (offset:=1) (b:=2) by (auto; lia).
      cbv [reduce Let_In].
      erewrite low_correct by eauto. Z.rewrite_mod_small.
      erewrite two_conditional_subtracts by solve_rep.
      rewrite !cond_sub2_correct.
      subst q; reflexivity.
    Qed.
  End Generic.

  Section BarrettReduction.
    Context (k : Z) (k_bound : 2 <= k).
    Context (M muLow : Z).
    Context (M_pos : 0 < M)
            (muLow_eq : muLow + 2^k = 2^(2*k) / M)
            (muLow_bounds : 0 <= muLow < 2^k)
            (M_bound1 : 2 ^ (k - 1) < M < 2^k)
            (M_bound2: 2 * (2 ^ (2 * k) mod M) <= 2 ^ (k + 1) - (muLow + 2^k)).

    Context (n:nat) (Hn_nz: n <> 0%nat) (n_le_k : Z.of_nat n <= k).
    Context (nout : nat) (Hnout : nout = 2%nat).
    Let w := weight k 1.
    Local Lemma k_range : 0 < 1 <= k. Proof using Hn_nz Hnout k_bound. lia. Qed.
    Let props : @weight_properties w := wprops k 1 k_range.

    Hint Rewrite Positional.eval_nil Positional.eval_snoc : push_eval.

    Definition low (t : list Z) : Z := nth_default 0 t 0.
    Definition high (t : list Z) : Z := nth_default 0 t 1.
    Definition represents (t : list Z) (x : Z) :=
      t = [x mod 2^k; x / 2^k] /\ 0 <= x < 2^k * 2^k.

    Lemma represents_eq t x :
      represents t x -> t = [x mod 2^k; x / 2^k].
    Proof using M_bound1 muLow_bounds. cbv [represents]; tauto. Qed.

    Lemma represents_length t x : represents t x -> length t = 2%nat.
    Proof using M_bound1 muLow_bounds. cbv [represents]; intuition. subst t; reflexivity. Qed.

    Lemma represents_low t x :
      represents t x -> low t = x mod 2^k.
    Proof using M_bound1 muLow_bounds. cbv [represents]; intros; rewrite (represents_eq t x) by auto; reflexivity. Qed.

    Lemma represents_high t x :
      represents t x -> high t = x / 2^k.
    Proof using M_bound1 muLow_bounds. cbv [represents]; intros; rewrite (represents_eq t x) by auto; reflexivity. Qed.

    Lemma represents_low_range t x :
      represents t x -> 0 <= x mod 2^k < 2^k.
    Proof using Hn_nz Hnout k_bound. clear -Hn_nz Hnout k_bound. auto with zarith. Qed.

    Lemma represents_high_range t x :
      represents t x -> 0 <= x / 2^k < 2^k.
    Proof using Hn_nz Hnout k_bound.
      clear -Hn_nz Hnout k_bound.
      destruct 1 as [? [? ?] ]; intros.
      auto using Z.div_lt_upper_bound with zarith.
    Qed.
    Local Hint Resolve represents_length represents_low_range represents_high_range.

    Lemma represents_range t x :
      represents t x -> 0 <= x < 2^k*2^k.
    Proof using M_bound1 muLow_bounds. cbv [represents]; tauto. Qed.

    Lemma represents_id x :
      0 <= x < 2^k * 2^k ->
      represents [x mod 2^k; x / 2^k] x.
    Proof using M_bound1 muLow_bounds.
      intros; cbv [represents]; autorewrite with cancel_pair.
      Z.rewrite_mod_small; tauto.
    Qed.

    Local Ltac push_rep :=
      repeat match goal with
             | H : represents ?t ?x |- _ => unique pose proof (represents_low_range _ _ H)
             | H : represents ?t ?x |- _ => unique pose proof (represents_high_range _ _ H)
             | H : represents ?t ?x |- _ => rewrite (represents_low t x) in * by assumption
             | H : represents ?t ?x |- _ => rewrite (represents_high t x) in * by assumption
             end.

    Definition shiftr (t : list Z) (n : Z) : list Z :=
      [Z.rshi (2^k) (high t) (low t) n; Z.rshi (2^k) 0 (high t) n].

    Lemma shiftr_represents a i x :
      represents a x ->
      0 <= i <= k ->
      represents (shiftr a i) (x / 2 ^ i).
    Proof using Hn_nz Hnout M_bound1 k_bound muLow_bounds.
      clear -Hn_nz Hnout M_bound1 k_bound muLow_bounds w.
      cbv [shiftr]; intros; push_rep.
      match goal with H : _ |- _ => pose proof (represents_range _ _ H) end.
      assert (0 < 2 ^ i) by auto with zarith.
      assert (x < 2 ^ i * 2 ^ k * 2 ^ k) by nia.
      assert (0 <= x / 2 ^ k / 2 ^ i < 2 ^ k) by
          (split; Z.zero_bounds; auto using Z.div_lt_upper_bound with zarith).
      repeat match goal with
             | _ => rewrite Z.rshi_correct by auto with zarith
             | _ => rewrite <-Z.div_mod''' by auto with zarith
             | _ => progress autorewrite with zsimplify_fast
             | _ => progress Z.rewrite_mod_small
             | |- context [represents [(?a / ?c) mod ?b; ?a / ?b / ?c] ] =>
               rewrite (Z.div_div_comm a b c) by auto with zarith
             | _ => solve [auto using represents_id, Z.div_lt_upper_bound with zarith lia]
             end.
    Qed.

    Context (Hw : forall i, w i = (2 ^ k) ^ Z.of_nat i).
    Ltac change_weight := rewrite !Hw, ?Z.pow_0_r, ?Z.pow_1_r, ?Z.pow_2_r.

    Definition wideadd t1 t2 := fst (Rows.add w 2 t1 t2).
    (* TODO: use this definition once issue #352 is resolved *)
    (* Definition widesub t1 t2 := fst (Rows.sub w 2 t1 t2). *)
    Definition widesub (t1 t2 : list Z) :=
      let t1_0 := hd 0 t1 in
      let t1_1 := hd 0 (tl t1) in
      let t2_0 := hd 0 t2 in
      let t2_1 := hd 0 (tl t2) in
      dlet_nd x0 := Z.sub_get_borrow_full (2^k) t1_0 t2_0 in
      dlet_nd x1 := Z.sub_with_get_borrow_full (2^k) (snd x0) t1_1 t2_1 in
      [fst x0; fst x1].
    Definition widemul := BaseConversion.widemul_inlined k n nout.

    Lemma partition_represents x :
      0 <= x < 2^k*2^k ->
      represents (Rows.partition w 2 x) x.
    Proof using Hn_nz Hnout Hw M_bound1 muLow_bounds.
      intros; cbn. change_weight.
      Z.rewrite_mod_small.
      autorewrite with zsimplify_fast.
      auto using represents_id.
    Qed.

    Lemma eval_represents t x :
      represents t x -> eval w 2 t = x.
    Proof using Hn_nz Hnout Hw M_bound1 k_bound muLow_bounds.
      clear -Hn_nz Hnout Hw M_bound1 k_bound muLow_bounds.
      intros; rewrite (represents_eq t x) by assumption.
      cbn. change_weight; push_rep.
      autorewrite with zsimplify. reflexivity.
    Qed.

    Ltac wide_op partitions_pf :=
      repeat match goal with
             | _ => rewrite partitions_pf by eauto
             | _ => rewrite partitions_pf by auto with zarith
             | _ => erewrite eval_represents by eauto
             | _ => solve [auto using partition_represents, represents_id]
             end.

    Lemma wideadd_represents t1 t2 x y :
      represents t1 x ->
      represents t2 y ->
      0 <= x + y < 2^k*2^k ->
      represents (wideadd t1 t2) (x + y).
    Proof using Hw M_bound1 muLow_bounds props. intros; cbv [wideadd]. wide_op Rows.add_partitions. Qed.

    Lemma widesub_represents t1 t2 x y :
      represents t1 x ->
      represents t2 y ->
      0 <= x - y < 2^k*2^k ->
      represents (widesub t1 t2) (x - y).
    Proof using Hn_nz Hnout M_bound1 k_bound muLow_bounds.
      clear -Hn_nz Hnout M_bound1 k_bound muLow_bounds w.
      intros; cbv [widesub Let_In].
      rewrite (represents_eq t1 x) by assumption.
      rewrite (represents_eq t2 y) by assumption.
      cbn [hd tl].
      autorewrite with to_div_mod.
      pull_Zmod.
      match goal with |- represents [?m; ?d] ?x =>
                      replace d with (x / 2 ^ k); [solve [auto using represents_id] |] end.
      rewrite <-(Z.mod_small ((x - y) / 2^k) (2^k)) by (split; try apply Z.div_lt_upper_bound; Z.zero_bounds).
      f_equal.
      transitivity ((x mod 2^k - y mod 2^k + 2^k * (x / 2 ^ k) - 2^k * (y / 2^k)) / 2^k). {
        rewrite (Z.div_mod x (2^k)) at 1 by auto using Z.pow_nonzero with lia.
        rewrite (Z.div_mod y (2^k)) at 1 by auto using Z.pow_nonzero with lia.
        f_equal. ring. }
      autorewrite with zsimplify.
      ring.
    Qed.
    (* Works with Rows.sub-based widesub definition
    Proof. intros; cbv [widesub]. wide_op Rows.sub_partitions. Qed.
    *)

    Lemma widemul_represents x y :
      0 <= x < 2^k ->
      0 <= y < 2^k ->
      represents (widemul x y) (x * y).
    Proof using Hn_nz Hnout M_bound1 k_bound muLow_bounds n_le_k.
      intros; cbv [widemul].
      assert (0 <= x * y < 2^k*2^k) by auto with zarith.
      wide_op BaseConversion.widemul_correct.
    Qed.

    Definition mul_high (a b : list Z) a0b1 : list Z :=
      dlet_nd a0b0 := widemul (low a) (low b) in
      dlet_nd ab := wideadd [high a0b0; high b] [low b; 0] in
      wideadd ab [a0b1; 0].

    Lemma mul_high_idea d a b a0 a1 b0 b1 :
      d <> 0 ->
      a = d * a1 + a0 ->
      b = d * b1 + b0 ->
      (a * b) / d = a0 * b0 / d + d * a1 * b1 + a1 * b0 + a0 * b1.
    Proof using Hn_nz Hnout k_bound.
      intros. subst a b. autorewrite with push_Zmul.
      ring_simplify_subterms. rewrite Z.pow_2_r.
      rewrite Z.div_add_exact by (push_Zmod; autorewrite with zsimplify; lia).
      repeat match goal with
             | |- context [d * ?a * ?b * ?c] =>
               replace (d * a * b * c) with (a * b * c * d) by ring
             | |- context [d * ?a * ?b] =>
               replace (d * a * b) with (a * b * d) by ring
             end.
      rewrite !Z.div_add by lia.
      autorewrite with zsimplify.
      rewrite (Z.mul_comm a0 b0).
      ring_simplify. ring.
    Qed.

    Lemma represents_trans t x y:
      represents t y -> y = x ->
      represents t x.
    Proof using Type. congruence. Qed.

    Lemma represents_add x y :
      0 <= x < 2 ^ k ->
      0 <= y < 2 ^ k ->
      represents [x;y] (x + 2^k*y).
    Proof using Hn_nz Hnout M_bound1 k_bound n_le_k.
      clear -Hn_nz Hnout M_bound1 k_bound n_le_k.
      intros; cbv [represents]; autorewrite with zsimplify.
      repeat split; (reflexivity || nia).
    Qed.

    Lemma represents_small x :
      0 <= x < 2^k ->
      represents [x; 0] x.
    Proof using Hn_nz Hnout M_bound1 k_bound n_le_k.
      clear -Hn_nz Hnout M_bound1 k_bound n_le_k w props.
      intros.
      eapply represents_trans.
      { eauto using represents_add with zarith. }
      { ring. }
    Qed.

    Lemma mul_high_represents a b x y a0b1 :
      represents a x ->
      represents b y ->
      2^k <= x < 2^(k+1) ->
      0 <= y < 2^(k+1) ->
      a0b1 = x mod 2^k * (y / 2^k) ->
      represents (mul_high a b a0b1) ((x * y) / 2^k).
    Proof using Hw M_bound1 muLow_bounds n_le_k props.
      clear -Hw M_bound1 muLow_bounds n_le_k props.
      cbv [mul_high Let_In]; rewrite Z.pow_add_r, Z.pow_1_r by lia; intros.
      assert (4 <= 2 ^ k) by (transitivity (Z.pow 2 2); auto with zarith).
      assert (0 <= x * y / 2^k < 2^k*2^k) by (Z.div_mod_to_quot_rem_in_goal; nia).

      rewrite mul_high_idea with (a:=x) (b:=y) (a0 := low a) (a1 := high a) (b0 := low b) (b1 := high b) in *
        by (push_rep; Z.div_mod_to_quot_rem_in_goal; lia).

      push_rep. subst a0b1.
      assert (y / 2 ^ k < 2) by (apply Z.div_lt_upper_bound; lia).
      replace (x / 2 ^ k) with 1 in * by (rewrite Z.div_between_1; lia).
      autorewrite with zsimplify_fast in *.

      eapply represents_trans.
      { repeat (apply wideadd_represents;
                [ | apply represents_small; Z.div_mod_to_quot_rem_in_goal; nia| ]).
        erewrite represents_high; [ | apply widemul_represents; solve [ auto with zarith ] ].
        { apply represents_add; try reflexivity; solve [auto with zarith]. }
        { match goal with H : 0 <= ?x + ?y < ?z |- 0 <= ?x < ?z =>
                          split; [ solve [Z.zero_bounds] | ];
                            eapply Z.le_lt_trans with (m:= x + y); nia
          end. }
        { lia. } }
      { ring. }
    Qed.

    Definition cond_sub1 (a : list Z) y : Z :=
      dlet_nd maybe_y := Z.zselect (Z.cc_l (high a)) 0 y in
      dlet_nd diff := Z.sub_get_borrow_full (2^k) (low a) maybe_y in
      fst diff.

    Lemma cc_l_only_bit : forall x s, 0 <= x < 2 * s -> Z.cc_l (x / s) = 0 <-> x < s.
    Proof using Hn_nz Hnout k_bound.
      clear -Hn_nz Hnout k_bound.
      cbv [Z.cc_l]; intros.
      rewrite Z.div_between_0_if by lia.
      break_match; Z.ltb_to_lt; Z.rewrite_mod_small; lia.
    Qed.

    Lemma cond_sub1_correct a x y :
      represents a x ->
      0 <= x < 2 * y ->
      0 <= y < 2 ^ k ->
      cond_sub1 a y = if (x <? 2 ^ k) then x else x - y.
    Proof using Hn_nz Hnout M_bound1 M_pos k_bound muLow_bounds.
      clear -Hn_nz Hnout M_bound1 M_pos k_bound muLow_bounds w props.
      intros; cbv [cond_sub1 Let_In]. rewrite Z.zselect_correct. push_rep.
      break_match; Z.ltb_to_lt; rewrite cc_l_only_bit in *; try lia;
        autorewrite with zsimplify_fast to_div_mod pull_Zmod; auto with zarith.
    Qed.

    Definition cond_sub2 x y := Z.add_modulo x 0 y.
    Lemma cond_sub2_correct x y :
      cond_sub2 x y = if (x <? y) then x else x - y.
    Proof using Hn_nz Hnout k.
      clear -Hn_nz Hnout k.
      cbv [cond_sub2]. rewrite Z.add_modulo_correct.
      autorewrite with zsimplify_fast. break_match; Z.ltb_to_lt; lia.
    Qed.

    Section Defn.
      Context (xLow xHigh : Z) (xLow_bounds : 0 <= xLow < 2^k) (xHigh_bounds : 0 <= xHigh < M).
      Let xt := [xLow; xHigh].
      Let x := xLow + 2^k * xHigh.

      Lemma x_rep : represents xt x.
      Proof using Hn_nz Hnout M_bound1 M_pos k_bound n_le_k xHigh_bounds xLow_bounds. clear -Hn_nz Hnout M_bound1 M_pos k_bound n_le_k xHigh_bounds xLow_bounds. cbv [represents]; subst xt x; autorewrite with cancel_pair zsimplify; repeat split; nia. Qed.

      Lemma x_bounds : 0 <= x < M * 2 ^ k.
      Proof using Hn_nz Hnout M_bound1 k_bound muLow_bounds n_le_k xHigh_bounds xLow_bounds. clear -Hn_nz Hnout M_bound1 k_bound muLow_bounds n_le_k xHigh_bounds xLow_bounds. subst x; nia. Qed.

      Definition muSelect := Z.zselect (Z.cc_m (2 ^ k) xHigh) 0 muLow.

      Local Hint Resolve Z.div_nonneg Z.div_lt_upper_bound.
      Local Hint Resolve shiftr_represents mul_high_represents widemul_represents widesub_represents
            cond_sub1_correct cond_sub2_correct represents_low represents_add.

      Lemma muSelect_correct :
        muSelect = (2 ^ (2 * k) / M) mod 2 ^ k * ((x / 2 ^ (k - 1)) / 2 ^ k).
      Proof using Hn_nz Hnout M_bound1 M_pos k_bound muLow_bounds muLow_eq n_le_k xHigh_bounds xLow_bounds.
        (* assertions to help arith tactics *)
        pose proof x_bounds.
        assert (2^k * M < 2 ^ (2*k)) by (rewrite <-Z.add_diag, Z.pow_add_r; nia).
        assert (0 <= x / (2 ^ k * (2 ^ k / 2)) < 2) by (Z.div_mod_to_quot_rem_in_goal; auto with nia).
        assert (0 < 2 ^ k / 2) by Z.zero_bounds.
        assert (2 ^ (k - 1) <> 0) by auto with zarith.
        assert (2 < 2 ^ k) by (eapply Z.le_lt_trans with (m:=2 ^ 1); auto with zarith).

        cbv [muSelect]. rewrite <-muLow_eq.
        rewrite Z.zselect_correct, Z.cc_m_eq by auto with zarith.
        replace xHigh with (x / 2^k) by (subst x; autorewrite with zsimplify; lia).
        autorewrite with pull_Zdiv push_Zpow.
        rewrite (Z.mul_comm (2 ^ k / 2)).
        break_match; [ ring | ].
        match goal with H : 0 <= ?x < 2, H' : ?x <> 0 |- _ => replace x with 1 by lia end.
        autorewrite with zsimplify; reflexivity.
      Qed.

      Lemma mu_rep : represents [muLow; 1] (2 ^ (2 * k) / M).
      Proof using Hn_nz Hnout M_bound1 k_bound muLow_bounds muLow_eq n_le_k x. clear -Hn_nz Hnout M_bound1 k_bound muLow_bounds muLow_eq n_le_k x w props. rewrite <-muLow_eq. eapply represents_trans; auto with zarith. Qed.

      Derive barrett_reduce
             SuchThat (barrett_reduce = x mod M)
             As barrett_reduce_correct.
      Proof.
        erewrite <- @reduce_correct with (rep:=represents) (muSelect:=muSelect) (k:=k) (mut:=[muLow;1]) (xt:=xt)
          by (auto using x_bounds, muSelect_correct, x_rep, mu_rep; lia).
        subst barrett_reduce. reflexivity.
      Qed.
    End Defn.
  End BarrettReduction.

  (* all the list operations from for_reification.ident *)
  Strategy 100 [length seq repeat combine map flat_map partition app rev fold_right update_nth nth_default ].

  Derive barrett_red_gen
         SuchThat (forall (k M muLow : Z)
                          (n nout: nat)
                          (xLow xHigh : Z),
                      Interp (t:=type.reify_type_of barrett_reduce)
                             barrett_red_gen k M muLow n nout xLow xHigh
                      = barrett_reduce k M muLow n nout xLow xHigh)
         As barrett_red_gen_correct.
  Proof. Time cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Time Qed.
  (* TODO : reification here is still quite slow (~90s on a beefy machine). Possibly just due to size of term, but warrants further investigation. *)
  Module Export ReifyHints.
    Global Hint Extern 1 (_ = barrett_reduce _ _ _ _ _ _ _) => simple apply barrett_red_gen_correct : reify_gen_cache.
  End ReifyHints.

  Section rbarrett_red.
    Context (M : Z)
            (machine_wordsize : Z).

    Let bound := Some r[0 ~> (2^machine_wordsize - 1)%Z]%zrange.
    Let mu := (2 ^ (2 * machine_wordsize)) / M.
    Let muLow := mu mod (2 ^ machine_wordsize).

    Redirect "log" Check barrett_reduce_correct.
    Redirect "log" Print Pipeline.Values_not_provably_distinct.

    Definition relax_zrange_of_machine_wordsize'
      := relax_zrange_gen [1; machine_wordsize / 2; machine_wordsize; 2 * machine_wordsize]%Z.
    (* TODO: This is a special-case hack to let the prefancy pass have enough bounds information. *)
    Definition relax_zrange_of_machine_wordsize r : option zrange :=
      if (lower r =? 0) && (upper r =? 2)
      then Some r
      else relax_zrange_of_machine_wordsize' r.

    Lemma relax_zrange_good (r r' z : zrange) :
      (z <=? r)%zrange = true ->
      relax_zrange_of_machine_wordsize r = Some r' -> (z <=? r')%zrange = true.
    Proof using Type.
      cbv [relax_zrange_of_machine_wordsize]; break_match; [congruence|].
      eauto using relax_zrange_gen_good.
    Qed.

    Local Arguments relax_zrange_of_machine_wordsize / .

    Let relax_zrange := relax_zrange_of_machine_wordsize.

    Definition check_args {T} (res : Pipeline.ErrorT T)
      : Pipeline.ErrorT T
      := if (mu / (2 ^ machine_wordsize) =? 0)
         then Pipeline.Error (Pipeline.Values_not_provably_distinct "mu / 2 ^ k ≠ 0" (mu / 2 ^ machine_wordsize) 0)
         else if (machine_wordsize <? 2)
              then Pipeline.Error (Pipeline.Value_not_le "~ (2 <=k)" 2 machine_wordsize)
              else if (negb (Z.log2 M + 1 =? machine_wordsize))
                   then Pipeline.Error
                          (Pipeline.Values_not_provably_equal "log2(M)+1 != k" (Z.log2 M + 1) machine_wordsize)
                   else if (2 ^ (machine_wordsize + 1) - mu <? 2 * (2 ^ (2 * machine_wordsize) mod M))
                        then Pipeline.Error
                               (Pipeline.Value_not_le "~ (2 * (2 ^ (2*k) mod M) <= 2^(k + 1) - mu)"
                                                      (2 * (2 ^ (2*machine_wordsize) mod M))
                                                      (2^(machine_wordsize + 1) - mu))
                        else res.

    Notation BoundsPipeline_correct in_bounds out_bounds op
      := (fun rv (rop : Expr (type.reify_type_of op)) Hrop
          => @Pipeline.BoundsPipeline_correct_trans
               false (* subst01 *)
               relax_zrange
               relax_zrange_good
               _
               rop
               in_bounds
               out_bounds
               op
               Hrop rv)
           (only parsing).

    Definition rbarrett_red_correct
      := BoundsPipeline_correct
           (bound, bound)
           bound
           (barrett_reduce machine_wordsize M muLow 2 2).

    Notation type_of_strip_3arrow := ((fun (d : Prop) (_ : forall A B C, d) => d) _).
    Definition rbarrett_red_correctT rv : Prop
      := type_of_strip_3arrow (@rbarrett_red_correct rv).
  End rbarrett_red.
End BarrettReduction.

Ltac solve_rbarrett_red := solve_rop BarrettReduction.rbarrett_red_correct.
Ltac solve_rbarrett_red_nocache := solve_rop_nocache BarrettReduction.rbarrett_red_correct.

Module Barrett256.

  Definition M := Eval lazy in (2^256-2^224+2^192+2^96-1).
  Definition machine_wordsize := 256.

  Import BarrettReduction.ReifyHints.

  Derive barrett_red256
         SuchThat (BarrettReduction.rbarrett_red_correctT M machine_wordsize barrett_red256)
         As barrett_red256_correct.
  Proof. Time solve_rbarrett_red machine_wordsize. Time Qed.

  Definition muLow := Eval lazy in (2 ^ (2 * machine_wordsize) / M) mod (2^machine_wordsize).
  Definition barrett_red256_prefancy' := PreFancy.of_Expr machine_wordsize [M; muLow] barrett_red256.

  Derive barrett_red256_prefancy
         SuchThat (barrett_red256_prefancy = barrett_red256_prefancy' type.interp)
         As barrett_red256_prefancy_eq.
  Proof. lazy - [type.interp]; reflexivity. Qed.

  Lemma barrett_reduce_correct_specialized :
    forall (xLow xHigh : Z),
      0 <= xLow < 2 ^ machine_wordsize ->
      0 <= xHigh < M ->
      BarrettReduction.barrett_reduce machine_wordsize M muLow 2 2 xLow xHigh = (xLow + 2 ^ machine_wordsize * xHigh) mod M.
  Proof using Type.
    intros.
    apply BarrettReduction.barrett_reduce_correct; cbv [machine_wordsize M muLow] in *;
      try lia;
      try match goal with
          | |- context [weight] => intros; cbv [weight]; autorewrite with zsimplify; auto using Z.pow_mul_r with lia
          end; lazy; try split; congruence.
  Qed.

  (* Note: If this is not factored out, then for some reason Qed takes forever in barrett_red256_correct_full. *)
  Lemma barrett_red256_correct_proj2 :
    forall xy : type.interp (type.prod type.Z type.Z),
      ZRange.type.option.is_bounded_by
        (t:=type.prod type.Z type.Z)
        (Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange, Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange)
        xy = true ->
       expr.Interp (@ident.interp) barrett_red256 xy = app_curried (t:=type.arrow (type.prod type.Z type.Z) type.Z) (fun xy => BarrettReduction.barrett_reduce machine_wordsize M muLow 2 2 (fst xy) (snd xy)) xy.
  Proof using Type. intros; destruct (barrett_red256_correct xy); assumption. Qed.
  Lemma barrett_red256_correct_proj2' :
    forall x y : Z,
      ZRange.type.option.is_bounded_by
        (t:=type.prod type.Z type.Z)
        (Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange, Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange)
        (x, y) = true ->
       expr.Interp (@ident.interp) barrett_red256 (x, y) = BarrettReduction.barrett_reduce machine_wordsize M muLow 2 2 x y.
  Proof using Type. intros; rewrite barrett_red256_correct_proj2 by assumption; unfold app_curried; exact eq_refl. Qed.

  Lemma barrett_red256_correct_full  :
    forall (xLow xHigh : Z),
      0 <= xLow < 2 ^ machine_wordsize ->
      0 <= xHigh < M ->
      expr.interp (@ident.interp) (barrett_red256 type.interp) (xLow, xHigh) = (xLow + 2 ^ machine_wordsize * xHigh) mod M.
  Proof using Type.
    intros.
    rewrite <-barrett_reduce_correct_specialized by assumption.
    rewrite <-barrett_red256_correct_proj2'.
    { cbv [expr.Interp type.uncurried_domain type.uncurry type.final_codomain].
      reflexivity. }
    { cbn. rewrite !andb_true_iff. cbv [machine_wordsize M] in *.
      cbn in *. repeat split; apply Z.leb_le; lia. }
  Qed.

  Import PreFancy.Tactics. (* for ok_expr_step *)
  Lemma barrett_red256_prefancy_correct :
    forall xLow xHigh dummy_arrow,
      0 <= xLow < 2 ^ machine_wordsize ->
      0 <= xHigh < M ->
      @PreFancy.interp machine_wordsize (PreFancy.interp_cast_mod machine_wordsize) type.Z (barrett_red256_prefancy (xLow, xHigh) dummy_arrow) = (xLow + 2 ^ machine_wordsize * xHigh) mod M.
  Proof using Type.
    intros. rewrite barrett_red256_prefancy_eq; cbv [barrett_red256_prefancy'].
    erewrite PreFancy.of_Expr_correct.
    { apply barrett_red256_correct_full; try assumption; reflexivity. }
    { reflexivity. }
    { lazy; reflexivity. }
    { lazy; reflexivity. }
    { repeat constructor. }
    { cbv [In M muLow]; intros; intuition; subst; cbv; congruence. }
    { let r := (eval compute in (2 ^ machine_wordsize)) in
      replace (2^machine_wordsize) with r in * by reflexivity.
      cbv [M muLow machine_wordsize] in *.
      assert (lower r[0~>1] = 0) by reflexivity.
      repeat (ok_expr_step; [ ]).
      ok_expr_step.
      lazy; congruence.
      constructor.
      constructor. }
    { lazy. lia. }
  Qed.

  Definition barrett_red256_fancy' (xLow xHigh RegMuLow RegMod RegZero error : positive) :=
    Fancy.of_Expr 3%positive
                  (fun z => if z =? muLow then Some RegMuLow else if z =? M then Some RegMod else if z =? 0 then Some RegZero else None)
                  [M; muLow]
                  barrett_red256
                  (xLow, xHigh)%positive
                  (fun _ _ => tt)
                  error.
  Derive barrett_red256_fancy
         SuchThat (forall xLow xHigh RegMuLow RegMod RegZero,
                      barrett_red256_fancy xLow xHigh RegMuLow RegMod RegZero = barrett_red256_fancy' xLow xHigh RegMuLow RegMod RegZero)
         As barrett_red256_fancy_eq.
  Proof.
    intros.
    lazy - [Fancy.ADD Fancy.ADDC Fancy.SUB Fancy.SUBC
                      Fancy.MUL128LL Fancy.MUL128LU Fancy.MUL128UL Fancy.MUL128UU
                      Fancy.RSHI Fancy.SELC Fancy.SELM Fancy.SELL Fancy.ADDM].
    reflexivity.
  Qed.

  Import Fancy.Registers.

  Definition barrett_red256_alloc' xLow xHigh RegMuLow :=
    fun errorP errorR =>
    Fancy.allocate register
                   positive Pos.eqb
                   errorR
                   (barrett_red256_fancy 1000%positive 1001%positive 1002%positive 1003%positive 1004%positive errorP)
                   [r2;r3;r4;r5;r6;r7;r8;r9;r10;r5;r11;r6;r12;r13;r14;r15;r16;r17;r18;r19;r20;r21;r22;r23;r24;r25;r26;r27;r28;r29]
                   (fun n => if n =? 1000 then xLow
                             else if n =? 1001 then xHigh
                                  else if n =? 1002 then RegMuLow
                                       else if n =? 1003 then RegMod
                                            else if n =? 1004 then RegZero
                                                 else errorR).
  Derive barrett_red256_alloc
         SuchThat (barrett_red256_alloc = barrett_red256_alloc')
         As barrett_red256_alloc_eq.
  Proof.
    intros.
    cbv [barrett_red256_alloc' barrett_red256_fancy].
    cbn. subst barrett_red256_alloc.
    reflexivity.
  Qed.

  Set Printing Depth 1000.
  Import ProdEquiv.

  Local Ltac solve_bounds :=
    match goal with
    | H : ?a = ?b mod ?c |- 0 <= ?a < ?c => rewrite H; apply Z.mod_pos_bound; lia
    | _ => assumption
    end.

  Lemma barrett_red256_alloc_equivalent errorP errorR cc_start_state start_context :
    forall x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5 extra_reg,
      NoDup [x; xHigh; RegMuLow; scratchp1; scratchp2; scratchp3; scratchp4; scratchp5; extra_reg; RegMod; RegZero] ->
      0 <= start_context x < 2^machine_wordsize ->
      0 <= start_context xHigh < 2^machine_wordsize ->
      0 <= start_context RegMuLow < 2^machine_wordsize ->
      ProdEquiv.interp256 (barrett_red256_alloc r0 r1 r30 errorP errorR) cc_start_state
                          (fun r => if reg_eqb r r0
                                    then start_context x
                                    else if reg_eqb r r1
                                         then start_context xHigh
                                         else if reg_eqb r r30
                                              then start_context RegMuLow
                                              else start_context r)
    = ProdEquiv.interp256 (Prod.MulMod x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5) cc_start_state start_context.
  Proof.
    intros.
    let r := eval compute in (2^machine_wordsize) in
        replace (2^machine_wordsize) with r in * by reflexivity.
    cbv [Prod.MulMod barrett_red256_alloc].

    (* Extract proofs that no registers are equal to each other *)
    repeat match goal with
           | H : NoDup _ |- _ => inversion H; subst; clear H
           | H : ~ In _ _ |- _ => cbv [In] in H
           | H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H; destruct H
           | H : ~ False |- _ => clear H
           end.

    step_both_sides.

    (* TODO: To prove equivalence between these two, we need to either relocate the RSHI instructions so they're in the same places or use instruction commutativity to push them down. *)

  Admitted.

  Import Fancy_PreFancy_Equiv.

  Definition interp_equivZZ_256 {s} :=
    @interp_equivZZ s 256 ltac:(cbv; congruence) 115792089237316195423570985008687907853269984665640564039457584007913129639935 ltac:(reflexivity).
  Definition interp_equivZ_256 {s} :=
    @interp_equivZ s 256 115792089237316195423570985008687907853269984665640564039457584007913129639935 ltac:(reflexivity).

  Local Ltac simplify_op_equiv start_ctx :=
    cbn - [Fancy.spec PreFancy.interp_ident Fancy.cc_spec Z.shiftl];
    repeat match goal with H : start_ctx _ = _ |- _ => rewrite H end;
    cbv - [
      Z.rshi Z.cc_m Fancy.CC.cc_m
        Z.add_with_get_carry_full Z.add_get_carry_full
        Z.sub_get_borrow_full Z.sub_with_get_borrow_full
        Z.le Z.lt Z.ltb Z.leb Z.geb Z.eqb Z.land Z.shiftr Z.shiftl
        Z.add Z.mul Z.div Z.sub Z.modulo Z.testbit Z.pow Z.ones
        fst snd]; cbn [fst snd];
    try (replace (2 ^ (256 / 2) - 1) with (Z.ones 128) by reflexivity; rewrite !Z.land_ones by lia);
    autorewrite with to_div_mod; rewrite ?Z.mod_mod, <-?Z.testbit_spec' by lia;
    let r := (eval compute in (2 ^ 256)) in
    replace (2^256) with r in * by reflexivity;
    repeat match goal with
           | H : 0 <= ?x < ?m |- context [?x mod ?m] => rewrite (Z.mod_small x m) by apply H
           | |- context [?x <? 0] => rewrite (proj2 (Z.ltb_ge x 0)) by (break_match; Z.zero_bounds)
           | _ => rewrite Z.mod_small with (b:=2) by (break_match; lia)
           | |- context [ (if Z.testbit ?a ?n then 1 else 0) + ?b + ?c] =>
             replace ((if Z.testbit a n then 1 else 0) + b + c) with (b + c + (if Z.testbit a n then 1 else 0)) by ring
           end.

  Local Ltac solve_nonneg ctx :=
    match goal with x := (Fancy.spec _ _ _) |- _ => subst x end;
    simplify_op_equiv ctx; Z.zero_bounds.

  Local Ltac generalize_result :=
    let v := fresh "v" in intro v; generalize v; clear v; intro v.

  Local Ltac generalize_result_nonneg ctx :=
    let v := fresh "v" in
    let v_nonneg := fresh "v_nonneg" in
    intro v; assert (0 <= v) as v_nonneg; [solve_nonneg ctx |generalize v v_nonneg; clear v v_nonneg; intros v v_nonneg].

  Local Ltac step ctx :=
    match goal with
    | |- Fancy.interp _ _ _ (Fancy.Instr (Fancy.ADD _) _ _ (Fancy.Instr (Fancy.ADDC _) _ _ _)) _ _ = _ =>
      apply interp_equivZZ_256; [ simplify_op_equiv ctx | simplify_op_equiv ctx | generalize_result_nonneg ctx]
    | _ => apply interp_equivZ_256; [simplify_op_equiv ctx | generalize_result]
    | _ => apply interp_equivZZ_256; [ simplify_op_equiv ctx | simplify_op_equiv ctx | generalize_result]
    end.

  Lemma prod_barrett_red256_correct :
    forall (cc_start_state : Fancy.CC.state) (* starting carry flags *)
           (start_context : register -> Z)   (* starting register values *)
           (x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5 extra_reg : register), (* registers to use in computation *)
      NoDup [x; xHigh; RegMuLow; scratchp1; scratchp2; scratchp3; scratchp4; scratchp5; extra_reg; RegMod; RegZero] -> (* registers are unique *)
             0 <= start_context x < 2^machine_wordsize ->
             0 <= start_context xHigh < M ->
             start_context RegMuLow = muLow ->
             start_context RegMod = M ->
             start_context RegZero = 0 ->
             cc_start_state.(Fancy.CC.cc_m) = (Z.cc_m (2^256) (start_context xHigh) =? 1) ->
             let X := start_context x + 2^machine_wordsize * start_context xHigh in
             ProdEquiv.interp256 (Prod.MulMod x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5) cc_start_state start_context = X mod M.
  Proof using Type.
    intros. subst X.
    assert (0 <= start_context xHigh < 2^machine_wordsize) by (cbv [M] in *; cbn; lia).
    let r := (eval compute in (2 ^ machine_wordsize)) in
    replace (2^machine_wordsize) with r in * by reflexivity.
    cbv [M muLow] in *.

    rewrite <-barrett_red256_prefancy_correct with (dummy_arrow := fun s d _ => DefaultValue.type.default) by auto.
    rewrite <-barrett_red256_alloc_equivalent with (errorR := RegZero) (errorP := 1%positive) (extra_reg:=extra_reg)
      by (cbn in *; auto with lia).
    cbv [ProdEquiv.interp256].
    let r := (eval compute in (2 ^ 256)) in
    replace (2^256) with r in * by reflexivity.
    cbv [barrett_red256_alloc barrett_red256_prefancy].

    step start_context.
    {
      match goal with H : Fancy.CC.cc_m _ = _ |- _ => rewrite H end.
      match goal with |- context [Z.cc_m ?s ?x] =>
                      pose proof (Z.cc_m_small s x ltac:(reflexivity) ltac:(lia));
                        let H := fresh in
                        assert (Z.cc_m s x = 1 \/ Z.cc_m s x = 0) as H by lia;
                          destruct H as [H | H]; rewrite H in *
      end; break_innermost_match; Z.ltb_to_lt; try congruence. }
    apply interp_equivZ_256; [ simplify_op_equiv start_context | ]. (* apply manually instead of using [step] to allow a custom bounds proof *)
    { rewrite Z.rshi_correct by lia.
      autorewrite with zsimplify_fast.
      rewrite Z.shiftr_div_pow2 by lia.
      reflexivity. }

    (* Special case to remember the bound for the output of RSHI *)
    let v := fresh "v" in
    let v_bound := fresh "v_bound" in
    intro v; assert (0 <= v <= 1) as v_bound; [ |generalize v v_bound; clear v v_bound; intros v v_bound].
    { solve_nonneg start_context. autorewrite with zsimplify_fast.
      rewrite Z.shiftr_div_pow2 by lia.
      rewrite Z.mod_pull_div by lia.
      rewrite Z.mod_small by (cbn; lia).
      split; [Z.zero_bounds|].
      apply Z.lt_succ_r.
      apply Z.div_lt_upper_bound; cbn; lia. }

    step start_context.
    { rewrite Z.rshi_correct by lia.
      rewrite Z.shiftr_div_pow2 by lia.
      repeat (f_equal; try ring). }
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context;
      [ rewrite Z.mod_small with (b:=2) by (rewrite Z.mod_small by lia; lia); (* Here we make use of the bound of RSHI *)
        reflexivity
      | rewrite Z.mod_small with (b:=2) by (rewrite Z.mod_small by lia; lia); (* Here we make use of the bound of RSHI *)
        reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context.
    { rewrite Z.rshi_correct by lia.
      rewrite Z.shiftr_div_pow2 by lia.
      repeat (f_equal; try ring). }

    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].

    step start_context.
    { reflexivity. }
    { autorewrite with zsimplify_fast.
      match goal with |- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)) end.
      rewrite <-Z.testbit_neg_eq_if with (n:=256) by (cbn; lia).
      reflexivity. }
    step start_context.
    { reflexivity. }
    { autorewrite with zsimplify_fast.
      rewrite Z.mod_small with (a:=(if (if _ <? 0 then true else _) then _ else _)) (b:=2) by (break_innermost_match; lia).
      match goal with |- context [?a - ?b - ?c] => replace (a - b - c) with (a - (b + c)) by ring end.
      match goal with |- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)) end.
      rewrite <-Z.testbit_neg_eq_if with (n:=256) by (break_innermost_match; cbn; lia).
      reflexivity. }
    step start_context.
    { rewrite Z.bit0_eqb.
      match goal with |- context [(?x mod ?m) &' 1] =>
                      replace (x mod m) with (x &' Z.ones 256) by (rewrite Z.land_ones by lia; reflexivity) end.
      rewrite <-Z.land_assoc.
      rewrite Z.land_ones with (n:=1) by lia.
      cbn.
      match goal with |- context [?x mod 2] =>
                      let H := fresh in
                      assert (x mod 2 = 0 \/ x mod 2 = 1) as H
                          by (pose proof (Z.mod_pos_bound x 2 ltac:(lia)); lia);
                        destruct H as [H | H]; rewrite H
      end; reflexivity. }
    step start_context.
    { reflexivity. }
    { autorewrite with zsimplify_fast.
      repeat match goal with |- context [?x mod ?m] => unique pose proof (Z.mod_pos_bound x m ltac:(lia)) end.
      rewrite <-Z.testbit_neg_eq_if with (n:=256) by (cbn; lia).
      reflexivity. }
    step start_context; [ break_innermost_match; Z.ltb_to_lt; lia | ].
    reflexivity.
  Qed.

  Import PrintingNotations.
  Set Printing Width 1000.
  Open Scope expr_scope.
  Redirect "log" Print barrett_red256.
  (*
barrett_red256 =  fun var : type -> Type => λ x : var (type.type_primitive type.Z * type.type_primitive type.Z)%ctype,
                expr_let x0 := SELM (x₂, 0, 26959946667150639793205513449348445388433292963828203772348655992835) in
                expr_let x1 := RSHI (0, x₂, 255) in
                expr_let x2 := RSHI (x₂, x₁, 255) in
                expr_let x3 := 79228162514264337589248983038 *₂₅₆ (uint128)(x2 >> 128) in
                expr_let x4 := 79228162514264337589248983038 *₂₅₆ ((uint128)(x2) & 340282366920938463463374607431768211455) in
                expr_let x5 := 340282366841710300930663525764514709507 *₂₅₆ (uint128)(x2 >> 128) in
                expr_let x6 := 340282366841710300930663525764514709507 *₂₅₆ ((uint128)(x2) & 340282366920938463463374607431768211455) in
                expr_let x7 := ADD_256 ((uint256)(((uint128)(x5) & 340282366920938463463374607431768211455) << 128), x6) in
                expr_let x8 := ADDC_256 (x7₂, (uint128)(x5 >> 128), x3) in
                expr_let x9 := ADD_256 ((uint256)(((uint128)(x4) & 340282366920938463463374607431768211455) << 128), x7₁) in
                expr_let x10 := ADDC_256 (x9₂, (uint128)(x4 >> 128), x8₁) in
                expr_let x11 := ADD_256 (x2, x10₁) in
                expr_let x12 := ADDC_128 (x11₂, 0, x1) in
                expr_let x13 := ADD_256 (x0, x11₁) in
                expr_let x14 := ADDC_128 (x13₂, 0, x12₁) in
                expr_let x15 := RSHI (x14₁, x13₁, 1) in
                expr_let x16 := 340282366841710300967557013911933812736 *₂₅₆ (uint128)(x15 >> 128) in
                expr_let x17 := 79228162514264337593543950335 *₂₅₆ (uint128)(x15 >> 128) in
                expr_let x18 := 340282366841710300967557013911933812736 *₂₅₆ ((uint128)(x15) & 340282366920938463463374607431768211455) in
                expr_let x19 := 79228162514264337593543950335 *₂₅₆ ((uint128)(x15) & 340282366920938463463374607431768211455) in
                expr_let x20 := ADD_256 ((uint256)(((uint128)(x18) & 340282366920938463463374607431768211455) << 128), x19) in
                expr_let x21 := ADDC_256 (x20₂, (uint128)(x18 >> 128), x16) in
                expr_let x22 := ADD_256 ((uint256)(((uint128)(x17) & 340282366920938463463374607431768211455) << 128), x20₁) in
                expr_let x23 := ADDC_256 (x22₂, (uint128)(x17 >> 128), x21₁) in
                expr_let x24 := SUB_256 (x₁, x22₁) in
                expr_let x25 := SUBB_256 (x24₂, x₂, x23₁) in
                expr_let x26 := SELL (x25₁, 0, 115792089210356248762697446949407573530086143415290314195533631308867097853951) in
                expr_let x27 := SUB_256 (x24₁, x26) in
                ADDM (x27₁, 0, 115792089210356248762697446949407573530086143415290314195533631308867097853951)
     : Expr (type.uncurry (type.type_primitive type.Z -> type.type_primitive type.Z -> type.type_primitive type.Z))
  *)

  Import PreFancy.
  Import PreFancy.Notations.
  Local Notation "'RegMod'" := (Straightline.expr.Primitive (t:=type.Z) 115792089210356248762697446949407573530086143415290314195533631308867097853951).
  Local Notation "'RegMuLow'" := (Straightline.expr.Primitive (t:=type.Z) 26959946667150639793205513449348445388433292963828203772348655992835).
  Redirect "log" Print barrett_red256_prefancy.
  (*
    selm@(y, $x₂, RegZero, RegMuLow);
    rshi@(y0, RegZero, $x₂,255);
    rshi@(y1, $x₂, $x₁,255);
    mulhh@(y2, RegMuLow, $y1);
    mulhl@(y3, RegMuLow, $y1);
    mullh@(y4, RegMuLow, $y1);
    mulll@(y5, RegMuLow, $y1);
    add@(y6, $y5, $y4, 128);
    addc@(y7, carry{$y6}, $y2, $y4, -128);
    add@(y8, $y6, $y3, 128);
    addc@(y9, carry{$y8}, $y7, $y3, -128);
    add@(y10, $y1, $y9, 0);
    addc@(y11, carry{$y10}, RegZero, $y0, 0); #128
    add@(y12, $y, $y10, 0);
    addc@(y13, carry{$y12}, RegZero, $y11, 0); #128
    rshi@(y14, $y13, $y12,1);
    mulhh@(y15, RegMod, $y14);
    mullh@(y16, RegMod, $y14);
    mulhl@(y17, RegMod, $y14);
    mulll@(y18, RegMod, $y14);
    add@(y19, $y18, $y17, 128);
    addc@(y20, carry{$y19}, $y15, $y17, -128);
    add@(y21, $y19, $y16, 128);
    addc@(y22, carry{$y21}, $y20, $y16, -128);
    sub@(y23, $x₁, $y21, 0);
    subb@(y24, carry{$y23}, $x₂, $y22, 0);
    sell@(y25, $y24, RegZero, RegMod);
    sub@(y26, $y23, $y25, 0);
    addm@(y27, $y26, RegZero, RegMod);
    ret $y27
  *)
End Barrett256.

Module SaturatedSolinas.
  Section MulMod.
    Context (s : Z) (c : list (Z * Z))
            (s_nz : s <> 0) (modulus_nz : s - Associational.eval c <> 0).
    Context (log2base : Z) (log2base_pos : 0 < log2base)
            (n nreductions : nat) (n_nz : n <> 0%nat).

    Let weight := weight log2base 1.
    Let props : @weight_properties weight := wprops log2base 1 ltac:(lia).
    Local Lemma base_nz : 2 ^ log2base <> 0. Proof using log2base_pos n_nz s_nz. clear -log2base_pos n_nz s_nz weight props. auto with zarith. Qed.

    Derive mulmod
           SuchThat (forall (f g : list Z)
                            (Hf : length f = n)
                            (Hg : length g = n),
                        (eval weight n (fst (mulmod f g)) + weight n * (snd (mulmod f g))) mod (s - Associational.eval c)
                        = (eval weight n f * eval weight n g) mod (s - Associational.eval c))
           As eval_mulmod.
    Proof.
      intros.
      rewrite <-Rows.eval_mulmod with (base:=2^log2base) (s:=s) (c:=c) (nreductions:=nreductions) by auto using base_nz.
      eapply f_equal2; [|trivial].
      (* expand_lists (). *) (* uncommenting this line removes some unused multiplications but also inlines a bunch of carry stuff at the end *)
      subst mulmod. reflexivity.
    Qed.
    Definition mulmod' := fun x y => fst (mulmod x y).
  End MulMod.

  Derive mulmod_gen
         SuchThat (forall (log2base s : Z) (c : list (Z * Z)) (n nreductions : nat)
                          (f g : list Z),
                      Interp (t:=type.reify_type_of mulmod')
                             mulmod_gen s c log2base n nreductions f g
                      = mulmod' s c log2base n nreductions f g)
         As mulmod_gen_correct.
  Proof. Time cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Time Qed.
  Module Export ReifyHints.
    Global Hint Extern 1 (_ = mulmod' _ _ _ _ _ _ _) => simple apply mulmod_gen_correct : reify_gen_cache.
  End ReifyHints.

  Section rmulmod.
    Context (s : Z)
            (c : list (Z * Z))
            (machine_wordsize : Z).

    Definition relax_zrange_of_machine_wordsize
      := relax_zrange_gen [1; machine_wordsize]%Z.

    Let n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
    (* Number of reductions is calculated as follows :
         Let i be the highest limb index of c. Then, each reduction
         decreases the number of extra limbs by (n-i). So, to go from
         the n extra limbs we have post-multiplication down to 0, we
         need ceil (n / (n - i)) reductions. *)
    Let nreductions : nat :=
      let i := fold_right Z.max 0 (map (fun t => Z.log2 (fst t) / machine_wordsize) c) in
      Z.to_nat (Qceiling (Z.of_nat n / (Z.of_nat n - i))).
    Let relax_zrange := relax_zrange_of_machine_wordsize.
    Let bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.
    Let boundsn : list (ZRange.type.option.interp type.Z)
      := repeat bound n.

    Definition check_args {T} (res : Pipeline.ErrorT T)
      : Pipeline.ErrorT T
      := if (negb (0 <? s - Associational.eval c))%Z
         then Pipeline.Error (Pipeline.Value_not_lt "s - Associational.eval c ≤ 0" 0 (s - Associational.eval c))
         else if (s =? 0)%Z
              then Pipeline.Error (Pipeline.Values_not_provably_distinct "s ≠ 0" s 0)
              else if (n =? 0)%nat
                   then Pipeline.Error (Pipeline.Values_not_provably_distinct "n ≠ 0" n 0%nat)
                   else if (negb (0 <? machine_wordsize))
                        then Pipeline.Error (Pipeline.Value_not_lt "0 < machine_wordsize" 0 machine_wordsize)
                        else res.

  Notation BoundsPipeline rop in_bounds out_bounds
    := (Pipeline.BoundsPipeline
          (*false*) true
          relax_zrange
          rop%Expr in_bounds out_bounds).

  Notation BoundsPipeline_correct in_bounds out_bounds op
    := (fun rv (rop : Expr (type.reify_type_of op)) Hrop
        => @Pipeline.BoundsPipeline_correct_trans
             (*false*) true
             relax_zrange
             (relax_zrange_gen_good _)
             _
             rop
             in_bounds
             out_bounds
             op
             Hrop rv)
         (only parsing).

  Definition rmulmod_correct
    := BoundsPipeline_correct
         (Some boundsn, Some boundsn)
         (Some boundsn)
         (mulmod' s c machine_wordsize n nreductions).

    Notation type_of_strip_3arrow := ((fun (d : Prop) (_ : forall A B C, d) => d) _).
    Definition rmulmod_correctT rv : Prop
      := type_of_strip_3arrow (@rmulmod_correct rv).
  End rmulmod.
End SaturatedSolinas.

Ltac solve_rmulmod := solve_rop SaturatedSolinas.rmulmod_correct.
Ltac solve_rmulmod_nocache := solve_rop_nocache SaturatedSolinas.rmulmod_correct.

Module P192_64.
  Definition s := 2^192.
  Definition c :=  [(2^64, 1); (1,1)].
  Definition machine_wordsize := 64.

  Import SaturatedSolinas.ReifyHints.

  Derive mulmod
         SuchThat (SaturatedSolinas.rmulmod_correctT s c machine_wordsize mulmod)
         As mulmod_correct.
  Proof. Time solve_rmulmod machine_wordsize. Time Qed.

  Import PrintingNotations.
  Open Scope expr_scope.
  Set Printing Width 100000.
  Set Printing Depth 100000.

  Local Notation "'mul64' '(' x ',' y ')'" :=
    (Z.cast2 (uint64, _)%core @@ (Z.mul_split_concrete 18446744073709551616 @@ (x , y)))%expr (at level 50) : expr_scope.
  Local Notation "'add64' '(' x ',' y ')'" :=
    (Z.cast2 (uint64, bool)%core @@ (Z.add_get_carry_concrete 18446744073709551616 @@ (x , y)))%expr (at level 50) : expr_scope.
  Local Notation "'adc64' '(' c ',' x ',' y ')'" :=
    (Z.cast2 (uint64, bool)%core @@ (Z.add_with_get_carry_concrete 18446744073709551616 @@ (c, x , y)))%expr (at level 50) : expr_scope.
  Local Notation "'adx64' '(' c ',' x ',' y ')'" :=
    (Z.cast bool @@ (Z.add_with_carry @@ (c, x , y)))%expr (at level 50) : expr_scope.

  Redirect "log" Print mulmod.
(*
mulmod = fun var : type -> Type => λ x : var (type.list (type.type_primitive type.Z) * type.list (type.type_primitive type.Z))%ctype,
         expr_let x0 := mul64 ((uint64)(x₁[[2]]), (uint64)(x₂[[2]])) in
         expr_let x1 := mul64 ((uint64)(x₁[[2]]), (uint64)(x₂[[1]])) in
         expr_let x2 := mul64 ((uint64)(x₁[[2]]), (uint64)(x₂[[0]])) in
         expr_let x3 := mul64 ((uint64)(x₁[[1]]), (uint64)(x₂[[2]])) in
         expr_let x4 := mul64 ((uint64)(x₁[[1]]), (uint64)(x₂[[1]])) in
         expr_let x5 := mul64 ((uint64)(x₁[[1]]), (uint64)(x₂[[0]])) in
         expr_let x6 := mul64 ((uint64)(x₁[[0]]), (uint64)(x₂[[2]])) in
         expr_let x7 := mul64 ((uint64)(x₁[[0]]), (uint64)(x₂[[1]])) in
         expr_let x8 := mul64 ((uint64)(x₁[[0]]), (uint64)(x₂[[0]])) in
         expr_let x9 := add64 (x0₂, x8₂) in
         expr_let x10 := adc64 (x9₂, 0, x7₂) in
         expr_let x11 := add64 (x0₁, x9₁) in
         expr_let x12 := adc64 (x11₂, 0, x10₁) in
         expr_let x13 := add64 (x1₂, x11₁) in
         expr_let x14 := adc64 (x13₂, 0, x12₁) in
         expr_let x15 := add64 (x3₂, x13₁) in
         expr_let x16 := adc64 (x15₂, x0₂, x14₁) in
         expr_let x17 := add64 (x1₁, x15₁) in
         expr_let x18 := adc64 (x17₂, x0₁, x16₁) in
         expr_let x19 := add64 (x0₂, x8₁) in
         expr_let x20 := adc64 (x19₂, x2₂, x17₁) in
         expr_let x21 := adc64 (x20₂, x1₂, x18₁) in
         expr_let x22 := add64 (x1₁, x19₁) in
         expr_let x23 := adc64 (x22₂, x3₁, x20₁) in
         expr_let x24 := adc64 (x23₂, x3₂, x21₁) in
         expr_let x25 := add64 (x2₂, x22₁) in
         expr_let x26 := adc64 (x25₂, x4₂, x23₁) in
         expr_let x27 := adc64 (x26₂, x2₁, x24₁) in
         expr_let x28 := add64 (x3₁, x25₁) in
         expr_let x29 := adc64 (x28₂, x6₂, x26₁) in
         expr_let x30 := adc64 (x29₂, x4₁, x27₁) in
         expr_let x31 := add64 (x4₂, x28₁) in
         expr_let x32 := adc64 (x31₂, x5₁, x29₁) in
         expr_let x33 := adc64 (x32₂, x5₂, x30₁) in
         expr_let x34 := add64 (x6₂, x31₁) in
         expr_let x35 := adc64 (x34₂, x7₁, x32₁) in
         expr_let x36 := adc64 (x35₂, x6₁, x33₁) in
         x34₁ :: x35₁ :: x36₁ :: []
     : Expr (type.uncurry (type.list (type.type_primitive type.Z) -> type.list (type.type_primitive type.Z) -> type.list (type.type_primitive type.Z)))
*)

End P192_64.

Module P192_32.
  Definition s := 2^192.
  Definition c :=  [(2^64, 1); (1,1)].
  Definition machine_wordsize := 32.

  Import SaturatedSolinas.ReifyHints.

  Derive mulmod
         SuchThat (SaturatedSolinas.rmulmod_correctT s c machine_wordsize mulmod)
         As mulmod_correct.
  Proof. Time solve_rmulmod machine_wordsize. Time Qed.

  Import PrintingNotations.
  Open Scope expr_scope.
  Set Printing Width 100000.
  Set Printing Depth 100000.

  Local Notation "'mul32' '(' x ',' y ')'" :=
    (Z.cast2 (uint32, _)%core @@ (Z.mul_split_concrete 4294967296 @@ (x , y)))%expr (at level 50) : expr_scope.
  Local Notation "'add32' '(' x ',' y ')'" :=
    (Z.cast2 (uint32, bool)%core @@ (Z.add_get_carry_concrete 4294967296 @@ (x , y)))%expr (at level 50) : expr_scope.
  Local Notation "'adc32' '(' c ',' x ',' y ')'" :=
    (Z.cast2 (uint32, bool)%core @@ (Z.add_with_get_carry_concrete 4294967296 @@ (c, x , y)))%expr (at level 50) : expr_scope.

  Redirect "log" Print mulmod.
  (*
mulmod = fun var : type -> Type => λ x : var (type.list (type.type_primitive type.Z) * type.list (type.type_primitive type.Z))%ctype,
         expr_let x0 := mul32 ((uint32)(x₁[[5]]), (uint32)(x₂[[5]])) in
         expr_let x1 := mul32 ((uint32)(x₁[[5]]), (uint32)(x₂[[4]])) in
         expr_let x2 := mul32 ((uint32)(x₁[[5]]), (uint32)(x₂[[3]])) in
         expr_let x3 := mul32 ((uint32)(x₁[[5]]), (uint32)(x₂[[2]])) in
         expr_let x4 := mul32 ((uint32)(x₁[[5]]), (uint32)(x₂[[1]])) in
         expr_let x5 := mul32 ((uint32)(x₁[[5]]), (uint32)(x₂[[0]])) in
         expr_let x6 := mul32 ((uint32)(x₁[[4]]), (uint32)(x₂[[5]])) in
         expr_let x7 := mul32 ((uint32)(x₁[[4]]), (uint32)(x₂[[4]])) in
         expr_let x8 := mul32 ((uint32)(x₁[[4]]), (uint32)(x₂[[3]])) in
         expr_let x9 := mul32 ((uint32)(x₁[[4]]), (uint32)(x₂[[2]])) in
         expr_let x10 := mul32 ((uint32)(x₁[[4]]), (uint32)(x₂[[1]])) in
         expr_let x11 := mul32 ((uint32)(x₁[[4]]), (uint32)(x₂[[0]])) in
         expr_let x12 := mul32 ((uint32)(x₁[[3]]), (uint32)(x₂[[5]])) in
         expr_let x13 := mul32 ((uint32)(x₁[[3]]), (uint32)(x₂[[4]])) in
         expr_let x14 := mul32 ((uint32)(x₁[[3]]), (uint32)(x₂[[3]])) in
         expr_let x15 := mul32 ((uint32)(x₁[[3]]), (uint32)(x₂[[2]])) in
         expr_let x16 := mul32 ((uint32)(x₁[[3]]), (uint32)(x₂[[1]])) in
         expr_let x17 := mul32 ((uint32)(x₁[[3]]), (uint32)(x₂[[0]])) in
         expr_let x18 := mul32 ((uint32)(x₁[[2]]), (uint32)(x₂[[5]])) in
         expr_let x19 := mul32 ((uint32)(x₁[[2]]), (uint32)(x₂[[4]])) in
         expr_let x20 := mul32 ((uint32)(x₁[[2]]), (uint32)(x₂[[3]])) in
         expr_let x21 := mul32 ((uint32)(x₁[[2]]), (uint32)(x₂[[2]])) in
         expr_let x22 := mul32 ((uint32)(x₁[[2]]), (uint32)(x₂[[1]])) in
         expr_let x23 := mul32 ((uint32)(x₁[[2]]), (uint32)(x₂[[0]])) in
         expr_let x24 := mul32 ((uint32)(x₁[[1]]), (uint32)(x₂[[5]])) in
         expr_let x25 := mul32 ((uint32)(x₁[[1]]), (uint32)(x₂[[4]])) in
         expr_let x26 := mul32 ((uint32)(x₁[[1]]), (uint32)(x₂[[3]])) in
         expr_let x27 := mul32 ((uint32)(x₁[[1]]), (uint32)(x₂[[2]])) in
         expr_let x28 := mul32 ((uint32)(x₁[[1]]), (uint32)(x₂[[1]])) in
         expr_let x29 := mul32 ((uint32)(x₁[[1]]), (uint32)(x₂[[0]])) in
         expr_let x30 := mul32 ((uint32)(x₁[[0]]), (uint32)(x₂[[5]])) in
         expr_let x31 := mul32 ((uint32)(x₁[[0]]), (uint32)(x₂[[4]])) in
         expr_let x32 := mul32 ((uint32)(x₁[[0]]), (uint32)(x₂[[3]])) in
         expr_let x33 := mul32 ((uint32)(x₁[[0]]), (uint32)(x₂[[2]])) in
         expr_let x34 := mul32 ((uint32)(x₁[[0]]), (uint32)(x₂[[1]])) in
         expr_let x35 := mul32 ((uint32)(x₁[[0]]), (uint32)(x₂[[0]])) in
         expr_let x36 := add32 (x0₁, x34₂) in
         expr_let x37 := adc32 (x36₂, 0, x33₂) in
         expr_let x38 := adc32 (x37₂, 0, x32₂) in
         expr_let x39 := adc32 (x38₂, 0, x31₂) in
         expr_let x40 := add32 (x1₂, x36₁) in
         expr_let x41 := adc32 (x40₂, 0, x37₁) in
         expr_let x42 := adc32 (x41₂, 0, x38₁) in
         expr_let x43 := adc32 (x42₂, 0, x39₁) in
         expr_let x44 := add32 (x6₂, x40₁) in
         expr_let x45 := adc32 (x44₂, 0, x41₁) in
         expr_let x46 := adc32 (x45₂, 0, x42₁) in
         expr_let x47 := adc32 (x46₂, 0, x43₁) in
         expr_let x48 := add32 (x2₁, x44₁) in
         expr_let x49 := adc32 (x48₂, 0, x45₁) in
         expr_let x50 := adc32 (x49₂, 0, x46₁) in
         expr_let x51 := adc32 (x50₂, 0, x47₁) in
         expr_let x52 := add32 (x3₂, x48₁) in
         expr_let x53 := adc32 (x52₂, x0₂, x49₁) in
         expr_let x54 := adc32 (x53₂, 0, x50₁) in
         expr_let x55 := adc32 (x54₂, 0, x51₁) in
         expr_let x56 := add32 (x7₁, x52₁) in
         expr_let x57 := adc32 (x56₂, x1₁, x53₁) in
         expr_let x58 := adc32 (x57₂, 0, x54₁) in
         expr_let x59 := adc32 (x58₂, 0, x55₁) in
         expr_let x60 := add32 (x8₂, x56₁) in
         expr_let x61 := adc32 (x60₂, x2₂, x57₁) in
         expr_let x62 := adc32 (x61₂, 0, x58₁) in
         expr_let x63 := adc32 (x62₂, 0, x59₁) in
         expr_let x64 := add32 (x12₁, x60₁) in
         expr_let x65 := adc32 (x64₂, x6₁, x61₁) in
         expr_let x66 := adc32 (x65₂, x0₁, x62₁) in
         expr_let x67 := adc32 (x66₂, 0, x63₁) in
         expr_let x68 := add32 (x13₂, x64₁) in
         expr_let x69 := adc32 (x68₂, x7₂, x65₁) in
         expr_let x70 := adc32 (x69₂, x1₂, x66₁) in
         expr_let x71 := adc32 (x70₂, 0, x67₁) in
         expr_let x72 := add32 (x18₂, x68₁) in
         expr_let x73 := adc32 (x72₂, x12₂, x69₁) in
         expr_let x74 := adc32 (x73₂, x6₂, x70₁) in
         expr_let x75 := adc32 (x74₂, x0₂, x71₁) in
         expr_let x76 := add32 (x4₁, x72₁) in
         expr_let x77 := adc32 (x76₂, x3₁, x73₁) in
         expr_let x78 := adc32 (x77₂, x2₁, x74₁) in
         expr_let x79 := adc32 (x78₂, x1₁, x75₁) in
         expr_let x80 := add32 (x0₁, x35₁) in
         expr_let x81 := adc32 (x80₂, 0, x35₂) in
         expr_let x82 := adc32 (x81₂, x5₂, x76₁) in
         expr_let x83 := adc32 (x82₂, x4₂, x77₁) in
         expr_let x84 := adc32 (x83₂, x3₂, x78₁) in
         expr_let x85 := adc32 (x84₂, x2₂, x79₁) in
         expr_let x86 := add32 (x1₂, x80₁) in
         expr_let x87 := adc32 (x86₂, 0, x81₁) in
         expr_let x88 := adc32 (x87₂, x9₁, x82₁) in
         expr_let x89 := adc32 (x88₂, x8₁, x83₁) in
         expr_let x90 := adc32 (x89₂, x7₁, x84₁) in
         expr_let x91 := adc32 (x90₂, x6₁, x85₁) in
         expr_let x92 := add32 (x6₂, x86₁) in
         expr_let x93 := adc32 (x92₂, x0₂, x87₁) in
         expr_let x94 := adc32 (x93₂, x10₂, x88₁) in
         expr_let x95 := adc32 (x94₂, x9₂, x89₁) in
         expr_let x96 := adc32 (x95₂, x8₂, x90₁) in
         expr_let x97 := adc32 (x96₂, x7₂, x91₁) in
         expr_let x98 := add32 (x4₁, x92₁) in
         expr_let x99 := adc32 (x98₂, x3₁, x93₁) in
         expr_let x100 := adc32 (x99₂, x14₁, x94₁) in
         expr_let x101 := adc32 (x100₂, x13₁, x95₁) in
         expr_let x102 := adc32 (x101₂, x12₁, x96₁) in
         expr_let x103 := adc32 (x102₂, x12₂, x97₁) in
         expr_let x104 := add32 (x5₂, x98₁) in
         expr_let x105 := adc32 (x104₂, x4₂, x99₁) in
         expr_let x106 := adc32 (x105₂, x15₂, x100₁) in
         expr_let x107 := adc32 (x106₂, x14₂, x101₁) in
         expr_let x108 := adc32 (x107₂, x13₂, x102₁) in
         expr_let x109 := adc32 (x108₂, x5₁, x103₁) in
         expr_let x110 := add32 (x9₁, x104₁) in
         expr_let x111 := adc32 (x110₂, x8₁, x105₁) in
         expr_let x112 := adc32 (x111₂, x19₁, x106₁) in
         expr_let x113 := adc32 (x112₂, x18₁, x107₁) in
         expr_let x114 := adc32 (x113₂, x18₂, x108₁) in
         expr_let x115 := adc32 (x114₂, x10₁, x109₁) in
         expr_let x116 := add32 (x10₂, x110₁) in
         expr_let x117 := adc32 (x116₂, x9₂, x111₁) in
         expr_let x118 := adc32 (x117₂, x20₂, x112₁) in
         expr_let x119 := adc32 (x118₂, x19₂, x113₁) in
         expr_let x120 := adc32 (x119₂, x11₁, x114₁) in
         expr_let x121 := adc32 (x120₂, x11₂, x115₁) in
         expr_let x122 := add32 (x14₁, x116₁) in
         expr_let x123 := adc32 (x122₂, x13₁, x117₁) in
         expr_let x124 := adc32 (x123₂, x24₁, x118₁) in
         expr_let x125 := adc32 (x124₂, x24₂, x119₁) in
         expr_let x126 := adc32 (x125₂, x16₁, x120₁) in
         expr_let x127 := adc32 (x126₂, x15₁, x121₁) in
         expr_let x128 := add32 (x15₂, x122₁) in
         expr_let x129 := adc32 (x128₂, x14₂, x123₁) in
         expr_let x130 := adc32 (x129₂, x25₂, x124₁) in
         expr_let x131 := adc32 (x130₂, x17₁, x125₁) in
         expr_let x132 := adc32 (x131₂, x17₂, x126₁) in
         expr_let x133 := adc32 (x132₂, x16₂, x127₁) in
         expr_let x134 := add32 (x19₁, x128₁) in
         expr_let x135 := adc32 (x134₂, x18₁, x129₁) in
         expr_let x136 := adc32 (x135₂, x30₂, x130₁) in
         expr_let x137 := adc32 (x136₂, x22₁, x131₁) in
         expr_let x138 := adc32 (x137₂, x21₁, x132₁) in
         expr_let x139 := adc32 (x138₂, x20₁, x133₁) in
         expr_let x140 := add32 (x20₂, x134₁) in
         expr_let x141 := adc32 (x140₂, x19₂, x135₁) in
         expr_let x142 := adc32 (x141₂, x23₁, x136₁) in
         expr_let x143 := adc32 (x142₂, x23₂, x137₁) in
         expr_let x144 := adc32 (x143₂, x22₂, x138₁) in
         expr_let x145 := adc32 (x144₂, x21₂, x139₁) in
         expr_let x146 := add32 (x24₁, x140₁) in
         expr_let x147 := adc32 (x146₂, x24₂, x141₁) in
         expr_let x148 := adc32 (x147₂, x28₁, x142₁) in
         expr_let x149 := adc32 (x148₂, x27₁, x143₁) in
         expr_let x150 := adc32 (x149₂, x26₁, x144₁) in
         expr_let x151 := adc32 (x150₂, x25₁, x145₁) in
         expr_let x152 := add32 (x25₂, x146₁) in
         expr_let x153 := adc32 (x152₂, x29₁, x147₁) in
         expr_let x154 := adc32 (x153₂, x29₂, x148₁) in
         expr_let x155 := adc32 (x154₂, x28₂, x149₁) in
         expr_let x156 := adc32 (x155₂, x27₂, x150₁) in
         expr_let x157 := adc32 (x156₂, x26₂, x151₁) in
         expr_let x158 := add32 (x30₂, x152₁) in
         expr_let x159 := adc32 (x158₂, x34₁, x153₁) in
         expr_let x160 := adc32 (x159₂, x33₁, x154₁) in
         expr_let x161 := adc32 (x160₂, x32₁, x155₁) in
         expr_let x162 := adc32 (x161₂, x31₁, x156₁) in
         expr_let x163 := adc32 (x162₂, x30₁, x157₁) in
         x158₁ :: x159₁ :: x160₁ :: x161₁ :: x162₁ :: x163₁ :: []
     : Expr (type.uncurry (type.list (type.type_primitive type.Z) -> type.list (type.type_primitive type.Z) -> type.list (type.type_primitive type.Z)))
*)

End P192_32.

(* TODO : Too slow! Many, many terms in this one. *)
(*
Module P256_32.
  Definition s := 2^256.
  Definition c :=  [(2^224, 1); (2^192, -1); (2^96, -1); (1,1)].
  Definition machine_wordsize := 32.

  Derive mulmod
         SuchThat (SaturatedSolinas.rmulmod_correctT s c machine_wordsize mulmod)
         As mulmod_correct.
  Proof. Time solve_rmulmod machine_wordsize. Time Qed.

  Import PrintingNotations.
  Open Scope expr_scope.
  Set Printing Width 100000.

  Print mulmod.

End P256_32.
*)

Module MontgomeryReduction.
  Section MontRed'.
    Context (N R N' R' : Z).
    Context (HN_range : 0 <= N < R) (HN'_range : 0 <= N' < R) (HN_nz : N <> 0) (R_gt_1 : R > 1)
            (N'_good : Z.equiv_modulo R (N*N') (-1)) (R'_good: Z.equiv_modulo N (R*R') 1).

    Context (Zlog2R : Z) .
    Let w : nat -> Z := weight Zlog2R 1.
    Context (n:nat) (Hn_nz: n <> 0%nat) (n_good : Zlog2R mod Z.of_nat n = 0).
    Context (R_big_enough : n <= Zlog2R)
            (R_two_pow : 2^Zlog2R = R).
    Let w_mul : nat -> Z := weight (Zlog2R / n) 1.
    Context (nout : nat) (Hnout : nout = 2%nat).

    Definition montred' (lo_hi : (Z * Z)) :=
      dlet_nd y := nth_default 0 (BaseConversion.widemul_inlined Zlog2R n nout (fst lo_hi) N') 0  in
      dlet_nd t1_t2 := (BaseConversion.widemul_inlined_reverse Zlog2R n nout N y) in
      dlet_nd sum_carry := Rows.add (weight Zlog2R 1) 2 [fst lo_hi; snd lo_hi] t1_t2 in
      dlet_nd y' := Z.zselect (snd sum_carry) 0 N in
      dlet_nd lo''_carry := Z.sub_get_borrow_full R (nth_default 0 (fst sum_carry) 1) y' in
      Z.add_modulo (fst lo''_carry) 0 N.

    Local Lemma Hw : forall i, w i = R ^ Z.of_nat i.
    Proof using R_big_enough R_two_pow.
      clear -R_big_enough R_two_pow; cbv [w weight]; intro.
      autorewrite with zsimplify.
      rewrite Z.pow_mul_r, R_two_pow by lia; reflexivity.
    Qed.

    Local Ltac change_weight := rewrite !Hw, ?Z.pow_0_r, ?Z.pow_1_r, ?Z.pow_2_r, ?Z.pow_1_l in *.
    Local Ltac solve_range :=
      repeat match goal with
             | _ => progress change_weight
             | |- context [?a mod ?b] => unique pose proof (Z.mod_pos_bound a b ltac:(lia))
             | |- 0 <= _ => progress Z.zero_bounds
             | |- 0 <= _ * _ < _ * _ =>
               split; [ solve [Z.zero_bounds] | apply Z.mul_lt_mono_nonneg; lia ]
             | _ => solve [auto]
             | _ => lia
             end.

    Local Lemma eval2 x y : eval w 2 [x;y] = x + R * y.
    Proof using R_big_enough R_two_pow. cbn. change_weight. ring. Qed.

    Hint Rewrite BaseConversion.widemul_inlined_reverse_correct BaseConversion.widemul_inlined_correct
         using (autorewrite with widemul push_nth_default; solve [solve_range]) : widemul.

    Lemma montred'_eq lo_hi T (HT_range: 0 <= T < R * N)
          (Hlo: fst lo_hi = T mod R) (Hhi: snd lo_hi = T / R):
      montred' lo_hi = reduce_via_partial N R N' T.
    Proof using HN'_range HN_nz HN_range Hn_nz Hnout R_big_enough R_gt_1 R_two_pow.
      rewrite <-reduce_via_partial_alt_eq by nia.
      cbv [montred' partial_reduce_alt reduce_via_partial_alt prereduce Let_In].
      rewrite Hlo, Hhi.
      assert (0 <= (T mod R) * N' < w 2) by  (solve_range).

      autorewrite with widemul.
      rewrite Rows.add_partitions, Rows.add_div by (distr_length; apply wprops; lia).
      rewrite R_two_pow.
      cbv [Rows.partition seq]. rewrite !eval2.
      autorewrite with push_nth_default push_map.
      autorewrite with to_div_mod. rewrite ?Z.zselect_correct, ?Z.add_modulo_correct.
      change_weight.

      (* pull out value before last modular reduction *)
      match goal with |- (if (?n <=? ?x)%Z then ?x - ?n else ?x) = (if (?n <=? ?y) then ?y - ?n else ?y)%Z =>
                      let P := fresh "H" in assert (x = y) as P; [|rewrite P; reflexivity] end.

      autorewrite with zsimplify.
      rewrite (Z.mul_comm (((T mod R) * N') mod R) N) in *.
      break_match; try reflexivity; Z.ltb_to_lt; rewrite Z.div_small_iff in * by lia;
        repeat match goal with
               | _ => progress autorewrite with zsimplify_fast
               | |- context [?x mod (R * R)] =>
                 unique pose proof (Z.mod_pos_bound x (R * R));
                   try rewrite (Z.mod_small x (R * R)) in * by Z.rewrite_mod_small_solver
               | _ => lia
               | _ => progress Z.rewrite_mod_small
               end.
    Qed.

    Lemma montred'_correct lo_hi T (HT_range: 0 <= T < R * N)
          (Hlo: fst lo_hi = T mod R) (Hhi: snd lo_hi = T / R): montred' lo_hi = (T * R') mod N.
    Proof using HN'_range HN_nz HN_range Hn_nz Hnout N'_good R'_good R_big_enough R_gt_1 R_two_pow.
      erewrite montred'_eq by eauto.
      apply Z.equiv_modulo_mod_small; auto using reduce_via_partial_correct.
      replace 0 with (Z.min 0 (R-N)) by (apply Z.min_l; lia).
      apply reduce_via_partial_in_range; lia.
    Qed.
  End MontRed'.

  Derive montred_gen
         SuchThat (forall (N R N' : Z)
                          (Zlog2R : Z)
                          (n nout: nat)
                          (lo_hi : Z * Z),
                      Interp (t:=type.reify_type_of montred')
                             montred_gen N R N' Zlog2R n nout lo_hi
                      = montred' N R N' Zlog2R n nout lo_hi)
         As montred_gen_correct.
  Proof. Time cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Time Qed.
  Module Export ReifyHints.
    Global Hint Extern 1 (_ = montred' _ _ _ _ _ _ _) => simple apply montred_gen_correct : reify_gen_cache.
  End ReifyHints.

  Section rmontred.
    Context (N R N' : Z)
            (machine_wordsize : Z).

    Let bound := Some r[0 ~> (2^machine_wordsize - 1)%Z]%zrange.

    Definition relax_zrange_of_machine_wordsize
      := relax_zrange_gen [1; machine_wordsize / 2; machine_wordsize; 2 * machine_wordsize]%Z.
    Local Arguments relax_zrange_of_machine_wordsize / .

    Let relax_zrange := relax_zrange_of_machine_wordsize.

    Definition check_args {T} (res : Pipeline.ErrorT T)
      : Pipeline.ErrorT T
      := res. (* TODO: this should actually check stuff that corresponds with preconditions of montred'_correct *)

    Notation BoundsPipeline_correct in_bounds out_bounds op
      := (fun rv (rop : Expr (type.reify_type_of op)) Hrop
          => @Pipeline.BoundsPipeline_correct_trans
               false (* subst01 *)
               relax_zrange
               (relax_zrange_gen_good _)
               _
               rop
               in_bounds
               out_bounds
               op
               Hrop rv)
           (only parsing).

    Definition rmontred_correct
      := BoundsPipeline_correct
           (bound, bound)
           bound
           (montred' N R N' (Z.log2 R) 2 2).

    Notation type_of_strip_3arrow := ((fun (d : Prop) (_ : forall A B C, d) => d) _).
    Definition rmontred_correctT rv : Prop
      := type_of_strip_3arrow (@rmontred_correct rv).
  End rmontred.
End MontgomeryReduction.

Ltac solve_rmontred := solve_rop MontgomeryReduction.rmontred_correct.
Ltac solve_rmontred_nocache := solve_rop_nocache MontgomeryReduction.rmontred_correct.

Module Montgomery256.

  Definition N := Eval lazy in (2^256-2^224+2^192+2^96-1).
  Definition N':= (115792089210356248768974548684794254293921932838497980611635986753331132366849).
  Definition R := Eval lazy in (2^256).
  Definition R' := 115792089183396302114378112356516095823261736990586219612555396166510339686400.
  Definition machine_wordsize := 256.

  Import MontgomeryReduction.ReifyHints.

  Derive montred256
         SuchThat (MontgomeryReduction.rmontred_correctT N R N' machine_wordsize montred256)
         As montred256_correct.
  Proof. Time solve_rmontred machine_wordsize. Time Qed.

  Definition montred256_prefancy' := PreFancy.of_Expr machine_wordsize [N;N'] montred256.

  Derive montred256_prefancy
         SuchThat (montred256_prefancy = montred256_prefancy' type.interp)
         As montred256_prefancy_eq.
  Proof. lazy - [type.interp]; reflexivity. Qed.


  Lemma montred'_correct_specialized R' (R'_correct : Z.equiv_modulo N (R * R') 1) :
    forall (lo hi : Z),
      0 <= lo < R -> 0 <= hi < R -> 0 <= lo + R * hi < R * N ->
      MontgomeryReduction.montred' N R N' (Z.log2 R) 2 2 (lo, hi) = ((lo + R * hi) * R') mod N.
  Proof using Type.
    intros.
    apply MontgomeryReduction.montred'_correct with (T:=lo + R * hi) (R':=R');
      try match goal with
            | |- context[R'] => assumption
            | |- context [lo] =>
              try assumption; progress autorewrite with zsimplify cancel_pair; reflexivity
          end; lazy; try split; congruence.
  Qed.

  (* Note: If this is not factored out, then for some reason Qed takes forever in montred256_correct_full. *)
  Lemma montred256_correct_proj2 :
    forall xy : type.interp (type.prod type.Z type.Z),
      ZRange.type.option.is_bounded_by
        (t:=type.prod type.Z type.Z)
        (Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange, Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange)
        xy = true ->
       expr.Interp (@ident.interp) montred256 xy = app_curried (t:=type.arrow (type.prod type.Z type.Z) type.Z) (MontgomeryReduction.montred' N R N' (Z.log2 R) 2 2) xy.
  Proof using Type. intros; destruct (montred256_correct xy); assumption. Qed.
  Lemma montred256_correct_proj2' :
    forall xy : type.interp (type.prod type.Z type.Z),
      ZRange.type.option.is_bounded_by
        (t:=type.prod type.Z type.Z)
        (Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange, Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange)
        xy = true ->
       expr.Interp (@ident.interp) montred256 xy = MontgomeryReduction.montred' N R N' (Z.log2 R) 2 2 xy.
  Proof using Type. intros; rewrite montred256_correct_proj2 by assumption; unfold app_curried; exact eq_refl. Qed.

  Lemma montred256_correct_full  R' (R'_correct : Z.equiv_modulo N (R * R') 1) :
    forall (lo hi : Z),
      0 <= lo < R -> 0 <= hi < R -> 0 <= lo + R * hi < R * N ->
      expr.interp (@ident.interp) (montred256 type.interp) (lo, hi) = ((lo + R * hi) * R') mod N.
  Proof using Type.
    intros.
    rewrite <-montred'_correct_specialized by assumption.
    rewrite <-montred256_correct_proj2'.
    { cbv [expr.Interp type.uncurried_domain type.uncurry type.final_codomain].
      reflexivity. }
    { cbn. rewrite !andb_true_iff. cbv [R N] in *.
      repeat split; apply Z.leb_le; lia. }
  Qed.

  (* TODO : maybe move these ok_expr tactics somewhere else *)
  Ltac ok_expr_step' :=
    match goal with
    | _ => assumption
    | |- _ <= _ <= _ \/ @eq zrange _ _ =>
      right; lazy; try split; congruence
    | |- _ <= _ <= _ \/ @eq zrange _ _ =>
      left; lazy; try split; congruence
    | |- lower r[0~>_]%zrange = 0 => reflexivity
    | |- context [PreFancy.ok_ident] => constructor
    | |- context [PreFancy.ok_scalar] => constructor; try lia
    | |- context [PreFancy.is_halved] => eapply PreFancy.is_halved_constant; [lazy; reflexivity | ]
    | |- context [PreFancy.is_halved] => constructor
    | |- context [PreFancy.in_word_range] => lazy; reflexivity
    | |- context [PreFancy.in_flag_range] => lazy; reflexivity
    | |- context [PreFancy.get_range] =>
      cbn [PreFancy.get_range lower upper fst snd ZRange.map]
    | x : type.interp (type.prod _ _) |- _ => destruct x
    | |- (_ <=? _)%zrange = true =>
      match goal with
      | |- context [PreFancy.get_range_var] =>
        cbv [is_tighter_than_bool PreFancy.has_range fst snd upper lower R N] in *; cbn;
        apply andb_true_iff; split; apply Z.leb_le
      | _ => lazy
      end; lia || reflexivity
    | |- @eq zrange _ _ => lazy; reflexivity
    | |- _ <= _ => cbv [machine_wordsize]; lia
    | |- _ <= _ <= _ => cbv [machine_wordsize]; lia
    end; intros.

  (* TODO : maybe move these ok_expr tactics somewhere else *)
  Ltac ok_expr_step :=
    match goal with
    | |- context [PreFancy.ok_expr] => constructor; cbn [fst snd]; repeat ok_expr_step'
    end; intros; cbn [Nat.max].

  Lemma montred256_prefancy_correct :
    forall (lo hi : Z) dummy_arrow,
      0 <= lo < R -> 0 <= hi < R -> 0 <= lo + R * hi < R * N ->
      @PreFancy.interp machine_wordsize (PreFancy.interp_cast_mod machine_wordsize) type.Z (montred256_prefancy (lo,hi) dummy_arrow) = ((lo + R * hi) * R') mod N.
  Proof using Type.
    intros. rewrite montred256_prefancy_eq; cbv [montred256_prefancy'].
    erewrite PreFancy.of_Expr_correct.
    { apply montred256_correct_full; try assumption; reflexivity. }
    { reflexivity. }
    { lazy; reflexivity. }
    { lazy; reflexivity. }
    { repeat constructor. }
    { cbv [In N N']; intros; intuition; subst; cbv; congruence. }
    { assert (340282366920938463463374607431768211455 * 2 ^ 128 <= 2 ^ machine_wordsize - 1) as shiftl_128_ok by (lazy; congruence).
      repeat (ok_expr_step; [ ]).
      ok_expr_step.
      lazy; congruence.
      constructor.
      constructor. }
    { lazy. lia. }
   Qed.

  Definition montred256_fancy' (lo hi RegMod RegPInv RegZero error : positive) :=
    Fancy.of_Expr 3%positive
                  (fun z => if z =? N then Some RegMod else if z =? N' then Some RegPInv else if z =? 0 then Some RegZero else None)
                  [N;N']
                  montred256
                  (lo, hi)%positive
                  (fun _ _ => tt)
                  error.
  Derive montred256_fancy
         SuchThat (forall RegMod RegPInv RegZero,
                      montred256_fancy RegMod RegPInv RegZero = montred256_fancy' RegMod RegPInv RegZero)
         As montred256_fancy_eq.
  Proof.
    intros.
    lazy - [Fancy.ADD Fancy.ADDC Fancy.SUB
                      Fancy.MUL128LL Fancy.MUL128LU Fancy.MUL128UL Fancy.MUL128UU
                      Fancy.RSHI Fancy.SELC Fancy.SELM Fancy.SELL Fancy.ADDM].
    reflexivity.
  Qed.

  Import Fancy.Registers.

  Definition montred256_alloc' lo hi RegPInv :=
    fun errorP errorR =>
    Fancy.allocate register
                   positive Pos.eqb
                   errorR
                   (montred256_fancy 1000%positive 1001%positive 1002%positive 1003%positive 1004%positive errorP)
                   [r2;r3;r4;r5;r6;r7;r8;r9;r10;r11;r12;r13;r14;r15;r16;r17;r18;r19;r20]
                   (fun n => if n =? 1000 then lo
                             else if n =? 1001 then hi
                                  else if n =? 1002 then RegMod
                                       else if n =? 1003 then RegPInv
                                            else if n =? 1004 then RegZero
                                                 else errorR).
  Derive montred256_alloc
         SuchThat (montred256_alloc = montred256_alloc')
         As montred256_alloc_eq.
  Proof.
    intros.
    cbv [montred256_alloc' montred256_fancy].
    cbn. subst montred256_alloc.
    reflexivity.
  Qed.

  Import ProdEquiv.

  Local Ltac solve_bounds :=
    match goal with
    | H : ?a = ?b mod ?c |- 0 <= ?a < ?c => rewrite H; apply Z.mod_pos_bound; lia
    | _ => assumption
    end.

  Lemma montred256_alloc_equivalent errorP errorR cc_start_state start_context :
    forall lo hi y t1 t2 scratch RegPInv extra_reg,
      NoDup [lo; hi; y; t1; t2; scratch; RegPInv; extra_reg; RegMod; RegZero] ->
      0 <= start_context lo < R ->
      0 <= start_context hi < R ->
      0 <= start_context RegPInv < R ->
      ProdEquiv.interp256 (montred256_alloc r0 r1 r30 errorP errorR) cc_start_state
                          (fun r => if reg_eqb r r0
                                    then start_context lo
                                    else if reg_eqb r r1
                                         then start_context hi
                                         else if reg_eqb r r30
                                              then start_context RegPInv
                                              else start_context r)
    = ProdEquiv.interp256 (Prod.MontRed256 lo hi y t1 t2 scratch RegPInv) cc_start_state start_context.
  Proof using Type.
    intros. cbv [R] in *.
    cbv [Prod.MontRed256 montred256_alloc].

    (* Extract proofs that no registers are equal to each other *)
    repeat match goal with
           | H : NoDup _ |- _ => inversion H; subst; clear H
           | H : ~ In _ _ |- _ => cbv [In] in H
           | H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H; destruct H
           | H : ~ False |- _ => clear H
           end.

    rewrite ProdEquiv.interp_Mul256 with (tmp2:=extra_reg) by (congruence || push_value_unused).

    step_both_sides.
    step_both_sides.
    rewrite mulll_comm. step_both_sides.
    step_both_sides.
    step_both_sides.

    rewrite ProdEquiv.interp_Mul256x256 with (tmp2:=extra_reg) by (congruence || push_value_unused).

    rewrite mulll_comm. step_both_sides.
    step_both_sides.
    step_both_sides.
    rewrite mulhh_comm. step_both_sides.
    step_both_sides.
    step_both_sides.
    step_both_sides.
    step_both_sides.


    rewrite add_comm by (cbn; solve_bounds). step_both_sides.
    rewrite addc_comm by (cbn; solve_bounds). step_both_sides.
    step_both_sides.
    step_both_sides.
    step_both_sides.

    cbn; repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl by congruence.
    reflexivity.
  Qed.

  Import Fancy_PreFancy_Equiv.

  Definition interp_equivZZ_256 {s} :=
    @interp_equivZZ s 256 ltac:(cbv; congruence) 115792089237316195423570985008687907853269984665640564039457584007913129639935 ltac:(reflexivity).
  Definition interp_equivZ_256 {s} :=
    @interp_equivZ s 256 115792089237316195423570985008687907853269984665640564039457584007913129639935 ltac:(reflexivity).

  Local Ltac simplify_op_equiv start_ctx :=
    cbn - [Fancy.spec PreFancy.interp_ident Fancy.cc_spec];
    repeat match goal with H : start_ctx _ = _ |- _ => rewrite H end;
    cbv - [
      Z.add_with_get_carry_full
        Z.add_get_carry_full Z.sub_get_borrow_full
        Z.le Z.ltb Z.leb Z.geb Z.eqb Z.land Z.shiftr Z.shiftl
        Z.add Z.mul Z.div Z.sub Z.modulo Z.testbit Z.pow Z.ones
        fst snd]; cbn [fst snd];
    try (replace (2 ^ (256 / 2) - 1) with (Z.ones 128) by reflexivity; rewrite !Z.land_ones by lia);
    autorewrite with to_div_mod; rewrite ?Z.mod_mod, <-?Z.testbit_spec' by lia;
    repeat match goal with
           | H : 0 <= ?x < ?m |- context [?x mod ?m] => rewrite (Z.mod_small x m) by apply H
           | |- context [?x <? 0] => rewrite (proj2 (Z.ltb_ge x 0)) by (break_match; Z.zero_bounds)
           | _ => rewrite Z.mod_small with (b:=2) by (break_match; lia)
           | |- context [ (if Z.testbit ?a ?n then 1 else 0) + ?b + ?c] =>
             replace ((if Z.testbit a n then 1 else 0) + b + c) with (b + c + (if Z.testbit a n then 1 else 0)) by ring
           end.

  Local Ltac solve_nonneg ctx :=
    match goal with x := (Fancy.spec _ _ _) |- _ => subst x end;
    simplify_op_equiv ctx; Z.zero_bounds.

  Local Ltac generalize_result :=
    let v := fresh "v" in intro v; generalize v; clear v; intro v.

  Local Ltac generalize_result_nonneg ctx :=
    let v := fresh "v" in
    let v_nonneg := fresh "v_nonneg" in
    intro v; assert (0 <= v) as v_nonneg; [solve_nonneg ctx |generalize v v_nonneg; clear v v_nonneg; intros v v_nonneg].

  Local Ltac step ctx :=
    match goal with
    | |- Fancy.interp _ _ _ (Fancy.Instr (Fancy.ADD _) _ _ (Fancy.Instr (Fancy.ADDC _) _ _ _)) _ _ = _ =>
      apply interp_equivZZ_256; [ simplify_op_equiv ctx | simplify_op_equiv ctx | generalize_result_nonneg ctx]
    | _ => apply interp_equivZ_256; [simplify_op_equiv ctx | generalize_result]
    | _ => apply interp_equivZZ_256; [ simplify_op_equiv ctx | simplify_op_equiv ctx | generalize_result]
    end.

  Lemma prod_montred256_correct :
    forall (cc_start_state : Fancy.CC.state) (* starting carry flags can be anything *)
           (start_context : register -> Z)   (* starting register values *)
           (lo hi y t1 t2 scratch RegPInv extra_reg : register), (* registers to use in computation *)
      NoDup [lo; hi; y; t1; t2; scratch; RegPInv; extra_reg; RegMod; RegZero] -> (* registers must be distinct *)
      start_context RegPInv = N' ->  (* RegPInv needs to hold the inverse of the modulus *)
      start_context RegMod = N ->    (* RegMod needs to hold the modulus *)
      start_context RegZero = 0 ->   (* RegZero needs to hold zero *)
      (0 <= start_context lo < R) -> (* low half of the input is in bounds (R=2^256) *)
      (0 <= start_context hi < R) -> (* high half of the input is in bounds (R=2^256) *)
      let x := (start_context lo) + R * (start_context hi) in (* x is the input (split into two registers) *)
      (0 <= x < R * N) -> (* input precondition *)
      (ProdEquiv.interp256 (Prod.MontRed256 lo hi y t1 t2 scratch RegPInv) cc_start_state start_context = (x * R') mod N).
  Proof using Type.
    intros. subst x. cbv [N R N'] in *.
    rewrite <-montred256_prefancy_correct with (dummy_arrow := fun s d _ => DefaultValue.type.default) by auto.
    rewrite <-montred256_alloc_equivalent with (errorR := RegZero) (errorP := 1%positive) (extra_reg:=extra_reg)
      by (cbv [R]; auto with lia).
    cbv [ProdEquiv.interp256].
    cbv [montred256_alloc montred256_prefancy].

    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].

    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ break_innermost_match; Z.ltb_to_lt; lia | ].
    step start_context; [ reflexivity | | ].
    {
      let r := eval cbv in (2^256) in replace (2^256) with r by reflexivity.
      rewrite !Z.shiftl_0_r, !Z.mod_mod by lia.
      repeat match goal with
             | |- context [?a mod ?b] => unique pose proof (Z.mod_pos_bound a b ltac:(lia))
             end.
      apply Z.testbit_neg_eq_if;
        let r := eval cbv in (2^256) in replace (2^256) with r by reflexivity;
                               lia. }
    step start_context; [ break_innermost_match; Z.ltb_to_lt; lia | ].
    reflexivity.
  Qed.

  Import PrintingNotations.
  Set Printing Width 10000.

  Redirect "log" Print montred256.
(*
montred256 = fun var : type -> Type => (λ x : var (type.type_primitive type.Z * type.type_primitive type.Z)%ctype,
    expr_let x0 := 79228162514264337593543950337 *₂₅₆ (uint128)(x₁ >> 128) in
    expr_let x1 := 340282366841710300986003757985643364352 *₂₅₆ ((uint128)(x₁) & 340282366920938463463374607431768211455) in
    expr_let x2 := 79228162514264337593543950337 *₂₅₆ ((uint128)(x₁) & 340282366920938463463374607431768211455) in
    expr_let x3 := ADD_256 ((uint256)(((uint128)(x1) & 340282366920938463463374607431768211455) << 128), x2) in
    expr_let x4 := ADD_256 ((uint256)(((uint128)(x0) & 340282366920938463463374607431768211455) << 128), x3₁) in
    expr_let x5 := 79228162514264337593543950335 *₂₅₆ ((uint128)(x4₁) & 340282366920938463463374607431768211455) in
    expr_let x6 := 79228162514264337593543950335 *₂₅₆ (uint128)(x4₁ >> 128) in
    expr_let x7 := 340282366841710300967557013911933812736 *₂₅₆ ((uint128)(x4₁) & 340282366920938463463374607431768211455) in
    expr_let x8 := 340282366841710300967557013911933812736 *₂₅₆ (uint128)(x4₁ >> 128) in
    expr_let x9 := ADD_256 ((uint256)(((uint128)(x7) & 340282366920938463463374607431768211455) << 128), x5) in
    expr_let x10 := ADDC_256 (x9₂, (uint128)(x7 >> 128), x8) in
    expr_let x11 := ADD_256 ((uint256)(((uint128)(x6) & 340282366920938463463374607431768211455) << 128), x9₁) in
    expr_let x12 := ADDC_256 (x11₂, (uint128)(x6 >> 128), x10₁) in
    expr_let x13 := ADD_256 (x11₁, x₁) in
    expr_let x14 := ADDC_256 (x13₂, x12₁, x₂) in
    expr_let x15 := SELC (x14₂, 0, 115792089210356248762697446949407573530086143415290314195533631308867097853951) in
    expr_let x16 := SUB_256 (x14₁, x15) in
    ADDM (x16₁, 0, 115792089210356248762697446949407573530086143415290314195533631308867097853951))%expr
     : Expr (type.uncurry (type.type_primitive type.Z * type.type_primitive type.Z -> type.type_primitive type.Z))
*)

  Import PreFancy.
  Import PreFancy.Notations.
  Local Notation "'RegMod'" := (Straightline.expr.Primitive (t:=type.Z) 115792089210356248762697446949407573530086143415290314195533631308867097853951).
  Local Notation "'RegPInv'" := (Straightline.expr.Primitive (t:=type.Z) 115792089210356248768974548684794254293921932838497980611635986753331132366849).
  Redirect "log" Print montred256_prefancy.
  (*
   mulhl@(y0, RegPInv, $x₁);
   mulll@(y1, RegPInv, $x₁);
   add@(y2, $y1, $y0, 128);
   add@(y3, $y2, $y, 128);
   mulll@(y4, RegMod, $y3);
   mullh@(y5, RegMod, $y3);
   mulhl@(y6, RegMod, $y3);
   mulhh@(y7, RegMod, $y3);
   add@(y8, $y4, $y6, 128);
   addc@(y9, carry{$y8}, $y7, $y6, -128);
   add@(y10, $y8, $y5, 128);
   addc@(y11, carry{$y10}, $y9, $y5, -128);
   add@(y12, $y10, $x₁, 0);
   addc@(y13, carry{$y12}, $y11, $x₂, 0);
   selc@(y14, carry{$y13}, RegZero, RegMod);
   sub@(y15, $y13, $y14, 0);
   addm@(y16, $y15, RegZero, RegMod);
   ret $y16
  *)

End Montgomery256.

Local Notation "i rd x y ; cont" := (Fancy.Instr i rd (x, y) cont) (at level 40, cont at level 200, format "i  rd  x  y ; '//' cont").
Local Notation "i rd x y z ; cont" := (Fancy.Instr i rd (x, y, z) cont) (at level 40, cont at level 200, format "i  rd  x  y  z ; '//' cont").

Import Fancy.Registers.
Import Fancy.

Import Barrett256 Montgomery256.

(*** Montgomery Reduction ***)

(* Status: Code in final form is proven correct modulo admits in compiler portions. *)

(* Montgomery Code : *)
Redirect "log" Eval cbv beta iota delta [Prod.MontRed256 Prod.Mul256 Prod.Mul256x256] in Prod.MontRed256.
(*
     = fun lo hi y t1 t2 scratch RegPInv : register =>
       MUL128LL y lo RegPInv;
       MUL128UL t1 lo RegPInv;
       ADD 128 y y t1;
       MUL128LU t1 lo RegPInv;
       ADD 128 y y t1;
       MUL128LL t1 y RegMod;
       MUL128UU t2 y RegMod;
       MUL128UL scratch y RegMod;
       ADD 128 t1 t1 scratch;
       ADDC (-128) t2 t2 scratch;
       MUL128LU scratch y RegMod;
       ADD 128 t1 t1 scratch;
       ADDC (-128) t2 t2 scratch;
       ADD 0 lo lo t1;
       ADDC 0 hi hi t2;
       SELC y RegMod RegZero;
       SUB 0 lo hi y;
       ADDM lo lo RegZero RegMod;
       Ret lo
 *)

(* Uncomment to see proof statement and remaining admitted statements,
or search for "prod_montred256_correct" to see comments on the proof
preconditions. *)
(*
Check Montgomery256.prod_montred256_correct.
Print Assumptions Montgomery256.prod_montred256_correct.
*)

(*** Barrett Reduction ***)

(* Status: Code is proven correct modulo admits in compiler
portions. However, unlike for Montgomery, this code is not proven
equivalent to the register-allocated and efficiently-scheduled
reference (Prod.MulMod). This proof is currently admitted and would
require either fiddling with code generation to make instructions come
out in the right order or reasoning about which instructions
commute. *)

(* Barrett reference code: *)
Redirect "log" Eval cbv beta iota delta [Prod.MulMod Prod.Mul256x256] in Prod.MulMod.
(*
     = fun x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5 : register =>
       let q1Bottom256 := scratchp1 in
       let muSelect := scratchp2 in
       let q2 := scratchp3 in
       let q2High := scratchp4 in
       let q2High2 := scratchp5 in
       let q3 := scratchp1 in
       let r2 := scratchp2 in
       let r2High := scratchp3 in
       let maybeM := scratchp1 in
       SELM muSelect RegMuLow RegZero;
       RSHI 255 q1Bottom256 xHigh x;
       MUL128LL q2 q1Bottom256 RegMuLow;
       MUL128UU q2High q1Bottom256 RegMuLow;
       MUL128UL scratchp5 q1Bottom256 RegMuLow;
       ADD 128 q2 q2 scratchp5;
       ADDC (-128) q2High q2High scratchp5;
       MUL128LU scratchp5 q1Bottom256 RegMuLow;
       ADD 128 q2 q2 scratchp5;
       ADDC (-128) q2High q2High scratchp5;
       RSHI 255 q2High2 RegZero xHigh;
       ADD 0 q2High q2High q1Bottom256;
       ADDC 0 q2High2 q2High2 RegZero;
       ADD 0 q2High q2High muSelect;
       ADDC 0 q2High2 q2High2 RegZero;
       RSHI 1 q3 q2High2 q2High;
       MUL128LL r2 RegMod q3;
       MUL128UU r2High RegMod q3;
       MUL128UL scratchp4 RegMod q3;
       ADD 128 r2 r2 scratchp4;
       ADDC (-128) r2High r2High scratchp4;
       MUL128LU scratchp4 RegMod q3;
       ADD 128 r2 r2 scratchp4;
       ADDC (-128) r2High r2High scratchp4;
       SUB 0 muSelect x r2;
       SUBC 0 xHigh xHigh r2High;
       SELL maybeM RegMod RegZero;
       SUB 0 q3 muSelect maybeM;
       ADDM x q3 RegZero RegMod;
       Ret x
 *)

(* Barrett generated code (equivalence with reference admitted) *)
Redirect "log" Eval cbv beta iota delta [barrett_red256_alloc] in barrett_red256_alloc.
(*
     = fun (xLow xHigh RegMuLow : register) (_ : positive) (_ : register) =>
       SELM r2 RegMuLow RegZero;
       RSHI 255 r3 RegZero xHigh;
       RSHI 255 r4 xHigh xLow;
       MUL128UU r5 RegMuLow r4;
       MUL128UL r6 r4 RegMuLow;
       MUL128LU r7 r4 RegMuLow;
       MUL128LL r8 RegMuLow r4;
       ADD 128 r9 r8 r7;
       ADDC (-128) r10 r5 r7;
       ADD 128 r5 r9 r6;
       ADDC (-128) r11 r10 r6;
       ADD 0 r6 r4 r11;
       ADDC 0 r12 RegZero r3;
       ADD 0 r13 r2 r6;
       ADDC 0 r14 RegZero r12;
       RSHI 1 r15 r14 r13;
       MUL128UU r16 RegMod r15;
       MUL128LU r17 r15 RegMod;
       MUL128UL r18 r15 RegMod;
       MUL128LL r19 RegMod r15;
       ADD 128 r20 r19 r18;
       ADDC (-128) r21 r16 r18;
       ADD 128 r22 r20 r17;
       ADDC (-128) r23 r21 r17;
       SUB 0 r24 xLow r22;
       SUBC 0 r25 xHigh r23;
       SELL r26 RegMod RegZero;
       SUB 0 r27 r24 r26;
       ADDM r28 r27 RegZero RegMod;
       Ret r28
 *)

(* Uncomment to see proof statement and remaining admitted statements. *)
(*
Check prod_barrett_red256_correct.
Print Assumptions prod_barrett_red256_correct.
(* The equivalence with generated code is admitted as barrett_red256_alloc_equivalent. *)
*)
