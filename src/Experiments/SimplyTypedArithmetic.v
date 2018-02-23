(* Following http://adam.chlipala.net/theses/andreser.pdf chapter 3 *)
Require Import Coq.ZArith.ZArith Coq.micromega.Lia Crypto.Algebra.Nsatz.
Require Import Coq.Strings.String.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.derive.Derive.
Require Import Crypto.Util.Tactics.UniquePose Crypto.Util.Decidable.
Require Import Crypto.Util.Tuple Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.NatUtil.
Require Import QArith.QArith_base QArith.Qround Crypto.Util.QUtil.
Require Import Crypto.Algebra.Ring Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.Tactics.RunTacticAsConstr.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.ZUtil.Definitions.
Import ListNotations. Local Open Scope Z_scope.

Module Associational.
  Definition eval (p:list (Z*Z)) : Z :=
    fold_right (fun x y => x + y) 0%Z (map (fun t => fst t * snd t) p).

  Lemma eval_nil : eval nil = 0.
  Proof. trivial.                                             Qed.
  Lemma eval_cons p q : eval (p::q) = fst p * snd p + eval q.
  Proof. trivial.                                             Qed.
  Lemma eval_app p q: eval (p++q) = eval p + eval q.
  Proof. induction p; rewrite <-?List.app_comm_cons;
           rewrite ?eval_nil, ?eval_cons; nsatz.              Qed.

  Hint Rewrite eval_nil eval_cons eval_app : push_eval.
  Local Ltac push := autorewrite with
      push_eval push_map push_partition push_flat_map
      push_fold_right push_nth_default cancel_pair.

  Lemma eval_map_mul (a x:Z) (p:list (Z*Z))
  : eval (List.map (fun t => (a*fst t, x*snd t)) p) = a*x*eval p.
  Proof. induction p; push; nsatz.                            Qed.
  Hint Rewrite eval_map_mul : push_eval.

  Definition mul (p q:list (Z*Z)) : list (Z*Z) :=
    flat_map (fun t =>
      map (fun t' =>
        (fst t * fst t', snd t * snd t'))
    q) p.
  Lemma eval_mul p q : eval (mul p q) = eval p * eval q.
  Proof. induction p; cbv [mul]; push; nsatz.                 Qed.
  Hint Rewrite eval_mul : push_eval.

  Definition negate_snd (p:list (Z*Z)) : list (Z*Z) :=
    map (fun cx => (fst cx, -snd cx)) p.
  Lemma eval_negate_snd p : eval (negate_snd p) = - eval p.
  Proof. induction p; cbv [negate_snd]; push; nsatz.          Qed.
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
  Proof. cbv [Let_In split]; induction p;
    repeat match goal with
    | |- context[?a/?b] =>
      unique pose proof (Z_div_exact_full_2 a b ltac:(trivial) ltac:(trivial))
    | _ => progress push
    | _ => progress break_match
    | _ => progress nsatz                                end. Qed.

  Lemma reduction_rule a b s c (modulus_nz:s-c<>0) :
    (a + s * b) mod (s - c) = (a + c * b) mod (s - c).
  Proof. replace (a + s * b) with ((a + c*b) + b*(s-c)) by nsatz.
    rewrite Z.add_mod,Z_mod_mult,Z.add_0_r,Z.mod_mod;trivial. Qed.

  Definition reduce (s:Z) (c:list _) (p:list _) : list (Z*Z) :=
    let lo_hi := split s p in fst lo_hi ++ mul c (snd lo_hi).

  Lemma eval_reduce s c p (s_nz:s<>0) (modulus_nz:s-eval c<>0) :
    eval (reduce s c p) mod (s - eval c) = eval p mod (s - eval c).
  Proof. cbv [reduce]; push.
         rewrite <-reduction_rule, eval_split; trivial.      Qed.
  Hint Rewrite eval_reduce : push_eval.

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
End Associational.

Module Positional. Section Positional.
  Context (weight : nat -> Z)
          (weight_0 : weight 0%nat = 1)
          (weight_nz : forall i, weight i <> 0).

  Definition to_associational (n:nat) (xs:list Z) : list (Z*Z)
    := combine (map weight (List.seq 0 n)) xs.
  Definition eval n x := Associational.eval (@to_associational n x).
  Lemma eval_to_associational n x :
    Associational.eval (@to_associational n x) = eval n x.
  Proof. trivial.                                             Qed.
  Hint Rewrite @eval_to_associational : push_eval.
  Lemma eval_nil n : eval n [] = 0.
  Proof. cbv [eval to_associational]. rewrite combine_nil_r. reflexivity. Qed.
  Hint Rewrite eval_nil : push_eval.
  Lemma eval0 p : eval 0 p = 0.
  Proof. cbv [eval to_associational]. reflexivity. Qed.
  Hint Rewrite eval0 : push_eval.

  Lemma eval_snoc n m x y : n = length x -> m = S n -> eval m (x ++ [y]) = eval n x + weight n * y.
  Proof.
    cbv [eval to_associational]; intros; subst n m.
    rewrite seq_snoc, map_app.
    rewrite combine_app_samelength by distr_length.
    autorewrite with push_eval. simpl.
    autorewrite with push_eval cancel_pair; ring.
  Qed.

  (* SKIP over this: zeros, add_to_nth *)
  Local Ltac push := autorewrite with push_eval push_map distr_length
    push_flat_map push_fold_right push_nth_default cancel_pair natsimplify.
  Definition zeros n : list Z := List.repeat 0 n.
  Lemma length_zeros n : length (zeros n) = n. Proof. cbv [zeros]; distr_length. Qed.
  Hint Rewrite length_zeros : distr_length.
  Lemma eval_zeros n : eval n (zeros n) = 0.
  Proof.
    cbv [eval Associational.eval to_associational zeros].
    rewrite <- (seq_length n 0) at 2.
    generalize dependent (List.seq 0 n); intro xs.
    induction xs; simpl; nsatz.                               Qed.
  Definition add_to_nth i x (ls : list Z) : list Z
    := ListUtil.update_nth i (fun y => x + y) ls.
  Lemma length_add_to_nth i x ls : length (add_to_nth i x ls) = length ls.
  Proof. cbv [add_to_nth]; distr_length. Qed.
  Hint Rewrite length_add_to_nth : distr_length.
  Lemma eval_add_to_nth (n:nat) (i:nat) (x:Z) (xs:list Z) (H:(i<length xs)%nat)
        (Hn : length xs = n) (* N.B. We really only need [i < Nat.min n (length xs)] *) :
    eval n (add_to_nth i x xs) = weight i * x + eval n xs.
  Proof.
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
  Proof. induction n; cbv [place nat_rect] in *; break_match; autorewrite with cancel_pair; try omega. Qed.
  Lemma weight_place t i : weight (fst (place t i)) * snd (place t i) = fst t * snd t.
  Proof. induction i; cbv [place nat_rect] in *; break_match; push;
    repeat match goal with |- context[?a/?b] =>
      unique pose proof (Z_div_exact_full_2 a b ltac:(auto) ltac:(auto))
           end; nsatz.                                        Qed.
  Hint Rewrite weight_place : push_eval.

  Definition from_associational n (p:list (Z*Z)) :=
    List.fold_right (fun t ls =>
      let p := place t (pred n) in
      add_to_nth (fst p) (snd p) ls ) (zeros n) p.
  Lemma eval_from_associational n p (n_nz:n<>O \/ p = nil) :
    eval n (from_associational n p) = Associational.eval p.
  Proof. destruct n_nz; [ induction p | subst p ];
  cbv [from_associational] in *; push; try
  pose proof place_in_range a (pred n); try omega; try nsatz;
  apply fold_right_invariant; cbv [zeros add_to_nth];
  intros; rewrite ?map_length, ?List.repeat_length, ?seq_length, ?length_update_nth;
  try omega.                                                  Qed.
  Hint Rewrite @eval_from_associational : push_eval.
  Lemma length_from_associational n p : length (from_associational n p) = n.
  Proof. cbv [from_associational]. apply fold_right_invariant; intros; distr_length. Qed.
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
    Proof. cbv [mulmod]; push; trivial.
    destruct f, g; simpl in *; [ right; subst n | left; try omega.. ].
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
  Proof. cbv [add]; push; trivial. destruct n; auto.          Qed.
  Hint Rewrite @eval_add : push_eval.
  Lemma length_add n f g
        (Hf : length f = n) (Hg : length g = n) :
    length (add n f g) = n.
  Proof. clear -Hf Hf; cbv [add]; distr_length.               Qed.
  Hint Rewrite @length_add : distr_length.

  Section Carries.
    Definition carry n m (index:nat) (p:list Z) : list Z :=
      from_associational
        m (@Associational.carry (weight index)
                                (weight (S index) / weight index)
                                (to_associational n p)).

    Lemma length_carry n m index p : length (carry n m index p) = m.
    Proof. cbv [carry]; distr_length. Qed.
    Lemma eval_carry n m i p: (n <> 0%nat) -> (m <> 0%nat) ->
                              weight (S i) / weight i <> 0 ->
      eval m (carry n m i p) = eval n p.
    Proof.
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
    Proof. cbv [carry_reduce]; intros; push; auto.            Qed.
    Hint Rewrite @eval_carry_reduce : push_eval.
    Lemma length_carry_reduce n s c index p
      : length p = n -> length (carry_reduce n s c index p) = n.
    Proof. cbv [carry_reduce]; distr_length.                  Qed.
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
    Proof.
      intros; cbv [chained_carries]; induction (rev idxs) as [|x xs IHxs];
        cbn [fold_right]; distr_length.
    Qed. Hint Rewrite @length_chained_carries : distr_length.

    (* carries without modular reduction; useful for converting between bases *)
    Definition chained_carries_no_reduce n p (idxs : list nat) :=
      fold_right (fun a b => carry n n a b) p (rev idxs).
    Lemma eval_chained_carries_no_reduce n p idxs:
      (forall i, In i idxs -> weight (S i) / weight i <> 0) ->
      eval n (chained_carries_no_reduce n p idxs) = eval n p.
    Proof.
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
    Proof using Type*. cbv [encode]; intros; push; auto; f_equal; omega. Qed.
    Lemma length_encode n s c x
      : length (encode n s c x) = n.
    Proof. cbv [encode]; repeat distr_length.                 Qed.

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
    Proof.
      destruct (zerop n); subst; try reflexivity.
      intros; cbv [sub balance scmul negate_snd]; push; repeat distr_length;
        eauto with omega.
      push_Zmod; push; pull_Zmod; push_Zmod; pull_Zmod; distr_length; eauto.
    Qed.
    Hint Rewrite eval_sub : push_eval.
    Lemma length_sub a b
      : length a = n -> length b = n ->
        length (sub a b) = n.
    Proof. intros; cbv [sub balance scmul negate_snd]; repeat distr_length. Qed.
    Hint Rewrite length_sub : distr_length.
    Definition opp (a:list Z) : list Z
      := sub (zeros n) a.
    Lemma eval_opp
          (a:list Z)
      : (length a = n) ->
        (forall i, In i (seq 0 n) -> weight (S i) / weight i <> 0) ->
        eval n (opp a) mod (s - Associational.eval c)
        = (- eval n a) mod (s - Associational.eval c).
    Proof. intros; cbv [opp]; push; distr_length; auto.       Qed.
    Lemma length_opp a
      : length a = n -> length (opp a) = n.
    Proof. cbv [opp]; intros; repeat distr_length.            Qed.
  End sub.
  Hint Rewrite @eval_opp @eval_sub : push_eval.
  Hint Rewrite @length_sub @length_opp : distr_length.

  Section mod_ops.
    Context (s : Z)
            (c : list (Z*Z))
            (n : nat)
            (len_c : nat)
            (idxs : list nat)
            (len_idxs : nat)
            (m_nz:s - Associational.eval c <> 0) (s_nz:s <> 0)
            (Hn_nz : n <> 0%nat)
            (Hc : length c = len_c)
            (Hidxs : length idxs = len_idxs)
            (Hw_div_nz : forall i : nat, weight (S i) / weight i <> 0).

    Derive carry_mulmod
           SuchThat (forall (fg : list Z * list Z)
                            (f := fst fg) (g := snd fg)
                            (Hf : length f = n)
                            (Hg : length g = n),
                        (eval n (carry_mulmod fg)) mod (s - Associational.eval c)
                        = (eval n f * eval n g) mod (s - Associational.eval c))
           As eval_carry_mulmod.
    Proof.
      intros.
      rewrite <-eval_mulmod with (s:=s) (c:=c) by auto.
      etransitivity;
        [ | rewrite <- @eval_chained_carries with (s:=s) (c:=c) (idxs:=idxs)
            by auto; reflexivity ].
      eapply f_equal2; [|trivial]. eapply f_equal.
      expand_lists ().
      subst f g carry_mulmod; reflexivity.
    Qed.

    Derive carrymod
           SuchThat (forall (f : list Z)
                            (Hf : length f = n),
                        (eval n (carrymod f)) mod (s - Associational.eval c)
                        = (eval n f) mod (s - Associational.eval c))
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
           SuchThat (forall (fg: list Z * list Z)
                            (f := fst fg) (g := snd fg)
                            (Hf : length f = n)
                            (Hg : length g = n),
                        (eval n (addmod fg)) mod (s - Associational.eval c)
                        = (eval n f + eval n g) mod (s - Associational.eval c))
           As eval_addmod.
    Proof.
      intros.
      rewrite <-eval_add by assumption.
      eapply f_equal2; [|trivial]. eapply f_equal.
      expand_lists ().
      subst f g addmod; reflexivity.
    Qed.

    Derive submod
           SuchThat (forall (coef:Z)
                            (fg: list Z * list Z)
                            (f := fst fg) (g := snd fg)
                            (Hf : length f = n)
                            (Hg : length g = n),
                        (eval n (submod coef fg)) mod (s - Associational.eval c)
                        = (eval n f - eval n g) mod (s - Associational.eval c))
           As eval_submod.
    Proof.
      intros.
      rewrite <-eval_sub with (coef:=coef) by auto.
      eapply f_equal2; [|trivial]. eapply f_equal.
      expand_lists ().
      subst f g submod; reflexivity.
    Qed.

    Derive oppmod
           SuchThat (forall (coef:Z)
                            (f: list Z)
                            (Hf : length f = n),
                        (eval n (oppmod coef f)) mod (s - Associational.eval c)
                        = (- eval n f) mod (s - Associational.eval c))
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
                        (eval n (encodemod f)) mod (s - Associational.eval c)
                        = f mod (s - Associational.eval c))
           As eval_encodemod.
    Proof.
      intros.
      etransitivity.
      2:rewrite <-@eval_encode with (n:=n) by auto; reflexivity.
      eapply f_equal2; [|trivial]. eapply f_equal.
      expand_lists ().
      subst encodemod; reflexivity.
    Qed.
  End mod_ops.
End Positional. End Positional.

Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.

Module BaseConversion.
  Import Positional.
  Section BaseConversion.
    Context (sw dw : nat -> Z) (* source/destination weight functions *)
            (dw_0 : dw 0%nat = 1)
            (dw_nz : forall i, dw i <> 0).
    Context (dw_divides : forall i : nat, dw (S i) / dw i > 0).

    Definition convert_bases (sn dn : nat) (p : list Z) : list Z :=
      let p' := Positional.from_associational dw dn (Positional.to_associational sw sn p) in
      chained_carries_no_reduce dw dn p' (seq 0 (pred dn)).

    Lemma eval_convert_bases sn dn p :
      (dn <> 0%nat) -> length p = sn ->
      eval dw dn (convert_bases sn dn p) = eval sw sn p.
    Proof.
      cbv [convert_bases]; intros.
      rewrite eval_chained_carries_no_reduce; auto using ZUtil.Z.positive_is_nonzero.
      rewrite eval_from_associational; auto.
    Qed.

  End BaseConversion.
End BaseConversion.

(* Non-CPS version of Arithmetic/Saturated/MulSplit.v *)
Module MulSplit.
  Module Associational.
    Section Associational.

      Definition sat_multerm s (t t' : (Z * Z)) : list (Z * Z) :=
        dlet_nd xy := Z.mul_split s (snd t) (snd t') in
        [(fst t * fst t', fst xy); (fst t * fst t' * s, snd xy)].

      Definition sat_mul s (p q : list (Z * Z)) : list (Z * Z) :=
        flat_map (fun t => flat_map (sat_multerm s t) q) p.

      Lemma eval_map_sat_multerm s a q (s_nonzero:s<>0):
        Associational.eval (flat_map (sat_multerm s a) q) = fst a * snd a * Associational.eval q.
      Proof.
        cbv [sat_multerm Let_In]; induction q;
          repeat match goal with
                 | _ => progress autorewrite with cancel_pair push_eval to_div_mod in *
                 | _ => progress simpl flat_map
                 | _ => rewrite IHq
                 | _ => rewrite Z.mod_eq by assumption
                 | _ => ring_simplify; omega
                 end.
      Qed.
      Hint Rewrite eval_map_sat_multerm using (omega || assumption) : push_eval.

      Lemma eval_sat_mul s p q (s_nonzero:s<>0):
        Associational.eval (sat_mul s p q) = Associational.eval p * Associational.eval q.
      Proof.
      cbv [sat_mul]; induction p; [reflexivity|].
      repeat match goal with
              | _ => progress (autorewrite with push_eval in * )
              | _ => progress simpl flat_map
              | _ => rewrite IHp
              | _ => ring_simplify; omega
              end.
      Qed.
      Hint Rewrite eval_sat_mul : push_eval.
    End Associational.
  End Associational.
End MulSplit.

Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Hints.PullPush.

Module Columns.
  Section Columns.
    Context (weight : nat->Z)
            {weight_0 : weight 0%nat = 1}
            {weight_nonzero : forall i, weight i <> 0}
            {weight_positive : forall i, weight i > 0}
            {weight_multiples : forall i, weight (S i) mod weight i = 0}
            {weight_divides : forall i : nat, weight (S i) / weight i > 0}.

    Definition eval n (x : list (list Z)) : Z := Positional.eval weight n (map sum x).

    Lemma eval_nil n : eval n [] = 0.
    Proof. cbv [eval]; simpl. apply Positional.eval_nil. Qed.
    Hint Rewrite eval_nil : push_eval.
    Lemma eval_snoc n x y : n = length x -> eval (S n) (x ++ [y]) = eval n x + weight n * sum y.
    Proof.
      cbv [eval]; intros; subst. rewrite map_app. simpl map.
      apply Positional.eval_snoc; distr_length.
    Qed.

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

    Lemma list_rect_to_match A (P:list A -> Type) (Pnil: P []) (PS: forall a tl, P (a :: tl)) ls :
      @list_rect A P Pnil (fun a tl _ => PS a tl) ls = match ls with
                                                       | cons a tl => PS a tl
                                                       | nil => Pnil
                                                       end.
    Proof. destruct ls; reflexivity. Qed.

    Lemma flatten_column_mod fw (xs : list Z) :
      fst (flatten_column fw xs)  = sum xs mod fw.
    Proof.
      induction xs; simpl flatten_column; cbv [Let_In];
        repeat match goal with
               | _ => progress autorewrite with cancel_pair to_div_mod pull_Zmod
               | _ => rewrite IHxs
               | |- context [list_rect _ _ _ ?ls] =>
                 rewrite list_rect_to_match; destruct ls
               | _ => progress (rewrite ?sum_cons, ?sum_nil in * )
               | _ => progress break_match; try discriminate
               | _ => reflexivity
               | _ => f_equal; ring
               end.
    Qed. Hint Rewrite flatten_column_mod : to_div_mod.

    Lemma flatten_column_div fw (xs : list Z) (fw_nz : fw <> 0) :
      snd (flatten_column fw xs)  = sum xs / fw.
    Proof.
      induction xs; simpl flatten_column; cbv [Let_In];
        repeat match goal with
               | _ => progress autorewrite with cancel_pair to_div_mod pull_Zmod
               | _ => rewrite IHxs
               | |- context [list_rect _ _ _ ?ls] =>
                 rewrite list_rect_to_match; destruct ls
               | _ => rewrite <-Z.div_add_mod_cond_r by auto
               | _ => progress (rewrite ?sum_cons, ?sum_nil in * )
               | _ => progress break_match; try discriminate
               | _ => reflexivity
               | _ => f_equal; ring
               end.
    Qed. Hint Rewrite flatten_column_div using auto with zarith : to_div_mod.

    (* helper for some of the modular logic in flatten *)
    Lemma flatten_mod_step a b c d: 0 < a -> 0 < b ->
      c mod a + a * ((c / a + d) mod b) = (a * d + c) mod (a * b).
    Proof.
      clear. rewrite Z.add_comm.
      intros Ha Hb. assert (a <= a * b) by (apply Z.le_mul_diag_r; omega).
      pose proof (Z.mod_pos_bound c a Ha).
      pose proof (Z.mod_pos_bound (c/a+d) b Hb).
      apply Z.small_mod_eq.
      { rewrite <-(Z.mod_small (c mod a) (a * b)) by omega.
        rewrite <-Z.mul_mod_distr_l with (c:=a) by omega.
        rewrite Z.mul_add_distr_l, Z.mul_div_eq, <-Z.add_mod_full by omega.
        f_equal; ring. }
      { split; [zero_bounds|].
        apply Z.lt_le_trans with (m:=a*(b-1)+a); [|ring_simplify; omega].
        apply Z.add_le_lt_mono; try apply Z.mul_le_mono_nonneg_l; omega. }
    Qed.

    Lemma flatten_div_step a b c d : 0 < a -> 0 < b ->
      (c / a + d) / b = (a * d + c) / (a * b).
    Proof.
      clear. intros Ha Hb.
      rewrite <-Z.div_div by omega.
      rewrite Z.div_add_l' by omega.
      f_equal; ring.
    Qed.

    Hint Rewrite Positional.eval_nil : push_eval.

    Lemma flatten_length inp : length (fst (flatten inp)) = length inp.
    Proof.
      cbv [flatten].
      unfold flatten_step; fold flatten_step.
      induction inp using rev_ind; [reflexivity|].
      repeat match goal with
             | _ => progress autorewrite with list cancel_pair push_fold_right
             | _ => progress (unfold flatten_step; fold flatten_step)
             | _ => progress cbv [Let_In]
             | _ => solve [distr_length]
             end.
    Qed.
    Hint Rewrite flatten_length : distr_length.

    Lemma flatten_div_mod n inp :
      length inp = n ->
      (Positional.eval weight n (fst (flatten inp))
       = (eval n inp) mod (weight n))
        /\ (snd (flatten inp) = eval n inp / weight n).
    Proof.
      (* to make the invariant take the right form, we make everything depend on output length, not input length *)
      intro. subst n. rewrite <-(flatten_length inp). cbv [flatten].
      unfold flatten_step; fold flatten_step.
      induction inp using rev_ind;
        repeat match goal with
               | _ => progress intros
               | H: _ = ?x mod ?y /\ _ = ?x / ?y |- _ => destruct H as [IHmod IHdiv]
               | _ => split
               | _ => rewrite Nat.add_1_r
               | _ => erewrite Positional.eval_snoc by reflexivity
               | _ => rewrite IHmod
               | _ => rewrite IHdiv
               | _ => rewrite sum_cons
               | _ => rewrite eval_snoc by (rewrite <-(flatten_length inp); reflexivity)
               | _ => rewrite flatten_mod_step by auto using Z.gt_lt
               | _ => rewrite flatten_div_step by auto using Z.gt_lt
               | _ => rewrite Z.mul_div_eq_full by auto
               | _ => rewrite weight_multiples
               | _ => progress (unfold flatten_step; fold flatten_step)
               | _ => progress cbv [Let_In]
               | _ => progress autorewrite with list cancel_pair distr_length to_div_mod push_fold_right
               | _ => f_equal; ring
               end.
    Qed.

    Lemma flatten_mod {n} inp :
      length inp = n ->
      (Positional.eval weight n (fst (flatten inp)) = (eval n inp) mod (weight n)).
    Proof. intro. apply (proj1 (flatten_div_mod n inp ltac:(assumption))). Qed.
    Hint Rewrite @flatten_mod : push_eval.

    Lemma flatten_div {n} inp :
      length inp = n -> snd (flatten inp) = eval n inp / weight n.
    Proof. intro. apply (proj2 (flatten_div_mod n inp ltac:(assumption))). Qed.
    Hint Rewrite @flatten_div : push_eval.

    (* nils *)
    Definition nils n : list (list Z) := List.repeat nil n.
    Lemma length_nils n : length (nils n) = n. Proof. cbv [nils]. distr_length. Qed.
    Hint Rewrite length_nils : distr_length.
    Lemma eval_nils n : eval n (nils n) = 0.
    Proof.
      erewrite <-Positional.eval_zeros by eauto.
      cbv [eval nils]; rewrite List.map_repeat; reflexivity.
    Qed. Hint Rewrite eval_nils : push_eval.

    (* cons_to_nth *)
    Definition cons_to_nth i x (xs : list (list Z)) : list (list Z) :=
      ListUtil.update_nth i (fun y => cons x y) xs.
    Lemma length_cons_to_nth i x xs : length (cons_to_nth i x xs) = length xs.
    Proof. cbv [cons_to_nth]. distr_length. Qed.
    Hint Rewrite length_cons_to_nth : distr_length.
    Lemma cons_to_nth_add_to_nth xs : forall i x,
      map sum (cons_to_nth i x xs) = Positional.add_to_nth i x (map sum xs).
    Proof.
      cbv [cons_to_nth]; induction xs as [|? ? IHxs];
        intros i x; destruct i; simpl; rewrite ?IHxs; reflexivity.
    Qed.
    Lemma eval_cons_to_nth n i x xs : (i < length xs)%nat -> length xs = n ->
      eval n (cons_to_nth i x xs) = weight i * x + eval n xs.
    Proof using Type.
      cbv [eval]; intros. rewrite cons_to_nth_add_to_nth.
      apply Positional.eval_add_to_nth; distr_length.
    Qed. Hint Rewrite eval_cons_to_nth using omega : push_eval.

    (* from_associational *)
    Definition from_associational n (p:list (Z*Z)) : list (list Z) :=
      List.fold_right (fun t ls =>
        let p := Positional.place weight t (pred n) in
        cons_to_nth (fst p) (snd p) ls ) (nils n) p.
    Lemma length_from_associational n p : length (from_associational n p) = n.
    Proof. cbv [from_associational]. apply fold_right_invariant; intros; distr_length. Qed.
    Hint Rewrite length_from_associational: distr_length.
    Lemma eval_from_associational n p (n_nonzero:n<>0%nat\/p=nil):
      eval n (from_associational n p) = Associational.eval p.
    Proof.
      erewrite <-Positional.eval_from_associational by eauto. induction p.
      { simpl. autorewrite with push_eval. rewrite Positional.eval_zeros; auto. }
      { pose proof (length_from_associational n p).
        cbv [from_associational] in *. destruct n_nonzero; try congruence; [ ].
        simpl. rewrite eval_cons_to_nth, Positional.eval_add_to_nth;
                 rewrite ?Positional.length_from_associational;
        try match goal with |- context [Positional.place _ ?x ?n] =>
                        pose proof (Positional.weight_place weight ltac:(assumption) ltac:(assumption) x n);
                          pose proof (Positional.place_in_range weight x n); rewrite Nat.succ_pred in * by auto
            end; auto; try omega.
        rewrite IHp by tauto. ring. }
    Qed.

    Lemma flatten_snoc x inp : flatten (inp ++ [x]) = flatten_step x (flatten inp).
    Proof. cbv [flatten]. rewrite rev_unit. reflexivity. Qed.

    Lemma weight_multiples_full j : forall i, (i <= j)%nat -> weight j mod weight i = 0.
    Proof.
      induction j; intros; [replace i with 0%nat by omega
                           | destruct (dec (i <= j)%nat); [ rewrite (Z.div_mod (weight (S j)) (weight j)) by auto
                                                          | replace i with (S j) by omega ] ];
      repeat match goal with
             | _ => rewrite weight_0
             | _ => rewrite weight_multiples
             | _ => rewrite IHj by omega
             | _ => progress autorewrite with push_Zmod zsimplify
             | _ => reflexivity
             end.
    Qed.

    (* TODO: move to ZUtil *)
    Lemma Z_divide_div_mul_exact' a b c : b <> 0 -> (b | a) -> a * c / b = c * (a / b).
    Proof. intros. rewrite Z.mul_comm. auto using Z.divide_div_mul_exact. Qed.

    Lemma flatten_partitions inp:
      forall n i, length inp = n -> (i < n)%nat ->
                  nth_default 0 (fst (flatten inp)) i = (((eval n inp) / weight i)) mod (weight (S i) / weight i).
    Proof.
      induction inp using rev_ind; distr_length; intros.
      { cbn.
        autorewrite with push_eval push_nth_default zsimplify.
        reflexivity. }
      {
        destruct n as [| n]; [omega|].
        rewrite flatten_snoc, eval_snoc by omega.
        cbv [flatten_step Let_In]. cbn [fst].
        rewrite nth_default_app.
        break_match; distr_length.
        { rewrite IHinp with (n:=n) by omega.
          rewrite (Z.div_mod (weight n) (weight i)) by auto.
          rewrite weight_multiples_full by omega.
          rewrite (Z.div_mod (weight n) (weight (S i))) by auto.
          rewrite weight_multiples_full by omega.
          autorewrite with zsimplify.
          repeat match goal with
                 | _ => rewrite Z_divide_div_mul_exact' by (try apply Z.mod_divide; auto)
                 | |- context [ (_ + ?a * ?b * ?c) / ?a ] =>
                   replace (a * b * c) with (a * (b * c)) by ring;
                     rewrite Z.div_add' by auto
                 | |- context [ (_ + ?a * ?b * ?c) mod ?b ] =>
                   replace (a * b * c) with (a * c * b) by ring;
                     rewrite Z.mod_add by auto using ZUtil.Z.positive_is_nonzero
                 | _ => reflexivity
                 end.
        }
        { repeat match goal with
                 | _ => progress replace (Datatypes.length inp) with n by omega
                 | _ => progress replace i with n by omega
                 | _ => rewrite nth_default_cons
                 | _ => rewrite sum_cons
                 | _ => rewrite flatten_column_mod
                 | _ => erewrite flatten_div by eauto
                 | _ => progress autorewrite with natsimplify
                 end.
          rewrite Z.div_add' by auto.
          reflexivity. } }
    Qed.

    Section mul.
      Definition mul s n m (p q : list Z) : list Z :=
        let p_a := Positional.to_associational weight n p in
        let q_a := Positional.to_associational weight n q in
        let pq_a := MulSplit.Associational.sat_mul s p_a q_a in
        fst (flatten (from_associational m pq_a)).
    End mul.
  End Columns.

  Section mul_converted.
      Context (w w' : nat -> Z).
      Context (w'_0 : w' 0%nat = 1)
              (w'_nonzero : forall i, w' i <> 0)
              (w'_positive : forall i, w' i > 0)
              (w'_divides : forall i : nat, w' (S i) / w' i > 0).
      Context (w_0 : w 0%nat = 1)
              (w_nonzero : forall i, w i <> 0)
              (w_positive : forall i, w i > 0)
              (w_multiples : forall i, w (S i) mod w i = 0)
              (w_divides : forall i : nat, w (S i) / w i > 0).

      (* takes in inputs in base w, converts to w', multiplies in that
         format, converts to w again, then flattens. *)
      Definition mul_converted
              n1 n2 (* lengths in original format *)
              m1 m2 (* lengths in converted format *)
              (n3 : nat) (* final length *)
              (idxs : list nat) (* carries to do -- this helps preemptively line up weights *)
              (p1 p2 : list Z) :=
      let p1' := BaseConversion.convert_bases w w' n1 m1 p1 in
      let p2' := BaseConversion.convert_bases w w' n2 m2 p2 in
      let p1_a := Positional.to_associational w' m1 p1' in
      let p2_a := Positional.to_associational w' m2 p2' in
      let p3_a := Associational.mul p1_a p2_a in
      (* important not to use Positional.carry here; we don't want to accumulate yet *)
      let p3'_a := fold_right (fun i acc => Associational.carry (w' i) (w' (S i) / w' i) acc) p3_a (rev idxs) in
      fst (flatten w (from_associational w n3 p3'_a)).

      Hint Rewrite
           @Columns.eval_from_associational
           @Associational.eval_carry
           @Associational.eval_mul
           @Positional.eval_to_associational
           @BaseConversion.eval_convert_bases using solve [auto using Z.positive_is_nonzero] : push_eval.

      Lemma eval_carries p idxs :
        Associational.eval (fold_right (fun i acc => Associational.carry (w' i) (w' (S i) / w' i) acc) p idxs) =
        Associational.eval p.
      Proof. apply fold_right_invariant; intros; autorewrite with push_eval; congruence. Qed.
      Hint Rewrite eval_carries: push_eval.

      Lemma eval_mul_converted n1 n2 m1 m2 n3 idxs p1 p2 (_:n3<>0%nat) (_:m1<>0%nat) (_:m2<>0%nat):
        length p1 = n1 -> length p2 = n2 ->
        0 <= (Positional.eval w n1 p1 * Positional.eval w n2 p2) < w n3 ->
        Positional.eval w n3 (mul_converted n1 n2 m1 m2 n3 idxs p1 p2) = (Positional.eval w n1 p1) * (Positional.eval w n2 p2).
      Proof.
        cbv [mul_converted]; intros.
        rewrite Columns.flatten_mod by auto using Columns.length_from_associational.
        autorewrite with push_eval. auto using Z.mod_small.
      Qed.
      Hint Rewrite eval_mul_converted : push_eval.

      Hint Rewrite @length_from_associational : distr_length.

      Lemma mul_converted_mod n1 n2 m1 m2 n3 idxs p1 p2  (_:n3<>0%nat) (_:m1<>0%nat) (_:m2<>0%nat):
        length p1 = n1 -> length p2 = n2 ->
        0 <= (Positional.eval w n1 p1 * Positional.eval w n2 p2) < w n3 ->
        nth_default 0 (mul_converted n1 n2 m1 m2 n3 idxs p1 p2) 0 = (Positional.eval w n1 p1 * Positional.eval w n2 p2) mod (w 1).
      Proof.
        intros; cbv [mul_converted].
        erewrite flatten_partitions by (auto; distr_length).
        autorewrite with distr_length push_eval natsimplify.
        rewrite w_0; autorewrite with zsimplify.
        reflexivity.
      Qed.

      Lemma mul_converted_div n1 n2 m1 m2 n3 idxs p1 p2:
        m1 <> 0%nat -> m2 <> 0%nat -> n3 = 2%nat ->
        length p1 = n1 -> length p2 = n2 ->
        0 <= Positional.eval w n1 p1  ->
        0 <= Positional.eval w n2 p2  ->
        0 <= (Positional.eval w n1 p1 * Positional.eval w n2 p2) < w n3 ->
        nth_default 0 (mul_converted n1 n2 m1 m2 n3 idxs p1 p2) 1 = (Positional.eval w n1 p1 * Positional.eval w n2 p2) / (w 1).
      Proof.
        intros; subst n3; cbv [mul_converted].
        erewrite flatten_partitions by (auto; distr_length).
        autorewrite with distr_length push_eval.
        pose proof (w_positive 1).
        apply Z.mod_small.
        split; [ solve[Z.zero_bounds] | ].
        apply Z.div_lt_upper_bound; [omega|].
        rewrite Z.mul_div_eq_full by auto.
        rewrite w_multiples. omega.
      Qed.

      (* shortcut definition for convert-mul-convert for cases when we are halving the bitwidth before multiplying. *)
      (* the most important feature here is the carries--we carry from all the odd indices after multiplying,
         thus pre-aligning everything with the double-size bitwidth *)
      Definition mul_converted_halve n n2 :=
        mul_converted n n n2 n2 n2 (map (fun x => 2*x + 1)%nat (seq 0 n)).

  End mul_converted.
End Columns.

Module Compilers.
  Module type.
    Variant primitive := unit | Z | nat | bool.
    Inductive type := type_primitive (_:primitive) | prod (A B : type) | arrow (s d : type) | list (A : type).
    Module Export Coercions.
      Global Coercion type_primitive : primitive >-> type.
    End Coercions.

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

    Fixpoint under_arrows (t : type) (f : type -> type) : type
      := match t with
         | type_primitive _ as t
         | prod _ _ as t
         | list _ as t
           => f t
         | arrow s d => arrow s (under_arrows d f)
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

      Module Export Notations.
        Bind Scope expr_scope with expr.
        Delimit Scope expr_scope with expr.

        Infix "@" := App : expr_scope.
        Infix "@@" := AppIdent : expr_scope.
        Notation "( x , y , .. , z )" := (Pair .. (Pair x%expr y%expr) .. z%expr) : expr_scope.
        Notation "( )" := TT : expr_scope.
        Notation "()" := TT : expr_scope.
        Notation "'λ'  x .. y , t" := (Abs (fun x => .. (Abs (fun y => t%expr)) ..)) : expr_scope.
      End Notations.

      Definition Expr {ident : type -> type -> Type} t := forall var, @expr ident var t.

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
          | Nat_mul : ident (nat * nat) nat
          | Nat_add : ident (nat * nat) nat
          | nil {t} : ident () (list t)
          | cons {t} : ident (t * list t) (list t)
          | fst {A B} : ident (A * B) A
          | snd {A B} : ident (A * B) B
          | bool_rect {T} : ident (T * T * bool) T
          | nat_rect {P} : ident (P * (nat * P -> P) * nat) P
          | list_rect {A P} : ident (P * (A * list A * P -> P) * list A) P
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
          | Z_add_with_get_carry : ident (Z * Z * Z * Z) (Z * Z)
          | Z_sub_get_borrow : ident (Z * Z * Z) (Z * Z)
          | Z_zselect : ident (Z * Z * Z) Z
          | Z_add_modulo : ident (Z * Z * Z) Z
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

          Definition interp {s d} (idc : ident s d) : type.interp s -> type.interp d
            := match idc in ident s d return type.interp s -> type.interp d with
               | primitive _ v => curry0 v
               | Let_In tx tC => curry2 (@LetIn.Let_In (type.interp tx) (fun _ => type.interp tC))
               | Nat_succ => Nat.succ
               | Nat_add => curry2 Nat.add
               | Nat_mul => curry2 Nat.mul
               | nil t => curry0 (@Datatypes.nil (type.interp t))
               | cons t => curry2 (@Datatypes.cons (type.interp t))
               | fst A B => @Datatypes.fst (type.interp A) (type.interp B)
               | snd A B => @Datatypes.snd (type.interp A) (type.interp B)
               | bool_rect T => curry3 (@Datatypes.bool_rect (fun _ => type.interp T))
               | nat_rect P => curry3_2 (@Datatypes.nat_rect (fun _ => type.interp P))
               | list_rect A P => curry3_3 (@Datatypes.list_rect (type.interp A) (fun _ => type.interp P))
               | pred => Nat.pred
               | List_length T => @List.length (type.interp T)
               | List_seq => curry2 List.seq
               | List_combine A B => curry2 (@List.combine (type.interp A) (type.interp B))
               | List_map A B => curry2 (@List.map (type.interp A) (type.interp B))
               | List_repeat A => curry2 (@List.repeat (type.interp A))
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
               | Z_add_with_get_carry => curry4 Z.add_with_get_carry_full
               | Z_sub_get_borrow => curry3 Z.sub_get_borrow_full
               | Z_zselect => curry3 Z.zselect
               | Z_add_modulo => curry3 Z.add_modulo
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
            | Nat.mul ?x ?y => mkAppIdent Nat_mul (x, y)
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
                 mkAppIdent (@ident.bool_rect rT) (Ptrue, Pfalse, b)
            | @Datatypes.nat_rect (fun _ => ?T) ?P0 (fun (n' : Datatypes.nat) Pn => ?PS) ?n
              => let rT := type.reify T in
                 let pat := fresh "pat" in (* fresh for COQBUG(https://github.com/coq/coq/issues/6562) *)
                 mkAppIdent (@ident.nat_rect rT) (P0,
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
                 mkAppIdent (@ident.list_rect rA rT) (Pnil,
                                                      (fun pat : A * Datatypes.list A * T
                                                       => let '(a, tl, Ptl) := pat in PS),
                                                      ls)
            | @Datatypes.list_rect ?A (fun _ => ?T) ?Pnil ?PS ?ls
              => let dummy := match goal with _ => fail 1 "list_rect successor case is not syntactically a function of three arguments:" PS end in
                 constr:(I : I)
            | Nat.pred ?x => mkAppIdent ident.pred x
            | @List.length ?A ?x =>
              let rA := type.reify A in
              mkAppIdent (@ident.List_length rA) x
            | List.seq ?x ?y  => mkAppIdent ident.List_seq (x, y)
            | @List.repeat ?A ?x ?y
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
            | Z.add_with_get_carry_full ?x ?y ?z ?a => mkAppIdent ident.Z_add_with_get_carry (x, y, z, a)
            | Z.sub_get_borrow_full ?x ?y ?z => mkAppIdent ident.Z_sub_get_borrow (x, y, z)
            | Z.zselect ?x ?y ?z => mkAppIdent ident.Z_zselect (x, y, z)
            | Z.add_modulo ?x ?y ?z => mkAppIdent ident.Z_add_modulo (x,y,z)
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
            Notation add_with_get_carry := Z_add_with_get_carry.
            Notation sub_get_borrow := Z_sub_get_borrow.
            Notation zselect := Z_zselect.
            Notation add_modulo := Z_add_modulo.
          End Z.

          Module Nat.
            Notation succ := Nat_succ.
            Notation add := Nat_add.
            Notation mul := Nat_mul.
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
          | Nat_mul : ident (nat * nat) nat
          | nil {t} : ident () (list t)
          | cons {t} : ident (t * list t) (list t)
          | fst {A B} : ident (A * B) A
          | snd {A B} : ident (A * B) B
          | bool_rect {T} : ident (T * T * bool) T
          | nat_rect {P} : ident (P * (nat * P -> P) * nat) P
          | pred : ident nat nat
          | list_rect {A P} : ident (P * (A * list A * P -> P) * list A) P
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
          | Z_add_with_get_carry : ident (Z * Z * Z * Z) (Z * Z)
          | Z_add_with_get_carry_concrete (s:BinInt.Z) : ident (Z * Z * Z) (Z * Z)
          | Z_sub_get_borrow : ident (Z * Z * Z) (Z * Z)
          | Z_sub_get_borrow_concrete (s:BinInt.Z) : ident (Z * Z) (Z * Z)
          | Z_zselect : ident (Z * Z * Z) Z
          | Z_add_modulo : ident (Z * Z * Z) Z
          | Z_cast (range : zrange) : ident Z Z
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

          Definition cast_outside_of_range (r : zrange) (v : BinInt.Z) : BinInt.Z.
          Proof. exact v. Qed.

          Definition interp {s d} (idc : ident s d) : type.interp s -> type.interp d
            := match idc in ident s d return type.interp s -> type.interp d with
               | primitive _ v => curry0 v
               | Let_In tx tC => curry2 (@LetIn.Let_In (type.interp tx) (fun _ => type.interp tC))
               | Nat_succ => Nat.succ
               | Nat_add => curry2 Nat.add
               | Nat_mul => curry2 Nat.mul
               | nil t => curry0 (@Datatypes.nil (type.interp t))
               | cons t => curry2 (@Datatypes.cons (type.interp t))
               | fst A B => @Datatypes.fst (type.interp A) (type.interp B)
               | snd A B => @Datatypes.snd (type.interp A) (type.interp B)
               | bool_rect T => curry3 (@Datatypes.bool_rect (fun _ => type.interp T))
               | nat_rect P => curry3_2 (@Datatypes.nat_rect (fun _ => type.interp P))
               | pred => Nat.pred
               | list_rect A P => curry3_23 (@Datatypes.list_rect (type.interp A) (fun _ => type.interp P))
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
               | Z_add_get_carry_concrete s => curry2 (Z.add_get_carry s)
               | Z_add_with_get_carry => curry4 Z.add_with_get_carry_full
               | Z_add_with_get_carry_concrete s => curry3 (Z.add_with_get_carry s)
               | Z_sub_get_borrow => curry3 Z.sub_get_borrow_full
               | Z_sub_get_borrow_concrete s => curry2 (Z.sub_get_borrow s)
               | Z_zselect => curry3 Z.zselect
               | Z_add_modulo => curry3 Z.add_modulo
               | Z_cast r => fun x => if (lower r <=? x) && (x <=? upper r)
                                      then x
                                      else cast_outside_of_range r x
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
            | Nat.mul ?x ?y => mkAppIdent Nat_mul (x, y)
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
                 mkAppIdent (@ident.bool_rect rT) (Ptrue, Pfalse, b)
            | @Datatypes.nat_rect (fun _ => ?T) ?P0 (fun (n' : Datatypes.nat) Pn => ?PS) ?n
              => let rT := type.reify T in
                 let pat := fresh "pat" in (* fresh for COQBUG(https://github.com/coq/coq/issues/6562) *)
                 mkAppIdent (@ident.nat_rect rT) (P0,
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
                            (Pnil,
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
            | Z.add_with_get_carry_full ?x ?y ?z ?a => mkAppIdent ident.Z_add_with_get_carry (x, y, z, a)
            | Z.sub_get_borrow_full ?x ?y ?z => mkAppIdent ident.Z_sub_get_borrow (x, y, z)
            | Z.zselect ?x ?y ?z => mkAppIdent ident.Z_zselect (x, y, z)
            | Z.add_modulo ?x ?y ?z => mkAppIdent ident.Z_add_modulo (x,y,z)
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
            Notation add_with_get_carry := Z_add_with_get_carry.
            Notation add_with_get_carry_concrete := Z_add_with_get_carry_concrete.
            Notation sub_get_borrow := Z_sub_get_borrow.
            Notation sub_get_borrow_concrete := Z_sub_get_borrow_concrete.
            Notation zselect := Z_zselect.
            Notation add_modulo := Z_add_modulo.
            Notation cast := Z_cast.
          End Z.

          Module Nat.
            Notation succ := Nat_succ.
            Notation add := Nat_add.
            Notation mul := Nat_mul.
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
             | for_reification.ident.Nat_mul
               => AppIdent ident.Nat_mul
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
             | for_reification.ident.Z_add_with_get_carry
               => AppIdent ident.Z.add_with_get_carry
             | for_reification.ident.Z_sub_get_borrow
               => AppIdent ident.Z.sub_get_borrow
             | for_reification.ident.Z_zselect
               => AppIdent ident.Z.zselect
             | for_reification.ident.Z_add_modulo
               => AppIdent ident.Z.add_modulo
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

    Definition invert_bool_rect P Q v1 v2 d (idc : ident (v1 * v2 * type.bool)%ctype d)
      : P v1
        -> Q v2
        -> option (P d * Q d)
      := match idc in ident.ident s d
               return (match s return Type with
                       | (v1 * v2 * type.bool)%ctype => P v1
                       | _ => unit
                       end
                       -> match s return Type with
                          | (v1 * v2 * type.bool)%ctype => Q v2
                          | _ => unit
                          end
                       -> option (P d * Q d))
         with
         | ident.bool_rect T => fun p q => Some (p, q)
         | _ => fun _ _ => None
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
  Proof.
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
          | App_bool_rect (Ptrue : expr) (Pfalse : expr) (b : var type.bool)
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

          Fixpoint interp (e : @expr ident (type.interp R) r) (k : type.interp R r -> R)
                   {struct e}
            : R
            := match e with
               | Halt v => k v
               | App A f x => f x
               | App_bool_rect Ptrue Pfalse b => bool_rect _ (interp Ptrue k) (interp Pfalse k) b
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
                (invert_bool_rect
                 : forall P Q v1 v2 d,
                    ident' (v1 * v2 * type.bool)%ctype d
                    -> P v1
                    -> Q v2
                    -> option (P d * Q d))
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
               | App_bool_rect Ptrue Pfalse b
                 => App_bool_rect (@splice Ptrue e2) (@splice Pfalse e2) b
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

        (** Note: We special-case [bool_rect] because reduction of the
            bodies of eliminators should block on the branching.  We
            would like to just write:
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
            hit exactly once. *)
        Fixpoint translate {t}
                 (e : @Compilers.Uncurried.expr.expr ident' var' t)
          : @Output.expr.expr ident var (type.translate t)
          := match e with
             | Var t v => Halt v
             | TT => x <- () ; Halt x
             | AppIdent s d idc args
               => let default
                      := (args' <-- @translate _ args;
                            k <- Output.expr.Abs (fun r => Halt r);
                            p <- (args', k);
                            f <- Output.expr.Ident (translate_ident s d idc);
                            f @ p) in
                  match args in Compilers.Uncurried.expr.expr t
                        return ident' t d
                               -> Output.expr.expr _
                               -> Output.expr.expr _
                  with
                  | Pair AB type.bool ab c
                    => match ab in Compilers.Uncurried.expr.expr t
                             return ident' (t * type.bool)%ctype d
                                    -> Output.expr.expr _
                                    -> Output.expr.expr _
                       with
                       | Pair A B a b
                         => fun idc default
                            => match invert_bool_rect
                                       (fun t => @Output.expr.expr ident var (type.translate t))
                                       (fun t => @Output.expr.expr ident var (type.translate t))
                                       A B d idc (@translate _ a) (@translate _ b) with
                               | Some (Ptrue, Pfalse)%core
                                 => (b' <-- @translate _ c;
                                       App_bool_rect Ptrue Pfalse b')
                               | None => default
                               end
                       | _ => fun _ default => default
                       end
                  | _ => fun _ default => default
                  end idc default
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
                 (invert_bool_rect
                  : forall P Q v1 v2 d,
                     ident' (v1 * v2 * type.bool)%ctype d
                     -> P v1
                     -> Q v2
                     -> option (P d * Q d))
                 (translate_ident : forall s d, ident' s d -> ident (type.translate (s -> d)))
                 {t} (e : @Compilers.Uncurried.expr.Expr ident' t)
        : @Output.expr.Expr ident (type.translate t)
        := fun var => translate invert_bool_rect translate_ident (e _).

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
                (isnd : forall A B, ident (A * B)%ctype B)
                (ibool_rect : forall A, ident (A * A * type.bool)%ctype A).

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
             | expr.App_bool_rect Ptrue Pfalse b
               => AppIdent (ibool_rect _) (call_with_continuation Ptrue k,
                                           call_with_continuation Pfalse k,
                                           b)
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
                 (ibool_rect : forall A, ident (A * A * type.bool)%ctype A)
                 {t} (e : @Output.expr.Expr ident' t)
                 (k : forall var, @Uncurried.expr.expr ident var (type.untranslate R t) -> @Uncurried.expr.expr ident var R)
        : @Compilers.Uncurried.expr.Expr ident R
        := fun var => call_with_continuation
                        (fun t idc => untranslate_ident t idc _) ifst isnd ibool_rect (e _) (k _).
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

      Definition interp {R} {t} (idc : ident t) : type.interp R t
        := match idc in ident t return type.interp R t with
           | wrap s d idc
             => fun '((x, k) : type.interp R (type.translate s) * (type.interp R (type.translate d) -> R))
                =>
                  match idc in Uncurried.expr.default.ident s d return type.interp R (type.translate s) -> (type.interp R (type.translate d) -> R) -> R with
                  | ident.primitive _ _ as idc
                  | ident.Nat_succ as idc
                  | ident.Nat_add as idc
                  | ident.Nat_mul as idc
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
                  | ident.Z_add_with_get_carry as idc
                  | ident.Z_sub_get_borrow as idc
                  | ident.Z_zselect as idc
                  | ident.Z_add_modulo as idc
                  | ident.Z_cast _ as idc
                    => cps_of (Uncurried.expr.default.ident.interp idc)
                  | ident.Z_mul_split_concrete s
                    => cps_of (curry2 (Z.mul_split s))
                  | ident.Z_add_get_carry_concrete s
                    => cps_of (curry2 (Z.add_get_carry s))
                  | ident.Z_add_with_get_carry_concrete s
                    => cps_of (curry3 (Z.add_with_get_carry s))
                  | ident.Z_sub_get_borrow_concrete s
                    => cps_of (curry2 (Z.sub_get_borrow s))
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
                               (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) type.interp R (type.translate T) * type.interp R (type.translate T) * bool)
                           k
                       => @Datatypes.bool_rect
                            (fun _ => R)
                            (k tc)
                            (k fc)
                            b
                  | ident.nat_rect P
                    => fun '((PO, PS, n) :
                               (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) interp R (type.translate P) * (nat * interp R (type.translate P) * (interp R (type.translate P) -> R) -> R) * nat)
                           k
                       => @Datatypes.nat_rect
                            (fun _ => (interp R (type.translate P) -> R) -> R)
                            (fun k => k PO)
                            (fun n' rec k
                             => rec (fun rec => PS (n', rec, k)))
                            n
                            k
                  | ident.list_rect A P
                    => fun '((Pnil, Pcons, ls) :
                               (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) interp R (type.translate P) * (interp R (type.translate A) * Datatypes.list (interp R (type.translate A)) * interp R (type.translate P) * (interp R (type.translate P) -> R) -> R) * Datatypes.list (interp R (type.translate A)))
                           k
                       => @Datatypes.list_rect
                            (interp R (type.translate A))
                            (fun _ => (interp R (type.translate P) -> R) -> R)
                            (fun k => k Pnil)
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
           => match idc in ident t return Compilers.Uncurried.expr.expr (type.untranslate _ t) with
              | wrap s d idc
                =>
                match idc in default.ident s d return Compilers.Uncurried.expr.expr (type.untranslate _ (type.translate (s -> d))) with
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
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate P) * (type.nat * type.untranslate _ (type.translate P) * (type.untranslate _ (type.translate P) -> R) -> R) * type.nat * (type.untranslate _ (type.translate P) -> R))%ctype) ,
                     let (PO_PS_n, k) := var_eta (Var PO_PS_n_k) in
                     let (PO_PS, n) := var_eta PO_PS_n in
                     let (PO, PS) := var_eta PO_PS in
                     ((@ident.nat_rect ((type.untranslate _ (type.translate P) -> R) -> R))
                        @@ ((λ k , Var k @ PO),
                            (λ n'rec k ,
                             let (n', rec) := var_eta (Var n'rec) in
                             rec @ (λ rec , PS @ (n', Var rec, Var k))),
                            n))
                       @ k
                | ident.list_rect A P
                  => λ (Pnil_Pcons_ls_k :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate P) * (type.untranslate _ (type.translate A) * Compilers.type.list (type.untranslate _ (type.translate A)) * type.untranslate _ (type.translate P) * (type.untranslate _ (type.translate P) -> R) -> R) * Compilers.type.list (type.untranslate _ (type.translate A)) * (type.untranslate _ (type.translate P) -> R))%ctype) ,
                     let (Pnil_Pcons_ls, k) := var_eta (Var Pnil_Pcons_ls_k) in
                     let (Pnil_Pcons, ls) := var_eta Pnil_Pcons_ls in
                     let (Pnil, Pcons) := var_eta Pnil_Pcons in
                     ((@ident.list_rect
                         (type.untranslate _ (type.translate A))
                         ((type.untranslate _ (type.translate P) -> R) -> R))
                        @@ ((λ k, Var k @ Pnil),
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
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate T) * type.untranslate _ (type.translate T) * type.bool * (type.untranslate _ (type.translate T) -> R))%ctype) ,
                     ident.bool_rect
                       @@ ((ident.snd @@ (Var xyzk))
                             @ (ident.fst @@ (ident.fst @@ (ident.fst @@ (Var xyzk)))),
                           (ident.snd @@ (Var xyzk))
                             @ (ident.snd @@ (ident.fst @@ (ident.fst @@ (Var xyzk)))),
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
                | ident.Nat_mul as idc
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
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.Z * type.Z * type.Z * ((type.Z * type.Z) -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ (type.Z * type.Z))
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Z_mul_split_concrete _ as idc
                | ident.Z_add_get_carry_concrete _ as idc
                | ident.Z_sub_get_borrow_concrete _ as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.Z * type.Z * ((type.Z * type.Z) -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ (type.Z * type.Z))
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Z_zselect as idc
                | ident.Z_add_modulo as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.Z * type.Z * type.Z * (type.Z -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ type.Z)
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Z_add_with_get_carry as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.Z * type.Z * type.Z * type.Z * ((type.Z * type.Z) -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ (type.Z * type.Z))
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
        := expr.Translate (invert_bool_rect) (@ident.wrap) e.

      Definition call_with_continuation
                 {var}
                 {R : Compilers.type.type}
                 {t} (e : @expr _ t)
                 (k : @Uncurried.expr.default.expr var (type.untranslate R t) -> @Uncurried.expr.default.expr var R)
        : @Compilers.Uncurried.expr.default.expr var R
        := expr.call_with_continuation (fun t idc => @ident.untranslate _ t idc _) (@ident.fst) (@ident.snd) (@ident.bool_rect) e k.

      Definition CallWithContinuation
                 {R : Compilers.type.type}
                 {t} (e : Expr t)
                 (k : forall var, @Uncurried.expr.default.expr var (type.untranslate R t) -> @Uncurried.expr.default.expr var R)
        : @Compilers.Uncurried.expr.default.Expr R
        := expr.CallWithContinuation (@ident.untranslate _) (@ident.fst) (@ident.snd) (@ident.bool_rect) e k.

      (** It's not clear how to "plug in the identity continuation"
          for the CPS'd form of an expression of type [((A -> B) -> C)
          -> D].  So we must describe types of at most second order
          functions, so that we can write a uniform "plug in the
          identity continuation" transformation. *)
      Module second_order.
        Import Compilers.type.
        Module Import type.
          Inductive flat_type :=
          | type_primitive (_ : primitive)
          | prod (_ : flat_type) (_ : flat_type)
          | list (_ : flat_type).
          Inductive argtype :=
          | flat_arg (_ : flat_type)
          | arrow_arg (s : flat_type) (d : argtype)
          | prod_arg (_ _ : argtype).
          Inductive type :=
          | flat (_ : flat_type)
          | arrow (s : argtype) (d : type).
        End type.

        Module Export Coercions.
          Coercion type_primitive : primitive >-> flat_type.
          Coercion flat_arg : flat_type >-> argtype.
          Coercion flat : flat_type >-> type.
        End Coercions.
        Notation flat_type := flat_type.
        Notation argtype := argtype.
        Notation type := type.

        Fixpoint flat_to_type (t : flat_type) : Compilers.type.type
          := match t with
             | type_primitive x => x
             | prod A B => Compilers.type.prod (flat_to_type A) (flat_to_type B)
             | list A => Compilers.type.list (flat_to_type A)
             end.

        Fixpoint arg_to_type (t : argtype) : Compilers.type.type
          := match t with
             | flat_arg t => flat_to_type t
             | arrow_arg s d => Compilers.type.arrow (flat_to_type s) (arg_to_type d)
             | prod_arg A B => Compilers.type.prod (arg_to_type A) (arg_to_type B)
             end.

        Fixpoint to_type (t : type) : Compilers.type.type
          := match t with
             | flat t => flat_to_type t
             | arrow s d => Compilers.type.arrow (arg_to_type s) (to_type d)
             end.

        Fixpoint flat_of_type (t : Compilers.type.type) : option flat_type
          := match t with
             | Compilers.type.type_primitive x => @Some flat_type x
             | Compilers.type.prod A B
               => match flat_of_type A, flat_of_type B with
                  | Some A, Some B => @Some flat_type (prod A B)
                  | _, _ => None
                  end
             | Compilers.type.arrow s d => None
             | Compilers.type.list A
               => option_map list (flat_of_type A)
             end.

        Fixpoint arg_of_type (t : Compilers.type.type) : option argtype
          := match t with
             | Compilers.type.prod A B as t
               => match flat_of_type t, arg_of_type A, arg_of_type B with
                  | Some t, _, _
                    => @Some argtype t
                  | None, Some A, Some B
                    => @Some argtype (prod_arg A B)
                  | _, _, _ => None
                  end
             | Compilers.type.arrow s d
               => match flat_of_type s, arg_of_type d with
                  | Some s, Some d => Some (arrow_arg s d)
                  | _, _ => None
                  end
             | Compilers.type.type_primitive _ as t
             | Compilers.type.list _ as t
               => option_map flat_arg (flat_of_type t)
             end.

        Fixpoint of_type (t : Compilers.type.type) : option type
          := match t with
             | Compilers.type.arrow s d
               => match arg_of_type s, of_type d with
                  | Some s, Some d => Some (arrow s d)
                  | _, _ => None
                  end
             | Compilers.type.prod _ _ as t
             | Compilers.type.type_primitive _ as t
             | Compilers.type.list _ as t
               => option_map flat (flat_of_type t)
             end.

        Fixpoint try_transport_flat_of_type P (t : Compilers.type.type)
          : P t -> option { t' : _ & P (flat_to_type t') }
          := match t with
             | Compilers.type.type_primitive x
               => fun v => Some (existT _ (x : flat_type) v)
             | Compilers.type.prod A B
               => fun v
                  => match try_transport_flat_of_type (fun a => P (a * _)%ctype) A v with
                     | Some (existT A v)
                       => match try_transport_flat_of_type (fun b => P (_ * b)%ctype) B v with
                          | Some (existT B v)
                            => Some (existT _ (prod A B) v)
                          | None => None
                          end
                     | None => None
                     end
             | Compilers.type.arrow s d => fun _ => None
             | Compilers.type.list A
               => fun v
                  => option_map
                       (fun '(existT A v) => existT (fun t => P (flat_to_type t)) (list A) v)
                       (try_transport_flat_of_type (fun a => P (Compilers.type.list a)) A v)
             end.

        Fixpoint try_transport_arg_of_type P (t : Compilers.type.type)
          : P t -> option { t' : _ & P (arg_to_type t') }
          := match t with
             | Compilers.type.prod A B as t
               => fun v
                  => match try_transport_flat_of_type P t v with
                     | Some (existT t v) => Some (existT (fun t' => P (arg_to_type t')) t v)
                     | None
                       => match try_transport_arg_of_type (fun a => P (a * _)%ctype) A v with
                          | Some (existT A v)
                            => match try_transport_arg_of_type (fun b => P (_ * b)%ctype) B v with
                               | Some (existT B v)
                                 => Some (existT _ (prod_arg A B) v)
                               | None => None
                               end
                          | None => None
                          end
                     end
             | Compilers.type.arrow s d
               => fun v
                  => match try_transport_flat_of_type (fun s => P (s -> _)%ctype) s v with
                     | Some (existT s v)
                       => match try_transport_flat_of_type (fun d => P (_ -> d)%ctype) d v with
                          | Some (existT d v)
                            => Some (existT (fun t' => P (arg_to_type t')) (arrow_arg s d) v)
                          | None => None
                          end
                     | None => None
                     end
             | Compilers.type.type_primitive _ as t
             | Compilers.type.list _ as t
               => fun v
                  => option_map
                       (fun '(existT t v) => existT (fun t => P (arg_to_type t)) (flat_arg t) v)
                       (try_transport_flat_of_type P t v)
             end.

        Fixpoint try_transport_of_type P (t : Compilers.type.type)
          : P t -> option { t' : _ & P (to_type t') }
          := match t with
             | Compilers.type.arrow s d
               => fun v
                  => match try_transport_arg_of_type (fun s => P (s -> _)%ctype) s v with
                     | Some (existT s v)
                       => match try_transport_of_type (fun d => P (_ -> d)%ctype) d v with
                          | Some (existT d v)
                            => Some (existT (fun t' => P (to_type t')) (arrow s d) v)
                          | None => None
                          end
                     | None => None
                     end
             | Compilers.type.prod _ _ as t
             | Compilers.type.type_primitive _ as t
             | Compilers.type.list _ as t
               => fun v
                  => option_map
                       (fun '(existT t v) => existT (fun t => P (to_type t)) (flat t) v)
                       (try_transport_flat_of_type P t v)
             end.
      End second_order.
      Import second_order.Coercions.

      Fixpoint untranslate_translate_flat
               (P : Compilers.type.type -> Type)
               {R}
               {t : second_order.flat_type}
               (e : P (second_order.to_type t))
               {struct t}
        : P (type.untranslate R (type.translate (second_order.to_type t)))
        := match t return P (second_order.to_type t)
                          -> P (type.untranslate R (type.translate (second_order.to_type t)))
           with
           | second_order.type.type_primitive x => id
           | second_order.type.prod A B
             => fun ab : P (second_order.flat_to_type A * second_order.flat_to_type B)%ctype
                => @untranslate_translate_flat
                     (fun a => P (a * _)%ctype)
                     R A
                     (@untranslate_translate_flat
                        (fun b => P (_ * b)%ctype)
                        R B
                        ab)
           | second_order.type.list A
             => @untranslate_translate_flat
                  (fun t => P (Compilers.type.list t))
                  R A
           end e.

      Fixpoint untranslate_translate_flat'
               (P : Compilers.type.type -> Type)
               {R}
               {t : second_order.flat_type}
               (e : P (type.untranslate R (type.translate (second_order.to_type t))))
               {struct t}
        : P (second_order.to_type t)
        := match t return P (type.untranslate R (type.translate (second_order.to_type t)))
                          -> P (second_order.to_type t)
           with
           | second_order.type.type_primitive x => id
           | second_order.type.prod A B
             => fun ab :
                      (* ignore this line *) P (type.untranslate R (type.translate (second_order.flat_to_type A)) * type.untranslate R (type.translate (second_order.flat_to_type B)))%ctype
                => @untranslate_translate_flat'
                     (fun a => P (a * _)%ctype)
                     R A
                     (@untranslate_translate_flat'
                        (fun b => P (_ * b)%ctype)
                        R B
                        ab)
           | second_order.type.list A
             => @untranslate_translate_flat'
                  (fun t => P (Compilers.type.list t))
                  R A
           end e.

      Definition transport_final_codomain_flat P {t}
        : P (second_order.flat_to_type t)
          -> P (type.final_codomain (second_order.flat_to_type t))
        := match t with
           | second_order.type.type_primitive x => id
           | second_order.type.prod x x0 => id
           | second_order.type.list x => id
           end.

      Definition transport_final_codomain_flat' P {t}
        : P (type.final_codomain (second_order.flat_to_type t))
          -> P (second_order.flat_to_type t)
        := match t with
           | second_order.type.type_primitive x => id
           | second_order.type.prod x x0 => id
           | second_order.type.list x => id
           end.

      Fixpoint untranslate_translate_arg
               {var}
               {R}
               {t : second_order.argtype}
               (e : @Compilers.Uncurried.expr.default.expr var (second_order.arg_to_type t))
               {struct t}
        : @Compilers.Uncurried.expr.default.expr var (type.untranslate R (type.translate (second_order.arg_to_type t)))
        := match t return Compilers.Uncurried.expr.default.expr (second_order.arg_to_type t)
                          -> Compilers.Uncurried.expr.default.expr (type.untranslate R (type.translate (second_order.arg_to_type t)))
           with
           | second_order.type.flat_arg t
             => untranslate_translate_flat _
           | second_order.type.arrow_arg s d
             => fun e'
                => Abs (fun v :
                              (* ignore this line *) var (type.untranslate R (type.translate (second_order.flat_to_type s)) * (type.untranslate R (type.translate (second_order.arg_to_type d)) -> R))%ctype
                        => (ident.snd @@ Var v)
                             @ (@untranslate_translate_arg
                                  var R d
                                  (e' @ (untranslate_translate_flat' _ (ident.fst @@ Var v)))))%expr
           | second_order.type.prod_arg A B
             => fun e' : expr.default.expr (second_order.arg_to_type A * second_order.arg_to_type B)
                => ((Abs (fun a => Abs (fun b => (Var a, Var b))))
                      @ (@untranslate_translate_arg var R A (ident.fst @@ e'))
                      @ (@untranslate_translate_arg var R B (ident.snd @@ e')))%expr
           end e.

      Local Notation "x <-- e1 ; e2" := (expr.splice e1 (fun x => e2%cpsexpr)) : cpsexpr_scope.

      Fixpoint call_fun_with_id_continuation'
               {var}
               {t : second_order.type}
               (R := type.final_codomain (second_order.to_type t))
               (e : @expr (fun t0 =>
                             @Uncurried.expr.expr default.ident.ident var (type.untranslate R t0))
                          (type.translate (second_order.to_type t)))
               {struct t}
        : @Compilers.Uncurried.expr.default.expr var (second_order.to_type t)
        := match t
                 return (@expr (fun t0 =>
                                  @Uncurried.expr.expr default.ident.ident var (type.untranslate (type.final_codomain (second_order.to_type t)) t0))
                               (type.translate (second_order.to_type t)))
                        -> @Compilers.Uncurried.expr.default.expr var (second_order.to_type t)
           with
           | second_order.type.flat t
             => fun e'
                => transport_final_codomain_flat'
                     _
                     (@call_with_continuation
                        var _ _ e'
                        (fun e'' => transport_final_codomain_flat _ (untranslate_translate_flat' _ e'')))
           | second_order.type.arrow s d
             => fun e' :
                      (* ignore this line *) expr (type.translate (second_order.arg_to_type s) * (type.translate (second_order.to_type d) --->) --->)
                => Abs (s:=second_order.arg_to_type s) (d:=second_order.to_type d)
                       (fun v
                        => @call_fun_with_id_continuation'
                             var d
                             (f <-- e';
                                k <- (λ r, expr.Halt r);
                                p <- (untranslate_translate_arg (Var v), k);
                                f @ p)%cpsexpr)
           end e.
      Definition CallFunWithIdContinuation'
                 {t : second_order.type}
                 (e : Expr (type.translate (second_order.to_type t)))
        : @Compilers.Uncurried.expr.default.Expr (second_order.to_type t)
        := fun var => @call_fun_with_id_continuation' _ t (e _).

      Definition CallFunWithIdContinuation
                 {t}
                 (e : Expr (type.translate t))
        := match second_order.try_transport_of_type (fun t => Expr (type.translate t)) _
                                                  e
                 as o return match o with None => _ | _ => _ end
           with
           | Some v => CallFunWithIdContinuation' (projT2 v)
           | None => I
           end.
    End default.
    Include default.
  End CPS.

  Module ZRange.
    Module type.
      Module primitive.
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
      Fixpoint interp (t : type) : Set
        := match t with
           | type.type_primitive x => primitive.interp x
           | type.prod A B => interp A * interp B
           | type.arrow s d => interp s -> interp d
           | type.list A => list (interp A)
           end.
      Fixpoint fold_andb_map {A B} (f : A -> B -> bool) (ls1 : list A) (ls2 : list B)
        : bool
        := match ls1, ls2 with
           | nil, nil => true
           | nil, _ => false
           | cons x xs, cons y ys => andb (f x y) (@fold_andb_map A B f xs ys)
           | cons _ _, _ => false
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
        Fixpoint interp (t : type) : Set
          := match t with
             | type.type_primitive x => primitive.option.interp x
             | type.prod A B => interp A * interp B
             | type.arrow s d => interp s -> interp d
             | type.list A => list (interp A)
             end.
        Fixpoint None {t : type} : interp t
          := match t with
             | type.type_primitive x => @primitive.option.None x
             | type.prod A B => (@None A, @None B)
             | type.arrow s d => fun _ => @None d
             | type.list A => @nil (interp A)
             end.
        Fixpoint Some {t : type} : type.interp t -> interp t
          := match t with
             | type.type_primitive x => @primitive.option.Some x
             | type.prod A B
               => fun x : type.interp A * type.interp B
                  => (@Some A (fst x), @Some B (snd x))
             | type.arrow s d => fun _ _ => @None d
             | type.list A => List.map (@Some A)
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
               => fold_andb_map (@is_tighter_than A)
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
               => fold_andb_map (@is_bounded_by A)
             end.

        Lemma fold_andb_map_map {A B C} f g ls1 ls2
          : @fold_andb_map A B f ls1 (@List.map C _ g ls2)
            = fold_andb_map (fun a b => f a (g b)) ls1 ls2.
        Proof. revert ls1 ls2; induction ls1, ls2; cbn; congruence. Qed.

        Lemma is_tighter_than_Some_is_bounded_by {t} r1 r2 val
              (Htight : @is_tighter_than t r1 (Some r2) = true)
              (Hbounds : is_bounded_by r1 val = true)
          : type.is_bounded_by r2 val = true.
        Proof.
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
                         | Z.ltb_to_lt; omega
                         | rewrite @fold_andb_map_map in * ].
          { revert r1 r2 val Htight Hbounds IHt.
            induction r1, r2, val; cbn; auto with nocore; try congruence; [].
            rewrite !Bool.andb_true_iff; intros; destruct_head'_and; split; eauto with nocore. }
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

        Definition interp {s d} (idc : ident s d) : type.option.interp s -> type.option.interp d
          := match idc in ident.ident s d return type.option.interp s -> type.option.interp d with
             | ident.primitive type.Z v => fun _ => Some r[v ~> v]
             | ident.Let_In tx tC => fun '(x, C) => C x
             | ident.primitive _ _
             | ident.Nat_succ
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
             | ident.Z_modulo
               => fun _ => type.option.None
             | ident.nil t => curry0 (@nil (type.option.interp t))
             | ident.cons t => curry2 (@Datatypes.cons (type.option.interp t))
             | ident.fst A B => @Datatypes.fst (type.option.interp A) (type.option.interp B)
             | ident.snd A B => @Datatypes.snd (type.option.interp A) (type.option.interp B)
             | ident.List_nth_default_concrete T d n
               => fun ls => @nth_default (type.option.interp T) type.option.None ls n
             | ident.Z_shiftr _ as idc
             | ident.Z_shiftl _ as idc
             | ident.Z_opp as idc
               => option_map (ZRange.two_corners (ident.interp idc))
             | ident.Z_land mask
               => option_map
                    (fun r : zrange
                     => ZRange.land_bounds r r[mask~>mask])
             | ident.Z_add as idc
             | ident.Z_mul as idc
             | ident.Z_sub as idc
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
                            (ZRange.split_bounds (ZRange.four_corners BinInt.Z.sub x y) split_at)
                     | Some _, None | None, Some _ | None, None => type.option.None
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
  End DefaultValue.

  Module partial.
    Notation Zdata := (option zrange).
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
           | type.type_primitive type.Z as t
             => Zdata * @expr var t + value_prestep value t
           | type.prod _ _ as t
           | type.list _ as t
           | type.type_primitive _ as t
             => @expr var t + value_prestep value t
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
    End value.

    Module expr.
      Section reify.
        Context (relax_zrange : zrange -> option zrange).
        Context {var : type -> Type}.
        Fixpoint reify {t : type} {struct t}
          : value var t -> @expr var t
          := match t return value var t -> expr t with
             | type.prod A B as t
               => fun x : expr t + value var A * value var B
                  => match x with
                     | inl v => v
                     | inr (a, b) => (@reify A a, @reify B b)%expr
                     end
             | type.arrow s d
               => fun (f : value var s -> value var d)
                  => Abs (fun x
                          => @reify d (f (@reflect s (Var x))))
             | type.list A as t
               => fun x : expr t + list (value var A)
                  => match x with
                     | inl v => v
                     | inr v => reify_list (List.map (@reify A) v)
                     end
             | type.type_primitive type.Z as t
               => fun x : Zdata * expr t + type.interp t
                  => match x with
                     | inl (Some r, v)
                       => match relax_zrange r with
                          | Some r => ident.Z.cast r @@ v
                          | None => v
                          end
                     | inl (None, v) => v
                     | inr v => ident.primitive v @@ TT
                     end%core%expr
             | type.type_primitive _ as t
               => fun x : expr t + type.interp t
                  => match x with
                     | inl v => v
                     | inr v => ident.primitive v @@ TT
                     end%expr
             end
        with reflect {t : type}
             : @expr var t -> value var t
             := match t return expr t -> value var t with
                | type.arrow s d
                  => fun (f : expr (s -> d)) (x : value var s)
                     => @reflect d (App f (@reify s x))
                | type.prod A B as t
                  => fun v : expr t
                     => let inr := @inr (expr t) (value_prestep (value var) t) in
                        let inl := @inl (expr t) (value_prestep (value var) t) in
                        match invert_Pair v with
                        | Some (a, b)
                          => inr (@reflect A a, @reflect B b)
                        | None
                          => inl v
                        end
                | type.list A as t
                  => fun v : expr t
                     => let inr := @inr (expr t) (value_prestep (value var) t) in
                        let inl := @inl (expr t) (value_prestep (value var) t) in
                        match reflect_list v with
                        | Some ls
                          => inr (List.map (@reflect A) ls)
                        | None
                          => inl v
                        end
                | type.type_primitive type.Z as t
                  => fun v : expr t
                     => let inr' := @inr (Zdata * expr t) (value_prestep (value var) t) in
                        let inl' := @inl (Zdata * expr t) (value_prestep (value var) t) in
                        match reflect_primitive v, invert_Z_cast v with
                        | Some v, _ => inr' v
                        | None, Some (r, v) => inl' (Some r, v)
                        | None, None => inl' (None, v)
                        end
                | type.type_primitive _ as t
                  => fun v : expr t
                     => let inr := @inr (expr t) (value_prestep (value var) t) in
                        let inl := @inl (expr t) (value_prestep (value var) t) in
                        match reflect_primitive v with
                        | Some v => inr v
                        | None => inl v
                        end
                end.
      End reify.
    End expr.

    Module ident.
      Section interp.
        Context (relax_zrange : zrange -> option zrange)
                {var : type -> Type}.
        Fixpoint is_var_like {t} (e : @expr var t) : bool
          := match e with
             | Var t v => true
             | TT => true
             | AppIdent _ _ (ident.fst _ _) args => @is_var_like _ args
             | AppIdent _ _ (ident.snd _ _) args => @is_var_like _ args
             | Pair A B a b => @is_var_like A a && @is_var_like B b
             | AppIdent _ _ _ _ => false
             | App _ _ _ _
             | Abs _ _ _
               => false
             end.
        Fixpoint interp_let_in {tC tx : type} {struct tx} : value var tx -> (value var tx -> value var tC) -> value var tC
          := match tx return value var tx -> (value var tx -> value var tC) -> value var tC with
             | type.arrow _ _
               => fun x f => f x
             | type.list T as t
               => fun (x : expr t + list (value var T)) (f : expr t + list (value var T) -> value var tC)
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
               => fun (x : expr t + value var A * value var B) (f : expr t + value var A * value var B -> value var tC)
                  => match x with
                     | inr (a, b)
                       => @interp_let_in
                            _ A a
                            (fun a
                             => @interp_let_in
                                  _ B b
                                  (fun b => f (inr (a, b))))
                     | inl e => partial.expr.reflect relax_zrange (expr_let y := e in partial.expr.reify relax_zrange (f (inl (Var y))))%expr
                     end
             | type.type_primitive type.Z as t
               => fun (x : Zdata * expr t + type.interp t)
                      (f : Zdata * expr t + type.interp t -> value var tC)
                  => match x with
                     | inl (data, e)
                       => if is_var_like e
                          then f (inl (data, e))
                          else partial.expr.reflect
                                 relax_zrange
                                 (expr_let y := (partial.expr.reify relax_zrange (t:=t) x) in
                                      partial.expr.reify relax_zrange (f (inl (data, Var y)%core)))%expr
                     | inr v => f (inr v)
                     end
             | type.type_primitive _ as t
               => fun (x : expr t + type.interp t) (f : expr t + type.interp t -> value var tC)
                  => match x with
                     | inl e
                       => match invert_Var e with
                          | Some v => f (inl (Var v))
                          | None => partial.expr.reflect
                                      relax_zrange
                                      (expr_let y := e in
                                           partial.expr.reify relax_zrange (f (inl (Var y))))%expr
                          end
                     | inr v => f (inr v) (* FIXME: do not substitute [S (big stuck term)] *)
                     end
             end.

        Definition interp {s d} (idc : ident s d) : value var (s -> d)
          := match idc in ident s d return value var (s -> d) with
             | ident.Let_In tx tC as idc
               => fun (xf : expr (tx * (tx -> tC)) + value var tx * value var (tx -> tC))
                  => match xf with
                     | inr (x, f) => interp_let_in x f
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=tx * (tx -> tC)) xf))
                     end
             | ident.nil t
               => fun _ => inr (@nil (value var t))
             | ident.primitive type.Z v
               => fun _ => inr v
             | ident.primitive t v
               => fun _ => inr v
             | ident.cons t as idc
               => fun (x_xs : expr (t * type.list t) + value var t * (expr (type.list t) + list (value var t)))
                  => match x_xs return expr (type.list t) + list (value var t) with
                     | inr (x, inr xs) => inr (cons x xs)
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=t * type.list t) x_xs))
                     end
             | ident.fst A B as idc
               => fun x : expr (A * B) + value var A * value var B
                  => match x with
                     | inr x => fst x
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=A*B) x))
                     end
             | ident.snd A B as idc
               => fun x : expr (A * B) + value var A * value var B
                  => match x with
                     | inr x => snd x
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=A*B) x))
                     end
             | ident.bool_rect T as idc
               => fun (true_case_false_case_b : expr (T * T * type.bool) + (expr (T * T) + value var T * value var T) * (expr type.bool + bool))
                  => match true_case_false_case_b with
                     | inr (inr (true_case, false_case), inr b)
                       => @bool_rect (fun _ => value var T) true_case false_case b
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=T*T*type.bool) true_case_false_case_b))
                     end
             | ident.nat_rect P as idc
               => fun (O_case_S_case_n : expr (P * (type.nat * P -> P) * type.nat) + (expr (P * (type.nat * P -> P)) + value var P * value var (type.nat * P -> P)) * (expr type.nat + nat))
                  => match O_case_S_case_n with
                     | inr (inr (O_case, S_case), inr n)
                       => @nat_rect (fun _ => value var P)
                                    O_case
                                    (fun n' rec => S_case (inr (inr n', rec)))
                                    n
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=P * (type.nat * P -> P) * type.nat) O_case_S_case_n))
                     end
             | ident.list_rect A P as idc
               => fun (nil_case_cons_case_ls : expr (P * (A * type.list A * P -> P) * type.list A) + (expr (P * (A * type.list A * P -> P)) + value var P * value var (A * type.list A * P -> P)) * (expr (type.list A) + list (value var A)))
                  => match nil_case_cons_case_ls with
                     | inr (inr (nil_case, cons_case), inr ls)
                       => @list_rect
                            (value var A)
                            (fun _ => value var P)
                            nil_case
                            (fun x xs rec => cons_case (inr (inr (x, inr xs), rec)))
                            ls
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=P * (A * type.list A * P -> P) * type.list A) nil_case_cons_case_ls))
                     end
             | ident.List.nth_default type.Z as idc
               => fun (default_ls_idx : expr (type.Z * type.list type.Z * type.nat) + (expr (type.Z * type.list type.Z) + (_ * expr type.Z + type.interp type.Z) * (expr (type.list type.Z) + list (value var type.Z))) * (expr type.nat + nat))
                  => match default_ls_idx with
                     | inr (inr (default, inr ls), inr idx)
                       => List.nth_default default ls idx
                     | inr (inr (inr default, ls), inr idx)
                       => expr.reflect relax_zrange (AppIdent (ident.List.nth_default_concrete default idx) (expr.reify relax_zrange (t:=type.list type.Z) ls))
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=type.Z * type.list type.Z * type.nat) default_ls_idx))
                     end
             | ident.List.nth_default (type.type_primitive A) as idc
               => fun (default_ls_idx : expr (A * type.list A * type.nat) + (expr (A * type.list A) + (expr A + type.interp A) * (expr (type.list A) + list (value var A))) * (expr type.nat + nat))
                  => match default_ls_idx with
                     | inr (inr (default, inr ls), inr idx)
                       => List.nth_default default ls idx
                     | inr (inr (inr default, ls), inr idx)
                       => expr.reflect relax_zrange (AppIdent (ident.List.nth_default_concrete default idx) (expr.reify relax_zrange (t:=type.list A) ls))
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=A * type.list A * type.nat) default_ls_idx))
                     end
             | ident.List.nth_default A as idc
               => fun (default_ls_idx : expr (A * type.list A * type.nat) + (expr (A * type.list A) + value var A * (expr (type.list A) + list (value var A))) * (expr type.nat + nat))
                  => match default_ls_idx with
                     | inr (inr (default, inr ls), inr idx)
                       => List.nth_default default ls idx
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=A * type.list A * type.nat) default_ls_idx))
                     end
             | ident.List.nth_default_concrete A default idx as idc
               => fun (ls : expr (type.list A) + list (value var A))
                  => match ls with
                     | inr ls
                       => List.nth_default (expr.reflect relax_zrange (t:=A) (AppIdent (ident.primitive default) TT)) ls idx
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=type.list A) ls))
                     end
             | ident.Z_mul_split as idc
               => fun (x_y_z :  (expr (type.Z * type.Z * type.Z) +
                                 (expr (type.Z * type.Z) + (_ * expr type.Z + Z) * (_ * expr type.Z + Z)) * (_ * expr type.Z + Z))%type)
                  => match x_y_z return (expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) with
                     | inr (inr (inr x, inr y), inr z) =>
                       let result := ident.interp idc (x, y, z) in
                       inr (inr (fst result), inr (snd result))
                     | inr (inr (inr x, y), z)
                       => expr.reflect relax_zrange (AppIdent (ident.Z.mul_split_concrete x) (expr.reify relax_zrange (t:=type.Z*type.Z) (inr (y, z))))
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=_*_*_) x_y_z))
                     end
             | ident.Z_add_get_carry as idc
               => fun (x_y_z :  (expr (type.Z * type.Z * type.Z) +
                                 (expr (type.Z * type.Z) + (_ * expr type.Z + Z) * (_ * expr type.Z + Z)) * (_ * expr type.Z + Z))%type)
                  => match x_y_z return (expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) with
                     | inr (inr (inr x, inr y), inr z) =>
                       let result := ident.interp idc (x, y, z) in
                       inr (inr (fst result), inr (snd result))
                     | inr (inr (inr x, y), z)
                       => let default := expr.reflect relax_zrange (AppIdent (ident.Z.add_get_carry_concrete x) (expr.reify relax_zrange (t:=type.Z*type.Z) (inr (y, z)))) in
                          match (y, z) with
                          | (inr xx, inl e)
                          | (inl e, inr xx)
                            => if Z.eqb xx 0
                               then inr (inl e, inr 0%Z)
                               else default
                          | _ => default
                          end
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=_*_*_) x_y_z))
                     end
             | ident.Z_add_with_get_carry as idc
               => fun (x_y_z_a : (expr (_ * _ * _ * _) +
                                  (expr (_ * _ * _) +
                                   (expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) *
                                   (_ * expr _ + type.interp _)) * (_ * expr _ + type.interp _))%type)
                  => match x_y_z_a return (expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) with
                     | inr (inr (inr (inr x, inr y), inr z), inr a) =>
                       let result := ident.interp idc (x, y, z, a) in
                       inr (inr (fst result), inr (snd result))
                     | inr (inr (inr (inr x, y), z), a)
                        => expr.reflect relax_zrange (AppIdent (ident.Z.add_with_get_carry_concrete x) (expr.reify relax_zrange (t:=type.Z*type.Z*type.Z) (inr (inr (y, z), a))))
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=_*_*_*_) x_y_z_a))
                     end
             | ident.Z_sub_get_borrow as idc
               => fun (x_y_z :  (expr (type.Z * type.Z * type.Z) +
                                 (expr (type.Z * type.Z) + (_ * expr type.Z + Z) * (_ * expr type.Z + Z)) * (_ * expr type.Z + Z))%type)
                  => match x_y_z return (expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) with
                     | inr (inr (inr x, inr y), inr z) =>
                       let result := ident.interp idc (x, y, z) in
                       inr (inr (fst result), inr (snd result))
                     | inr (inr (inr x, y), z)
                       => expr.reflect relax_zrange (AppIdent (ident.Z.sub_get_borrow_concrete x) (expr.reify relax_zrange (t:=type.Z*type.Z) (inr (y, z))))
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=_*_*_) x_y_z))
                     end
             | ident.Z_mul_split_concrete _ as idc
             | ident.Z.sub_get_borrow_concrete _ as idc
               => fun (x_y : expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => match x_y return (expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) with
                     | inr (inr x, inr y) =>
                       let result := ident.interp idc (x, y) in
                       inr (inr (fst result), inr (snd result))
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=_*_) x_y))
                     end
             | ident.Z.add_get_carry_concrete _ as idc
               => fun (x_y : expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => let default := expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=_*_) x_y)) in
                     match x_y return (expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) with
                     | inr (inr x, inr y) =>
                       let result := ident.interp idc (x, y) in
                       inr (inr (fst result), inr (snd result))
                     | inr (inr x, inl e)
                     | inr (inl e, inr x) =>
                       if Z.eqb x 0%Z
                       then inr (inl e, inr 0%Z)
                       else default
                     | _ => default
                     end
             | ident.Z.add_with_get_carry_concrete _ as idc
               => fun (x_y_z :  (expr (type.Z * type.Z * type.Z) +
                                 (expr (type.Z * type.Z) + (_ * expr type.Z + Z) * (_ * expr type.Z + Z)) * (_ * expr type.Z + Z))%type)
                  => match x_y_z return (expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) with
                     | inr (inr (inr x, inr y), inr z) =>
                       let result := ident.interp idc (x, y, z) in
                       inr (inr (fst result), inr (snd result))
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=_*_*_) x_y_z))
                     end
             | ident.pred as idc
             | ident.Nat_succ as idc
               => fun x : expr _ + type.interp _
                  => match x return expr _ + type.interp _ with
                     | inr x => inr (ident.interp idc x)
                     | inl x => expr.reflect relax_zrange (AppIdent idc x)
                     end
             | ident.Z_of_nat as idc
               => fun x : expr _ + type.interp _
                  => match x return _ * expr _ + type.interp _ with
                     | inr x => inr (ident.interp idc x)
                     | inl x => expr.reflect relax_zrange (AppIdent idc x)
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
               => fun x : _ * expr _ + type.interp _
                  => match x return _ * expr _ + type.interp _ with
                     | inr x => inr (ident.interp idc x)
                     | inl _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=type.Z) x))
                     end
             | ident.Nat_add as idc
             | ident.Nat_mul as idc
             | ident.Z_pow as idc
               => fun (x_y : expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => match x_y return _ * expr _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=_*_) x_y))
                     end
             | ident.Z_eqb as idc
             | ident.Z_leb as idc
               => fun (x_y : expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => match x_y return expr _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=_*_) x_y))
                     end
             | ident.Z_div as idc
               => fun (x_y : expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => let default := expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=_*_) x_y)) in
                     match x_y return _ * expr _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | inr (x, inr y)
                       => if Z.eqb y (2^Z.log2 y)
                          then expr.reflect relax_zrange (AppIdent (ident.Z.shiftr (Z.log2 y)) (expr.reify relax_zrange (t:=type.Z) x))
                          else default
                     | _ => default
                     end
             | ident.Z_modulo as idc
               => fun (x_y : expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => let default := expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=_*_) x_y)) in
                     match x_y return _ * expr _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | inr (x, inr y)
                       => if Z.eqb y (2^Z.log2 y)
                          then expr.reflect relax_zrange (AppIdent (ident.Z.land (y-1)) (expr.reify relax_zrange (t:=type.Z) x))
                          else default
                     | _ => default
                     end
             | ident.Z_mul as idc
               => fun (x_y : expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => let default := expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=_*_) x_y)) in
                     match x_y return _ * expr _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | inr (inr x, inl (data, e) as y)
                     | inr (inl (data, e) as y, inr x)
                       => let data' := ZRange.ident.option.interp idc (data, Some r[x~>x]%zrange) in
                          if Z.eqb x 0
                          then inr 0%Z
                          else if Z.eqb x 1
                               then y
                               else if Z.eqb x (-1)
                                    then inl (data', AppIdent ident.Z.opp (expr.reify relax_zrange (t:=type.Z) y))
                                    else if Z.eqb x (2^Z.log2 x)
                                         then inl (data',
                                                   AppIdent (ident.Z.shiftl (Z.log2 x)) (expr.reify relax_zrange (t:=type.Z) y))
                                         else inl (data',
                                                   AppIdent idc (ident.primitive (t:=type.Z) x @@ TT, expr.reify relax_zrange (t:=type.Z) y))
                     | inr (inl (dataa, a), inl (datab, b))
                       => inl (ZRange.ident.option.interp idc (dataa, datab),
                               AppIdent idc (a, b))
                     | inl _ => default
                     end
             | ident.Z_add as idc
               => fun (x_y : expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => let default0 := AppIdent idc (expr.reify relax_zrange (t:=_*_) x_y) in
                     let default := expr.reflect relax_zrange default0 in
                     match x_y return _ * expr _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | inr (inr x, inl (data, e) as y)
                     | inr (inl (data, e) as y, inr x)
                       => let data' := ZRange.ident.option.interp idc (data, Some r[x~>x]%zrange) in
                          if Z.eqb x 0
                          then y
                          else inl (data', match invert_Z_opp e with
                                           | Some e => AppIdent
                                                         ident.Z.sub
                                                         (ident.primitive (t:=type.Z) x @@ TT,
                                                          e)
                                           | None => default0
                                           end)
                     | inr (inl (dataa, a), inl (datab, b))
                       => let data' := ZRange.ident.option.interp idc (dataa, datab) in
                          match invert_Z_opp a, invert_Z_opp b with
                          | Some a, Some b
                            => inl (data',
                                    AppIdent
                                      ident.Z.opp
                                      (idc @@ (a, b)))
                          | Some a, None
                            => inl (data', AppIdent ident.Z.sub (b, a))
                          | None, Some b
                            => inl (data', AppIdent ident.Z.sub (a, b))
                          | None, None => inl (data', default0)
                          end
                     | inl _ => default
                     end
             | ident.Z_sub as idc
               => fun (x_y : expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                  => let default0 := AppIdent idc (expr.reify relax_zrange (t:=_*_) x_y) in
                     let default := expr.reflect relax_zrange default0 in
                     match x_y return _ * expr _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | inr (inr x, inl (data, e))
                       => let data' := ZRange.ident.option.interp idc (Some r[x~>x]%zrange, data) in
                          if Z.eqb x 0
                          then inl (data, AppIdent ident.Z.opp e)
                          else inl (data, default0)
                     | inr (inl (data, e), inr x)
                       => let data' := ZRange.ident.option.interp idc (data, Some r[x~>x]%zrange) in
                          if Z.eqb x 0
                          then inl (data', e)
                          else inl (data', default0)
                     | inr (inl (dataa, a), inl (datab, b))
                       => let data' := ZRange.ident.option.interp idc (dataa, datab) in
                          match invert_Z_opp a, invert_Z_opp b with
                          | Some a, Some b
                            => inl (data',
                                    AppIdent
                                      ident.Z.opp
                                      (idc @@ (a, b)))
                          | Some a, None
                            => inl (data', AppIdent ident.Z.add (b, a))
                          | None, Some b
                            => inl (data', AppIdent ident.Z.add (a, b))
                          | None, None => inl (data', default0)
                          end
                     | inl _ => default
                     end
             | ident.Z_zselect as idc
             | ident.Z_add_modulo as idc
               => fun (x_y_z :  (expr (_ * _ * _) +
                                 (expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _)) * (_ * expr _ + type.interp _))%type)
                  => match x_y_z return _ * expr _ + type.interp _ with
                     | inr (inr (inr x, inr y), inr z) => inr (ident.interp idc (x, y, z))
                     | _ => expr.reflect relax_zrange (AppIdent idc (expr.reify relax_zrange (t:=_*_*_) x_y_z))
                     end
             | ident.Z_cast r as idc
               => fun (x : _ * expr _ + type.interp _)
                  => match x with
                     | inr x => inr (ident.interp idc x)
                     | inl (data, e)
                       => inl (ZRange.ident.option.interp idc data, e)
                     end
           end.
      End interp.
    End ident.
  End partial.

  Section partial_reduce.
    Context (relax_zrange : zrange -> option zrange)
            {var : type -> Type}.

    Fixpoint partial_reduce' {t} (e : @expr (partial.value var) t)
      : partial.value var t
      := match e in expr.expr t return partial.value var t with
         | Var t v => v
         | TT => inr tt
         | AppIdent s d idc args => partial.ident.interp relax_zrange idc (@partial_reduce' _ args)
         | Pair A B a b => inr (@partial_reduce' A a, @partial_reduce' B b)
         | App s d f x => @partial_reduce' _ f (@partial_reduce' _ x)
         | Abs s d f => fun x => @partial_reduce' d (f x)
         end.

    Definition partial_reduce {t} (e : @expr (partial.value var) t) : @expr var t
      := partial.expr.reify relax_zrange (@partial_reduce' t e).

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
                         relax_zrange
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
                 | Some r, inr v => inr (ident.interp (ident.Z.cast r) v)
                 | Some r, inl (data, e)
                   => inl (ZRange.ident.option.interp (ident.Z.cast r) data, e)
                 | None, e => e
                 end
         | type.type_primitive t => fun _ => id
         | type.prod A B
           => fun '((ra, rb) : ZRange.type.option.interp A * ZRange.type.option.interp B)
                  (e : expr _ + partial.value var A * partial.value var B)
              => match e with
                 | inr (a, b)
                   => inr (@extend_with_obounds A ra a,
                           @extend_with_obounds B rb b)
                 | inl e
                   => if partial.ident.is_var_like e
                      then inr (@extend_with_obounds A ra (partial.expr.reflect relax_zrange (AppIdent ident.fst e)),
                                @extend_with_obounds B rb (partial.expr.reflect relax_zrange (AppIdent ident.snd e)))
                      else inl e
                 end
         | type.arrow s d => fun _ => id
         | type.list A
           => fun (ls : Datatypes.list (ZRange.type.option.interp A))
                  (e : expr _ + list (partial.value var A))
              => match e with
                 | inl e
                   => match A return (ZRange.type.option.interp A -> partial.value var A -> partial.value var A)
                                     -> Datatypes.list (ZRange.type.option.interp A)
                                     -> expr (type.list A)
                                     -> partial.value var (type.list A)
                      with
                      | type.type_primitive A
                        => fun extend_with_obounds ls e
                           => inr (extend_list_expr_with_obounds
                                     extend_with_obounds 0 ls e)
                      | A'
                        => fun _ _ e => inl e
                      end (@extend_with_obounds A) ls e
                 | inr e => inr (extend_concrete_list_with_obounds
                                   (@extend_with_obounds A) ls e)
                 end
         end.
    Definition extend_with_bounds {t}
               (b : ZRange.type.interp t)
               (e : partial.value var t)
      : partial.value var t
      := @extend_with_obounds t (ZRange.type.option.Some b) e.

    Section extract.
      Context (fill_var : forall t, var t).
      Fixpoint extract_bounds {t} : partial.value var t -> ZRange.type.option.interp t
        := match t return partial.value var t -> ZRange.type.option.interp t with
           | type.type_primitive type.Z
             => fun (e : option zrange * _ + type.interp _)
                => match e with
                   | inl (data, _) => data
                   | inr z => Some r[z~>z]%zrange
                   end
           | type.type_primitive t => fun _ => ZRange.type.option.None
           | type.prod A B
             => fun (e : expr _ + partial.value var A * partial.value var B)
                => match e with
                   | inl e => ZRange.type.option.None
                   | inr (a, b) => (@extract_bounds A a, @extract_bounds B b)
                   end
           | type.arrow s d
             => fun (f : partial.value var s -> partial.value var d)
                    (b : ZRange.type.option.interp s)
                => @extract_bounds d (f (extend_with_obounds b (partial.expr.reflect relax_zrange (Var (fill_var _)))))
           | type.list A
             => fun (e : expr _ + list (partial.value var A))
                => match e with
                   | inl e => ZRange.type.option.None
                   | inr ls => List.map (@extract_bounds A) ls
                   end
           end.
    End extract.

    Definition partial_reduce_with_bounds1' {s d} (e : @expr (partial.value var) (s -> d))
               (b : ZRange.type.interp s)
      : partial.value var (s -> d)
      := fun x : partial.value var s
         => partial_reduce' e (extend_with_bounds b x).

    Definition partial_reduce_with_bounds1 {s d} (e : @expr (partial.value var) (s -> d))
               (b : ZRange.type.interp s)
      := partial.expr.reify relax_zrange (@partial_reduce_with_bounds1' s d e b).
  End partial_reduce.

  Definition PartialReduce {t} (e : Expr t) : Expr t
    := fun var => @partial_reduce (fun r => Some r) var t (e _).

  Definition PartialReduceWithBounds1
             (relax_zrange : zrange -> option zrange)
             {s d} (e : Expr (s -> d)) (b : ZRange.type.interp s)
    : Expr (s -> d)
    := fun var => @partial_reduce_with_bounds1 relax_zrange var s d (e _) b.

  Definition CheckedPartialReduceWithBounds1
             (relax_zrange : zrange -> option zrange)
             {s d} (e : Expr (s -> d))
             (b_in : ZRange.type.interp s)
             (b_out : ZRange.type.interp d)
    : Expr (s -> d) + ZRange.type.option.interp d
    := dlet_nd v := (fun var => @partial_reduce_with_bounds1' relax_zrange var s d (e _) b_in) in
             let b_computed := extract_bounds relax_zrange (@DefaultValue.type.default) (v type.interp) (ZRange.type.option.Some b_in) in
             if ZRange.type.option.is_tighter_than b_computed (ZRange.type.option.Some b_out)
             then @inl (Expr (s -> d)) _ (fun var => partial.expr.reify relax_zrange (v var))
             else @inr _ (ZRange.type.option.interp d) b_computed.

  Definition CheckedPartialReduceWithBounds0
             (relax_zrange : zrange -> option zrange)
             {t} (e : Expr t)
             (b_out : ZRange.type.interp t)
    : Expr t + ZRange.type.option.interp t
    := dlet_nd v := (fun var => @partial_reduce' relax_zrange var t (e _)) in
             let b_computed := extract_bounds relax_zrange (@DefaultValue.type.default) (v type.interp) in
             if ZRange.type.option.is_tighter_than b_computed (ZRange.type.option.Some b_out)
             then @inl (Expr t) _ (fun var => partial.expr.reify relax_zrange (v var))
             else @inr _ (ZRange.type.option.interp t) b_computed.

  Axiom admit_pf : False.
  Local Notation admit := (match admit_pf with end).

  Theorem CheckedPartialReduceWithBounds1_Correct
          (relax_zrange : zrange -> option zrange)
          (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                   -> relax_zrange r = Some r'
                                   -> is_tighter_than_bool z r' = true)
          {s d} (e : Expr (s -> d))
          (b_in : ZRange.type.interp s)
          (b_out : ZRange.type.interp d)
          rv (Hrv : CheckedPartialReduceWithBounds1 relax_zrange e b_in b_out = inl rv)
    : forall arg
             (Harg : ZRange.type.is_bounded_by b_in arg = true),
      Interp rv arg = Interp e arg
      /\ ZRange.type.is_bounded_by b_out (Interp rv arg) = true.
  Proof.
    cbv [CheckedPartialReduceWithBounds1 Let_In] in *;
      break_innermost_match_hyps; inversion_sum; subst.
    intros arg Harg.
    split.
    { exact admit. (* correctness of interp *) }
    { eapply ZRange.type.option.is_tighter_than_Some_is_bounded_by; [ eassumption | ].
      cbv [expr.Interp].
      revert Harg.
      exact admit. (* boundedness *) }
  Qed.

  Theorem CheckedPartialReduceWithBounds0_Correct
          (relax_zrange : zrange -> option zrange)
          (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                   -> relax_zrange r = Some r'
                                   -> is_tighter_than_bool z r' = true)
          {t} (e : Expr t)
          (b_out : ZRange.type.interp t)
          rv (Hrv : CheckedPartialReduceWithBounds0 relax_zrange e b_out = inl rv)
    : Interp rv = Interp e
      /\ ZRange.type.is_bounded_by b_out (Interp rv) = true.
  Proof.
    cbv [CheckedPartialReduceWithBounds0 Let_In] in *;
      break_innermost_match_hyps; inversion_sum; subst.
    split.
    { exact admit. (* correctness of interp *) }
    { eapply ZRange.type.option.is_tighter_than_Some_is_bounded_by; [ eassumption | ].
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
           => let default := @compute_live' _ args cur_idx in
              match args in expr.expr t return ident.ident t d -> _ with
              | Pair A B x (Abs s d f)
                => fun idc
                   => match idc with
                      | ident.Let_In _ _
                        => let '(idx, live) := @compute_live' A x cur_idx in
                           let '(_, live) := @compute_live' _ (f (PositiveSet.add idx live)) (Pos.succ idx) in
                           (Pos.succ idx, live)
                      | _ => default
                      end
              | _ => fun _ => default
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
             => let default := @eliminate_dead' _ args cur_idx in
                let default := (fst default, AppIdent idc (snd default)) in
                match args in expr.expr t return ident.ident t d -> positive * expr d -> positive * expr d with
                | Pair A B x y
                  => match y in expr.expr Y return ident.ident (A * Y) d -> positive * expr d -> positive * expr d with
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
                                           -> positive * expr d
                                           -> positive * expr d)
                             with
                             | ident.Let_In _ _
                               => fun x' f' _
                                  => if PositiveSet.mem idx live
                                     then (Pos.succ idx, AppIdent ident.Let_In (Pair x' (Abs (fun v => f' (Var v)))))
                                     else (Pos.succ idx, f' (OUGHT_TO_BE_UNUSED x' (Pos.succ idx, PositiveSet.elements live)))
                             | _ => fun _ _ default => default
                             end x' f'
                     | _ => fun _ default => default
                     end
                | _ => fun _ default => default
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

      Fixpoint to_add_mul_list (e : @expr var type.Z) : list (list (@expr var type.Z))
        := match e in expr.expr t return list (list (@expr var t)) with
           | AppIdent s type.Z ident.Z_add (Pair type.Z type.Z x y)
             => to_add_mul_list x ++ to_add_mul_list y
           | AppIdent s type.Z ident.Z_mul (Pair type.Z type.Z x y)
             => [to_mul_list x ++ to_mul_list y]
           | Var _ _ as e
           | TT as e
           | App _ _ _ _ as e
           | Abs _ _ _ as e
           | Pair _ _ _ _ as e
           | AppIdent _ _ _ _ as e
             => [ [ e ] ]
           end.

      Definition is_small_prim (e : @expr var type.Z) : bool
        := match e with
           | AppIdent _ _ (ident.primitive type.Z v) _
             => Z.abs v <=? Z.abs max_const_val
           | _ => false
           end.
      Definition is_not_small_prim (e : @expr var type.Z) : bool
        := negb (is_small_prim e).

      Definition reorder_add_mul_list (ls : list (list (@expr var type.Z)))
        : list (list (@expr var type.Z))
        := List.map
             (fun ls
              => filter is_not_small_prim ls ++ filter is_small_prim ls)
             ls.

      Fixpoint of_mul_list (ls : list (@expr var type.Z)) : @expr var type.Z
        := match ls with
           | nil => AppIdent (ident.primitive (t:=type.Z) 1) TT
           | cons x nil
             => x
           | cons x xs
             => AppIdent ident.Z_mul (x, of_mul_list xs)
           end.

      Fixpoint of_add_mul_list (ls : list (list (@expr var type.Z))) : @expr var type.Z
        := match ls with
           | nil => AppIdent (ident.primitive (t:=type.Z) 0) TT
           | cons x nil
             => of_mul_list x
           | cons x xs
             => AppIdent ident.Z_add (of_mul_list x, of_add_mul_list xs)
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
             => of_add_mul_list (reorder_add_mul_list (to_add_mul_list (AppIdent idc (@reassociate s args))))
           | AppIdent s d idc args
             => AppIdent idc (@reassociate s args)
           end.
    End with_var.

    Definition Reassociate (max_const_val : Z) {t} (e : Expr t) : Expr t
      := fun var => reassociate max_const_val (e _).
  End ReassociateSmallConstants.

  (*Module Indexed.
    Module Export Range.
      Import type.

      Section with_relax.
        Context (relax_zrange : zrange -> option zrange).

          Definition primitive_for_option_zrange (v : option zrange) : type.primitive
            := match v with
               | Some v => ZBounded (lower v) (upper v)
               | None => Z
               end.
          Definition primitive_for_zrange (v : zrange) : type.primitive
            := primitive_for_option_zrange (relax_zrange v).

          Fixpoint range (t : type) : Set
            := match t with
               | type_primitive _ => zrange
               | prod A B => range A * range B
               | list A => Datatypes.list zrange
               end%type.

          Fixpoint range_is_tighter_than {t}
            : forall (tight_range loose_range : range t), bool
            := match t return range t -> range t -> bool with
               | type_primitive x => is_tighter_than_bool
               | prod A B
                 => fun '((r1, r2) : range _ * range _)
                        '((r1', r2') : range _ * range _)
                    => @range_is_tighter_than _ r1 r1' && @range_is_tighter_than _ r2 r2'
               | list A
                 => fun ls1 ls2
                    => if (List.length ls1 =? List.length ls2)%nat
                       then List.forallb (fun '(r1, r2) => is_tighter_than_bool r1 r2)
                                         (combine ls1 ls2)
                       else false
               end.

          Definition primitive_bounded_by {t} : type.primitive.interp t -> zrange -> bool
            := match t return primitive.interp t -> zrange -> bool with
               | unit => fun _ _ => true
               | Z => fun v r => (lower r <=? v) && (v <=? upper r)
               | ZBounded _ _
                 => fun v r => (lower r <=? value v) && (value v <=? upper r)
               end.

          Fixpoint list_bounded_by {t} (ls : Datatypes.list (primitive.interp t))
                   (r : Datatypes.list zrange)
            : bool
            := match ls, r with
               | nil, nil => true
               | nil, _ => false
               | cons x xs, cons r rs
                 => primitive_bounded_by x r && @list_bounded_by _ xs rs
               | cons _ _, _ => false
               end.

          Lemma length_list_bounded_by {t} ls r
                (H : @list_bounded_by t ls r = true)
            : List.length ls = List.length r.
          Proof.
            revert dependent r; induction ls as [|x xs IHxs], r;
              cbn; try reflexivity; try discriminate.
            rewrite Bool.andb_true_iff.
            intros [? ?]; erewrite IHxs; [ reflexivity | assumption ].
          Qed.

          Fixpoint bounded_by {t} : type.interp t -> range t -> bool
            := match t return type.interp t -> range t -> bool with
               | type_primitive x => primitive_bounded_by
               | prod A B => fun '((a, a') : type.interp A * type.interp B)
                                 '((r, r') : range A * range B)
                             => @bounded_by A a r && @bounded_by B a' r'
               | list A => list_bounded_by
               end.

          Fixpoint type_for_range {t} : range t -> type
            := match t return range t -> type with
               | type_primitive _ => primitive_for_zrange
               | prod A B => fun (ab : range A * range B)
                             => prod (@type_for_range A (Datatypes.fst ab))
                                     (@type_for_range B (Datatypes.snd ab))
               | list A
                 => fun ls : Datatypes.list zrange
                    => type.list
                         (primitive_for_zrange (List.fold_right ZRange.union r[0 ~> 0]%zrange ls))
               end.

          Fixpoint type_for_range_bounded_by {t}
            : forall (r : range t)
                     (v : type.interp (type_for_range r)),
              bool
            := match t return forall (r : range t), type.interp (type_for_range r) -> bool with
               | type_primitive x => fun r v => primitive_bounded_by v r
               | prod A B => fun '((r, r') : range A * range B)
                                 '((a, a') : type.interp (type_for_range r) * type.interp (type_for_range r'))
                             => @type_for_range_bounded_by A r a && @type_for_range_bounded_by B r' a'
               | list A => fun r v => list_bounded_by v r
               end.
        End with_relax.
      End Range.

      Module Context.
        Notation t val := (PositiveMap.t { t : type & val t }).

        Definition find_at_type {val} (ctx : t val) {T} (p : positive) : option (val T)
          := match PositiveMap.find p ctx with
             | Some (existT t' r)
               => type.transport val t' T r
             | None => None
             end.
        Definition extendb {val} (ctx : t val) {T} (p : positive) (r : val T)
          : t val
          := PositiveMap.add p (existT _ T r) ctx.
      End Context.

      Module expr.
        Inductive expr {ident : type -> type -> Type} : type -> Type :=
        | Var (t : type) (p : positive) : expr t
        | TT : expr type.unit
        | AppIdent {s d} (idc : ident s d) (args : expr s) : expr d
        | Pair {A B} (a : expr A) (b : expr B) : expr (A * B)
        | Let_In {s d} (n : positive) (x : expr s) (body : expr d) : expr d.

        Module Export Notations.
          Bind Scope nexpr_scope with expr.
          Delimit Scope nexpr_scope with nexpr.

          Infix "@@" := AppIdent : nexpr_scope.
          Notation "( x , y , .. , z )" := (Pair .. (Pair x%nexpr y%nexpr) .. z%nexpr) : nexpr_scope.
          Notation "( )" := TT : nexpr_scope.
          Notation "()" := TT : nexpr_scope.
          Notation "'expr_let' x := A 'in' b" := (Let_In x A b) : nexpr_scope.
          Notation expr := expr.
        End Notations.

        Section with_ident.
          Import Context.
          Context {ident : type -> type -> Type}
                  (interp_ident : forall s d, ident s d -> type.interp s -> type.interp d).

          Fixpoint interp {t} (e : @expr ident t)
                   (ctx : Context.t type.interp)
            : option (type.interp t)
            := match e with
               | Var t n
                 => find_at_type ctx n
               | TT => Some tt
               | AppIdent s d idc args
                 => args <- @interp s args ctx;
                      Some (interp_ident s d idc args)
               | Pair A B a b
                 => a <- @interp A a ctx;
                      b <- @interp B b ctx;
                      Some (a, b)
               | Let_In s d n x f
                 => v <- @interp s x ctx;
                      let v' := v in
                      @interp d f (extendb ctx n v')
               end.
        End with_ident.
      End expr.
      Export expr.Notations.

      Module OfPHOAS.
        Module type.
          Module primitive.
            Definition compile (t : Compilers.type.primitive) : type.primitive
              := match t with
                 | Compilers.type.unit => type.unit
                 | Compilers.type.Z => type.Z
                 | type.nat => type.unit
                 | type.bool => type.unit
                 end.
          End primitive.
          Fixpoint compile (t : Compilers.type.type) : type
            := match t with
               | Compilers.type.prod A B
                 => type.prod (compile A) (compile B)
               | type.arrow s d => compile d
               | Compilers.type.list (Compilers.type.type_primitive A)
                 => type.list (primitive.compile A)
               | Compilers.type.list A
                 => type.list type.unit
               | Compilers.type.type_primitive t
                 => primitive.compile t
               end.
        End type.

        Module ident.
          Import BoundsAnalysis.ident.
          Definition is_let_in {s d} (idc : Compilers.Uncurried.expr.default.ident.ident s d)
          : bool
            := match idc with
               | ident.Let_In tx tC => true
               | _ => false
               end.

          Definition compile {s d} (idc : Compilers.Uncurried.expr.default.ident.ident s d)
            : option (ident (type.compile s) (type.compile d))
            := match idc in Compilers.Uncurried.expr.default.ident.ident s d
                     return option (ident (type.compile s) (type.compile d))
               with
               | default.ident.primitive Compilers.type.Z v => Some (primitive (t:=type.Z) v)
               | default.ident.primitive _ _ => None
               | ident.Let_In tx tC => None
               | ident.Nat_succ => None
               | ident.Nat_add => None
               | ident.Nat_mul => None
               | default.ident.nil (Compilers.type.type_primitive t)
                 => Some (@nil (type.primitive.compile t))
               | default.ident.nil _
                 => None
               | default.ident.cons (Compilers.type.type_primitive t)
                 => Some (@cons (type.primitive.compile t))
               | default.ident.cons _
                 => None
               | default.ident.fst A B
                 => Some (@fst (type.compile A) (type.compile B))
               | default.ident.snd A B
                 => Some (@snd (type.compile A) (type.compile B))
               | ident.bool_rect T => None
               | ident.nat_rect P => None
               | ident.pred => None
               | ident.list_rect A P => None
               | default.ident.List_nth_default T => None
               | ident.List_nth_default_concrete T d n
                 => Some (@List_nth (type.primitive.compile T) n)
               | default.ident.Z_mul
                 => Some Z.mul
               | default.ident.Z_add
                 => Some Z.add
               | default.ident.Z_sub
                 => Some Z.sub
               | ident.Z_shiftr n
                 => Some (Z.shiftr n)
               | ident.Z_shiftl n
                 => Some (Z.shiftl n)
               | ident.Z_land mask
                 => Some (Z.land mask)
               | ident.Z_mul_split_concrete s
                 => Some (Z.mul_split_concrete s)
               | ident.Z_add_get_carry_concrete s
                 => Some (Z.add_get_carry_concrete s)
               | ident.Z_sub_get_borrow_concrete s
                 => Some (Z.sub_get_borrow_concrete s)
               | ident.Z_add_with_get_carry_concrete s
                 => Some (Z.add_with_get_carry_concrete s)
               | default.ident.Z.zselect
                 => Some Z.zselect
               | default.ident.Z.add_modulo
                 => Some Z.add_modulo
               | ident.Z_pow
               | ident.Z_opp
               | ident.Z_div
               | ident.Z_modulo
               | ident.Z_eqb
               | ident.Z_leb
               | ident.Z_of_nat
               | ident.Z.mul_split
               | ident.Z.add_get_carry
               | ident.Z.add_with_get_carry
               | ident.Z.sub_get_borrow
                 => None
               end.
        End ident.

        Module expr.
          Import Indexed.expr.
          Section with_ident.
            Context {ident ident'}
                    (compile_ident : forall s d : Compilers.type.type,
                        ident s d
                        -> option (ident' (type.compile s) (type.compile d)))
                    (is_let_in
                     : forall s d,
                        ident s d
                        -> bool).

            Fixpoint compile' {t}
                     (e : @Compilers.Uncurried.expr.expr ident (fun _ => positive) t)
                     (base : positive)
              : positive * option (@expr ident' (type.compile t))
              := match e with
                 | Uncurried.expr.Var t v
                   => (base, Some (Var (type.compile t) v))
                 | Uncurried.expr.TT
                   => (base, Some TT)
                 | Uncurried.expr.AppIdent s d idc args
                   => if is_let_in _ _ idc
                      then
                        match args with
                        | Uncurried.expr.Pair A B a b
                          => let '(base, a) := @compile' A a base in
                             let '(base', b) := @compile' B b base in
                             (base',
                              match a, b with
                              | Some a, Some b
                                => type.transport _ _ _ (Let_In base a b)
                              | _, _ => None
                              end)
                        | _ => (base, None)
                        end
                      else
                        let '(base, args) := @compile' _ args base in
                        (base,
                         match compile_ident _ _ idc, args with
                         | Some idc, Some args
                           => Some (AppIdent idc args)
                         | Some _, None | None, None | None, Some _ => None
                         end)
                 | App s d f x => (base, None)
                 | Uncurried.expr.Pair A B a b
                   => let '(base, a) := @compile' A a base in
                      let '(base, b) := @compile' B b base in
                      (base,
                       match a, b with
                       | Some a, Some b => Some (Pair a b)
                       | _, _ => None
                       end)
                 | Abs s d f
                   => @compile' _ (f base) (Pos.succ base)
                 end.
          End with_ident.

          Definition compile {t}
                     (e : @Compilers.Uncurried.expr.expr default.ident (fun _ => positive) t)
            : option (@expr ident (type.compile t))
            := snd (@compile' _ _ (@ident.compile) (@ident.is_let_in) t e 1).

          Definition Compile {t}
                     (e : @default.Expr t)
            : option (@expr ident (type.compile t))
            := compile (e _).
        End expr.
      End OfPHOAS.
    End Indexed.
    Module Export Notations.
      Export BoundsAnalysis.type.Notations.
      Export BoundsAnalysis.Indexed.expr.Notations.
      Export BoundsAnalysis.ident.Notations.
      Import BoundsAnalysis.type.
      Import BoundsAnalysis.Indexed.expr.
      Import BoundsAnalysis.ident.
      Notation "[ ]" := (AppIdent ident.nil _) : nexpr_scope.
      Notation "x :: xs" := (AppIdent ident.cons (Pair x%nexpr xs%nexpr)) : nexpr_scope.
      Notation "x" := (AppIdent (ident.primitive x) _) (only printing, at level 9) : nexpr_scope.
      Notation "ls [[ n ]]"
        := (AppIdent ident.List.nth_default (_, ls, AppIdent (ident.primitive n%nat) _)%nexpr)
           : nexpr_scope.
      Notation "'x_' n" := (Var _ n) (at level 10, format "'x_' n") : nexpr_scope.
    End Notations.

    Module AdjustBounds.
      Local Notation "( a ; b )" := (existT _ a b) : core_scope.
      Import Indexed.
      Import type expr ident.
      Module ident.
        Section with_relax.
          Context (relax_zrange : zrange -> option zrange).

          Local Notation primitive_for_zrange := (primitive_for_zrange relax_zrange).
          Local Notation type_for_range := (type_for_range relax_zrange).

          Definition upper_lor_and_bounds (x y : BinInt.Z) : BinInt.Z
            := 2^(1 + Z.log2_up (Z.max x y)).
          Definition extreme_lor_land_bounds (x y : zrange) : zrange
            := let mx := ZRange.upper (ZRange.abs x) in
               let my := ZRange.upper (ZRange.abs y) in
               {| lower := -upper_lor_and_bounds mx my ; upper := upper_lor_and_bounds mx my |}.
          Definition extremization_bounds (f : zrange -> zrange -> zrange) (x y : zrange) : zrange
            := let (lx, ux) := x in
               let (ly, uy) := y in
               if ((lx <? 0) || (ly <? 0))%Z%bool
               then extreme_lor_land_bounds x y
               else f x y.
          Definition land_bounds : zrange -> zrange -> zrange
            := extremization_bounds
                 (fun x y
                  => let (lx, ux) := x in
                     let (ly, uy) := y in
                     {| lower := Z.min 0 (Z.min lx ly) ; upper := Z.max 0 (Z.min ux uy) |}).

          Definition split_bounds (r : zrange) (split_at : BinInt.Z) : zrange * zrange :=
            if upper r <? split_at
            then if 0 <=? lower r
                 then (r, {| lower := 0; upper := 0 |})
                 else ( {| lower := 0; upper := split_at - 1 |},
                        {| lower := 0; upper := Z.max ( -(lower r / split_at)) (upper r / split_at) |} )
            else ( {| lower := 0; upper := split_at - 1 |},
                   {| lower := 0; upper := Z.max ( -(lower r / split_at)) (upper r / split_at) |} ).

          (** TODO: Move me *)
          Definition smart_fst {A B} (e : @expr ident (A * B)) : @expr ident A
            := match e in @expr _ t
                     return @expr ident match t with
                                        | type.prod A B => A
                                        | _ => A
                                        end
                            -> @expr ident match t with
                                           | type.prod A B => A
                                           | _ => A
                                           end
               with
               | Pair A B a b => fun _ => a
               | _ => fun x => x
               end (AppIdent fst e).
          Definition smart_snd {A B} (e : @expr ident (A * B)) : @expr ident B
            := match e in @expr _ t
                     return @expr ident match t with
                                        | type.prod A B => B
                                        | _ => B
                                        end
                            -> @expr ident match t with
                                           | type.prod A B => B
                                           | _ => B
                                           end
               with
               | Pair A B a b => fun _ => b
               | _ => fun x => x
               end (AppIdent snd e).
          Definition smart_cast {A B : type.primitive} (e : @expr ident A) : @expr ident B
            := match transport (@expr ident) A B e with
               | Some e' => e'
               | None => AppIdent (cast A B) e
               end.

          (** We would like to just write the following.  Alas, we must await a solution to COQBUG(https://github.com/coq/coq/issues/6320) *)
          (**
<<
          Fixpoint list_map {A B : type.primitive}
                   (f : @expr ident A -> @expr ident B)
                   (e : @expr ident (type.list A))
            : option (@expr ident (type.list B))
            := match e with
               | AppIdent _ _ (ident.nil _) _
                 => Some (AppIdent ident.nil TT)
               | AppIdent _ _ (ident.cons _) (Pair _ _ x xs)
                 => option_map
                      (fun f_xs => AppIdent ident.cons (f x, f_xs))
                      (@list_map _ _ f xs)
               | _ => None
               end.
>> *)
          Fixpoint list_map {A B : type.primitive}
                   (f : @expr ident A -> @expr ident B)
                   (e : @expr ident (type.list A))
            : option (@expr ident (type.list B))
            := match e in @expr _ T
                     return (@expr ident match T with
                                         | type.list A => A
                                         | _ => A
                                         end
                             -> @expr ident B)
                            -> option (@expr ident (type.list B))
               with
               | AppIdent s (type.list d) idc args
                 => match args in expr s
                          return ident s (type.list d)
                                 -> (@expr ident d -> @expr ident B)
                                 -> option (expr (type.list B))
                    with
                    | Pair A' (type.list B') a' b'
                      => fun idc f
                         => match idc in ident s d
                                  return (match s return Type with
                                          | type.prod A _ => expr A
                                          | _ => Datatypes.unit
                                          end
                                          -> match s return Type with
                                             | type.prod _ (type.list A)
                                               => (expr A -> expr B)
                                                  -> option (expr (type.list B))
                                             | _ => Datatypes.unit
                                             end
                                          -> match d return Type with
                                             | type.list d
                                               => expr d -> expr B
                                             | _ => Datatypes.unit
                                             end
                                          -> option (expr (type.list B)))
                            with
                            | ident.nil t
                              => fun _ _ _ => Some (AppIdent ident.nil TT)
                            | ident.cons t
                              => fun x rec_xs f
                                 => option_map
                                      (fun f_xs => AppIdent ident.cons (f x, f_xs))
                                      (rec_xs f)
                            | _ => fun _ _ _ => None
                            end a' (fun f => @list_map _ _ f b') f
                    | TT
                      => match idc with
                         | ident.nil _
                           => fun _ _ => Some (AppIdent ident.nil TT)
                         | _ => fun _ _ => None
                         end
                    | _ => fun _ _ => None
                    end idc
               | _ => fun _ => None
               end f.

          Definition adjust_bounds {s d} (idc : ident s d)
            : option { r : range s & @expr ident (type_for_range r) }
              -> option { r : range d & @expr ident (type_for_range r) }
            := match idc in ident s d
                     return option { r : range s & @expr ident (type_for_range r) }
                            -> option { r : range d & @expr ident (type_for_range r) }
               with
               | primitive type.Z v
               | primitive (type.ZBounded _ _) v
                 => fun _ => Some (existT
                                     (fun r : range type.Z => @expr ident (type_for_range r))
                                     r[v~>v]%zrange
                                     (AppIdent (primitive (t:=primitive_for_zrange r[v~>v])
                                                          match relax_zrange r[v ~> v] as t
                                                                return type.interp (primitive_for_option_zrange t)
                                                          with
                                                          | Some _ => {| value := v ; value_bounded := admit (* XXX needs proof about relax *) |}
                                                          | None => v
                                                          end)
                                               TT))
               | primitive type.unit _ as idc
                 => fun _ => None
               | nil _ as idc
                 => fun _ => Some (existT _ Datatypes.nil (AppIdent nil TT))
               | cons t
                 => fun args
                    => args' <- args;
                         let '(r; args) := args' in
                         snd_args <- (list_map
                                        smart_cast
                                        (smart_snd args));
                           Some ((Datatypes.fst r :: Datatypes.snd r);
                                   (AppIdent
                                      cons
                                      (smart_cast (smart_fst args),
                                       snd_args)))
               | fst A B
                 => option_map
                      (fun '(existT r args)
                       => existT _ (Datatypes.fst r) (AppIdent fst args))
               | snd A B
                 => option_map
                      (fun '(existT r args)
                       => existT _ (Datatypes.snd r) (AppIdent snd args))
               | List_nth T n
                 => option_map
                      (fun '(existT r args)
		       => existT _ _ (AppIdent (List_nth n) args))
               | mul _ _ _
                 => option_map
                      (fun '(existT r args)
		       => existT _ (ZRange.four_corners BinInt.Z.mul (Datatypes.fst r) (Datatypes.snd r))
                                 (AppIdent (mul _ _ _) args))
               | add _ _ _
                 => option_map
                      (fun '(existT r args)
		       => existT _ (ZRange.four_corners BinInt.Z.add (Datatypes.fst r) (Datatypes.snd r))
                                 (AppIdent (add _ _ _) args))
               | sub _ _ _
                 => option_map
                      (fun '(existT r args)
		       => existT _ (ZRange.four_corners BinInt.Z.sub (Datatypes.fst r) (Datatypes.snd r))
                                 (AppIdent (sub _ _ _) args))
               | shiftr _ _ offset
                 => option_map
                      (fun '(existT r args)
		       => existT _ (ZRange.two_corners (fun v => BinInt.Z.shiftr v offset) r)
                                 (AppIdent (shiftr _ _ offset) args))
               | shiftl _ _ offset
                 => option_map
                      (fun '(existT r args)
		       => existT _ (ZRange.two_corners (fun v => BinInt.Z.shiftr v offset) r)
                                 (AppIdent (shiftl _ _ offset) args))
               | land _ _ mask
                 => option_map
                      (fun '(existT r args)
		       => existT _ (land_bounds r r[mask~>mask]%zrange)
                                 (AppIdent (land _ _ mask) args))
               | cast _ (type.ZBounded l u)
                 => option_map
                      (fun '(existT r[l'~>u'] args)
		       => existT _ r[Z.max l l' ~> Z.min u u']
                                 (AppIdent (cast _ _) args))
               | cast _ _
                 => fun _ => None
               | mul_split_concrete _ _ _ _ split_at
                 => option_map
                      (fun '(existT r args)
                       => existT _ (split_bounds (ZRange.four_corners (BinInt.Z.mul) (Datatypes.fst r) (Datatypes.snd r)) split_at)
                                 (AppIdent (mul_split_concrete _ _ _ _ split_at) args))
               | add_get_carry_concrete _ _ _ _ split_at
                 => option_map
                      (fun '(existT r args)
                       => existT _ (split_bounds (ZRange.four_corners (BinInt.Z.add) (Datatypes.fst r) (Datatypes.snd r)) split_at)
                                 (AppIdent (add_get_carry_concrete _ _ _ _ split_at) args))
               | add_with_get_carry_concrete _ _ _ _ _ split_at
                 => option_map
                      (fun '(existT r args)
                       => existT _ (split_bounds (ZRange.eight_corners (fun a b c => (a + b + c)%Z)
                                                                       (Datatypes.fst (Datatypes.fst r))
                                                                       (Datatypes.snd (Datatypes.fst r))
                                                                       (Datatypes.snd r)) split_at)
                                 (AppIdent (add_with_get_carry_concrete _ _ _ _ _ split_at) args))
               | sub_get_borrow_concrete _ _ _ _ split_at
                 => option_map
                      (fun '(existT r args)
                       => existT _ (split_bounds (ZRange.four_corners (BinInt.Z.sub) (Datatypes.fst r) (Datatypes.snd r)) split_at)
                                 (AppIdent (sub_get_borrow_concrete _ _ _ _ split_at) args))
               | zselect _ _ _ _
                 => option_map
                      (fun '(existT r args)
                       => existT _ (ZRange.union (Datatypes.snd (Datatypes.fst r)) (Datatypes.snd r))
                                 (AppIdent (zselect _ _ _ _) args))
               | add_modulo _ _ _ _
                 => option_map
                      (fun '(existT r args)
                       => existT _ (ZRange.union (ZRange.four_corners BinInt.Z.add
                                                                      (Datatypes.fst (Datatypes.fst r))
                                                                      (Datatypes.snd (Datatypes.fst r)))
                                                 (ZRange.eight_corners (fun x y m=> Z.max 0 (x + y - m)%Z)
                                                                      (Datatypes.fst (Datatypes.fst r))
                                                                      (Datatypes.snd (Datatypes.fst r))
                                                                      (Datatypes.snd r)))
                                 (AppIdent (add_modulo _ _ _ _) args))
               end%zrange%option.
        End with_relax.
      End ident.

      Module expr.
        Import ident.
        Section with_relax.
          Import Context.
          Context (relax_zrange : zrange -> option zrange).

          Local Notation RangeCtx := (Context.t range).
          Local Notation expr := (@expr ident).
          Local Notation type_for_range := (type_for_range relax_zrange).

          Local Open Scope option_scope.

          Fixpoint adjust_bounds (ctx : RangeCtx) {t} (e : expr t)
            : option { r : range t & expr (type_for_range r) }
            := match e with
               | TT => None
               | AppIdent s d idc args
                 => ident.adjust_bounds relax_zrange idc (@adjust_bounds ctx s args)
               | Var t x
                 => range <- find_at_type ctx x;
                      Some (range; (Var _ x))
               | Pair A B a b
                 => b1 <- @adjust_bounds ctx A a;
                      b2 <- @adjust_bounds ctx B b;
                      let '(range1; arg1) := b1 in
                      let '(range2; arg2) := b2 in
                      Some ((range1, range2); Pair arg1 arg2)
               | Let_In tx tC x ex eC
                 => bx <- @adjust_bounds ctx tx ex;
                      let '(range_x; ex') := bx in
                      let ctx' := extendb ctx x range_x in
                      bC <- @adjust_bounds ctx' tC eC;
                        let '(range_C; eC') := bC in
                        Some (range_C; Let_In x ex' eC')
               end.
        End with_relax.
      End expr.
    End AdjustBounds.

    Module OfPHOAS.
      Import Indexed.Range.
      Import Indexed.Context.
      Definition AnalyzeBounds
                 {s d : Compilers.type.Notations.type}
                 (relax_zrange : zrange -> option zrange)
                 (e : Expr (s -> d))
                 (s_bounds : range (Indexed.OfPHOAS.type.compile s))
      : option
          { bs : range (Indexed.OfPHOAS.type.compile d) &
                 @expr ident (type_for_range relax_zrange bs) }
        := let e := Indexed.OfPHOAS.expr.Compile e in
           match e with
           | Some e
             => let e := AdjustBounds.expr.adjust_bounds
                           relax_zrange
                           (PositiveMap.add 1%positive (existT _ _ s_bounds) (PositiveMap.empty _))
                           e in
                e
           | None => None
           end.

      Definition cast_back_primitive
                 {d : Compilers.type.primitive}
                 (relax_zrange : zrange -> option zrange)
                 {bs : zrange}
        : type.primitive.interp (primitive_for_zrange relax_zrange bs)
          -> Compilers.type.interp d
        := match d, relax_zrange bs as rbs
                 return type.primitive.interp (primitive_for_option_zrange rbs)
                        -> Compilers.type.interp d
           with
           | Compilers.type.unit, _ => fun _ => tt
           | Compilers.type.Z, Some r => fun x => type.value x
           | Compilers.type.Z, None => fun x => x
           | type.nat, _ => fun _ => 0%nat
           | type.bool, _ => fun _ => true
           end.

      Fixpoint cast_back
                 {d : Compilers.type.Notations.type}
                 (relax_zrange : zrange -> option zrange)
                 {bs : range (Indexed.OfPHOAS.type.compile d)}
                 (v : type.interp (type_for_range relax_zrange bs))
                 {struct d}
        : Compilers.type.interp d
        := match d
                 return (forall bs : range (Indexed.OfPHOAS.type.compile d),
                            type.interp (type_for_range relax_zrange bs)
                            -> Compilers.type.interp d)
           with
           | Compilers.type.type_primitive x => @cast_back_primitive _ _
           | Compilers.type.prod A B
             => fun (bs :
                       (* ignore this line, for type inference badness *) range (Indexed.OfPHOAS.type.compile A) * range (Indexed.OfPHOAS.type.compile B))
                    (v :
                       (* ignore this line, for type inference badness *) type.interp (type_for_range relax_zrange (fst bs)) * type.interp (type_for_range relax_zrange (snd bs)))
                => (@cast_back A relax_zrange (fst bs) (fst v),
                    @cast_back B relax_zrange (snd bs) (snd v))
           | type.arrow s d => fun bs v _ => @cast_back d relax_zrange bs v
           | Compilers.type.list (Compilers.type.type_primitive A)
             => fun bs
                => List.map (@cast_back_primitive A relax_zrange _)
           | Compilers.type.list A => fun _ _ => nil
           end bs v.

      Definition option_cast_back
                 {d : Compilers.type.Notations.type}
                 (relax_zrange : zrange -> option zrange)
                 {bs : range (Indexed.OfPHOAS.type.compile d)}
                 (v : option (type.interp (type_for_range relax_zrange bs)))
        := option_map (@cast_back d relax_zrange bs) v.

      Definition relax_is_good
                 (relax_zrange : zrange -> option zrange)
        : Prop
        := forall z z', relax_zrange z = Some z'
                        -> is_tighter_than_bool z z' = true.

      Definition cast_primitiveZ
                 (d : Compilers.type.primitive := Compilers.type.Z)
                 (relax_zrange : zrange -> option zrange)
                 {bs : zrange}
                 (v : Compilers.type.interp d)
                 (Hrelax : relax_is_good relax_zrange)
                 (Hv : is_bounded_by' None bs v)
        : type.primitive.interp (primitive_for_zrange relax_zrange bs).
      Proof.
        cbn in *; hnf in Hv; cbv [primitive_for_zrange primitive_for_option_zrange].
        specialize (Hrelax bs).
        destruct (relax_zrange bs) as [bs'|]; [ exists v | exact v ].
        clear d relax_zrange.
        abstract (
            specialize (Hrelax bs' eq_refl);
            unfold is_tighter_than_bool in *;
            rewrite Bool.andb_true_iff in *; split;
            destruct_head'_and;
            Z.ltb_to_lt;
            (apply Z.min_case_strong || apply Z.max_case_strong);
            omega
          ).
      Defined.

      Lemma cast_back_primitive_cast_primitive
            relax_zrange bs v Hrelax Hv
        : cast_back_primitive relax_zrange
                              (@cast_primitiveZ relax_zrange bs v Hrelax Hv)
          = v.
      Proof.
        cbv [cast_primitiveZ]; cbn.
        generalize (Hrelax bs).
        break_innermost_match; reflexivity.
      Qed.

      Definition Interp
                 {s d : Compilers.type.Notations.type}
                 (relax_zrange : zrange -> option zrange)
                 (s_bounds : range (Indexed.OfPHOAS.type.compile s))
                 {bs : range (Indexed.OfPHOAS.type.compile d)}
                 (args : type.interp (type_for_range relax_zrange s_bounds))
                 (e : @expr ident (type_for_range relax_zrange bs))
        : option (Compilers.type.interp d)
        := let ctx := extendb (PositiveMap.empty _) 1 args in
           let v := Indexed.expr.interp (@ident.interp) e ctx in
           option_cast_back relax_zrange v.

      Definition AnalyzeBoundsConst
                 {d : Compilers.type.Notations.type}
                 (relax_zrange : zrange -> option zrange)
                 (e : Expr d)
        : option
            { bs : range (Indexed.OfPHOAS.type.compile d) &
                   @expr ident (type_for_range relax_zrange bs) }
        := let e := Indexed.OfPHOAS.expr.Compile e in
           match e with
           | Some e
             => let e := AdjustBounds.expr.adjust_bounds
                           relax_zrange
                           (PositiveMap.empty _)
                           e in
                e
           | None => None
           end.

      Definition InterpConst
                 {d : Compilers.type.Notations.type}
                 (relax_zrange : zrange -> option zrange)
                 {bs : range (Indexed.OfPHOAS.type.compile d)}
                 (e : @expr ident (type_for_range relax_zrange bs))
        : option (Compilers.type.interp d)
        := let ctx := PositiveMap.empty _ in
           let v := Indexed.expr.interp (@ident.interp) e ctx in
           option_cast_back relax_zrange v.
    End OfPHOAS.
  End BoundsAnalysis.*)
End Compilers.
Import Associational Positional Compilers.
Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.

(** TODO: FILES:
- Uncurried expr + reification + list canonicalization
- cps
- partial reduction + DCE
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

Require Import AdmitAxiom.

Example test1 : True.
Proof.
  let v := Reify ((fun x => 2^x) 255)%Z in
  pose v as E.
  vm_compute in E.
  pose (PartialReduce (canonicalize_list_recursion E)) as E'.
  vm_compute in E'.
  lazymatch (eval cbv delta [E'] in E') with
  | (fun var => AppIdent (ident.primitive ?v) TT) => idtac
  end.
  constructor.
Qed.
Module test2.
  Example test2 : True.
  Proof.
    let v := Reify (fun y : Z
                    => (fun k : Z * Z -> Z * Z
                        => dlet_nd x := (y * y) in
                            dlet_nd z := (x * x) in
                            k (z, z))
                         (fun v => v)) in
    pose v as E.
    vm_compute in E.
    pose (PartialReduce (canonicalize_list_recursion E)) as E'.
    vm_compute in E'.
    lazymatch (eval cbv delta [E'] in E') with
    | (fun var : type -> Type =>
         (λ x : var (type.type_primitive type.Z),
                expr_let x0 := (Var x * Var x) in
              expr_let x1 := (Var x0 * Var x0) in
              (Var x1, Var x1))%expr) => idtac
    end.
    pose (PartialReduceWithBounds1 (fun r => Some r) E' r[0~>10]%zrange) as E''.
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
  Proof.
    let v := Reify (fun y : Z
                    => dlet_nd x := dlet_nd x := (y * y) in
                        (x * x) in
                        dlet_nd z := dlet_nd z := (x * x) in
                        (z * z) in
                        (z * z)) in
    pose v as E.
    vm_compute in E.
    pose (PartialReduce (CPS.CallFunWithIdContinuation (CPS.Translate (canonicalize_list_recursion E)))) as E'.
    vm_compute in E'.
    lazymatch (eval cbv delta [E'] in E') with
    | (fun var : type -> Type =>
         (λ x : var (type.type_primitive type.Z),
                expr_let x0 := Var x * Var x in
              expr_let x1 := Var x0 * Var x0 in
              expr_let x2 := Var x1 * Var x1 in
              expr_let x3 := Var x2 * Var x2 in
              Var x3 * Var x3)%expr)
      => idtac
    end.
    pose (PartialReduceWithBounds1 (fun r => Some r) E' r[0~>10]%zrange) as E'''.
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
  Proof.
    let v := Reify (fun y : (list Z * list Z)
                    => dlet_nd x := List.nth_default (-1) (fst y) 0 in
                        dlet_nd z := List.nth_default (-1) (snd y) 0 in
                        dlet_nd xz := (x * z) in
                        (xz :: xz :: nil)) in
    pose v as E.
    vm_compute in E.
    pose (PartialReduce (CPS.CallFunWithIdContinuation (CPS.Translate (canonicalize_list_recursion E)))) as E'.
    lazy in E'.
    clear E.
    pose (PartialReduceWithBounds1 (fun r => Some r) E' ([r[0~>10]%zrange],[r[0~>10]%zrange])) as E''.
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
  Proof.
    let v := Reify (fun y : (Z * Z)
                    => dlet_nd x := (13 * (fst y * snd y)) in
                        x) in
    pose v as E.
    vm_compute in E.
    pose (ReassociateSmallConstants.Reassociate (2^8) (PartialReduce (CPS.CallFunWithIdContinuation (CPS.Translate (canonicalize_list_recursion E))))) as E'.
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
  Proof.
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
    pose (PartialReduce E') as E''.
    lazy in E''.
    lazymatch eval cbv delta [E''] in E'' with
    | fun var : type -> Type => (λ x : var (type.type_primitive type.Z), Var x)%expr
      => idtac
    end.
    exact I.
  Qed.
End test6.

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
  let E' := constr:(PartialReduce (CPS.CallFunWithIdContinuation (CPS.Translate (canonicalize_list_recursion E)))) in
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

Derive carry_mul_gen
       SuchThat (forall (w : nat -> Z)
                        (fg : list Z * list Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (len_c : nat)
                        (idxs : list nat)
                        (len_idxs : nat),
                    Interp (t:=type.reify_type_of carry_mulmod)
                           carry_mul_gen w s c n len_c idxs len_idxs fg
                    = carry_mulmod w s c n len_c idxs len_idxs fg)
       As carry_mul_gen_correct.
Proof. Time cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Time Qed.

Derive carry_gen
       SuchThat (forall (w : nat -> Z)
                        (f : list Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (len_c : nat)
                        (idxs : list nat)
                        (len_idxs : nat),
                    Interp (t:=type.reify_type_of carrymod)
                           carry_gen w s c n len_c idxs len_idxs f
                    = carrymod w s c n len_c idxs len_idxs f)
       As carry_gen_correct.
Proof. cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Qed.

Derive encode_gen
       SuchThat (forall (w : nat -> Z)
                        (v : Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (len_c : nat),
                    Interp (t:=type.reify_type_of encodemod)
                           encode_gen w s c n len_c v
                    = encodemod w s c n len_c v)
       As encode_gen_correct.
Proof. cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Qed.

Derive add_gen
       SuchThat (forall (w : nat -> Z)
                        (fg : list Z * list Z)
                        (n : nat),
                    Interp (t:=type.reify_type_of addmod)
                           add_gen w n fg
                    = addmod w n fg)
       As add_gen_correct.
Proof. cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Qed.

Derive sub_gen
       SuchThat (forall (w : nat -> Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (len_c : nat)
                        (coef : Z)
                        (fg : list Z * list Z),
                    Interp (t:=type.reify_type_of submod)
                           sub_gen w s c n len_c coef fg
                    = submod w s c n len_c coef fg)
       As sub_gen_correct.
Proof. cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Qed.

Derive opp_gen
       SuchThat (forall (w : nat -> Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (len_c : nat)
                        (coef : Z)
                        (f : list Z),
                    Interp (t:=type.reify_type_of oppmod)
                           opp_gen w s c n len_c coef f
                    = oppmod w s c n len_c coef f)
       As opp_gen_correct.
Proof. cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Qed.

Definition zeromod w n s c len_c := encodemod w n s c len_c 0.
Definition onemod w n s c len_c := encodemod w n s c len_c 1.

Derive zero_gen
       SuchThat (forall (w : nat -> Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (len_c : nat),
                    Interp (t:=type.reify_type_of zeromod)
                           zero_gen w s c n len_c
                    = zeromod w s c n len_c)
       As zero_gen_correct.
Proof. cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Qed.

Derive one_gen
       SuchThat (forall (w : nat -> Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (len_c : nat),
                    Interp (t:=type.reify_type_of onemod)
                           one_gen w s c n len_c
                    = onemod w s c n len_c)
       As one_gen_correct.
Proof. cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Qed.

Definition expanding_id (n : nat) (ls : list Z) := expand_list (-1)%Z ls n.

Lemma expanding_id_id n ls (H : List.length ls = n)
  : expanding_id n ls = ls.
Proof.
  unfold expanding_id. rewrite expand_list_correct by assumption; reflexivity.
Qed.

Derive id_gen
       SuchThat (forall (n : nat)
                        (ls : list Z),
                    Interp (t:=type.reify_type_of expanding_id)
                           id_gen n ls
                    = expanding_id n ls)
       As id_gen_correct.
Proof. cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Qed.

Module Pipeline.
  Inductive ErrorMessage :=
  | Computed_bounds_are_not_tight_enough
      {t} (computed_bounds expected_bounds : ZRange.type.option.interp t)
  | Bounds_analysis_failed
  | Return_type_mismatch {T'} (found expected : T')
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

  Definition BoundsPipeline
             (with_dead_code_elimination : bool)
             relax_zrange
             {s d}
             arg_bounds
             out_bounds
             (E : Expr (s -> d))
  : ErrorT (Expr (s -> d))
    := let E := PartialReduce E in
       let E := if with_dead_code_elimination then DeadCodeElimination.EliminateDead E else E in
       let E := ReassociateSmallConstants.Reassociate (2^8) E in
       let E := CheckedPartialReduceWithBounds1 relax_zrange E arg_bounds out_bounds in
       let E := match E with
                | inl v => Success v
                | inr b => Error (Computed_bounds_are_not_tight_enough b (ZRange.type.option.Some out_bounds))
                end in
       E.

  Lemma BoundsPipeline_correct
             (with_dead_code_elimination : bool)
             relax_zrange
             (Hrelax : forall r r' z : zrange,
                 (z <=? r)%zrange = true -> relax_zrange r = Some r' -> (z <=? r')%zrange = true)
             {s d}
             arg_bounds
             out_bounds
             (E : Expr (s -> d))
             rv
             (Hrv : BoundsPipeline with_dead_code_elimination relax_zrange arg_bounds out_bounds E = Success rv)
    : forall arg
             (Harg : ZRange.type.is_bounded_by arg_bounds arg = true),
      ZRange.type.is_bounded_by out_bounds (Interp rv arg) = true
      /\ Interp rv arg = Interp E arg.
  Proof.
    cbv [BoundsPipeline] in *; edestruct (CheckedPartialReduceWithBounds1 _ _ _ _) eqn:H.
    inversion Hrv; subst.
    { intros; eapply CheckedPartialReduceWithBounds1_Correct in H; [ | eassumption.. ].
      destruct H as [H0 H1].
      split; [ exact H1 | rewrite H0 ].
      exact admit. (* interp correctness *) }
    { congruence. }
  Qed.

  Definition BoundsPipelineConst
             (with_dead_code_elimination : bool)
             relax_zrange
             {t}
             bounds
             (E : Expr t)
  : ErrorT (Expr t)
    := let E := PartialReduce E in
       let E := if with_dead_code_elimination then DeadCodeElimination.EliminateDead E else E in
       let E := ReassociateSmallConstants.Reassociate (2^8) E in
       let E := CheckedPartialReduceWithBounds0 relax_zrange E bounds in
       let E := match E with
                | inl v => Success v
                | inr b => Error (Computed_bounds_are_not_tight_enough b (ZRange.type.option.Some bounds))
                end in
       E.

  Lemma BoundsPipelineConst_correct
             (with_dead_code_elimination : bool)
             relax_zrange
             (Hrelax : forall r r' z : zrange,
                 (z <=? r)%zrange = true -> relax_zrange r = Some r' -> (z <=? r')%zrange = true)
             {d}
             bounds
             (E : Expr d)
             rv
             (Hrv : BoundsPipelineConst with_dead_code_elimination relax_zrange bounds E = Success rv)
    : ZRange.type.is_bounded_by bounds (Interp rv) = true
      /\ Interp rv = Interp E.
  Proof.
    cbv [BoundsPipelineConst] in *; edestruct (CheckedPartialReduceWithBounds0 _ _ _) eqn:H.
    inversion Hrv; subst.
    { intros; eapply CheckedPartialReduceWithBounds0_Correct in H; [ | eassumption.. ].
      destruct H as [H0 H1].
      split; [ exact H1 | rewrite H0 ].
      exact admit. (* interp correctness *) }
    { congruence. }
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

Definition relax_zrange_gen (possible_values : list Z) : zrange -> option zrange
  := (fun '(r[ l ~> u ])
      => if (0 <=? l)%Z
         then option_map (fun u => r[0~>2^u-1])
                         (round_up_bitwidth_gen possible_values (Z.log2_up (u+1)))
         else None)%zrange.

(** TODO: Move me? *)
Definition app_and_maybe_cancel {s d} (f : Expr (s -> d)) (x : Expr s) : Expr d
  := (fun var
      => let f' := (match f _ in expr.expr t return option match t with
                                                           | (s -> d)%ctype => expr s -> expr d
                                                           | _ => unit
                                                           end with
                    | Abs s d f => Some f
                    | _ => None
                    end) in
         match f' with
         | Some f => unexpr (f (x _))
         | None => f var @ x var
         end%expr).

Derive rweight
       SuchThat (forall (limbwidth : Q)
                        (i : nat),
                    Interp (t:=(type.nat -> type.Z)%ctype) (rweight limbwidth) i
                    = 2^Qceiling(limbwidth*i))
       As Interp_rweight.
Proof.
  intros; destruct limbwidth as [n d].
  cbv [Qceiling Qfloor Qopp Qnum Qdiv Qplus inject_Z Qmult Qinv Qden].
  rewrite Pos.mul_1_r.
  remember (Z.pos d) as dz.
  etransitivity.
  Focus 2.
  { repeat match goal with H : _ |- _ => clear H end.
    revert n dz i.
    lazymatch goal with
    | [ |- forall a b c, ?ev = @?RHS a b c ]
      => refine (fun a b c => f_equal (fun F => F a b c) (_ : _ = RHS));
           clear a b c
    end.
    Reify_rhs ().
    reflexivity. }
  Unfocus.
  cbv beta.
  let E := lazymatch goal with | [ |- _ = expr.Interp _ ?E ?n ?dz ?i ] => E end in
  let E := constr:(app_and_maybe_cancel
                     (app_and_maybe_cancel
                        (canonicalize_list_recursion E)
                        (GallinaReify.Reify n))
                     (GallinaReify.Reify dz)) in
  let E := (eval vm_compute in E) in
  transitivity (Interp E i);
    [
    | lazy [expr.Interp expr.interp for_reification.ident.interp ident.interp]; reflexivity ].
  subst dz rweight.
  set (q := n # d).
  change n with (Qnum q); change d with (Qden q); clearbody q; clear.
  reflexivity.
Qed.

Require Import Crypto.Algebra.Ring.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

(** XXX TODO: Translate Jade's python script *)
Section rcarry_mul.
  Context (n : nat)
          (s : Z)
          (c : list (Z * Z))
          (machine_wordsize : Z).

  Let limbwidth := (Z.log2_up (s - Associational.eval c) / Z.of_nat n)%Q.
  Let idxs := (seq 0 n ++ [0; 1])%list%nat.
  Let upperbound_tight := (2^Qceiling limbwidth + 2^(Qceiling limbwidth - 3))%Z.
  Let upperbound_loose := (3 * upperbound_tight)%Z.
  Let f_bounds_tight := List.repeat r[0~>upperbound_tight]%zrange n.
  Let f_bounds_loose := List.repeat r[0~>upperbound_loose]%zrange n.
  Let prime_bound : ZRange.type.interp (type.Z)
    := r[0~>(s - Associational.eval c - 1)]%zrange.

  Definition relax_zrange_of_machine_wordsize
    := relax_zrange_gen [machine_wordsize; 2 * machine_wordsize]%Z.
  Local Arguments relax_zrange_of_machine_wordsize / .

  Let rw := rweight limbwidth.
  Let rs := GallinaReify.Reify s.
  Let rc := GallinaReify.Reify c.
  Let rn := GallinaReify.Reify n.
  Let ridxs := GallinaReify.Reify idxs.
  Let rlen_c := GallinaReify.Reify (List.length c).
  Let rlen_idxs := GallinaReify.Reify (List.length idxs).
  Let rcoef := GallinaReify.Reify 2.
  Let relax_zrange := relax_zrange_of_machine_wordsize.
  Let tight_bounds : ZRange.type.interp (type.list type.Z)
    := f_bounds_tight.
  Let tight2_bounds : ZRange.type.interp (type.list type.Z * type.list type.Z)
    := (tight_bounds, tight_bounds).
  Let loose_bounds : ZRange.type.interp (type.list type.Z)
    := f_bounds_loose.
  Let loose2_bounds : ZRange.type.interp (type.list type.Z * type.list type.Z)
    := (loose_bounds, loose_bounds).

  Lemma relax_zrange_of_machine_wordsize_good
    : forall r r' z : zrange,
      (z <=? r)%zrange = true -> relax_zrange_of_machine_wordsize r = Some r' -> (z <=? r')%zrange = true.
  Proof.
    cbv [is_tighter_than_bool relax_zrange_of_machine_wordsize relax_zrange_gen]; intros *.
    pose proof (Z.log2_up_nonneg (upper r + 1)).
    rewrite !Bool.andb_true_iff; destruct_head' zrange; cbn [ZRange.lower ZRange.upper] in *.
    cbv [round_up_bitwidth_gen fold_right option_map].
    break_innermost_match; intros; destruct_head'_and;
      inversion_option; inversion_zrange;
        subst;
        repeat apply conj;
        Z.ltb_to_lt; try omega;
          destruct (Z_gt_le_dec 0 machine_wordsize);
          try (rewrite <- Z.log2_up_le_pow2_full in *; omega).
  Qed.

  Let relax_zrange_good
    : forall r r' z : zrange,
      (z <=? r)%zrange = true -> relax_zrange r = Some r' -> (z <=? r')%zrange = true
    := relax_zrange_of_machine_wordsize_good.

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

  Lemma check_args_success_id {T} {rv : T} {res}
    : check_args res = Pipeline.Success rv
      -> res = Pipeline.Success rv.
  Proof.
    cbv [check_args]; break_innermost_match; congruence.
  Qed.

  Local Ltac solve_correct_gen pipeline_lem gen_correct :=
    let Hrv := lazymatch goal with H : ?rop = Pipeline.Success _ |- _ => H end in
    let rop := lazymatch type of Hrv with ?rop = Pipeline.Success _ => rop end in
    hnf; intros; cbv [rop] in Hrv;
    eapply pipeline_lem in Hrv; [ | eassumption.. ];
    let Hrv' := fresh "Hrv'" in
    destruct Hrv as [Hrv Hrv'];
    apply conj; [ exact Hrv | rewrite Hrv' ];
    repeat match goal with H := _ |- _ => subst H end;
    erewrite <- gen_correct;
    cbv [expr.Interp];
    cbn [expr.interp];
    f_equal;
    cbn -[reify_list];
    try (rewrite interp_reify_list, map_map; cbn;
         erewrite map_ext with (g:=id), map_id; try reflexivity);
    try (intros []; reflexivity).
  Local Ltac solve_correct gen_correct :=
    solve_correct_gen Pipeline.BoundsPipeline_correct gen_correct.
  Local Ltac solve_correct_const gen_correct :=
    solve_correct_gen Pipeline.BoundsPipelineConst_correct gen_correct.

  Let BoundsPipeline21 in_bounds out_bounds res
    := let res := Pipeline.BoundsPipeline
                    false
                    relax_zrange
                    (s:=(type.list type.Z * type.list type.Z)%ctype)
                    (d:=(type.list type.Z)%ctype)
                    (in_bounds, in_bounds)
                    out_bounds
                    res in
       res.

  Let BoundsPipeline11 in_bounds out_bounds res
    := let res := Pipeline.BoundsPipeline
                    false
                    relax_zrange
                    (s:=(type.list type.Z)%ctype)
                    (d:=(type.list type.Z)%ctype)
                    (in_bounds)
                    out_bounds
                    res in
       res.

  Definition rexpr_1_correctT_Interp
             {t}
             t_out
             (Interp : Expr t -> _)
             out_bounds
             (f : type.interp t_out)
             rv
    := (ZRange.type.is_bounded_by out_bounds (Interp rv) = true
        /\ Interp rv = f).

  Definition rexpr_n1_correctT
             t_in t_out
             in_bounds out_bounds
             (f : type.interp t_in -> type.interp t_out)
             rv
    := forall arg
              (Harg : ZRange.type.is_bounded_by in_bounds arg = true),
      @rexpr_1_correctT_Interp (t_in -> t_out) t_out (fun rv => Interp rv arg) out_bounds (f arg) rv.

  Definition rexpr_1_correctT
             t_out
             out_bounds
             (f : type.interp t_out)
             rv
    := @rexpr_1_correctT_Interp t_out t_out Interp out_bounds f rv.

  Definition rexpr_21_correctT
             in_bounds out_bounds
             (f : _ -> type.interp (type.list type.Z))
             rv
    := @rexpr_n1_correctT (type.list type.Z * type.list type.Z)
                          (type.list type.Z)
                          (in_bounds, in_bounds) out_bounds f rv.

  Definition rexpr_11_correctT
             in_bounds out_bounds
             (f : _ -> type.interp (type.list type.Z))
             rv
    := @rexpr_n1_correctT (type.list type.Z)
                          (type.list type.Z)
                          in_bounds out_bounds f rv.

  Definition rexpr_Z1_correctT
             in_bounds out_bounds
             (f : _ -> type.interp (type.list type.Z))
             rv
    := @rexpr_n1_correctT type.Z (type.list type.Z)
                          in_bounds out_bounds f rv.

  Definition rexpr_01_correctT
             out_bounds
             (f : type.interp (type.list type.Z))
             rv
    := @rexpr_1_correctT (type.list type.Z) out_bounds f rv.

  Definition rcarry_mul
    := let res := BoundsPipeline21
                    loose_bounds
                    tight_bounds
                    (fun var
                     => (carry_mul_gen _)
                          @ (rw _)
                          @ (rs _)
                          @ (rc _)
                          @ (rn _)
                          @ (rlen_c _)
                          @ (ridxs _)
                          @ (rlen_idxs _)
                    )%expr in
       res.

  Definition rcarry_mul_correctT
             rv
    := Eval hnf in
        rexpr_21_correctT
          loose_bounds tight_bounds
          (carry_mulmod (Interp rw) s c n (Interp rlen_c) idxs (Interp rlen_idxs))
          rv.

  Lemma rcarry_mul_correct
        rv (Hrv : rcarry_mul = Pipeline.Success rv)
    : rcarry_mul_correctT rv.
  Proof. solve_correct carry_mul_gen_correct. Qed.

  Definition rcarry
    := let res := Pipeline.BoundsPipeline
                    false
                    relax_zrange
                    (s:=(type.list type.Z)%ctype)
                    (d:=(type.list type.Z)%ctype)
                    loose_bounds
                    tight_bounds
                    (fun var
                     => (carry_gen _)
                          @ (rw _)
                          @ (rs _)
                          @ (rc _)
                          @ (rn _)
                          @ (rlen_c _)
                          @ (ridxs _)
                          @ (rlen_idxs _)
                    )%expr in
       res.

  Definition rcarry_correctT
             rv
    := Eval hnf in
        rexpr_11_correctT
          loose_bounds tight_bounds
          (carrymod (Interp rw) s c n (Interp rlen_c) idxs (Interp rlen_idxs))
          rv.

  Lemma rcarry_correct
        rv (Hrv : rcarry = Pipeline.Success rv)
    : rcarry_correctT rv.
  Proof. solve_correct carry_gen_correct. Qed.

  Definition rrelax
    := let res := Pipeline.BoundsPipeline
                    false
                    relax_zrange
                    (s:=(type.list type.Z)%ctype)
                    (d:=(type.list type.Z)%ctype)
                    tight_bounds
                    loose_bounds
                    (fun var
                     => (id_gen _)
                          @ (rn _)
                    )%expr in
       res.

  Definition rrelax_correctT
             rv
    := Eval hnf in
        rexpr_11_correctT
          tight_bounds loose_bounds
          (expanding_id n)
          rv.

  Lemma rrelax_correct
        rv (Hrv : rrelax = Pipeline.Success rv)
    : rrelax_correctT rv.
  Proof. solve_correct id_gen_correct. Qed.

  Definition radd
    := let res := BoundsPipeline21
                    tight_bounds
                    loose_bounds
                    (fun var
                     => (add_gen _)
                          @ (rw _)
                          @ (rn _)
                    )%expr in
       res.

  Definition radd_correctT
             rv
    := Eval hnf in
        rexpr_21_correctT
          tight_bounds loose_bounds
          (addmod (Interp rw) n)
          rv.

  Lemma radd_correct
        rv (Hrv : radd = Pipeline.Success rv)
    : radd_correctT rv.
  Proof. solve_correct add_gen_correct. Qed.

  Definition rsub
    := let res := BoundsPipeline21
                    tight_bounds
                    loose_bounds
                    (fun var
                     => (sub_gen _)
                          @ (rw _)
                          @ (rs _)
                          @ (rc _)
                          @ (rn _)
                          @ (rlen_c _)
                          @ (rcoef _)
                    )%expr in
       res.

  Definition rsub_correctT
             rv
    := Eval hnf in
        rexpr_21_correctT
          tight_bounds loose_bounds
          (submod (Interp rw) s c n (Interp rlen_c) (Interp rcoef))
          rv.

  Lemma rsub_correct
        rv (Hrv : rsub = Pipeline.Success rv)
    : rsub_correctT rv.
  Proof. solve_correct sub_gen_correct. Qed.

  Definition ropp
    := let res := BoundsPipeline11
                    tight_bounds
                    loose_bounds
                    (fun var
                     => (opp_gen _)
                          @ (rw _)
                          @ (rs _)
                          @ (rc _)
                          @ (rn _)
                          @ (rlen_c _)
                          @ (rcoef _)
                    )%expr in
       res.

  Definition ropp_correctT
             rv
    := Eval hnf in
        rexpr_11_correctT
          tight_bounds loose_bounds
          (oppmod (Interp rw) s c n (Interp rlen_c) (Interp rcoef))
          rv.

  Lemma ropp_correct
        rv (Hrv : ropp = Pipeline.Success rv)
    : ropp_correctT rv.
  Proof. solve_correct opp_gen_correct. Qed.

  Definition rencode
    := let res := Pipeline.BoundsPipeline
                    false
                    relax_zrange
                    (s:=type.Z)
                    (d:=(type.list type.Z)%ctype)
                    (prime_bound)
                    tight_bounds
                    (fun var
                     => (encode_gen _)
                          @ (rw _)
                          @ (rs _)
                          @ (rc _)
                          @ (rn _)
                          @ (rlen_c _)
                    )%expr in
       res.

  Definition rencode_correctT
             rv
    := Eval hnf in
        rexpr_Z1_correctT
          prime_bound tight_bounds
          (encodemod (Interp rw) s c n (Interp rlen_c))
          rv.

  Lemma rencode_correct
        rv (Hrv : rencode = Pipeline.Success rv)
    : rencode_correctT rv.
  Proof. solve_correct encode_gen_correct. Qed.

  Definition rzero
    := let res := Pipeline.BoundsPipelineConst
                    false
                    relax_zrange
                    (t:=(type.list type.Z)%ctype)
                    tight_bounds
                    (fun var
                     => (zero_gen _)
                          @ (rw _)
                          @ (rs _)
                          @ (rc _)
                          @ (rn _)
                          @ (rlen_c _)
                    )%expr in
       res.

  Definition rzero_correctT
             rv
    := Eval hnf in
        rexpr_01_correctT
          tight_bounds
          (zeromod (Interp rw) s c n (Interp rlen_c))
          rv.

  Lemma rzero_correct
        rv (Hrv : rzero = Pipeline.Success rv)
    : rzero_correctT rv.
  Proof. solve_correct_const zero_gen_correct. Qed.

  Definition rone
    := let res := Pipeline.BoundsPipelineConst
                    false
                    relax_zrange
                    (t:=(type.list type.Z)%ctype)
                    tight_bounds
                    (fun var
                     => (one_gen _)
                          @ (rw _)
                          @ (rs _)
                          @ (rc _)
                          @ (rn _)
                          @ (rlen_c _)
                    )%expr in
       res.

  Definition rone_correctT
             rv
    := Eval hnf in
        rexpr_01_correctT
          tight_bounds
          (onemod (Interp rw) s c n (Interp rlen_c))
          rv.

  Lemma rone_correct
        rv (Hrv : rone = Pipeline.Success rv)
    : rone_correctT rv.
  Proof. solve_correct_const one_gen_correct. Qed.

  Definition encodedT
    := { ls : list Z
       |  ZRange.type.is_bounded_by (t:=type.list type.Z) tight_bounds ls = true }.

  Definition list_of_encodedT (v : encodedT) : list _
    := proj1_sig v.

  Lemma length_list_of_encodedT v : List.length (list_of_encodedT v) = n.
  Proof.
    destruct v as [v H]; cbv [ZRange.type.is_bounded_by] in H; cbn in H |- *.
    exact admit (*destruct v; cbn in *; [ | discriminate ].
    apply BoundsAnalysis.Indexed.Range.length_list_bounded_by in H.
    inversion_option; subst.
    etransitivity; [ exact H | ].
    subst tight_bounds f_bounds_tight.
    rewrite repeat_length; reflexivity*).
  Qed.

  Let m : positive := Z.to_pos (s - Associational.eval c).
  Definition Zdecode (v : encodedT)
    := list_of_encodedT v.
  Definition Fdecode (v : encodedT) : F m
    := F.of_Z m (Positional.eval (Interp rw) n (Zdecode v)).
  Definition encodedT_eq (x y : encodedT)
    := Fdecode x = Fdecode y.

  Lemma length_Zdecode v : List.length (Zdecode v) = n.
  Proof. apply length_list_of_encodedT. Qed.

  Section make_ring.
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
                   | rewrite repeat_length
                   | progress cbv [Qceiling Qfloor Qopp Qdiv Qplus inject_Z Qmult Qinv] in *
                   | progress cbv [Qle] in *
                   | progress cbn -[reify_list] in *
                   | progress intros
                   | solve [ auto ] ].

    Lemma use_curve_good
      : Z.pos m = s - Associational.eval c
        /\ (Interp rw 0%nat = 1)
        /\ (forall i, Interp rw i <> 0)
        /\ ' m <> 0
        /\ s - Associational.eval c <> 0
        /\ s <> 0
        /\ 0 < machine_wordsize
        /\ n <> 0%nat
        /\ List.length (Interp ridxs) = Interp rlen_idxs
        /\ List.length (Interp rc) = Interp rlen_c
        /\ List.length idxs = Interp rlen_idxs
        /\ List.length c = Interp rlen_c
        /\ List.length tight_bounds = n
        /\ List.length loose_bounds = n
        /\ forall i, Interp rw (S i) / Interp rw i <> 0.
    Proof.
      clear -curve_good.
      cbv [check_args] in curve_good.
      break_innermost_match_hyps; try discriminate.
      rewrite negb_false_iff in *.
      Z.ltb_to_lt.
      rewrite Qle_bool_iff in *.
      rewrite NPeano.Nat.eqb_neq in *.
      generalize (@pow_ceil_mul_nat_divide_nonzero 2 limbwidth).
      generalize (@pow_ceil_mul_nat_nonzero 2 limbwidth).
      intros.
      cbv [Qle] in *; cbn [Qnum Qden] in *.
      cbv [Qceiling Qfloor Qopp Qdiv Qplus inject_Z Qmult Qinv] in *.
      cbn [Qnum Qden] in *.
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
      { use_curve_good_t. }
      { use_curve_good_t. }
      { use_curve_good_t. }
      { use_curve_good_t. }
      { use_curve_good_t. }
    Qed.

    Local Lemma m_eq : Z.pos m = s - Associational.eval c.
    Proof. apply use_curve_good. Qed.

    Local Lemma sc_pos : 0 < s - Associational.eval c.
    Proof. pose proof use_curve_good; destruct_head'_and; lia. Qed.

    Local Lemma length_tight_bounds : List.length tight_bounds = n.
    Proof. apply use_curve_good. Qed.

    Local Lemma length_loose_bounds : List.length loose_bounds = n.
    Proof. apply use_curve_good. Qed.

    Local Arguments Z.pow !_ !_ .

    Local Ltac specialize_from_interp _ :=
      repeat match goal with
             | [ H := Interp ?rv ?arg, Hc : context[?rv] |- _ ]
               => unique pose proof (Hc arg)
             end.
    Local Ltac specialize_with_bounded _ :=
      repeat match goal with
             | _ => progress cbv [Zdecode list_of_encodedT] in *
             | _ => progress cbn [ZRange.type.is_bounded_by proj1_sig] in *
             | [ H : context[andb ?x ?y = true] |- _ ]
               => rewrite (Bool.andb_true_iff x y) in H
             | [ H : _ /\ _ -> _ |- _ ] => specialize (fun a b => H (conj a b))
             | _ => progress destruct_head'_and
             | [ H : ?f (proj1_sig ?v) = true -> _ |- _ ]
               => specialize (H (proj2_sig v)); hnf in H
             | [ H : ?x = true -> _, H' : ?x = true |- _ ]
               => specialize (H H'); hnf in H
             | [ H : ?x = true |- { pf : ?x = true | _ } ] => exists H
             end.
    Local Ltac rewrite_interp _ :=
      repeat match goal with
             | [ H := _ |- _ ] => subst H
             | [ H : ?x = _ |- context[?x] ] => rewrite H
             | _ => rewrite expanding_id_id
             | [ |- ?x = ?x ] => reflexivity
             | [ |- List.length (proj1_sig _) = _ ] => apply length_list_of_encodedT
             end.

    Local Ltac solve_encodedT _ :=
      specialize_from_interp ();
      specialize_with_bounded ();
      rewrite_interp ().
    (*Local Ltac solve_encodedT _ :=
      repeat match goal with
             | _ => progress destruct_head' encodedT
             | _ => progress (destruct_head'_ex; destruct_head'_and; subst)
             | _ => progress cbn [proj1_sig Option.bind always_invert_Some] in *
             | [ H : ?x = Some _ |- context[?x] ] => rewrite H
             | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
             (*| [ |- BoundsAnalysis.Indexed.Range.type_for_range_bounded_by _ _ (_, _) = true ]
               => progress cbn [BoundsAnalysis.Indexed.Range.type_for_range_bounded_by BoundsAnalysis.Indexed.OfPHOAS.type.compile]*)
             | _ => progress cbn [BoundsAnalysis.Indexed.Range.type_for_range BoundsAnalysis.Indexed.OfPHOAS.type.compile fst snd] in * (* for getting rewrite to match *)
             | [ |- andb _ _ = true ] => rewrite Bool.andb_true_iff
             | _ => solve [ eauto ]
             | [ |- sig _ ] => progress rewrite expanding_id_id in *
             | [ |- List.length (List.map _ _) = _ ] => rewrite map_length
             (*| [ H : BoundsAnalysis.Indexed.Range.type_for_range_bounded_by _ _ ?x = true
                 |- List.length ?x = _ ]
               => erewrite BoundsAnalysis.Indexed.Range.length_list_bounded_by by exact H*)
             | _ => progress rewrite ?length_tight_bounds, ?length_loose_bounds
             | [ H : map _ ?x = map _ _ |- _ ] => rewrite H in *
             | [ H : map _ ?x = _ |- context[map _ ?x] ]
               => cbv [tight_bounds loose_bounds] in H |- *; rewrite H
             | _ => rewrite BoundsAnalysis.OfPHOAS.cast_back_primitive_cast_primitive in *
             (*| [ fx := (BoundsAnalysis.Indexed.expr.interp _ ?rop (BoundsAnalysis.Indexed.Context.extendb _ _ ?x)),
                       H : forall arg, BoundsAnalysis.Indexed.Range.type_for_range_bounded_by _ ?bs arg = true -> rexpr_1_correctT_ctx _ _ _ _ _ ?rop
                                       |- _ ]
               => destruct (H x); [ clear H | subst fx ]*)
             | [ fx := Option.bind ?x ?f, H : ?x = Some ?v |- _ ]
               => let H' := fresh in
                  let fx' := fresh fx in
                  pose (Option.bind (Some v) f) as fx';
                  assert (H' : fx = fx')
                    by (subst fx fx'; apply f_equal2; [ exact H | reflexivity ]);
                  cbn [Option.bind] in fx'; clearbody fx; subst fx
             | _ => progress cbn [BoundsAnalysis.OfPHOAS.cast_back] in * (* for getting eauto to work *)
             end.*)

    Definition ring_mul_sig
      : forall (x y : encodedT),
        { v : encodedT
        | Zdecode v = carry_mulmod (Interp rw) s c n (Interp rlen_c) idxs (Interp rlen_idxs) (Zdecode x, Zdecode y) }.
    Proof.
      simple refine
             (fun x y
              => let x' := Interp rrelaxv (proj1_sig x) in
                 let y' := Interp rrelaxv (proj1_sig y) in
                 let v' := Interp rcarry_mulv (x', y') in
                 let pf : { pf0 : _ | Zdecode (exist _ v' pf0) = _ }
                     := _ in
                 exist _ (exist _ v' (proj1_sig pf)) (proj2_sig pf)).
      abstract solve_encodedT ().
    Defined.

    Definition ring_add_sig
      : forall (x y : encodedT),
        { v : encodedT
        | Zdecode v = carrymod
                        (Interp rw) s c n (Interp rlen_c) idxs (Interp rlen_idxs)
                        (addmod (Interp rw) n (Zdecode x, Zdecode y)) }.
    Proof.
      simple refine
             (fun x y
              => let v'' := Interp raddv (proj1_sig x, proj1_sig y) in
                 let v' := Interp rcarryv v'' in
                 let pf : { pf0 : _ | Zdecode (exist _ v' pf0) = _ }
                     := _ in
                 exist _ (exist _ v' (proj1_sig pf)) (proj2_sig pf)).
      abstract solve_encodedT ().
    Defined.
    Definition ring_sub_sig
      : forall (x y : encodedT),
        { v : encodedT
        | Zdecode v = carrymod
                        (Interp rw) s c n (Interp rlen_c) idxs (Interp rlen_idxs)
                        (submod (Interp rw) s c n (Interp rlen_c) (Interp rcoef) (Zdecode x, Zdecode y)) }.
    Proof.
      simple refine
             (fun x y
              => let v'' := Interp rsubv (proj1_sig x, proj1_sig y) in
                 let v' := Interp rcarryv v'' in
                 let pf : { pf0 : _ | Zdecode (exist _ v' pf0) = _ }
                     := _ in
                 exist _ (exist _ v' (proj1_sig pf)) (proj2_sig pf)).
      abstract solve_encodedT ().
    Defined.
    Definition ring_opp_sig
      : forall (x : encodedT),
        { v : encodedT
        | Zdecode v = carrymod
                        (Interp rw) s c n (Interp rlen_c) idxs (Interp rlen_idxs)
                        (oppmod (Interp rw) s c n (Interp rlen_c) (Interp rcoef) (Zdecode x)) }.
    Proof.
      simple refine
             (fun x
              => let v'' := Interp roppv (proj1_sig x) in
                 let v' := Interp rcarryv v'' in
                 let pf : { pf0 : _ | Zdecode (exist _ v' pf0) = _ }
                     := _ in
                 exist _ (exist _ v' (proj1_sig pf)) (proj2_sig pf)).
      abstract solve_encodedT ().
    Defined.
    Definition ring_zero_sig
      : { v : encodedT
        | Zdecode v = zeromod
                        (Interp rw) s c n (Interp rlen_c) }.
    Proof.
      simple refine
             (let v' := Interp rzerov in
              let pf : { pf0 : _ | Zdecode (exist _ v' pf0) = _ }
                  := _ in
              exist _ (exist _ v' (proj1_sig pf)) (proj2_sig pf)).
      abstract (
          destruct Hrzerov; subst v';
          solve_encodedT ()
        ).
    Defined.
    Definition ring_one_sig
      : { v : encodedT
        | Zdecode v = onemod
                        (Interp rw) s c n (Interp rlen_c) }.
    Proof.
      simple refine
             (let v' := Interp ronev in
              let pf : { pf0 : _ | Zdecode (exist _ v' pf0) = _ }
                  := _ in
              exist _ (exist _ v' (proj1_sig pf)) (proj2_sig pf)).
      cbv [Zdecode list_of_encodedT]; cbn [proj1_sig].
      abstract (
          destruct Hronev; subst v';
          solve_encodedT ()
        ).
    Defined.
    Arguments Z.mul !_ !_ .
    Definition ring_encode_sig
      : forall (x : F m),
        { v : encodedT
        | Zdecode v = encodemod
                        (Interp rw) s c n (Interp rlen_c) (F.to_Z x) }.
    Proof.
      simple refine
             (fun v
              => let pf1 := _ in
                 let arg := F.to_Z v in
                 let Hrencodev' := Hrencodev arg pf1 in
                 let v' := Interp rencodev arg in
                 let pf : { pf0 : _ | Zdecode (exist _ v' pf0) = _ }
                     := _ in
                 exist _ (exist _ v' (proj1_sig pf)) (proj2_sig pf)).
      { generalize m_eq.
        generalize sc_pos.
        cbn; clear -v.
        abstract (
            intros sc_pos m_eq;
            destruct v as [v Hv]; cbn; rewrite m_eq in Hv;
            pose proof (Z.mod_pos_bound v _ sc_pos);
            rewrite Bool.andb_true_iff; split; Z.ltb_to_lt; lia
          ). }
      { cbv [Zdecode list_of_encodedT]; cbn [proj1_sig].
        subst v' arg; clearbody Hrencodev'; cbv beta zeta in *.
        abstract (
            destruct Hrencodev';
            solve_encodedT ()
          ). }
    Defined.

    Lemma length_addmod x y
      : List.length (addmod (Interp rw) n (Zdecode x, Zdecode y)) = n.
    Proof.
      cbv [addmod]; apply length_add; rewrite expand_list_correct;
        cbn [fst snd]; apply length_Zdecode.
    Qed.
    Lemma length_submod x y
      : List.length (submod (Interp rw) s c n (Interp rlen_c) (Interp rcoef) (Zdecode x, Zdecode y)) = n.
    Proof.
      cbv [submod]; apply length_sub; rewrite expand_list_correct;
        cbn [fst snd]; apply length_Zdecode.
    Qed.
    Lemma length_oppmod x
      : List.length (oppmod (Interp rw) s c n (Interp rlen_c) (Interp rcoef) (Zdecode x)) = n.
    Proof.
      cbv [oppmod]; apply length_opp; rewrite expand_list_correct;
        cbn [fst snd]; apply length_Zdecode.
    Qed.

    Definition ring_mul x y := proj1_sig (ring_mul_sig x y).
    Definition ring_add x y := proj1_sig (ring_add_sig x y).
    Definition ring_sub x y := proj1_sig (ring_sub_sig x y).
    Definition ring_opp x := proj1_sig (ring_opp_sig x).
    Definition ring_zero := proj1_sig ring_zero_sig.
    Definition ring_one := proj1_sig ring_one_sig.
    Definition ring_encode x := proj1_sig (ring_encode_sig x).

    Definition GoodT : Prop
      := @Hierarchy.ring
           encodedT encodedT_eq ring_zero ring_one ring_opp ring_add ring_sub ring_mul
         /\ @Ring.is_homomorphism
              (F m) eq 1%F F.add F.mul
              encodedT encodedT_eq ring_one ring_add ring_mul ring_encode
         /\ @Ring.is_homomorphism
              encodedT encodedT_eq ring_one ring_add ring_mul
              (F m) eq 1%F F.add F.mul
              Fdecode.

    Hint Rewrite ->@F.to_Z_add : push_FtoZ.
    Hint Rewrite ->@F.to_Z_mul : push_FtoZ.
    Hint Rewrite ->@F.to_Z_opp : push_FtoZ.
    Hint Rewrite ->@F.to_Z_of_Z : push_FtoZ.

    Local Ltac rewrite_proj2_sig _ :=
      lazymatch goal with
      | [ |- context[proj1_sig ?x] ] => rewrite (proj2_sig x)
      end.

    Lemma Good : GoodT.
    Proof.
      pose proof use_curve_good.
      destruct_head'_and.
      eapply ring_by_isomorphism; intros; [ | reflexivity | .. ]; rewrite F.eq_to_Z_iff;
        cbv [F.sub Fdecode];
        autorewrite with push_FtoZ;
        pull_Zmod;
        rewrite ?Z.add_opp_r.
      { cbv [ring_encode]; rewrite_proj2_sig ().
        erewrite m_eq, eval_encodemod, <- m_eq by assumption.
        let A := lazymatch goal with A : F _ |- _ => A end in
        destruct A as [v Hv]; cbn; congruence. }
      { cbv [ring_zero]; rewrite_proj2_sig ().
        cbv [zeromod]; erewrite m_eq, eval_encodemod, Zmod_0_l by eassumption; reflexivity. }
      { cbv [ring_one]; rewrite_proj2_sig ().
        cbv [onemod]; cbn; erewrite m_eq, eval_encodemod by eassumption; reflexivity. }
      { cbv [ring_opp]; rewrite_proj2_sig ().
        erewrite m_eq, eval_carrymod, eval_oppmod
          by eauto using length_Zdecode, length_oppmod;
          reflexivity. }
      { cbv [ring_add]; rewrite_proj2_sig ().
        erewrite m_eq, eval_carrymod, eval_addmod
          by eauto using length_Zdecode, length_addmod;
          reflexivity. }
      { cbv [ring_sub]; rewrite_proj2_sig ().
        erewrite m_eq, eval_carrymod, eval_submod
          by eauto using length_Zdecode, length_submod;
          reflexivity. }
      { cbv [ring_mul]; rewrite_proj2_sig ().
        erewrite m_eq, eval_carry_mulmod
          by eauto using length_Zdecode; reflexivity. }
    Qed.
  End make_ring.
End rcarry_mul.

Ltac solve_rop rop_correct machine_wordsizev :=
  eapply rop_correct with (machine_wordsize:=machine_wordsizev); lazy; reflexivity.
Ltac solve_rcarry_mul := solve_rop rcarry_mul_correct.
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
  Global Set Printing Width 100000.
  (*Notation "'uint256'"
    := (r[0 ~> 115792089237316195423570985008687907853269984665640564039457584007913129639935]%btype) : btype_scope.
  Notation "'uint128'"
    := (r[0 ~> 340282366920938463463374607431768211455]%btype) : btype_scope.
  Notation "'uint64'"
    := (r[0 ~> 18446744073709551615]) : btype_scope.
  Notation "'uint32'"
    := (r[0 ~> 4294967295]) : btype_scope.
  Notation "'ℤ'"
    := BoundsAnalysis.type.Z : btype_scope.
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
  (*Notation "'ADD_256'" := (add_get_carry_concrete _ _ uint256 _ TwoPow256) : nexpr_scope.
  Notation "'ADD_128'" := (add_get_carry_concrete _ _ uint128 _ TwoPow256) : nexpr_scope.
  Notation "'ADDC_256'" := (add_with_get_carry_concrete _ _ _ uint256 _ TwoPow256) : nexpr_scope.
  Notation "'SUB_256'" := (sub_get_borrow_concrete _ _ uint256 _ TwoPow256) : nexpr_scope.
  Notation "'ADDM'" := (add_modulo _ _ _ uint256) : nexpr_scope.
  Notation "'SELC'" := (zselect _ _ _ uint256) : nexpr_scope.
  Notation "'MUL_256'" := (mul uint128 uint128 uint256) : nexpr_scope.*)
End PrintingNotations.


Module X25519_64.
  Definition n := 5%nat.
  Definition s := 2^255.
  Definition c := [(1, 19)].
  Definition machine_wordsize := 64.

  Set Printing Width 80.

  Derive base_51_relax
         SuchThat (rrelax_correctT n s c base_51_relax)
         As base_51_relax_correct.
  Proof. Time solve_rrelax machine_wordsize. Time Qed.
  Derive base_51_carry_mul
         SuchThat (rcarry_mul_correctT n s c base_51_carry_mul)
         As base_51_carry_mul_correct.
  Proof.
    eapply rcarry_mul_correct with (machine_wordsize:=machine_wordsize).
    cbv [rcarry_mul].
    set (k := List.repeat _ _) at 1; lazy in k; subst k.
    set (k := List.repeat _ _) at 1; lazy in k; subst k.
    set (k := List.repeat _ _) at 1; lazy in k; subst k.
    cbv [Pipeline.BoundsPipeline].
    cbv [CheckedPartialReduceWithBounds1].
    cbv [Let_In].
    set (k := extract_bounds _ _ _).
    set (k' := k _); subst k.
    cbv [extract_bounds] in k'.
    set (k'' := partial_reduce_with_bounds1' _ _ _ _) in (value of k').
    exfalso.
    lazy in k''.

    Time solve_rcarry_mul machine_wordsize. Time Qed.
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
  Proof. vm_compute; reflexivity. Qed.

  Definition base_51_goodT
    := GoodT n s c machine_wordsize
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
  Theorem base_51_good : base_51_goodT.
  Proof. apply Good. Qed.

  Print Assumptions base_51_good.

  Import PrintingNotations.
  Print base_51_carry_mul.
(* base_51_carry_mul =
(expr_let 2 := fst @@ x_1 [[0]] *₆₄₋₆₄₋₁₂₈ snd @@ x_1 [[0]] +₁₂₈
               (fst @@ x_1 [[1]] *₆₄₋₆₄₋₁₂₈ (snd @@ x_1 [[4]] *₆₄₋₆₄₋₆₄ (19)) +₁₂₈
                (fst @@ x_1 [[2]] *₆₄₋₆₄₋₁₂₈ (snd @@ x_1 [[3]] *₆₄₋₆₄₋₆₄ (19)) +₁₂₈
                 (fst @@ x_1 [[3]] *₆₄₋₆₄₋₁₂₈ (snd @@ x_1 [[2]] *₆₄₋₆₄₋₆₄ (19)) +₁₂₈
                  fst @@ x_1 [[4]] *₆₄₋₆₄₋₁₂₈ (snd @@ x_1 [[1]] *₆₄₋₆₄₋₆₄ (19))))) in
 expr_let 3 := (uint64)(x_2 >> 51) in
 expr_let 4 := ((uint64)x_2 & 2251799813685247) in
 expr_let 5 := x_3 +₆₄₋₁₂₈₋₁₂₈
               (fst @@ x_1 [[0]] *₆₄₋₆₄₋₁₂₈ snd @@ x_1 [[1]] +₁₂₈
                (fst @@ x_1 [[1]] *₆₄₋₆₄₋₁₂₈ snd @@ x_1 [[0]] +₁₂₈
                 (fst @@ x_1 [[2]] *₆₄₋₆₄₋₁₂₈ (snd @@ x_1 [[4]] *₆₄₋₆₄₋₆₄ (19)) +₁₂₈
                  (fst @@ x_1 [[3]] *₆₄₋₆₄₋₁₂₈ (snd @@ x_1 [[3]] *₆₄₋₆₄₋₆₄ (19)) +₁₂₈
                   fst @@ x_1 [[4]] *₆₄₋₆₄₋₁₂₈ (snd @@ x_1 [[2]] *₆₄₋₆₄₋₆₄ (19)))))) in
 expr_let 6 := (uint64)(x_5 >> 51) in
 expr_let 7 := ((uint64)x_5 & 2251799813685247) in
 expr_let 8 := x_6 +₆₄₋₁₂₈₋₁₂₈
               (fst @@ x_1 [[0]] *₆₄₋₆₄₋₁₂₈ snd @@ x_1 [[2]] +₁₂₈
                (fst @@ x_1 [[1]] *₆₄₋₆₄₋₁₂₈ snd @@ x_1 [[1]] +₁₂₈
                 (fst @@ x_1 [[2]] *₆₄₋₆₄₋₁₂₈ snd @@ x_1 [[0]] +₁₂₈
                  (fst @@ x_1 [[3]] *₆₄₋₆₄₋₁₂₈ (snd @@ x_1 [[4]] *₆₄₋₆₄₋₆₄ (19)) +₁₂₈
                   fst @@ x_1 [[4]] *₆₄₋₆₄₋₁₂₈ (snd @@ x_1 [[3]] *₆₄₋₆₄₋₆₄ (19)))))) in
 expr_let 9 := (uint64)(x_8 >> 51) in
 expr_let 10 := ((uint64)x_8 & 2251799813685247) in
 expr_let 11 := x_9 +₆₄₋₁₂₈₋₁₂₈
                (fst @@ x_1 [[0]] *₆₄₋₆₄₋₁₂₈ snd @@ x_1 [[3]] +₁₂₈
                 (fst @@ x_1 [[1]] *₆₄₋₆₄₋₁₂₈ snd @@ x_1 [[2]] +₁₂₈
                  (fst @@ x_1 [[2]] *₆₄₋₆₄₋₁₂₈ snd @@ x_1 [[1]] +₁₂₈
                   (fst @@ x_1 [[3]] *₆₄₋₆₄₋₁₂₈ snd @@ x_1 [[0]] +₁₂₈
                    fst @@ x_1 [[4]] *₆₄₋₆₄₋₁₂₈ (snd @@ x_1 [[4]] *₆₄₋₆₄₋₆₄ (19)))))) in
 expr_let 12 := (uint64)(x_11 >> 51) in
 expr_let 13 := ((uint64)x_11 & 2251799813685247) in
 expr_let 14 := x_12 +₆₄₋₁₂₈₋₁₂₈
                (fst @@ x_1 [[0]] *₆₄₋₆₄₋₁₂₈ snd @@ x_1 [[4]] +₁₂₈
                 (fst @@ x_1 [[1]] *₆₄₋₆₄₋₁₂₈ snd @@ x_1 [[3]] +₁₂₈
                  (fst @@ x_1 [[2]] *₆₄₋₆₄₋₁₂₈ snd @@ x_1 [[2]] +₁₂₈
                   (fst @@ x_1 [[3]] *₆₄₋₆₄₋₁₂₈ snd @@ x_1 [[1]] +₁₂₈
                    fst @@ x_1 [[4]] *₆₄₋₆₄₋₁₂₈ snd @@ x_1 [[0]])))) in
 expr_let 15 := (uint64)(x_14 >> 51) in
 expr_let 16 := ((uint64)x_14 & 2251799813685247) in
 expr_let 17 := x_4 +₆₄ x_15 *₆₄₋₆₄₋₆₄ (19) in
 expr_let 18 := (uint64)(x_17 >> 51) in
 expr_let 19 := ((uint64)x_17 & 2251799813685247) in
 expr_let 20 := x_18 +₆₄ x_7 in
 expr_let 21 := (uint64)(x_20 >> 51) in
 expr_let 22 := ((uint64)x_20 & 2251799813685247) in
 x_19 :: x_22 :: x_21 +₆₄ x_10 :: x_13 :: x_16 :: [])%nexpr
     : expr
         (BoundsAnalysis.AdjustBounds.ident.type_for_range
            (relax_zrange_of_machine_wordsize machine_wordsize)
            (List.repeat
               r[0 ~> 2
                      ^ Qceiling
                          (inject_Z (Z.log2_up (s - Associational.eval c)) /
                           inject_Z (BinInt.Z.of_nat n)) +
                      2
                      ^ (Qceiling
                           (inject_Z (Z.log2_up (s - Associational.eval c)) /
                            inject_Z (BinInt.Z.of_nat n)) - 3)]%zrange n))
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

  Derive base_25p5_carry_mul
         SuchThat (rcarry_mul_correctT n s c machine_wordsize base_25p5_carry_mul)
         As base_25p5_carry_mul_correct.
  Proof. Time solve_rcarry_mul (). Time Qed.

  Import PrintingNotations.
  Print base_25p5_carry_mul.
(* base_25p5_carry_mul =
(expr_let 2 := fst @@ x_1 [[0]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[0]] +₆₄
               (fst @@ x_1 [[1]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[9]] *₃₂₋₃₂₋₃₂ ((2) *₃₂₋₃₂₋₃₂ (19))) +₆₄
                (fst @@ x_1 [[2]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[8]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                 (fst @@ x_1 [[3]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[7]] *₃₂₋₃₂₋₃₂ ((2) *₃₂₋₃₂₋₃₂ (19))) +₆₄
                  (fst @@ x_1 [[4]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[6]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                   (fst @@ x_1 [[5]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[5]] *₃₂₋₃₂₋₃₂ ((2) *₃₂₋₃₂₋₃₂ (19))) +₆₄
                    (fst @@ x_1 [[6]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[4]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                     (fst @@ x_1 [[7]] *₃₂₋₃₂₋₆₄
                      (snd @@ x_1 [[3]] *₃₂₋₃₂₋₃₂ ((2) *₃₂₋₃₂₋₃₂ (19))) +₆₄
                      (fst @@ x_1 [[8]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[2]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                       fst @@ x_1 [[9]] *₃₂₋₃₂₋₆₄
                       (snd @@ x_1 [[1]] *₃₂₋₃₂₋₃₂ ((2) *₃₂₋₃₂₋₃₂ (19))))))))))) in
 expr_let 3 := (uint64)(x_2 >> 26) in
 expr_let 4 := ((uint32)x_2 & 67108863) in
 expr_let 5 := x_3 +₆₄
               (fst @@ x_1 [[0]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[1]] +₆₄
                (fst @@ x_1 [[1]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[0]] +₆₄
                 (fst @@ x_1 [[2]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[9]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                  (fst @@ x_1 [[3]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[8]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                   (fst @@ x_1 [[4]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[7]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                    (fst @@ x_1 [[5]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[6]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                     (fst @@ x_1 [[6]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[5]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                      (fst @@ x_1 [[7]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[4]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                       (fst @@ x_1 [[8]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[3]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                        fst @@ x_1 [[9]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[2]] *₃₂₋₃₂₋₃₂ (19))))))))))) in
 expr_let 6 := (uint64)(x_5 >> 25) in
 expr_let 7 := ((uint32)x_5 & 33554431) in
 expr_let 8 := x_6 +₆₄
               (fst @@ x_1 [[0]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[2]] +₆₄
                (fst @@ x_1 [[1]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[1]] *₃₂₋₃₂₋₃₂ (2)) +₆₄
                 (fst @@ x_1 [[2]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[0]] +₆₄
                  (fst @@ x_1 [[3]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[9]] *₃₂₋₃₂₋₃₂ ((2) *₃₂₋₃₂₋₃₂ (19))) +₆₄
                   (fst @@ x_1 [[4]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[8]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                    (fst @@ x_1 [[5]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[7]] *₃₂₋₃₂₋₃₂ ((2) *₃₂₋₃₂₋₃₂ (19))) +₆₄
                     (fst @@ x_1 [[6]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[6]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                      (fst @@ x_1 [[7]] *₃₂₋₃₂₋₆₄
                       (snd @@ x_1 [[5]] *₃₂₋₃₂₋₃₂ ((2) *₃₂₋₃₂₋₃₂ (19))) +₆₄
                       (fst @@ x_1 [[8]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[4]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                        fst @@ x_1 [[9]] *₃₂₋₃₂₋₆₄
                        (snd @@ x_1 [[3]] *₃₂₋₃₂₋₃₂ ((2) *₃₂₋₃₂₋₃₂ (19)))))))))))) in
 expr_let 9 := (uint64)(x_8 >> 26) in
 expr_let 10 := ((uint32)x_8 & 67108863) in
 expr_let 11 := x_9 +₆₄
                (fst @@ x_1 [[0]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[3]] +₆₄
                 (fst @@ x_1 [[1]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[2]] +₆₄
                  (fst @@ x_1 [[2]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[1]] +₆₄
                   (fst @@ x_1 [[3]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[0]] +₆₄
                    (fst @@ x_1 [[4]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[9]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                     (fst @@ x_1 [[5]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[8]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                      (fst @@ x_1 [[6]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[7]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                       (fst @@ x_1 [[7]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[6]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                        (fst @@ x_1 [[8]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[5]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                         fst @@ x_1 [[9]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[4]] *₃₂₋₃₂₋₃₂ (19))))))))))) in
 expr_let 12 := (uint64)(x_11 >> 25) in
 expr_let 13 := ((uint32)x_11 & 33554431) in
 expr_let 14 := x_12 +₆₄
                (fst @@ x_1 [[0]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[4]] +₆₄
                 (fst @@ x_1 [[1]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[3]] *₃₂₋₃₂₋₃₂ (2)) +₆₄
                  (fst @@ x_1 [[2]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[2]] +₆₄
                   (fst @@ x_1 [[3]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[1]] *₃₂₋₃₂₋₃₂ (2)) +₆₄
                    (fst @@ x_1 [[4]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[0]] +₆₄
                     (fst @@ x_1 [[5]] *₃₂₋₃₂₋₆₄
                      (snd @@ x_1 [[9]] *₃₂₋₃₂₋₃₂ ((2) *₃₂₋₃₂₋₃₂ (19))) +₆₄
                      (fst @@ x_1 [[6]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[8]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                       (fst @@ x_1 [[7]] *₃₂₋₃₂₋₆₄
                        (snd @@ x_1 [[7]] *₃₂₋₃₂₋₃₂ ((2) *₃₂₋₃₂₋₃₂ (19))) +₆₄
                        (fst @@ x_1 [[8]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[6]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                         fst @@ x_1 [[9]] *₃₂₋₃₂₋₆₄
                         (snd @@ x_1 [[5]] *₃₂₋₃₂₋₃₂ ((2) *₃₂₋₃₂₋₃₂ (19)))))))))))) in
 expr_let 15 := (uint64)(x_14 >> 26) in
 expr_let 16 := ((uint32)x_14 & 67108863) in
 expr_let 17 := x_15 +₆₄
                (fst @@ x_1 [[0]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[5]] +₆₄
                 (fst @@ x_1 [[1]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[4]] +₆₄
                  (fst @@ x_1 [[2]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[3]] +₆₄
                   (fst @@ x_1 [[3]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[2]] +₆₄
                    (fst @@ x_1 [[4]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[1]] +₆₄
                     (fst @@ x_1 [[5]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[0]] +₆₄
                      (fst @@ x_1 [[6]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[9]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                       (fst @@ x_1 [[7]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[8]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                        (fst @@ x_1 [[8]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[7]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                         fst @@ x_1 [[9]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[6]] *₃₂₋₃₂₋₃₂ (19))))))))))) in
 expr_let 18 := (uint64)(x_17 >> 25) in
 expr_let 19 := ((uint32)x_17 & 33554431) in
 expr_let 20 := x_18 +₆₄
                (fst @@ x_1 [[0]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[6]] +₆₄
                 (fst @@ x_1 [[1]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[5]] *₃₂₋₃₂₋₃₂ (2)) +₆₄
                  (fst @@ x_1 [[2]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[4]] +₆₄
                   (fst @@ x_1 [[3]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[3]] *₃₂₋₃₂₋₃₂ (2)) +₆₄
                    (fst @@ x_1 [[4]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[2]] +₆₄
                     (fst @@ x_1 [[5]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[1]] *₃₂₋₃₂₋₃₂ (2)) +₆₄
                      (fst @@ x_1 [[6]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[0]] +₆₄
                       (fst @@ x_1 [[7]] *₃₂₋₃₂₋₆₄
                        (snd @@ x_1 [[9]] *₃₂₋₃₂₋₃₂ ((2) *₃₂₋₃₂₋₃₂ (19))) +₆₄
                        (fst @@ x_1 [[8]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[8]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                         fst @@ x_1 [[9]] *₃₂₋₃₂₋₆₄
                         (snd @@ x_1 [[7]] *₃₂₋₃₂₋₃₂ ((2) *₃₂₋₃₂₋₃₂ (19)))))))))))) in
 expr_let 21 := (uint64)(x_20 >> 26) in
 expr_let 22 := ((uint32)x_20 & 67108863) in
 expr_let 23 := x_21 +₆₄
                (fst @@ x_1 [[0]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[7]] +₆₄
                 (fst @@ x_1 [[1]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[6]] +₆₄
                  (fst @@ x_1 [[2]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[5]] +₆₄
                   (fst @@ x_1 [[3]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[4]] +₆₄
                    (fst @@ x_1 [[4]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[3]] +₆₄
                     (fst @@ x_1 [[5]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[2]] +₆₄
                      (fst @@ x_1 [[6]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[1]] +₆₄
                       (fst @@ x_1 [[7]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[0]] +₆₄
                        (fst @@ x_1 [[8]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[9]] *₃₂₋₃₂₋₃₂ (19)) +₆₄
                         fst @@ x_1 [[9]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[8]] *₃₂₋₃₂₋₃₂ (19))))))))))) in
 expr_let 24 := (uint64)(x_23 >> 25) in
 expr_let 25 := ((uint32)x_23 & 33554431) in
 expr_let 26 := x_24 +₆₄
                (fst @@ x_1 [[0]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[8]] +₆₄
                 (fst @@ x_1 [[1]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[7]] *₃₂₋₃₂₋₃₂ (2)) +₆₄
                  (fst @@ x_1 [[2]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[6]] +₆₄
                   (fst @@ x_1 [[3]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[5]] *₃₂₋₃₂₋₃₂ (2)) +₆₄
                    (fst @@ x_1 [[4]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[4]] +₆₄
                     (fst @@ x_1 [[5]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[3]] *₃₂₋₃₂₋₃₂ (2)) +₆₄
                      (fst @@ x_1 [[6]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[2]] +₆₄
                       (fst @@ x_1 [[7]] *₃₂₋₃₂₋₆₄ (snd @@ x_1 [[1]] *₃₂₋₃₂₋₃₂ (2)) +₆₄
                        (fst @@ x_1 [[8]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[0]] +₆₄
                         fst @@ x_1 [[9]] *₃₂₋₃₂₋₆₄
                         (snd @@ x_1 [[9]] *₃₂₋₃₂₋₃₂ ((2) *₃₂₋₃₂₋₃₂ (19)))))))))))) in
 expr_let 27 := (uint64)(x_26 >> 26) in
 expr_let 28 := ((uint32)x_26 & 67108863) in
 expr_let 29 := x_27 +₆₄
                (fst @@ x_1 [[0]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[9]] +₆₄
                 (fst @@ x_1 [[1]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[8]] +₆₄
                  (fst @@ x_1 [[2]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[7]] +₆₄
                   (fst @@ x_1 [[3]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[6]] +₆₄
                    (fst @@ x_1 [[4]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[5]] +₆₄
                     (fst @@ x_1 [[5]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[4]] +₆₄
                      (fst @@ x_1 [[6]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[3]] +₆₄
                       (fst @@ x_1 [[7]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[2]] +₆₄
                        (fst @@ x_1 [[8]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[1]] +₆₄
                         fst @@ x_1 [[9]] *₃₂₋₃₂₋₆₄ snd @@ x_1 [[0]]))))))))) in
 expr_let 30 := (uint32)(x_29 >> 25) in
 expr_let 31 := ((uint32)x_29 & 33554431) in
 expr_let 32 := x_4 +₃₂₋₆₄₋₆₄ x_30 *₃₂₋₃₂₋₆₄ (19) in
 expr_let 33 := (uint32)(x_32 >> 26) in
 expr_let 34 := ((uint32)x_32 & 67108863) in
 expr_let 35 := x_33 +₃₂ x_7 in
 expr_let 36 := (uint32)(x_35 >> 25) in
 expr_let 37 := ((uint32)x_35 & 33554431) in
 x_34 :: x_37 :: x_36 +₃₂ x_10 :: x_13 :: x_16 :: x_19 :: x_22 :: x_25 :: x_28 :: x_31 :: [])%nexpr
     : expr
         (BoundsAnalysis.AdjustBounds.ident.type_for_range
            (relax_zrange (make_carry_mul_rargs n s c machine_wordsize))
            (out_bounds (make_carry_mul_rargs n s c machine_wordsize)))
*)
End X25519_32.
*)

Require Import Crypto.Arithmetic.MontgomeryReduction.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.Proofs.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Tactics.
Require Import Crypto.Util.ZUtil.Zselect Crypto.Util.ZUtil.AddModulo.

Module MontgomeryReduction.
  Section MontRed'.
    Context (N R N' R' : Z).
    Context (HN_range : 0 <= N < R) (HN'_range : 0 <= N' < R) (HN_nz : N <> 0) (R_gt_1 : R > 1)
            (N'_good : Z.equiv_modulo R (N*N') (-1)) (R'_good: Z.equiv_modulo N (R*R') 1).

    Context (w w_half : nat -> Z).
    Context (w_half_sq : forall i, (w_half i) * (w_half i) = w i).
    Context (w_half_0 : w_half 0%nat = 1)
            (w_half_nonzero : forall i, w_half i <> 0)
            (w_half_positive : forall i, w_half i > 0)
            (w_half_multiples : forall i, w_half (S i) mod w_half i = 0)
            (w_half_divides : forall i : nat, w_half (S i) / w_half i > 0).
    Context (w_0 : w 0%nat = 1)
            (w_nonzero : forall i, w i <> 0)
            (w_positive : forall i, w i > 0)
            (w_multiples : forall i, w (S i) mod w i = 0)
            (w_divides : forall i : nat, w (S i) / w i > 0).
    Context (w_1_gt1 : w 1 > 1) (w_half_1_gt1 : w_half 1 > 1).
    Context (n:nat) (Hn: n = 2%nat).

    Definition montred' (lo_hi : (Z * Z)) :=
      dlet_nd y := nth_default 0 (Columns.mul_converted_halve w w_half 1%nat n [fst lo_hi] [N']) 0  in
      dlet_nd t1_t2 := Columns.mul_converted_halve w w_half 1%nat n [y] [N] in
      dlet_nd lo'_carry := Z.add_get_carry_full R (fst lo_hi) (nth_default 0 t1_t2 0) in
      dlet_nd hi'_carry := Z.add_with_get_carry_full R (snd lo'_carry) (snd lo_hi) (nth_default 0 t1_t2 1) in
      dlet_nd y' := Z.zselect (snd hi'_carry) 0 N in
      dlet_nd lo'' := fst (Z.sub_get_borrow_full R (fst hi'_carry) y') in
      Z.add_modulo lo'' 0 N.

    Context (Hw : forall i, w i = R ^ Z.of_nat i).

    Local Ltac solve_range :=
      repeat match goal with
             | _ => rewrite Hw, ?Z.pow_0_r, ?Z.pow_1_r, ?Z.pow_2_r
             | |- context [?a mod ?b] => unique pose proof (Z.mod_pos_bound a b ltac:(omega))
             | |- 0 <= _ => progress Z.zero_bounds
             | |- 0 <= _ * _ < _ * _ =>
               split; [ solve [Z.zero_bounds] | apply Z.mul_lt_mono_nonneg; omega ]
             | _ => solve [auto]
             | _ => cbn
             | _ => nia
             end.

    Hint Rewrite
         Columns.mul_converted_mod Columns.mul_converted_div using (solve [auto; autorewrite with mul_conv; solve_range])
      : mul_conv.

    Lemma montred'_eq lo_hi T (HT_range: 0 <= T < R * N)
          (Hlo: fst lo_hi = T mod R) (Hhi: snd lo_hi = T / R):
      montred' lo_hi = reduce_via_partial N R N' T.
    Proof.
      rewrite <-reduce_via_partial_alt_eq by nia.
      cbv [montred' partial_reduce_alt reduce_via_partial_alt prereduce Let_In].
      rewrite Hlo, Hhi. subst n.
      assert (0 <= T mod R * N' < w 2) by (solve_range).
      cbv [Columns.mul_converted_halve]. cbn.
      autorewrite with mul_conv.
      rewrite Hw, ?Z.pow_1_r.
      autorewrite with to_div_mod. rewrite ?Z.zselect_correct, ?Z.add_modulo_correct.

      (* pull out value before last modular reduction *)
      match goal with |- (if (?n <=? ?x)%Z then ?x - ?n else ?x) = (if (?n <=? ?y) then ?y - ?n else ?y)%Z =>
                      let P := fresh "H" in assert (x = y) as P; [|rewrite P; reflexivity] end.

      match goal with
        |- context [if R * R <=? ?x then _ else _] =>
        match goal with |- context [if dec (?xHigh / R = 0) then _ else _] =>
                        assert (x / R = xHigh) as cond_equiv end end.
      { apply Z.mul_cancel_r with (p:=R); [omega|]. cbn.
        rewrite w_0. autorewrite with zsimplify_fast.
        autorewrite with push_Zmul zdiv_to_mod push_Zmod; ring. }
      rewrite <-cond_equiv. rewrite ?Z.mod_pull_div, ?Z.div_div by omega.
      assert (0 < R * R)%Z by Z.zero_bounds.

      break_match; try reflexivity; autorewrite with ltb_to_lt in *; rewrite Z.div_small_iff in * by omega;
        repeat match goal with
               | _ => progress autorewrite with zsimplify_fast
               | |- context [?x mod (R * R)] =>
                 unique pose proof (Z.mod_pos_bound x (R * R));
                   try rewrite (Z.mod_small x (R * R)) in * by Z.rewrite_mod_small_solver
               | _ => omega
               | _ => progress Z.rewrite_mod_small
               end.
    Qed.

    Lemma montred'_correct lo_hi T (HT_range: 0 <= T < R * N)
          (Hlo: fst lo_hi = T mod R) (Hhi: snd lo_hi = T / R): montred' lo_hi = (T * R') mod N.
    Proof.
      erewrite montred'_eq by eauto.
      apply Z.equiv_modulo_mod_small; auto using reduce_via_partial_correct.
      replace 0 with (Z.min 0 (R-N)) by (apply Z.min_l; omega).
      apply reduce_via_partial_in_range; omega.
    Qed.
  End MontRed'.

  Derive montred_gen
         SuchThat (forall (N R N' : Z)
                          (w w_half : nat -> Z)
                          (n: nat)
                          (lo_hi : Z * Z),
                      Interp (t:=type.reify_type_of montred')
                             montred_gen N R N' w w_half n lo_hi
                      = montred' N R N' w w_half n lo_hi)
         As montred_gen_correct.
  Proof. Time cache_reify (). exact admit. (* correctness of initial parts of the pipeline *) Time Qed.

  Section rmontred.
    Context (N R N' : Z)
            (machine_wordsize : Z).

    Let n : nat := Z.to_nat (Qceiling ((Z.log2_up N) / machine_wordsize)).
    Let bound := r[0 ~> (2^machine_wordsize - 1)%Z]%zrange.

    Definition relax_zrange_of_machine_wordsize
      := relax_zrange_gen [machine_wordsize / 2; machine_wordsize; 2 * machine_wordsize; 4 * machine_wordsize]%Z.
    Local Arguments relax_zrange_of_machine_wordsize / .

    Let rw := rweight machine_wordsize.
    Let rw_half := rweight (machine_wordsize / 2).
    Let rN := GallinaReify.Reify N.
    Let rR := GallinaReify.Reify R.
    Let rN' := GallinaReify.Reify N'.
    Let rn := GallinaReify.Reify 2%nat.
    Let relax_zrange := relax_zrange_of_machine_wordsize.
    Let arg_bounds : ZRange.type.interp (type.Z * type.Z))
      := (bound, bound).
    Let out_bounds : ZRange.type.interp (type.Z))
      := bound.

    Definition check_args {T} (res : Pipeline.ErrorT T)
      : Pipeline.ErrorT T
      := if (N =? 0)%Z
         then Pipeline.Error (Pipeline.Values_not_provably_distinct "N ≠ 0" N 0)
         else if (n =? 0)%Z
              then Pipeline.Error (Pipeline.Values_not_provably_distinct "n ≠ 0" N 0)
              else res.

    Lemma check_args_success_id {T} {rv : T} {res}
      : check_args res = Pipeline.Success rv
        -> res = Pipeline.Success rv.
    Proof.
      cbv [check_args]; break_innermost_match; congruence.
    Qed.

    Definition rmontred
      := let res := Pipeline.BoundsPipeline
                      true
                      (relax_zrange)
                      (s:=(type.Z * type.Z)%ctype)
                      (d:=(type.Z)%ctype)
                      (arg_bounds)
                      (out_bounds)
                      (fun var
                       => (montred_gen _)
                            @ (rN _)
                            @ (rR _)
                            @ (rN' _)
                            @ (rw _)
                            @ (rw_half _)
                            @ (rn _)
                      )%expr in
         res.

    (* copied from above *)
    Local Ltac solve_correct_gen pipeline_lem gen_correct :=
      let Hrv := lazymatch goal with H : ?rop = Pipeline.Success _ |- _ => H end in
      let rop := lazymatch type of Hrv with ?rop = Pipeline.Success _ => rop end in
      hnf; intros; cbv [rop] in Hrv;
      eapply pipeline_lem in Hrv; [ | eassumption.. ];
      let res := fresh "res" in
      destruct Hrv as [res Hrv];
      exists res; do 2 try apply conj;
      [ | | etransitivity ];
      [ solve [ apply Hrv ].. | ];
      repeat match goal with H := _ |- _ => subst H end;
      erewrite <- gen_correct;
      cbv [expr.Interp];
      cbn [expr.interp];
      f_equal;
      cbn -[reify_list];
      try (rewrite interp_reify_list, map_map; cbn;
           erewrite map_ext with (g:=id), map_id; try reflexivity);
      try (intros []; reflexivity).
    Local Ltac solve_correct gen_correct :=
      solve_correct_gen Pipeline.BoundsPipeline_correct gen_correct.
    Local Ltac solve_correct_const gen_correct :=
      solve_correct_gen Pipeline.BoundsPipelineConst_correct gen_correct.

    Definition rmontred_correctT
               rv
      := Eval hnf in
          @rexpr_n1_correctT
            relax_zrange
            ((type.Z * type.Z)%ctype) type.Z
            arg_bounds out_bounds
            (montred' (Interp rN) (Interp rR) (Interp rN') (Interp rw) (Interp rw_half) (Interp rn))
            rv.

    Lemma rmontred_correct
          rv
          (Hrv : rmontred = Pipeline.Success rv)
      : rmontred_correctT rv.
    Proof. solve_correct montred_gen_correct. Qed.
  End rmontred.
End MontgomeryReduction.

Ltac solve_rmontred _ :=
  eapply MontgomeryReduction.rmontred_correct;
  lazy; reflexivity.

Module Montgomery256.

  Definition N := (2^256-2^224+2^192+2^96-1).
  Definition N':= (115792089210356248768974548684794254293921932838497980611635986753331132366849).
  Definition R := (2^256).
  Definition machine_wordsize := 256.

  Derive montred256
         SuchThat (MontgomeryReduction.rmontred_correctT N R N' machine_wordsize montred256)
         As montred256_correct.
  Proof. Time solve_rmontred(). Time Qed.

  Import PrintingNotations.
  Open Scope nexpr_scope.
  Set Printing Width 100000.
  Print montred256.
  (*
    expr_let 3 := (uint128)(fst @@ x_1 >> 128) in
    expr_let 4 := ((uint128)fst @@ x_1 & 340282366920938463463374607431768211455) in
    expr_let 5 := MUL_256 @@ (x_3, (79228162514264337593543950337)) in
    expr_let 7 := ((uint128)x_5 & 340282366920938463463374607431768211455) in
    expr_let 8 := MUL_256 @@ (x_4, (340282366841710300986003757985643364352)) in
    expr_let 10 := ((uint128)x_8 & 340282366920938463463374607431768211455) in
    expr_let 11 := (uint128)(x_10 << 128) in
    expr_let 12 := (uint128)(x_7 << 128) in
    expr_let 17 := MUL_256 @@ (x_4, (79228162514264337593543950337)) in
    expr_let 18 := ADD_128 @@ (x_11, x_12) in
    expr_let 19 := ADD_256 @@ (x_17, fst @@ x_18) in
    expr_let 43 := (uint128)(fst @@ x_19 >> 128) in
    expr_let 44 := ((uint128)fst @@ x_19 & 340282366920938463463374607431768211455) in
    expr_let 45 := MUL_256 @@ (x_43, (79228162514264337593543950335)) in
    expr_let 46 := (uint128)(x_45 >> 128) in
    expr_let 47 := ((uint128)x_45 & 340282366920938463463374607431768211455) in
    expr_let 48 := MUL_256 @@ (x_44, (340282366841710300967557013911933812736)) in
    expr_let 49 := (uint128)(x_48 >> 128) in
    expr_let 50 := ((uint128)x_48 & 340282366920938463463374607431768211455) in
    expr_let 51 := (uint128)(x_50 << 128) in
    expr_let 52 := (uint128)(x_47 << 128) in
    expr_let 57 := MUL_256 @@ (x_44, (79228162514264337593543950335)) in
    expr_let 58 := ADD_128 @@ (x_51, x_52) in
    expr_let 59 := ADD_256 @@ (x_57, fst @@ x_58) in
    expr_let 60 := snd @@ x_59 +₁₂₈ snd @@ x_58 in
    expr_let 67 := MUL_256 @@ (x_43, (340282366841710300967557013911933812736)) in
    expr_let 69 := ADD_256 @@ (x_46, x_67) in
    expr_let 70 := ADD_256 @@ (x_49, fst @@ x_69) in
    expr_let 80 := ADD_256 @@ (x_60, fst @@ x_70) in
    expr_let 83 := ADD_256 @@ (fst @@ x_1, fst @@ x_59) in
    expr_let 84 := ADDC_256 @@ (snd @@ x_83, snd @@ x_1, fst @@ x_80) in
    expr_let 85 := SELC @@ (snd @@ x_84, (0), (115792089210356248762697446949407573530086143415290314195533631308867097853951)) in
    expr_let 86 := fst @@ (SUB_256 @@ (fst @@ x_84, x_85)) in
    ADDM @@ (x_86, (0), (115792089210356248762697446949407573530086143415290314195533631308867097853951))
         : expr uint256
   *)
End Montgomery256.

(* Extra-specialized ad-hoc pretty-printing *)
Module Montgomery256PrintingNotations.
  Export ident.
  Export BoundsAnalysis.ident.
  Export BoundsAnalysis.type.Notations.
  Export BoundsAnalysis.Indexed.expr.Notations.
  Export BoundsAnalysis.ident.Notations.
  Import BoundsAnalysis.type.
  Import BoundsAnalysis.Indexed.expr.
  Import BoundsAnalysis.ident.
  Open Scope btype_scope.
  Notation "'RegMod'" :=
    (BoundsAnalysis.Indexed.expr.AppIdent
                   (primitive {| BoundsAnalysis.type.value := 115792089210356248762697446949407573530086143415290314195533631308867097853951; BoundsAnalysis.type.value_bounded := _ |})
                   BoundsAnalysis.Indexed.expr.TT) (only printing, at level 9) : nexpr_scope.
  Notation "'RegPinv'" :=
    (BoundsAnalysis.Indexed.expr.AppIdent
                   (primitive {| BoundsAnalysis.type.value := 115792089210356248768974548684794254293921932838497980611635986753331132366849; BoundsAnalysis.type.value_bounded := _ |})
                   BoundsAnalysis.Indexed.expr.TT) (only printing, at level 9) : nexpr_scope.
  Notation "'RegZero'" :=
    (BoundsAnalysis.Indexed.expr.AppIdent
                   (primitive {| BoundsAnalysis.type.value := 0; BoundsAnalysis.type.value_bounded := _ |})
                   BoundsAnalysis.Indexed.expr.TT) (only printing, at level 9) : nexpr_scope.
  Notation "'$R'" := 115792089237316195423570985008687907853269984665640564039457584007913129639936 : nexpr_scope.
  Notation "'Lower128{RegMod}'" :=
    (BoundsAnalysis.Indexed.expr.AppIdent
                   (primitive {| BoundsAnalysis.type.value := 79228162514264337593543950335; BoundsAnalysis.type.value_bounded := _ |})
                   BoundsAnalysis.Indexed.expr.TT) (only printing, at level 9) : nexpr_scope.
  Notation "'RegMod' '<<' '128'" :=
    (BoundsAnalysis.Indexed.expr.AppIdent
                   (primitive {| BoundsAnalysis.type.value := 340282366841710300967557013911933812736; BoundsAnalysis.type.value_bounded := _ |})
                   BoundsAnalysis.Indexed.expr.TT) (only printing, at level 9, format "'RegMod'  '<<'  '128'") : nexpr_scope.
  Notation "'Lower128{RegPinv}'" :=
    (BoundsAnalysis.Indexed.expr.AppIdent
                   (primitive {| BoundsAnalysis.type.value := 79228162514264337593543950337; BoundsAnalysis.type.value_bounded := _ |})
                   BoundsAnalysis.Indexed.expr.TT) (only printing, at level 9) : nexpr_scope.
  Notation "'RegPinv' '>>' '128'" :=
    (BoundsAnalysis.Indexed.expr.AppIdent
                   (primitive {| BoundsAnalysis.type.value := 340282366841710300986003757985643364352; BoundsAnalysis.type.value_bounded := _ |})
                   BoundsAnalysis.Indexed.expr.TT) (only printing, at level 9, format "'RegPinv'  '>>'  '128'") : nexpr_scope.
  Notation "'uint256'"
    := (BoundsAnalysis.type.ZBounded 0 115792089237316195423570985008687907853269984665640564039457584007913129639935) : btype_scope.
  Notation "'uint128'"
    := (BoundsAnalysis.type.ZBounded 0 340282366920938463463374607431768211455) : btype_scope.
  Notation "$r n" := (BoundsAnalysis.Indexed.expr.Var _ n) (at level 10, format "$r n") : nexpr_scope.
  Notation "$r n '_lo'" := (fst @@ (BoundsAnalysis.Indexed.expr.Var (BoundsAnalysis.type.prod _ _) n))%nexpr (at level 10, format "$r n _lo") : nexpr_scope.
  Notation "$r n '_hi'" := (snd @@ (BoundsAnalysis.Indexed.expr.Var (BoundsAnalysis.type.prod _ _) n))%nexpr (at level 10, format "$r n _hi") : nexpr_scope.
  Notation "'c.Mul128x128(' '$r' n ',' x ',' y ');' f" :=
    (expr_let n := mul _ _ uint256 @@ (x, y) in
         f)%nexpr (at level 40, f at level 200, right associativity, format "'[' 'c.Mul128x128(' '$r' n ','  x ','  y ');' ']' '//' f") : nexpr_scope.
  Notation "'c.Mul128x128(' '$r' n ',' x ',' y ')' '<<' count ';' f" :=
    (expr_let n := shiftl _ _ count @@ (mul _ _ uint256 @@ (x, y)) in
         f)%nexpr (at level 40, f at level 200, right associativity, format "'[' 'c.Mul128x128(' '$r' n ','  x ','  y ')'  '<<'  count ';' ']' '//' f") : nexpr_scope.
  Notation "'c.Add256(' '$r' n ',' x ',' y ');' f" :=
    (expr_let n := add_get_carry_concrete _ _ uint256 _ $R @@ (x, y) in
         f)%nexpr (at level 40, f at level 200, right associativity, format "'[' 'c.Add256(' '$r' n ','  x ','  y ');' ']' '//' f") : nexpr_scope.
  Notation "'c.Add128(' '$r' n ',' x ',' y ');' f" :=
    (expr_let n := add_get_carry_concrete _ _ uint128 _ $R @@ (x, y) in
         f)%nexpr (at level 40, f at level 200, right associativity, format "'[' 'c.Add128(' '$r' n ','  x ','  y ');' ']' '//' f") : nexpr_scope.
  Notation "'c.Add64(' '$r' n ',' x ',' y ');' f" :=
    (expr_let n := add _ _ uint128 @@ (x, y) in
         f)%nexpr (at level 40, f at level 200, right associativity, format "'[' 'c.Add64(' '$r' n ','  x ','  y ');' ']' '//' f") : nexpr_scope.
  Notation "'c.Addc(' '$r' n ',' x ',' y ');' f" :=
    (expr_let n := add_with_get_carry_concrete _ _ _ uint256 _ $R @@ (_, x, y) in
         f)%nexpr (at level 40, f at level 200, right associativity, format "'[' 'c.Addc(' '$r' n ','  x ','  y ');' ']' '//' f") : nexpr_scope.
  Notation "'c.Selc(' '$r' n ',' y ',' z ');' f" :=
    (expr_let n := zselect _ _ _ uint256 @@ (_, y, z) in
         f)%nexpr (at level 40, f at level 200, right associativity, format "'[' 'c.Selc(' '$r' n ',' y ','  z ');' ']' '//' f") : nexpr_scope.
  Notation "'c.Sub(' '$r' n ',' x ',' y ');' f" :=
    (expr_let n := fst @@ (sub_get_borrow_concrete _ _ uint256 _ $R @@ (x, y)) in
         f)%nexpr (at level 40, f at level 200, right associativity, format "'c.Sub(' '$r' n ','  x ','  y ');' '//' f") : nexpr_scope.
  Notation "'c.AddM(' '$ret' ',' x ',' y ',' z ');'" :=
    (add_modulo _ _ _ uint256 @@ (x, y, z))%nexpr (at level 40, format "'c.AddM(' '$ret' ','  x ','  y ','  z ');'") : nexpr_scope.
  Notation "'c.ShiftR(' '$r' n ',' x ',' y ');' f" :=
    (expr_let n := (shiftr _ _ y @@ x) in f)%nexpr (at level 40, f at level 200, right associativity, format "'[' 'c.ShiftR(' '$r' n ','  x ','  y ');' ']' '//' f") : nexpr_scope.
  Notation "'c.ShiftL(' '$r' n ',' x ',' y ');' f" :=
    (expr_let n := (shiftl _ _ y @@ x) in f)%nexpr (at level 40, f at level 200, right associativity, format "'[' 'c.ShiftL(' '$r' n ','  x ','  y ');' ']' '//' f") : nexpr_scope.
  Notation "'c.Lower128(' '$r' n ',' x ');' f" :=
    (expr_let n := (land _ _ 340282366920938463463374607431768211455 @@ x) in f)%nexpr (at level 40, f at level 200, right associativity, format "'[' 'c.Lower128(' '$r' n ','  x ');' ']' '//' f") : nexpr_scope.
  Notation "'Lower128'"
    := ((land uint256 uint128 340282366920938463463374607431768211455))
         (at level 10, only printing, format "Lower128")
  : nexpr_scope.
  Notation "( v << count )"
    := ((shiftl _ _ count @@ v)%nexpr)
         (format "( v  <<  count )")
       : nexpr_scope.
  Notation "( x >> count )"
    := ((shiftr _ _ count @@ x)%nexpr)
         (format "( x  >>  count )")
       : nexpr_scope.
End Montgomery256PrintingNotations.

Import Montgomery256PrintingNotations.
Local Open Scope nexpr_scope.


Print Montgomery256.montred256.
(*
c.ShiftR($r3, $r1_lo, 128);
c.Lower128($r4, $r1_lo);
c.Mul128x128($r5, $r3, Lower128{RegPinv});
c.Lower128($r7, $r5);
c.Mul128x128($r8, $r4, RegPinv >> 128);
c.Lower128($r10, $r8);
c.ShiftL($r11, $r10, 128);
c.ShiftL($r12, $r7, 128);
c.Mul128x128($r17, $r4, Lower128{RegPinv});
c.Add128($r18, $r11, $r12);
c.Add256($r19, $r17, $r18_lo);
c.ShiftR($r43, $r19_lo, 128);
c.Lower128($r44, $r19_lo);
c.Mul128x128($r45, $r43, Lower128{RegMod});
c.ShiftR($r46, $r45, 128);
c.Lower128($r47, $r45);
c.Mul128x128($r48, $r44, RegMod << 128);
c.ShiftR($r49, $r48, 128);
c.Lower128($r50, $r48);
c.ShiftL($r51, $r50, 128);
c.ShiftL($r52, $r47, 128);
c.Mul128x128($r57, $r44, Lower128{RegMod});
c.Add128($r58, $r51, $r52);
c.Add256($r59, $r57, $r58_lo);
c.Add64($r60, $r59_hi, $r58_hi);
c.Mul128x128($r67, $r43, RegMod << 128);
c.Add256($r69, $r46, $r67);
c.Add256($r70, $r49, $r69_lo);
c.Add256($r80, $r60, $r70_lo);
c.Add256($r83, $r1_lo, $r59_lo);
c.Addc($r84, $r1_hi, $r80_lo);
c.Selc($r85,RegZero, RegMod);
c.Sub($r86, $r84_lo, $r85);
c.AddM($ret, $r86, RegZero, RegMod);
     : expr uint256
 *)
