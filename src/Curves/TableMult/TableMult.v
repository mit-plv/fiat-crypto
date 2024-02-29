Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

Local Open Scope Z_scope.

Section FoldLemmas.

  Lemma fold_right_val_closed: forall (T : Type) (V: Type)
    (fT: T -> T -> T) (val: T -> Prop),
    (forall x y : T, val x -> val y -> val (fT x y)) ->
    forall (f: V -> T) t l,
      val t -> List.Forall (fun v : V => val (f v)) l -> val (fold_right fT t (map f l)).
  Proof.
    intros.
    induction l.
    - auto.
    - simpl. apply H; [ | apply IHl]; inversion H1; assumption.
  Qed.

  Lemma fold_right_map_cond: forall (T U V : Type)
    (fT: T -> T -> T) (fU: U -> U -> U) (TtoU: T -> U) (val: T -> Prop),
    (forall x y : T, val x -> val y -> fU (TtoU x) (TtoU y) = TtoU (fT x y)) ->
    (forall x y : T, val x -> val y -> val (fT x y)) ->
    forall (f : V -> T) l t u,
      TtoU t = u ->
      val t ->
      List.Forall (fun v : V => val (f v)) l ->
      fold_right fU u (map (fun x : V => TtoU (f x)) l) =
      TtoU (fold_right fT t (map f l)).
  Proof.
    intros.
    induction l.
    - auto.
    - simpl. rewrite IHl. rewrite H.
      + trivial.
      + inversion H3. assumption.
      + simpl. apply fold_right_val_closed; try assumption.
        inversion H3. assumption.
      + inversion H3. assumption.
  Qed.

  Lemma fold_right_map: forall (T U V : Type)
    (fT: T -> T -> T) (fU: U -> U -> U) (TtoU: T -> U),
    (forall x y : T, fU (TtoU x) (TtoU y) = TtoU (fT x y)) ->
    forall (f : V -> T) l t u,
      TtoU t = u ->
      fold_right fU u (map (fun x : V => TtoU (f x)) l) =
      TtoU (fold_right fT t (map f l)).
  Proof.
    intros.
    induction l.
    - auto.
    - simpl. rewrite IHl. rewrite H. trivial.
  Qed.

  Lemma app_cons: forall [A : Type] (l : list A) (a : A),
      a :: l = [a] ++ l.
  Proof.
    simpl. reflexivity.
  Qed.

  Lemma fold_right_flat_map: forall (T U : Type) (f: T -> list U) (l : list T),
    fold_right (@List.app _ ) [] (map f l) = flat_map f l.
  Proof.
    intros.
    induction l.
    - auto.
    - rewrite app_cons.
      rewrite map_app.
      rewrite fold_right_app.
      rewrite flat_map_app.
      rewrite IHl.
      simpl.
      rewrite app_nil_r.
      trivial.
  Qed.

End FoldLemmas.

Section TableMult.

  Context
    (P : Type)
    (addP : P -> P -> P)
    (doubleP : P -> P)
    (negP : P -> P)
    (mulP : Z -> P -> P)
    (O : P) (* zero element *)
    (B : P) (* base point *)
    (q : Z) (* order of B *)
    (odd_q : Zodd q)
    (addP_negP : forall Q R, addP (negP Q) (negP R) = negP (addP Q R))
    (mulP_q : mulP q B = O)
    (mulP_zero : forall Q, mulP 0 Q = O)
    (mulP_one : forall Q, mulP 1 Q = Q)
    (mulP_addP : forall m n Q, mulP (m + n) Q = addP (mulP m Q) (mulP n Q))
    (mulP_doubleP : forall n Q, mulP (2 * n) Q = doubleP (mulP n Q))
    (mulP_negP : forall n Q, mulP (- n) Q = negP (mulP n Q))
    (mulP_mulP : forall m n Q, mulP (m * n) Q = mulP m (mulP n Q)).

  Definition ZtoP (n : Z) : P := mulP n B.

  (* Table-based multiplication, as outlined in https://eprint.iacr.org/2012/309.pdf, Section 3.3 *)

  (* Here, n denotes # of blocks, s denotes spacing, t denotes # of teeth, 
           and D = s * n * t denotes the total number of digits *)
  Context (s : Z) (t : Z) (n : Z) (nt : Z) (D : Z) 
          (Hs: 0 <= s) (Ht: 1 <= t) (Hn: 1 <= n)
          (Hnt: nt = n * t) (HD: D = s * nt)
          (Hq: 0 < q) (HDq: q < 2 ^ D).

  Section Multicomb.

    (* ======================================== *)
    (* Definitions related to `eval` and `multicomb` *)

    (* A `state` is a list of (location, bit #). A state is `valid` if all locations are nonnegative. *)
    Definition state := list (Z * Z).
    Definition valid (st: state) : Prop
      := List.Forall (fun '(i, x) => i >= 0) st.

    (* `shift` shifts the location of every bit in a state by k *)
    Definition shift (k: Z) : state -> state := List.map (fun '(i, x) => (k+i, x)).

    (* `add` adds two states together *)
    Definition add : state -> state -> state := @List.app _ .

    (* Signed bit for a given odd e *)
    Definition sbit (e : Z) (x : Z) := 2 * Z.b2z (Z.testbit ((e + 2 ^ D - 1) / 2) x) - 1.

    (* Unscaled signed bit for a given odd e*)
    Definition sbit' (e : Z) (x : Z) := Z.b2z (Z.testbit ((e + 2 ^ D - 1) / 2) x).

    Definition eval (l: state) (e: Z): Z
      := List.fold_right Z.add 0 (List.map (fun '(i, x) => 2^i * (sbit e x)) l).

    Definition Zseq (k: Z) (l: Z) := List.map Z.of_nat (List.seq (Z.to_nat k) (Z.to_nat l)).

    Definition entry (bnum: Z) (offset: Z) 
      := List.map (fun x => (s * x, s * x + offset)) (Zseq (t * bnum) t).
    
    Definition comb (offset: Z) : state 
      := List.map (fun x => (s * x, s * x + offset)) (Zseq 0 nt).

    Definition multicomb : state
      := List.fold_right (fun x y => add x (shift 1 y)) [] (List.map (fun x => comb x) (Zseq 0 s)).

    Definition stateseq (k: Z) := List.map (fun x => (x, x)) (Zseq 0 k).

    (* ==================== *)
    (* Lemmas and theorems *)

    (* -------------------- *)
    (* Zseq *)

    Lemma Zseq_succ_r': forall m b : Z,
      0 <= m -> 0 <= b -> Zseq b (Z.succ m) = Zseq b m ++ [(b + m)].
    Proof.
      (* For some reason, Coq deduces the wrong dependencies when we don't
         clear out all context variables *)
      clear Hs Ht Hn Hnt HD HDq Hq odd_q mulP_q s t n nt q D.
      intros.
      unfold Zseq.
      rewrite Z2Nat.inj_succ by trivial.
      rewrite seq_S.
      rewrite map_app.
      simpl.
      f_equal.
      rewrite <- Z2Nat.inj_add by trivial.
      rewrite Z2Nat.id by lia; trivial.
    Qed.

    Lemma Zseq_succ_r: forall m : Z,
      0 <= m -> Zseq 0 (Z.succ m) = Zseq 0 m ++ [m].
    Proof.
      clear Hs Ht Hn Hnt HD HDq Hq odd_q mulP_q s t n nt q D.
      intros; apply Zseq_succ_r' with (b := 0); lia.
    Qed.
    
    Lemma Zseq_bound': forall r : Z, 0 <= r
      -> forall b : Z, 0 <= b
      -> (forall a : Z, In a (Zseq b r) <-> b <= a < b + r).
    Proof.
      refine (natlike_ind _ _ _).
      - intros. split; intro.
        + inversion H0.
        + lia.
      - intros.
        destruct (Z.eq_dec a (b + x)); split; intro.
        + lia.
        + rewrite Zseq_succ_r' by assumption.
          rewrite in_app_iff.
          right. subst. apply in_eq.
        + rewrite Zseq_succ_r' in H2 by assumption.
          apply in_app_or in H2.
          simpl in H1.
          destruct H2; split.
          1-2: apply H0 with (a := a) in H1;
               apply H1 in H2; lia.
          all: inversion H2; try lia; inversion H3.
        + rewrite Zseq_succ_r' by assumption.
          rewrite in_app_iff.
          left.
          assert (b <= a < b + x) by lia.
          apply H0; assumption.
    Qed.

    Lemma Zseq_bound: forall r : Z, 0 <= r
      -> forall a : Z, In a (Zseq 0 r) <-> 0 <= a < r.
    Proof.
      intros; apply Zseq_bound'; lia.
    Qed.

    Lemma Zseq_app: forall b r1 r2 : Z,
      0 <= b -> 0 <= r1 -> 0 <= r2
      -> Zseq b (r1 + r2) = Zseq b r1 ++ Zseq (b + r1) r2.
    Proof.
      intros.
      unfold Zseq.
      rewrite <- map_app.
      f_equal.
      rewrite Z2Nat.inj_add by trivial.
      rewrite seq_app.
      rewrite Z2Nat.inj_add by trivial.
      reflexivity.
    Qed.

    (* -------------------- *)
    (* shift, add *)

    Lemma shift_0: forall st : state,
      (shift 0 st) = st.
    Proof.
      intros.
      induction st; simpl.
      - trivial.
      - destruct a; rewrite IHst; trivial.
    Qed.

    Lemma valid_add: forall st1 st2 : state,
      valid st1 -> valid st2 -> valid (add st1 st2).
    Proof.
      intros.
      unfold valid in *.
      unfold add.
      apply Forall_app.
      intuition.
    Qed.

    Lemma valid_shift: forall st : state, forall k : Z,
      valid st -> 0 <= k -> valid (shift k st).
    Proof.
      intros.
      unfold valid in *.
      unfold shift.
      apply Forall_map.
      eapply Forall_impl; [ | exact H].
      intros.
      destruct a.
      lia.
    Qed.

    Lemma eval_add: forall st1 st2 : state, forall e : Z,
      eval (add st1 st2) e = eval st1 e + eval st2 e.
    Proof.
      intros st1 st2 e.
      unfold eval.
      induction st1.
      - simpl. reflexivity.
      - simpl. rewrite IHst1. rewrite Z.add_assoc. reflexivity.
    Qed.

    Lemma eval_shift: forall st : state, forall k e : Z,
      valid st -> 0 <= k -> eval (shift k st) e = 2^k * eval st e.
    Proof.
      intros.
      unfold eval.
      induction st.
      - simpl. ring.
      - simpl.
        rewrite IHst.
        clear IHst.
        destruct a.
        ring_simplify.
        f_equal.
        rewrite Z.pow_add_r.
        rewrite Z.mul_comm.
        rewrite Z.mul_assoc.
        trivial.
        trivial.
        + unfold valid in H.
          inversion H.
          lia.
        + unfold valid in H.
          inversion H.
          unfold valid.
          trivial.
    Qed.

    Lemma shift_add: forall st1 st2 k,
      add (shift k st1) (shift k st2) = shift k (add st1 st2).
    Proof.
      intros. unfold shift, add. rewrite map_app. trivial.
    Qed.

    Lemma shift_shift: forall st k l,
      shift k (shift l st) = shift (k + l) st.
    Proof.
      intros. unfold shift.
      rewrite map_map.
      apply map_ext_in.
      intros.
      destruct a.
      rewrite Z.add_assoc.
      trivial.
    Qed.

    Lemma fold_right_shift: forall t, 0 <= t -> forall (f : Z -> state) l,
      fold_right (fun x y => add x (shift 1 y)) l (map f (Zseq 0 t)) =
      fold_right add (shift t l) (map (fun n => (shift n (f n))) (Zseq 0 t)).
    Proof.
      refine (natlike_ind _ _ _).
      - intros. simpl. rewrite shift_0. trivial.
      - intros.
        repeat rewrite Zseq_succ_r by assumption.
        repeat rewrite map_app.
        repeat rewrite fold_right_app.
        rewrite H0.
        f_equal.
        simpl.
        rewrite <- shift_add.
        f_equal.
        rewrite shift_shift.
        f_equal.
    Qed.

    (* -------------------- *)
    (* eval, stateseq *)

    Lemma in_stateseq: forall n, 0 <= n -> forall x,
      In x (stateseq n) -> exists m, 0 <= m < n /\ x = (m, m).
    Proof.
      refine (natlike_ind _ _ _).
      - simpl. intuition.
      - unfold stateseq.
        intros.
        rewrite Zseq_succ_r in H1 by assumption.
        rewrite map_app in H1.
        simpl in H1.
        rewrite in_app_iff in H1.
        intuition.
        + apply H0 in H2.
          destruct H2.
          exists x1.
          intuition; lia.
        + exists x.
          intuition; try lia.
          inversion H2; try destruct H1; auto.
    Qed.

    Lemma mod_sub: forall a b c : Z, c <> 0 -> (a - b * c) mod c = a mod c.
    Proof.
      intros.
      rewrite <- Z.add_opp_r.
      rewrite <- Z.mul_opp_l.
      apply Z.mod_add.
      assumption.
    Qed.

    Theorem eval_stateseq_partial: forall n, 0 <= n < D
      -> forall e : Z, - 2 ^ D < e < 2 ^ D 
                    -> Zodd e
                    -> eval (stateseq n) e = (e mod 2 ^ (n + 1)) - 2 ^ n.
    Proof.
      intros m Hm.
      destruct Hm.
      generalize dependent m.
      refine (natlike_ind _ _ _).
      - intros. unfold stateseq, eval.
        rewrite <- Zodd_bool_iff in H1.
        pose proof Zmod_odd e.
        rewrite H1 in H2.
        replace (2 ^ (0 + 1)) with 2 by nia.
        simpl.
        lia.
      - intro m. intros.
        unfold stateseq in *.
        rewrite Zseq_succ_r by trivial.
        rewrite map_app.
        rewrite eval_add.
        erewrite H0;[ | lia | trivial | trivial].
        unfold eval.
        simpl.
        rewrite <- Z.add_1_r.
        rewrite -> Z.add_0_r.
        unfold sbit.

        remember ((e + 2 ^ D - 1) / 2) as f.
        assert (e = 2 * f + 1 - 2 ^ D). {
          rewrite Heqf.
          erewrite <- Z_div_exact_2; try lia.
          apply Zodd_ex in H3.
          destruct H3.
          rewrite H3 in *.
          replace D with (D - 1 + 1) by lia.
          remember (D - 1) as E.
          assert (0 <= E) by lia.
          rewrite Z.pow_add_r; try lia.
          rewrite Z.pow_1_r.
          replace (2 * x + 1 + 2 ^ E * 2 - 1) with ((x + 2 ^ E) * 2) by lia.
          apply Z_mod_mult.
        }
        replace (n + 1 - 1) with n by lia.
        rewrite H4.
        rewrite Z.mul_sub_distr_l.
        rewrite Z.add_sub_assoc.
        rewrite Z.mul_1_r.
        rewrite Z.testbit_spec' by lia.
        replace D with (D - (m + 1) + (m + 1)) at 1 by lia.
        replace D with (D - (m + 1 + 1) + (m + 1 + 1)) at 2 by lia.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_add_r with (c := m + 1 + 1) by lia.
        repeat rewrite mod_sub by lia.
        assert (f / 2 ^ m = (2 * f + 1) / (2 ^ m * 2)). {
          rewrite Z.mul_comm with (n := 2 ^ m).
          rewrite <- Z.div_div by lia.
          rewrite Z.mul_comm.
          rewrite Z.div_add_l by lia.
          replace (1 / 2) with 0 by auto.
          rewrite Z.add_0_r.
          trivial.
        }
        rewrite Z.mul_assoc.
        repeat rewrite Z.pow_add_r by lia.
        repeat rewrite Z.pow_1_r.
        rewrite H5.
        rewrite (Z.rem_mul_r (2 * f + 1) (2 ^ m * 2) 2) by lia.
        lia. 
    Qed.
        
    Theorem eval_stateseq: forall e : Z,
      - 2 ^ D < e < 2 ^ D
      -> Zodd e
      -> eval (stateseq D) e = e.
    Proof.
      intros.
      assert (HD1: 1 <= D). {
        destruct D.
        - rewrite Z.pow_0_r in H.
          apply Zodd_ex in H0.
          destruct H0; lia.
        - lia.
        - nia.
      }
      assert (stateseq D = stateseq (D - 1) ++ [(D - 1, D - 1)]).
      { 
        unfold stateseq.
        replace D with (Z.succ (D - 1)) at 1 by lia.
        rewrite Zseq_succ_r by lia.
        rewrite map_app.
        simpl.
        trivial.
      }
      rewrite H1.
      rewrite eval_add.
      erewrite eval_stateseq_partial with (n := (D - 1)) (e := e); try lia; try assumption.
      unfold eval.
      simpl.
      case_eq e; intros.
      - subst. inversion H0.
      - assert (1 <= e) by lia.
        rewrite <- H2.
        assert (sbit e (D - 1) = 1).
        {
          clear H1.
          unfold sbit.
          rewrite Z.testbit_spec' by lia.
          rewrite Z.div_div by lia.
          rewrite <- Z.pow_succ_r by lia.
          replace (Z.succ (D - 1)) with D by lia.
          replace (e + 2 ^ D - 1) with (e - 1 + (1 * 2 ^ D)) by lia.
          rewrite Z.div_add by lia.
          rewrite Z.div_small by lia.
          auto.
        }
        rewrite H4.
        rewrite Z.sub_add.
        rewrite Z.mod_small; lia.
      - assert (e <= -1) by lia.
        rewrite <- H2.
        assert (sbit e (D - 1) = -1).
        {
          clear H1.
          unfold sbit.
          rewrite Z.testbit_spec' by lia.
          rewrite Z.div_div by lia.
          rewrite <- Z.pow_succ_r by lia.
          replace (Z.succ (D - 1)) with D by lia.
          rewrite Z.div_small by lia.
          auto.
        }
        rewrite H4.
        rewrite Z.sub_add.
        replace e with (e + 2 ^ D - 1 * 2 ^ D) at 1 by lia.
        rewrite mod_sub by nia.
        rewrite Z.mod_small by lia.
        replace D with (D - 1 + 1) at 1 by lia.
        rewrite Z.pow_add_r by lia.
        nia.
    Qed.

    Theorem eval_permutation: forall st1 st2 : state, forall e : Z, 
      Permutation st1 st2 -> eval st1 e = eval st2 e.
    Proof.
      induction 1; simpl; auto.
      - rewrite app_cons.
        rewrite (app_cons l' x).
        rewrite eval_add.
        rewrite eval_add.
        rewrite IHPermutation.
        trivial.
      - rewrite app_cons.
        rewrite (app_cons l x).
        rewrite (app_cons (y :: l) x).
        rewrite (app_cons l y).
        repeat progress rewrite eval_add.
        ring.
      - rewrite IHPermutation1.
        eapply IHPermutation2.
    Qed.

    Theorem permute_comb_correct: forall e : Z, forall st : state, 
      - 2 ^ D < e < 2 ^ D -> Zodd e -> Permutation (stateseq D) st -> eval st e = e.
    Proof.
      intros.
      rewrite <- eval_permutation with (st1 := stateseq D).
      apply eval_stateseq.
      all: assumption.
    Qed.

    (* -------------------- *)
    (* comb, entry *)

    Lemma comb_entry: forall offset,
      comb offset = List.flat_map (fun x => entry x offset) (Zseq 0 n).
    Proof.
      assert (0 <= n) by lia.
      unfold comb.
      rewrite Hnt.
      clear Hn Hnt.
      generalize dependent n.
      refine (natlike_ind _ _ _).
      - simpl. trivial.
      - intros.
        rewrite Zseq_succ_r by assumption.
        rewrite flat_map_app.
        simpl.
        replace (Z.succ x * t) with (x * t + t) by nia.
        rewrite app_nil_r.
        rewrite Zseq_app by nia.
        rewrite map_app.
        unfold entry.
        f_equal.
        + apply H0.
        + f_equal.
          f_equal.
          nia.
    Qed.

    (* -------------------- *)
    (* multicomb *)

    Lemma multicomb_length:
      length multicomb = Z.to_nat D.
    Proof.
      unfold multicomb.
      erewrite <- fold_right_map with (u := 0%nat) (fU := Nat.add).
      - assert (map (fun x : Z => length (comb x)) (Zseq 0 s) = map (fun x : Z => Z.to_nat nt) (Zseq 0 s)).
        { apply map_ext_in.
          intros.
          unfold comb, Zseq.
          repeat rewrite map_length.
          apply seq_length. }
        rewrite H; clear H.
        rewrite HD; clear HD.
        generalize dependent s.
        refine (natlike_ind _ _ _).
        + auto.
        + intros.
          rewrite Zseq_succ_r by assumption.
          rewrite map_app.
          rewrite <- fold_symmetric by lia.
          rewrite fold_left_app.
          simpl.
          rewrite -> fold_symmetric by lia.
          rewrite H0.
          lia.
      - intros.
        unfold add.
        rewrite app_length.
        f_equal.
        unfold shift.
        rewrite map_length.
        trivial.
      - auto.
    Qed.

    Lemma multicomb_simple:
      multicomb = List.fold_right add [] (map (fun x =>
        (map (fun o => (s * o + x, s * o + x)) (Zseq 0 nt)))
        (Zseq 0 s)).
    Proof.
      unfold multicomb, comb.
      rewrite fold_right_shift by assumption.
      simpl.
      f_equal.
      apply map_ext_in; intros; unfold shift; rewrite map_map.
      apply map_ext_in; intros; rewrite Z.add_comm; trivial.
    Qed.

    Lemma multicomb_elts: forall n,
      0 <= n < D -> In (n, n) multicomb.
    Proof.
      intros.
      rewrite multicomb_simple.
      unfold add.
      setoid_rewrite fold_right_flat_map with
        (f := fun x : Z => map (fun o : Z => (s * o + x, s * o + x)) (Zseq 0 nt)) (l := (Zseq 0 s)).
      rewrite in_flat_map.
      exists (n0 mod s); split.
      - apply Zseq_bound; try apply Z.mod_pos_bound; lia.
      - apply in_map_iff.
        exists (n0 / s); split.
        + rewrite <- Z_div_mod_eq_full. trivial.
        + apply Zseq_bound; try nia; split.
          * apply Z_div_nonneg_nonneg; lia.
          * apply Z.div_lt_upper_bound; lia.
    Qed.

    Theorem multicomb_stateseq: 
      Permutation (stateseq D) multicomb.
    Proof.
      eapply NoDup_Permutation_bis.
      - unfold stateseq, Zseq.
        apply NoDup_map_inv with (f := (fun '(i, x) => Z.to_nat i)).
        repeat rewrite map_map.
        assert (forall l, map (fun x : nat => Z.to_nat (Z.of_nat x)) l = l).
        { intros.
          induction l.
          - auto.
          - simpl. rewrite IHl. rewrite Nat2Z.id. trivial. }
        rewrite H.
        apply seq_NoDup.
      - rewrite multicomb_length.
        unfold stateseq, Zseq.
        repeat rewrite map_length.
        rewrite seq_length.
        auto.
      - rewrite incl_Forall_in_iff.
        rewrite Forall_forall.
        intros.
        apply in_stateseq in H; [ | lia ].
        destruct H. rename x0 into m.
        destruct H.
        rewrite H0.
        apply multicomb_elts; assumption.
    Qed.

    Theorem multicomb_correct: forall e : Z, 
      - 2 ^ D < e < 2 ^ D -> Zodd e -> eval multicomb e = e.
    Proof.
      intros.
      apply permute_comb_correct; try assumption.
      exact multicomb_stateseq.
    Qed.

  End Multicomb.

  Section Table.

    (* ======================================== *)
    (* Definitions related to tables *)

    (*
                    1  0    0  1 = 9
      Table: c =  [+1; -1; -1; +1], offset |-> sum (c[i] * 2^(i*k))
          should be equal to eval (comb s t offset) e * P,
          where the c is the bits in the respective positions of e
    *)

    (* TODO *)
    (* 
    - submit PR
    - make it clear which part is used at runtime
    - (potentially) split file into code and proofs
    *)

    (* To be replaced by looking up in an actual precomputed table *)
    Definition table_entry (bnum: Z) (d: Z) : P
      := List.fold_right addP O
      (List.map
        (fun x => ZtoP ((2 * (Z.b2z (Z.testbit d (x - t * bnum))) - 1) * 2 ^ (s * x)))
        (Zseq (t * bnum) t)).

    Definition table_entry' (bnum: Z) (d: Z) : P
      := List.fold_right addP O
      (List.map
        (fun x => ZtoP ((2 * (Z.b2z (Z.testbit d (x - t * bnum))) - 1) * 2 ^ (s * x)))
        (Zseq (t * bnum) t)).

    Lemma table_entry_hyp: forall bnum d : Z,
      0 <= d < 2 ^ (t - 1) ->
      table_entry bnum d = table_entry' bnum d.
    Proof. intros. reflexivity. Qed.

    Opaque table_entry.

    Definition table_lookup (bnum: Z) (d: Z) : P 
      := if Z.testbit d (t - 1) then negP (table_entry bnum (2 ^ t - 1 - d)) else table_entry bnum d.

    (* Definition table := List.map table_entry (Zseq 0 (2 ^ t)). *)

    Definition extract_bits (offset: Z) (e: Z) : Z
      := List.fold_right Z.add 0 (
      List.map (fun x => (sbit' e (x * s + offset)) * (2 ^ x))
      (Zseq 0 t)).

    Definition table_comb (offset: Z) (e: Z) : P
      := List.fold_right addP O
      (List.map (fun x => table_lookup x (extract_bits (offset + x * s * t) e)) (Zseq 0 n)).

    Definition table_multicomb (e: Z) : P :=
      List.fold_right (fun x y => addP x (doubleP y)) O (List.map (fun x => table_comb x e) (Zseq 0 s)).

    (* ==================== *)
    (* Lemmas and theorems *)

    (* -------------------- *)
    (* extract_bits *)

    Lemma bitmap_bound: forall (t : Z), 0 <= t ->
      forall (f: Z -> bool),
        0 <= fold_right Z.add 0 (map (fun y : Z => Z.b2z (f y) * 2 ^ y) (Zseq 0 t)) < 2 ^ t.
    Proof.
      clear HD HDq D.
      refine (natlike_ind _ _ _).
      - intros. simpl. lia.
      - intros. simpl.
        rewrite Zseq_succ_r by lia.
        rewrite map_app.
        simpl.
        rewrite <- fold_symmetric by lia.
        rewrite fold_left_app.
        simpl.
        rewrite fold_symmetric by lia.
        specialize H0 with f.
        assert (0 <= Z.b2z (f x) * 2 ^ x <= 2 ^ x). {
          case (f x).
          - replace (Z.b2z true) with 1; [ lia | compute; trivial].
          - replace (Z.b2z false) with 0; [ lia | compute; trivial].
        }
        replace (2 ^ Z.succ x) with (2 ^ x + 2 ^ x); [ lia | ].
        rewrite <- Z.add_1_r.
        rewrite Z.pow_add_r by lia.
        nia.
    Qed.

    Lemma bitmap_testbit: forall (t : Z), 0 <= t ->
      forall (x : Z), 0 <= x < t ->
      forall (f: Z -> bool),
        Z.testbit (fold_right Z.add 0 
          (map (fun y : Z => Z.b2z (f y) * 2 ^ y) (Zseq 0 t))) x
        = f x.
    Proof.
      clear HD HDq D.
      refine (natlike_ind _ _ _).
      - intros. lia.
      - intros.
        rewrite Zseq_succ_r by lia.
        rewrite map_app.
        simpl.
        rewrite <- fold_symmetric by lia.
        rewrite fold_left_app.
        simpl.
        rewrite fold_symmetric by lia.
        simpl.
        destruct (Z.eq_dec x0 x).
        + subst.
          rewrite <- Z.div_pow2_bits with (n := x) (m := 0) by lia.
          rewrite Z.div_add by nia.
          pose proof bitmap_bound x H f.
          rewrite Z.div_small by assumption.
          rewrite Z.add_0_l.
          apply Z.b2z_bit0.
        + assert (x0 < x) by lia.
          rewrite <- Z.mod_pow2_bits_low with (m := x0) (n := x) by lia.
          rewrite Z.mod_add by nia.
          rewrite Z.mod_small; [ apply H0 | apply bitmap_bound ]; lia.
    Qed.   

    Lemma extract_bits_bound: forall offset e,
     0 <= extract_bits offset e < 2 ^ t.
    Proof.
      intros; unfold extract_bits; apply bitmap_bound; lia.
    Qed.

    Lemma extract_bits_spec: forall offset e x : Z,
      0 <= x -> 0 <= offset <= s * nt ->
        (x < t -> Z.testbit (extract_bits offset e) x 
          = Z.testbit ((e + 2 ^ (s * nt) - 1) / 2) (s * x + offset))
        /\ (t <= x -> Z.testbit (extract_bits offset e) x = false).
    Proof.
      intros.
      unfold extract_bits, sbit'.
      rewrite HD in *.
      intuition.
      - rewrite Z.mul_comm with (m := x).
        apply bitmap_testbit with
          (f := fun x : Z => Z.testbit ((e + 2 ^ (s * nt) - 1) / 2) (x * s + offset));
          lia.
      - rewrite <- Z.div_pow2_bits with (n := x) (m := 0) by lia.
        assert (Ht' : 0 <= t) by lia.
        pose proof bitmap_bound t Ht' (fun x : Z =>
          Z.testbit ((e + 2 ^ (s * nt) - 1) / 2) (x * s + offset)).
        assert (0 < 2) by lia.
        pose proof Z.pow_le_mono_r 2 t x H4 H0.
        rewrite Z.div_small; [ auto | lia ].
    Qed.

    (* -------------------- *)
    (* fold_right with addP and shiftP *)

    Lemma fold_right_ZtoP: forall fZ fP,
      (forall x y, fP (ZtoP x) (ZtoP y) = ZtoP (fZ x y)) ->
      forall f l,
        fold_right fP O (map (fun x : Z => ZtoP (f x)) l ) = 
        ZtoP (fold_right fZ 0 (map f l)).
    Proof.
      intros. apply fold_right_map. exact H. unfold ZtoP. apply mulP_zero.
    Qed.

    Lemma fold_right_addP: forall f l,
      fold_right addP O (map (fun x : Z => ZtoP (f x)) l) =
      ZtoP (fold_right Z.add 0 (map f l)).
    Proof.
      apply fold_right_ZtoP. unfold ZtoP. intros. rewrite mulP_addP. trivial.
    Qed.

    Lemma fold_right_addP_shiftP: forall f l,
      fold_right (fun x y : P => addP x (doubleP y)) O (map (fun x : Z => ZtoP (f x)) l) =
      ZtoP (fold_right (fun x y : Z => Z.add x (Z.double y)) 0 (map f l)).
    Proof.
      apply fold_right_ZtoP. unfold ZtoP. intros.
      rewrite mulP_addP. rewrite mulP_doubleP. trivial.
    Qed.

    (* -------------------- *)
    (* table_lookup *)

    Lemma table_entry'_spec: forall bnum offset e : Z,
      0 <= bnum < n -> 0 <= offset < s
        -> table_entry' bnum (extract_bits (offset + bnum * s * t) e) = ZtoP (eval (entry bnum offset) e).
    Proof.
      intros.
      unfold eval, entry, table_entry'.
      rewrite fold_right_addP.
      rewrite map_map.
      f_equal.
      f_equal.
      apply map_ext_in.
      intros.
      rewrite Z.mul_comm.
      f_equal.
      unfold sbit.
      f_equal.
      f_equal.
      f_equal.
      assert (Hb: 0 <= t * bnum) by nia.
      assert (Ht': 0 <= t) by lia.
      pose proof Zseq_bound' t Ht' (t * bnum) Hb.
      apply H2 in H1.
      replace a with (a - t * bnum + t * bnum) by lia.
      remember (a - t * bnum) as a'.
      rewrite Z.add_simpl_r.
      rewrite HD.
      replace (s * (a' + t * bnum) + offset) with (s * a' + (offset + bnum * s * t)) by nia.
      eapply extract_bits_spec; assert (0 < s * t) by nia; nia.
    Qed.


    Lemma testbit_flip: forall d t' b : Z,
      0 <= d < 2 ^ t' -> 0 <= b < t'
        -> Z.testbit (2 ^ t' - 1 - d) b = negb (Z.testbit d b).
    Proof.
      intros.
      rewrite <- Z.lnot_spec by lia.
      rewrite <- Z.mod_pow2_bits_low with (n := t') by lia.
      rewrite <- Z.mod_pow2_bits_low with (n := t') (a := Z.lnot d) by lia.
      f_equal.
      rewrite <- mod_sub with (b := 1) by nia.
      f_equal.
      pose proof Z.add_lnot_diag d.
      lia.
    Qed.

    Lemma b2z_testbit_flip: forall d t' b : Z,
      0 <= d < 2 ^ t' -> 0 <= b < t'
        -> 2 * (Z.b2z (Z.testbit (2 ^ t' - 1 - d) b)) - 1
           = - (2 * (Z.b2z (Z.testbit d b)) - 1).
    Proof.
      intros.
      rewrite testbit_flip by assumption.
      case (Z.testbit d b); reflexivity.
    Qed.

    Lemma testbit_top_bit: forall d t' : Z,
      1 <= t' -> 0 <= d < 2 ^ t'
        -> Z.testbit d (t' - 1) = (2 ^ (t' - 1) <=? d).
    Proof.
      intros.
      assert (0 <= t' - 1) by lia.
      case_eq (2 ^ (t' - 1) <=? d); intro.
      - rewrite Z.leb_le in H2.
        replace (t' - 1) with (0 + (t' - 1)) by lia.
        rewrite <- Z.div_pow2_bits by lia.
        replace (d / 2 ^ (t' - 1)) with 1; auto.
        replace d with (d - 2 ^ (t' - 1) + 1 * 2 ^ (t' - 1)) by lia.
        rewrite Z.div_add by nia.
        replace 1 with (0 + 1) at 1 by lia.
        apply Z.add_cancel_r.
        symmetry.
        apply Z.div_small.
        replace (2 ^ t') with (2 ^ (t' - 1) + 2 ^ (t' - 1)) in H0.
        lia.
        replace t' with (t' - 1 + 1) at 3 by lia.
        rewrite Z.pow_add_r by lia.
        nia.
      - rewrite Z.leb_gt in H2.
        replace (t' - 1) with (0 + (t' - 1)) by lia.
        rewrite <- Z.div_pow2_bits by lia.
        replace (d / 2 ^ (t' - 1)) with 0; auto.
        symmetry.
        apply Z.div_small.
        lia.
    Qed.      

    Lemma table_entry'_flip: forall bnum d : Z,
      0 <= d < 2 ^ t -> 0 <= bnum
        -> table_entry' bnum (2 ^ t - 1 - d) = negP (table_entry' bnum d).
    Proof.
      intros.
      unfold table_entry'.
      assert (rewrite_map:
        map (fun x : Z => ZtoP ((2 * Z.b2z (Z.testbit (2 ^ t - 1 - d) (x - t * bnum)) - 1) * 2 ^ (s * x)))
        (Zseq (t * bnum) t) =
        map (fun x : Z => negP (ZtoP ((2 * Z.b2z (Z.testbit d (x - t * bnum)) - 1) * 2 ^ (s * x))))
        (Zseq (t * bnum) t)).
      {
        apply map_ext_in.
        intros.
        rewrite Zseq_bound' in H1 by lia.
        rewrite b2z_testbit_flip by lia.
        unfold ZtoP.
        rewrite <- mulP_negP.
        f_equal.
        nia.
      }
      rewrite rewrite_map.
      apply fold_right_map.
      - exact addP_negP.
      - rewrite <- mulP_zero with (Q := B).
        rewrite <- mulP_negP.
        f_equal; lia.
    Qed.

    Lemma table_lookup_spec: forall bnum offset e : Z,
      0 <= bnum < n -> 0 <= offset < s
        -> table_lookup bnum (extract_bits (offset + bnum * s * t) e) = ZtoP (eval (entry bnum offset) e).
    Proof.
      intros.
      pose proof extract_bits_bound (offset + bnum * s * t) e.
      unfold table_lookup.
      pose proof testbit_top_bit (extract_bits (offset + bnum * s * t) e) t Ht H1.
      case_eq (Z.testbit (extract_bits (offset + bnum * s * t) e) (t - 1)); intro; rewrite H3 in *.
      - symmetry in H2. 
        rewrite Z.leb_le in H2.
        replace (2 ^ t) with (2 ^ (t - 1) + 2 ^ (t - 1)) in *;
          [ | replace t with (t - 1 + 1) at 3 by lia; rewrite Z.pow_add_r; nia ].
        rewrite table_entry_hyp by lia.
        rewrite <- table_entry'_flip.
        + rewrite <- table_entry'_spec by lia.
          f_equal.
          replace (2 ^ t) with (2 ^ (t - 1) + 2 ^ (t - 1)) in *;
            [ lia | replace t with (t - 1 + 1) at 3 by lia; rewrite Z.pow_add_r; nia ].
        + replace (2 ^ t) with (2 ^ (t - 1) + 2 ^ (t - 1)) in *;
            [ lia | replace t with (t - 1 + 1) at 3 by lia; rewrite Z.pow_add_r; nia ].
        + lia.
      - symmetry in H2.
        rewrite Z.leb_gt in H2.
        rewrite table_entry_hyp by lia.
        apply table_entry'_spec; assumption.
    Qed. 

    (* -------------------- *)
    (* table_comb *)

    Lemma table_comb_spec: forall offset e : Z,
      0 <= offset < s -> table_comb offset e = ZtoP (eval (comb offset) e).
    Proof.
      intros.
      unfold table_comb.
      assert (rewrite_map: map (fun x : Z => table_lookup x (extract_bits (offset + x * s * t) e))
                (Zseq 0 n) = map (fun x : Z => ZtoP (eval (entry x offset) e)) (Zseq 0 n)). {
        apply map_ext_in.
        intros.
        apply table_lookup_spec; apply Zseq_bound in H0; lia.
      }
      rewrite rewrite_map.
      rewrite fold_right_addP.
      f_equal.
      f_equal.
      rewrite comb_entry.
      rewrite <- fold_right_flat_map.
      rewrite fold_right_map with (t := []) (fT := add) (TtoU := fun x => eval x e).
      - f_equal.
      - intros. rewrite eval_add. trivial.
      - trivial.
    Qed.
    
    (* -------------------- *)
    (* table_multicomb *)

    Theorem table_multicomb_spec: forall e : Z,
      table_multicomb e = ZtoP (eval multicomb e).
    Proof.
      intros.
      unfold table_multicomb.
      unfold ZtoP.
      unfold multicomb.
      assert (rewrite_map: fold_right (fun x y : P => addP x (doubleP y)) O
                (map (fun x : Z => table_comb x e) (Zseq 0 s)) =
              fold_right (fun x y : P => addP x (doubleP y)) O
                (map (fun x : Z => ZtoP (eval (comb x) e)) (Zseq 0 s))).
      { f_equal.
        apply map_ext_in.
        intros.
        pose proof Zseq_bound s Hs.
        apply H0 in H.
        apply table_comb_spec; assumption. }
      rewrite rewrite_map.
      rewrite fold_right_addP_shiftP.
      unfold ZtoP.
      f_equal.
      eapply fold_right_map_cond with (TtoU := fun st : state => eval st e) (val := valid).
      - intros.
        rewrite eval_add.
        rewrite eval_shift by (try assumption; lia).
        nia.
      - intros.
        apply valid_add; try apply valid_shift; try assumption; lia.
      - compute. trivial.
      - unfold valid. auto.
      - unfold comb.
        rewrite Forall_forall.
        intros.
        unfold valid.
        rewrite Forall_map.
        rewrite Forall_forall.
        intros.
        apply Zseq_bound in H0; nia.
    Qed.

    Theorem table_multicomb_correct: forall e : Z,
      - 2 ^ D < e < 2 ^ D -> Zodd e -> table_multicomb e = ZtoP e.
    Proof.
      intros. rewrite table_multicomb_spec. f_equal.
      apply multicomb_correct; assumption.
    Qed.

  End Table.

  Section Oddify.

    (* ======================================== *)
    (* Oddify: support any value of e by reducing mod q to an odd number in bounds. *)

    Definition oddify (e: Z) : Z := if Z.odd e then e else (e - q).
    Definition positify (e: Z) : Z := (2 ^ D - 1 + oddify (e mod q)) / 2.
    (* 
      This can always be computed without negative intermediate values:
      if oddify (e mod q) <= 0 then this amounts to flipping the last D bits from  - (oddify (e mod q));
      else, we compute 2 ^ (D - 1) + (oddify (e mod q) >> 1).
    *)

    (*
    Definition positify' (e: Z) : Z :=
     let e := e mod q in 
     if Z.odd e then
       2 ^ (D - 1) + (e >> 1)
     else
      ((2 ^ D - 1) - (q - e)) >> 1.

    Definition positify'' (e: Z) : Z :=
     let e := e mod q in
     let o := 2 ^ D - 1 + e in
     let i := if Z.odd e then o else o - q in
     Z.shiftr i 1.
     *)

    Definition extract_bits_positify (offset: Z) (e: Z) : Z
    := List.fold_right Z.add 0 (
    List.map (fun x => Z.b2z (Z.testbit (positify e) (x * s + offset)) * (2 ^ x))
    (Zseq 0 t)).

    Definition table_comb_positify (offset: Z) (e: Z) : P
    := List.fold_right addP O
    (List.map (fun x => table_lookup x (extract_bits_positify (offset + x * s * t) e)) (Zseq 0 n)).

    (* This is the definition used at runtime! *)
    Definition table_multicomb_positify (e: Z) : P :=
    List.fold_right (fun x y => addP x (doubleP y)) O (List.map (fun x => table_comb_positify x e) (Zseq 0 s)).

    (* Evenify has been replaced by positify *)
    (* 
    Definition evenify (e: Z) : Z := if Z.odd e then e + q else e.

    Definition sbit_evenify (e: Z) (x: Z) := 2 * Z.b2z (Z.testbit (evenify (e + 2 ^ D - 1) / 2) x) - 1.
    Definition sbit'_evenify (e: Z) (x: Z) := Z.b2z (Z.testbit (evenify (e + 2 ^ D - 1) / 2) x).
    *)

    (* ==================== *)
    (* Lemmas and theorems *)

    (* -------------------- *)
    (* oddify *)

    Lemma oddify_odd: forall (e : Z), Zodd (oddify (e mod q)).
    Proof.
      intros.
      unfold oddify.
      case_eq (Z.odd (e mod q)); intros.
      - apply Zodd_bool_iff. assumption.
      - apply Zeven_plus_Zodd.
        apply Zeven_equiv.
        apply Z.even_spec.
        rewrite Zodd_even_bool in H.
        rewrite Bool.negb_false_iff in H.
        assumption.
        rewrite Z.opp_eq_mul_m1.
        apply Zodd_mult_Zodd; [ assumption | ].
        rewrite Zodd_ex_iff.
        exists (- 1).
        lia.
    Qed.

    Lemma oddify_bounds: forall (e : Z), - 2 ^ D < oddify (e mod q) < 2 ^ D.
    Proof.
      intros.
      unfold oddify.
      pose proof (Z.mod_pos_bound e q Hq).
      case_eq (Z.odd (e mod q)); intros; lia.
    Qed.

    Lemma oddify_mod_q: forall (e : Z), (oddify (e mod q)) mod q = e mod q.
    Proof.
      intros.
      unfold oddify.
      case_eq (Z.odd (e mod q)); intros.
      - rewrite Z.mod_mod; lia.
      - replace q with (1 * q) at 2 by lia.
        rewrite mod_sub by lia.
        rewrite Z.mod_mod; lia.
    Qed.
    
    Lemma ZtoP_oddify: forall (e : Z), ZtoP (oddify (e mod q)) = ZtoP e.
    Proof.
      intros.
      assert ((oddify (e mod q) - e) mod q = 0). {
        rewrite Zminus_mod.
        rewrite <- oddify_mod_q with (e := e) at 2.
        rewrite Z.sub_diag.
        rewrite Z.mod_0_l; lia.
      }
      apply Z.div_exact in H; [ | lia].
      rewrite Z.sub_move_r in H.
      rewrite H.
      rewrite Z.add_comm.
      unfold ZtoP.
      rewrite mulP_addP.
      rewrite Z.mul_comm.
      rewrite mulP_mulP.
      rewrite mulP_q.
      rewrite <- mulP_zero with (Q := B).
      rewrite <- mulP_mulP.
      rewrite Z.mul_0_r.
      rewrite <- mulP_addP.
      f_equal.
      lia.
    Qed.

    Theorem table_multicomb_oddify_correct: forall e : Z,
      table_multicomb (oddify (e mod q)) = ZtoP e.
    Proof.
      intros. rewrite table_multicomb_correct.
      - apply ZtoP_oddify.
      - apply oddify_bounds.
      - apply oddify_odd.
    Qed.

    (* -------------------- *)
    (* evenify *)

    (*
    Lemma oddify_evenify: forall e, 0 <= e < q ->
    exists f, f mod q = (oddify e) mod q /\
    (f + 2 ^ D - 1) / 2 = evenify (e + 2 ^ D - 1) / 2.
    Proof.
      intros.
      unfold oddify, evenify.
      f_equal.
      case_eq (Z.odd e); intros.
      - replace (Z.odd (e + 2 ^ D - 1)) with false.
        exists e.
        auto.
        admit.
      - replace (Z.odd (e + 2 ^ D - 1)) with true by admit.
        exists (e + q).
        split.
        admit.
        f_equal.
        lia.
    Admitted.
    *) 

    (* -------------------- *)
    (* positify *)

    Lemma positify_spec: forall e, 0 <= positify e < 2 ^ D.
    Proof.
      intros.
      unfold positify.
      pose proof oddify_bounds e.
      intuition auto with core.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; lia.
    Qed.

    Lemma extract_bits_positify_spec: forall offset e,
      extract_bits_positify offset e = extract_bits offset (oddify (e mod q)). 
    Proof.
      intros.
      unfold extract_bits, extract_bits_positify.
      f_equal.
      apply map_ext_in.
      intros.
      unfold sbit', positify.
      f_equal.
      f_equal.
      f_equal.
      f_equal.
      lia.
    Qed.

    Lemma table_comb_positify_spec: forall offset e,
      table_comb_positify offset e = table_comb offset (oddify (e mod q)).
    Proof.
      intros.
      unfold table_comb, table_comb_positify.
      f_equal.
      apply map_ext_in.
      intros.
      f_equal.
      apply extract_bits_positify_spec.
    Qed.

    Lemma table_multicomb_positify_spec: forall e,
      table_multicomb_positify e = table_multicomb (oddify (e mod q)).
    Proof.
      intros.
      unfold table_multicomb, table_multicomb_positify.
      f_equal.
      apply map_ext_in.
      intros.
      apply table_comb_positify_spec.
    Qed.

    Lemma table_multicomb_positify_correct: forall e,
      table_multicomb_positify e = ZtoP e.
    Proof.
      intros.
      rewrite table_multicomb_positify_spec.
      apply table_multicomb_oddify_correct.
    Qed.
    
  End Oddify.

End TableMult.

Print Transparent Dependencies table_multicomb_positify.

Section Instantiations.

Section AddMod.

  Require Import Spec.ModularArithmetic.

  Definition P := F ( 101 ).
  Definition O : P := F.zero.
  Definition B : P := F.of_Z _ 2.
  Definition addP : P -> P -> P := F.add.
  Definition doubleP : P -> P := F.mul (F.of_Z _ 2).
  Definition mulP (n : Z) : P -> P := F.mul (F.of_Z _ n).
  Definition negP : P -> P := F.opp.

  Definition n := 1.
  Definition s := 2.
  Definition t := 3.
  Definition D := s * t.

  Compute mulP 4 B.

  Print table_entry.
  Compute table_entry P addP mulP O B s t 0 1.
  (* (-16 -4 +1) * 2 mod 101 = 63 *)

  Print extract_bits.
  Compute extract_bits s t D 1 1.

  Print table_comb.
  Compute table_comb P addP negP mulP O B s t n D 1 1.

  Print table_multicomb.
  Compute table_multicomb P addP doubleP negP mulP O B s t n D (-7).

End AddMod.

(* TODO test on multiplication over F_p, using FLT to do negative exponents *)
(* TODO instantiate this for Curve25519 *)

End Instantiations.
