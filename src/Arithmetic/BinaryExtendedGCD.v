Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Crypto.Experiments.Loops.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.

Local Open Scope Z_scope.

Module BinaryExtendedGCD.
  Section BinaryExtendedGCD.
    (** This section implements a constant-time version of the binary extended
        GCD algorithm, for computing modular inverses. It is the fully general
        version, supporting even moduli. In most cases, more specific algorithms
        should be used. For instance, inverting by a prime is simpler to do with
        Fermat's Little Theorem. However, RSA key generation requires the most
        general version.

        This algorithm is adapted from the Handbook of Applied Cryptography,
        section 14.4.3, algorithm 14.61. It was modified slightly to better
        bound coefficients, then recast into constant-time selects:

        1. Negate [B] and [C] so they are positive. The invariant now involves a
           subtraction.

        2. If step 2 (both [x] and [y] are even) runs, abort immediately. This
           algorithm only cares about [x] and [y] relatively prime.

        3. Subtract copies of [x] and [y] as needed in step 6 (both [u] and [v]
           are odd) so coefficients stay in bounds.

        4. Replace the [u >= v] check with [u > v]. This changes the end
           condition to [v = 0] rather than [u = 0]. This saves an extra
           subtraction due to which coefficients were negated.

        5. Rename x and y to a and n, to capture that one is a modulus.

        6. Rearrange steps 4 through 6 slightly. Merge the loops in steps 4 and
           5 into the main loop (step 7's goto), and move step 6 to the start of
           the loop iteration, ensuring each loop iteration halves at least one
           value.

        Note this algorithm does not handle either input being zero. *)

    (** This is a constant-time algorithm, so first define fixed-width words to
        compute over. In particular, we want to capture the non-trivial bounds on
        the intermediate values. A [word] is an integer with specified bit
        width. The actual implementation will represent this with an array of
        smaller machine words. *)
    Inductive word (bits : Z) :=
    | Word : Z -> word bits.

    Definition wrap (bits val : Z) : Z := val mod 2^bits.

    Definition to_Z {bits : Z} (a : word bits) : Z :=
      match a with Word v => v end.
    Definition to_word {bits : Z} (val : Z) :=
      Word bits (wrap bits val).

    (** Our algorithm is implemented over the following constant-time
        primitives. [add] and [sub] return a carry and borrow bit,
        respectively. *)
    Definition add {bits : Z} (a b : word bits) : bool * word bits :=
      let a' := to_Z a in
      let b' := to_Z b in
      (2^bits <=? a' + b', to_word (a' + b')).
    Definition sub {bits : Z} (a b : word bits) : bool * word bits :=
      let a' := to_Z a in
      let b' := to_Z b in
      (a' <? b', to_word (a' - b')).
    Definition rshift1 {bits : Z} (a : word bits) : word bits :=
      to_word ((to_Z a) / 2).
    Definition select {bits : Z} (t : bool) (a b : word bits) : word bits :=
      if t then a else b.
    Definition odd {bits : Z} (a : word bits) : bool := Z.odd (to_Z a).
    Definition is_one {bits: Z} (a : word bits) : bool := to_Z a =? 1.


    (** These helpers are implemented with temporaries. They return the final
        values of the temporaries, to model clobbering them in imperative
        code. *)
    Definition maybe_rshift1_carry {bits : Z}
               (t carry : bool) (a : word bits) : word bits * word bits :=
      let tmp := rshift1 a in
      let a := select t tmp a in
      let a := if t && carry then to_word ((to_Z a)  + 2^(bits - 1))
               else a in
      (a, tmp).

    Definition maybe_rshift1 {bits : Z} (t : bool) :=
      @maybe_rshift1_carry bits t false.

    Definition maybe_add {bits : Z}
               (t : bool) (a b : word bits) : bool * word bits * word bits :=
      let (carry, tmp) := add a b in
      let a := select t tmp a in
      (carry && t, a, tmp).

    (** We ultimately wish to compute [a] inverse mod [n]. Parameterize over
        both values' public widths. ([a]'s width may be smaller than [n]'s if it
        publicly-bounded. For instance, RSA key generation involves a public
        small [a], typically 65537, and a large secret modulus, the totient. *)
    Context {abits nbits : Z}.
    Context {abits_positive : 0 < abits}.
    Context {nbits_positive : 0 < nbits}.

    (** This is our loop state. *)
    Definition state : Set :=
      word abits * word nbits * (* a, n *)
      word nbits * word abits * word nbits * word abits * (* A, B, C, D *)
      word nbits * word nbits (* u, v *).

    Definition step (s : state) : state :=
      let '(a, n, A, B, C, D, u, v) := s in
      (* If both |u| and |v| are odd, subtract the smaller from the larger. *)
      let both_odd := odd u && odd v in
      let (v_less_than_u, tmp) := sub v u in
      let v := select (both_odd && negb v_less_than_u) tmp v in
      let (_, tmp) := sub u v in
      let u := select (both_odd && v_less_than_u) tmp u in

      (* If we updated one of the values, update the corresponding
         coefficient. *)
      let (carry, tmp) := add A C in
      let (borrow, tmp2) := sub tmp n in
      let borrow := borrow && negb carry in
      let tmp := select borrow tmp tmp2 in
      let A := select (both_odd && v_less_than_u) tmp A in
      let C := select (both_odd && negb v_less_than_u) tmp C in

      let (_, tmp) := add B D in
      let (_, tmp2) := sub tmp a in
      let tmp := select borrow tmp tmp2 in
      let B := select (both_odd && v_less_than_u) tmp B in
      let D := select (both_odd && negb v_less_than_u) tmp D in

      (* Our loop invariants hold at this point. Additionally, exactly one of
         [u] and [v] is now even. *)
      let u_even := negb (odd u) in
      let v_even := negb (odd v) in

      (* Halve the even one and adjust the corresponding coefficient. *)
      let (u, tmp) := maybe_rshift1 u_even u in
      let A_or_B_odd := odd A || odd B in
      let '(A_carry, A, tmp) := maybe_add (A_or_B_odd && u_even) A n in
      let '(B_carry, B, tmp) := maybe_add (A_or_B_odd && u_even) B a in
      let (A, tmp) := maybe_rshift1_carry u_even A_carry A in
      let (B, tmp) := maybe_rshift1_carry u_even B_carry B in

      let (v, tmp) := maybe_rshift1 v_even v in
      let C_or_D_odd := odd C || odd D in
      let '(C_carry, C, tmp) := maybe_add (C_or_D_odd && v_even) C n in
      let '(D_carry, D, tmp) := maybe_add (C_or_D_odd && v_even) D a in
      let (C, tmp) := maybe_rshift1_carry v_even C_carry C in
      let (D, tmp) := maybe_rshift1_carry v_even D_carry D in
      (a, n, A, B, C, D, u, v).

    Definition mod_inverse_consttime
               (a : word abits) (n : word nbits) : option (word nbits) :=
      if negb (odd a) && negb (odd n)
      then None
      else
        let u := to_word (to_Z a) in
        let v := n in
        let A := to_word 1 in
        let B := to_word 0 in
        let C := to_word 0 in
        let D := to_word 1 in
        let i := 0 in
        let '(a, n, A, B, C, D, u, v, _) :=
            (while (fun '(_, i) => i <? abits + nbits)
                   (fun '(s, i) => (step s, i + 1))
                   (Z.to_nat (abits + nbits))
                   (a, n, A, B, C, D, u, v, i)) in
        if is_one u
        then Some A
        else None.


    (** Proofs *)

    (** To simplify analysis, we split each loop in the middle, where the loop
        invariant also holds. *)

    Definition odd_step (s : state) : state :=
      let '(a, n, A, B, C, D, u, v) := s in

      (* If both |u| and |v| are odd, subtract the smaller from the larger. *)
      let both_odd := odd u && odd v in
      let (v_less_than_u, tmp) := sub v u in
      let v := select (both_odd && negb v_less_than_u) tmp v in
      let (_, tmp) := sub u v in
      let u := select (both_odd && v_less_than_u) tmp u in

      (* If we updated one of the values, update the corresponding
         coefficient. *)
      let (carry, tmp) := add A C in
      let (borrow, tmp2) := sub tmp n in
      let borrow := borrow && negb carry in
      let tmp := select borrow tmp tmp2 in
      let A := select (both_odd && v_less_than_u) tmp A in
      let C := select (both_odd && negb v_less_than_u) tmp C in

      let (_, tmp) := add B D in
      let (_, tmp2) := sub tmp a in
      let tmp := select borrow tmp tmp2 in
      let B := select (both_odd && v_less_than_u) tmp B in
      let D := select (both_odd && negb v_less_than_u) tmp D in
      (a, n, A, B, C, D, u, v).

    Definition even_step (s : state) : state :=
      let '(a, n, A, B, C, D, u, v) := s in

      (* This step should be called after [odd_step], which ensures at least one
         of [u] and [v] are even. *)
      let u_even := negb (odd u) in
      let v_even := negb (odd v) in

      (* Halve the even one and adjust the corresponding coefficient. *)
      let (u, tmp) := maybe_rshift1 u_even u in
      let A_or_B_odd := odd A || odd B in
      let '(A_carry, A, tmp) := maybe_add (A_or_B_odd && u_even) A n in
      let '(B_carry, B, tmp) := maybe_add (A_or_B_odd && u_even) B a in
      let (A, tmp) := maybe_rshift1_carry u_even A_carry A in
      let (B, tmp) := maybe_rshift1_carry u_even B_carry B in

      let (v, tmp) := maybe_rshift1 v_even v in
      let C_or_D_odd := odd C || odd D in
      let '(C_carry, C, tmp) := maybe_add (C_or_D_odd && v_even) C n in
      let '(D_carry, D, tmp) := maybe_add (C_or_D_odd && v_even) D a in
      let (C, tmp) := maybe_rshift1_carry v_even C_carry C in
      let (D, tmp) := maybe_rshift1_carry v_even D_carry D in
      (a, n, A, B, C, D, u, v).

    Ltac destruct_state s :=
      destruct s as [[[[[[[[a] [n]] [A]] [B]] [C]] [D]] [u]] [v]].

    Lemma step_even_odd (s : state) :
      even_step (odd_step s) = step s.
    Proof.
      destruct_state s. reflexivity. Qed.

    (** Next, we establish a core GCD invariant that the loop will maintain. *)

    Definition invariant (s : state) :=
      match s with
      | (Word a, Word n, Word A, Word B, Word C, Word D, Word u, Word v) =>
        (* Bounds on all values. Note [B] and [D] have slightly looser bounds
           than [A] and [C]. *)
        0 < n < 2^nbits /\
        0 < a < 2^abits /\
        a < n /\
        0 < u <= a /\
        0 <= v <= n /\
        0 <= A < n /\
        0 <= B <= a /\
        0 <= C < n /\
        0 <= D <= a /\
        (* The both even case is discarded early; [a] cannot have an inverse mod
           [n] if both are even. *)
        (Z.odd u = true \/ Z.odd v = true) /\
        (Z.odd a = true \/ Z.odd n = true) /\
        (* The extended GCD invariant. *)
        u = A*a - B*n /\
        v = D*n - C*a /\
        Z.gcd u v = Z.gcd a n
      end.

    Lemma if_func_distr (X Y : Type) (f : X -> Y) (t : bool) (a b : X) :
      (if t then f a else f b) = f (if t then a else b).
    Proof. destruct t; reflexivity. Qed.

    Lemma if_mod_distr (t : bool) (a b n : Z) :
      (if t then a mod n else b mod n) = (if t then a else b) mod n.
    Proof. destruct t; reflexivity. Qed.

    Ltac simplify_words :=
      cbv [select odd add sub rshift1 maybe_add maybe_rshift1
                  maybe_rshift1_carry to_Z to_word wrap is_one];
      try rewrite !if_func_distr.

    Ltac bool_to_prop_once :=
      first [rewrite andb_true_iff in * |
             rewrite andb_false_iff in * |
             rewrite orb_true_iff in * |
             rewrite orb_false_iff in * |
             rewrite negb_true_iff in * |
             rewrite negb_false_iff in * |
             rewrite Z.eqb_eq in * |
             rewrite Z.eqb_neq in * |
             rewrite Z.ltb_lt in * |
             rewrite Z.ltb_ge in * |
             rewrite Z.leb_le in * |
             rewrite Z.leb_gt in *].

    (** Consider all possible parities for [u] and [v], but discard the one where
        [u] and [v] are both even. *)
    Ltac destruct_odd_u_v u v :=
      destruct (Z.odd u) eqn:Hu;
      destruct (Z.odd v) eqn:Hv;
      [ | | |
        (* [u] and [v] cannot both be even by [invariant]. *)
        destruct_head'_and;
        destruct_head'_or;
        match goal with
        | H : false = true |- _ => inversion H
        end ].

    (** This is a roundabout way of saying [n < A + C] that comes out of [add]
        and [sub] in [odd_step]. *)
    Lemma add_then_sub_gt (bits n A C : Z)
          (Hn : 0 <= n < 2^bits)
          (HA : 0 <= A < 2^bits)
          (HC : 0 <= C < 2^bits) :
      ((A + C) mod 2^bits <? n) && negb (2^bits <=? A + C) = (A + C <? n).
    Proof.
      destruct (A + C <? n) eqn:HACn;
        destruct (A + C <? 2^bits) eqn:HAC2bits;
        repeat first [bool_to_prop_once | split];
        repeat match goal with
               | H : ?a < ?m |- context[?a mod ?m] =>
                 rewrite (Z.mod_small a m) by lia
               | _ => lia
               end.
    Qed.

    (** Prove the left version of [Z.gcd_sub_diag_r]. *)
    Lemma Zgcd_sub_diag_l (n m : Z) : Z.gcd (n - m) m = Z.gcd n m.
    Proof.
      rewrite (Z.gcd_comm (n - m) m).
      rewrite (Z.gcd_comm n m).
      apply Z.gcd_sub_diag_r.
    Qed.

    (** The following bounds on [B + D] come out of [nia], but [nia] takes a
        long time to discover this in the context of the full proof. *)
    Lemma AC_lt_BD_le (a n A B C D : Z) :
      0 <= a < n ->
      0 < A*a - B*n <= a ->
      0 <= D*n - C*a <= n ->
      A + C < n ->
      B + D <= a.
    Proof. nia. Qed.

    Lemma AC_ge_BD_ge (a n A B C D : Z) :
      0 <= a < n ->
      0 < A*a - B*n <= a ->
      0 <= D*n - C*a <= n ->
      n <= A + C ->
      a <= B + D.
    Proof. nia. Qed.

    Lemma odd_step_invariant
          (s : state)
          (H : invariant s) :
      invariant (odd_step s).
    Proof.
      destruct_state s.
      unfold odd_step, invariant in *.
      simplify_words.

      rewrite add_then_sub_gt by lia.

      (* Expand all cases and simplify. While doing so, help [lia] with bounds
         on [B + D] to go with the [A + C] bounds. *)
      destruct (A + C <? n) eqn:HACn;
        [ assert (B + D <= a) by (apply (AC_lt_BD_le a n A B C D);
                                  repeat bool_to_prop_once; lia) |
          assert (a <= B + D) by (apply (AC_ge_BD_ge a n A B C D);
                                  repeat bool_to_prop_once; lia) ];
        destruct_odd_u_v u v;
        destruct (v <? u) eqn:Huv;
        cbn;

        (* Discard the cases where [odd_step] is a no-op. [Hu] and [Hv] must be
           re-applied due to some simplification. *)
        try rewrite Hu;
        try rewrite Hv;
        try apply H;

        destruct_head'_and;
        repeat match goal with
               | _ => bool_to_prop_once
               | _ => rewrite Zminus_mod_idemp_l
               (* Note this relies both on [destruct] and [cbn] above clearing
                  all dead branches, as well as [Zminus_mod_idemp_l] above
                  simplifying some expressions. Some operations intentionally
                  overflow or underflow, but are either discarded by [select] or
                  cancelled out by a later operation. *)
               | _ => rewrite Z.mod_small
               | _ => split
               | _ => apply Z.mod_pos_bound
               | _ => rewrite Zgcd_sub_diag_l
               | _ => rewrite Z.gcd_sub_diag_r
               | _ => progress auto
               | _ => lia
               end.
    Qed.

    (** [even_step] writes [(x + y) / 2] slightly funny. *)
    Lemma add_carry_div2 (bits x y : Z)
          (Hbits : 0 < bits)
          (Hx : 0 <= x < 2^bits)
          (Hy : 0 <= y < 2^bits) :
      (if 2^bits <=? x + y
       then ((x + y) mod 2^bits / 2 + 2^(bits-1))
       else (x + y) mod 2^bits / 2) = (x + y) / 2.
    Proof.
      destruct (2^bits <=? x + y) eqn:Hxy; repeat bool_to_prop_once.
      { (* 2^bits <= x + y *)
        rewrite Z.mod_small_1 by lia.
        replace (2^bits) with (2*2^(bits-1)) by (rewrite <- Z.pow_succ_r; f_equal; lia).
        rewrite Z.div_sub' by lia.
        lia. }
      { (* x + y < 2^bits *)
        rewrite Z.mod_small by lia.
        lia. }
    Qed.

    Lemma pos_even_le (z : Z) (Heven : Z.odd z = false) (Hpos : 0 < z) :
      2 <= z.
    Proof.
      destruct (z =? 1) eqn:H1; repeat bool_to_prop_once.
      { rewrite H1 in Heven.
        cbn in Heven.
        inversion Heven. }
      { lia. }
    Qed.

    Lemma gcd_div_rel_prime_l (a b c : Z)
          (Hc : 0 < c)
          (Hdiv : (c | a))
          (Hrel : rel_prime b c) :
      Z.gcd (a / c) b = Z.gcd a b.
    Proof.
      symmetry.
      apply Z.gcd_unique.
      - apply Z.gcd_nonneg.
      - apply (Z.divide_transitive (Z.gcd (a / c) b) (a / c) a).
        + apply Z.gcd_divide_l.
        + exists c; apply Zdivide_Zdiv_eq; trivial.
      - apply Z.gcd_divide_r.
      - intros q Hqa Hqb.
        destruct Hdiv as [x Hx].
        rewrite Hx in *.
        rewrite Z_div_mult by lia.
        apply Z.gcd_greatest;
          try apply (Gauss q c x);
          try apply (rel_prime_div b c q);
          try rewrite Z.mul_comm;
          trivial.
    Qed.

    Lemma gcd_div_rel_prime_r (a b c : Z)
          (Hc : 0 < c)
          (Hrel : rel_prime a c)
          (Hdiv : (c | b)) :
      Z.gcd a (b / c) = Z.gcd a b.
    Proof.
      rewrite (Z.gcd_comm a (b/c)).
      rewrite (Z.gcd_comm a b).
      apply gcd_div_rel_prime_l; trivial.
    Qed.

    (** Some easy lemmas bridging [Z.odd] with [Z.modulo], which
        [Z.div_mod_to_quot_rem] can handle. *)
    Lemma odd_mod_2 : forall z : Z,
        Z.odd z = true <-> z mod 2 = 1.
    Proof.
      intros z; split; intros H.
      - rewrite Zmod_odd; rewrite H; reflexivity.
      - rewrite Zmod_odd in H;
          destruct (Z.odd z); try trivial; lia.
    Qed.
    Lemma even_mod_2 : forall z : Z,
        Z.odd z = false <-> z mod 2 = 0.
    Proof.
      intros z; split; intros H.
      - rewrite Zmod_odd; rewrite H; reflexivity.
      - rewrite Zmod_odd in H;
          destruct (Z.odd z); try trivial; lia.
    Qed.

    Ltac fail_if_mod t m := match t with
                            | _ mod m => fail 1
                            | _ => idtac
                            end.

    Ltac push_mod_down_in t m :=
      match t with
      | context[(?x - ?y) mod m] =>
        first [fail_if_mod x m; rewrite (Z.sub_mod_l x y m) in * |
               fail_if_mod y m; rewrite (Z.sub_mod_r x y m) in *]
      | context[(?x + ?y) mod m] =>
        first [fail_if_mod x m; rewrite (Z.add_mod_l x y m) in * |
               fail_if_mod y m; rewrite (Z.add_mod_r x y m) in *]
      | context[(?x * ?y) mod m] =>
        first [fail_if_mod x m; rewrite (Z.mul_mod_l x y m) in * |
               fail_if_mod y m; rewrite (Z.mul_mod_r x y m) in *]
      end.

    Ltac brute_force_mod_2 :=
      solve [
          (* The easy cases are solved immediately. *)
          auto |
          (* Otherwise, brute force all possible even/odd assignments. Rewrite
             all hypotheses, variables, and goals as equations mod 2. *)
          repeat match goal with
                 | H : @eq Z ?a ?b |- _ =>
                   let H' := fresh in
                   fail_if_mod a 2;
                   fail_if_mod b 2;
                   assert (H' : a mod 2 = b mod 2) by (rewrite H; reflexivity);
                   clear H
                 | _ : ?H |- _ => push_mod_down_in H 2
                 | [ |- ?G ] => push_mod_down_in G 2
                 end;
          (* Apply any existing hypotheses. *)
          repeat match goal with
                 | z : Z |- _ =>
                   match goal with
                   | H : z mod 2 = _ |- _ =>
                     rewrite H in *
                   end
                 end;
          (* For each [Z], check both possible parities. *)
          repeat match goal with
                 (* Try to solve it right now. *)
                 | H : false = true \/ false = true |- _ =>
                   (* [lia] doesn't figure this one out. *)
                   destruct H as [H' | H']; inversion H'
                 | _ => progress cbn in *
                 | _ => lia
                 (* Pick a variable to branch on. *)
                 | z : Z |- _ =>
                   match z with
                   | nbits => fail 1 | abits => fail 1
                   | _ =>
                     match goal with
                     | H : z mod 2 = _ |- _ => fail 2
                     | _ =>
                       let Hz := fresh in
                       destruct (Z.odd z) eqn:Hz;
                       [ apply odd_mod_2 in Hz | apply even_mod_2 in Hz];
                       try rewrite Hz in *
                     end
                   end
                 end
        ].

    Lemma even_step_invariant
          (s : state)
          (H : invariant s) :
      invariant (even_step s).
    Proof.
      destruct_state s.
      unfold even_step, invariant in *.
      simplify_words.

      destruct_odd_u_v u v;
        [ (* The odd/odd case is a no-op. *)
          rewrite !andb_false_r; cbn; rewrite Hu; rewrite Hv;
          apply H
        | destruct (Z.odd C) eqn:HC;
          destruct (Z.odd D) eqn:HD
        | destruct (Z.odd A) eqn:HA;
          destruct (Z.odd B) eqn:HB ];
        try rewrite !andb_false_r;
        try rewrite !andb_true_r;
        cbn;

        destruct_head'_and;

        repeat match goal with
               | _ => rewrite Zplus_mod_idemp_l
               | _ => rewrite if_mod_distr
               | _ => rewrite add_carry_div2
               end;

        repeat split;
        (* Keep only the relevant half of the problem in the context. *)
        match goal with
        | [ |- context[u]] => idtac
        | [ |- context[A]] => idtac
        | [ |- context[B]] => idtac
        | _ => clear dependent u; clear dependent A; clear dependent B
        end;
        match goal with
        | [ |- context[v]] => idtac
        | [ |- context[C]] => idtac
        | [ |- context[D]] => idtac
        | _ => clear dependent v; clear dependent C; clear dependent D
        end;

        repeat match goal with
               | [ |- _ /\ _ ] => split
               | _ => rewrite Z.mod_small
               | _ => apply Z.div_pos
               | _ => apply Z.div_str_pos
               | _ => apply Z.div_le_upper_bound
               | _ => apply Z.div_lt_upper_bound
               | _ => apply pos_even_le
               | [ |- context[?a / 2 * ?b]] => rewrite (Z.mul_comm (a/2) b)
               | _ => rewrite <- Z.divide_div_mul_exact
               | _ => progress auto
               | H : Z.odd _ = true |- _ => apply odd_mod_2 in H
               | H : Z.odd _ = false |- _ => apply even_mod_2 in H
               | [ |- (2 | _) ] =>
                 rewrite <- Z.mod_divide by lia; brute_force_mod_2
               | [ |- ~ (2 | _) ] =>
                 let H := fresh in
                 rewrite <- Z.mod_divide by lia;
                   intros H; brute_force_mod_2
               | _ => rewrite gcd_div_rel_prime_l
               | _ => rewrite gcd_div_rel_prime_r
               | [ |- rel_prime _ 2 ] => apply rel_prime_sym
               | [ |- rel_prime 2 _ ] => apply prime_rel_prime
               | _ => apply prime_2
               | _ => progress Z.div_mod_to_quot_rem
               | _ => lia
               end.
    Qed.

    Lemma step_invariant
          (s : state)
          (H : invariant s) :
      invariant (step s).
    Proof.
      rewrite <- step_even_odd.
      apply even_step_invariant.
      apply odd_step_invariant.
      trivial.
    Qed.

    (** Next, we show that [step] causes [u * v] to decrease by two each step.
        That means that, after enough steps, the product must be zero. *)

    Definition u_v_prod (s : state) : Z :=
      match s with
      | (_, Word u, Word v) => u * v
      end.

    Lemma odd_step_non_increasing (s : state) (H : invariant s) :
      u_v_prod (odd_step s) <= u_v_prod s.
    Proof.
      destruct_state s.
      unfold odd_step, u_v_prod, invariant in *.
      simplify_words.

      destruct_odd_u_v u v;
        destruct (v <? u) eqn:Huv;
        repeat bool_to_prop_once;
        cbn;
        repeat match goal with
               | _ => rewrite Z.mod_small
               | _ => nia
               end.
    Qed.

    Definition u_or_v_even (s : state) : Prop :=
      match s with
      | (_, Word u, Word v) =>
        Z.odd u = false \/ Z.odd v = false
      end.

    Lemma odd_step_u_or_v_even (s : state) (H : invariant s) :
      u_or_v_even (odd_step s).
    Proof.
      destruct_state s.
      unfold odd_step, invariant, u_or_v_even in *.
      simplify_words.

      (* Throw away unnecessary bits. *)
      destruct_head'_and.
      clear dependent a; clear dependent n; clear dependent A;
        clear dependent B; clear dependent C; clear dependent D.

      destruct_odd_u_v u v;
        destruct (v <? u) eqn:Huv;
        repeat bool_to_prop_once;
        cbn;
        try rewrite !even_mod_2 in *;
        try rewrite !odd_mod_2 in *;
        try rewrite <- !Zmod_div_mod by (try apply Z.pow_pos_nonneg;
                                         try apply Zpow_facts.Zpower_divide;
                                         lia);
        (* Pick the subtraction, if there is one. Otherwise [auto] will figure
           it out. *)
        try match goal with
        | [ |- (_ - _) mod 2 = 0 \/ _ ] => left
        | [ |- _ \/ (_ - _) mod 2 = 0 ] => right
        end;
        brute_force_mod_2.
    Qed.

    Lemma even_step_shrinks
          (s : state)
          (H : invariant s)
          (Heven : u_or_v_even s) :
      u_v_prod (even_step s) <= (u_v_prod s) / 2.
    Proof.
      destruct_state s.
      unfold even_step, u_v_prod, invariant, u_or_v_even in *.
      simplify_words.

      destruct_odd_u_v u v;
      [ (* [u] and [v] cannot both be even by [Heven]. *)
        destruct_head'_and;
        destruct_head'_or;
        match goal with
        | H : false = true |- _ => inversion H
        | H : true = false |- _ => inversion H
        end | | ];
      cbn;
      repeat match goal with
             | H : Z.odd _ = true |- _ => apply odd_mod_2 in H
             | H : Z.odd _ = false |- _ => apply even_mod_2 in H
             | _ => split
             | _ => rewrite Z.mod_small
             | _ => Z.div_mod_to_quot_rem; nia
             end.
    Qed.

    Lemma step_shrinks (s : state) (H : invariant s) :
      u_v_prod (step s) <= (u_v_prod s) / 2.
    Proof.
      repeat first [ rewrite <- step_even_odd
                   | rewrite even_step_shrinks
                   | apply Z.div_le_mono
                   | apply odd_step_non_increasing
                   | apply odd_step_invariant
                   | apply odd_step_u_or_v_even
                   | solve [trivial | lia]].
    Qed.

    (** Help the main proof learn that [step] leaves [a] and [n] unchanged. *)
    Definition state_get_a (s : state) :=
      match s with
      | (Word a, _, _, _, _, _, _, _) => a
      end.
    Definition state_get_n (s : state) :=
      match s with
      | (_, Word n, _, _, _, _, _, _) => n
      end.

    Lemma step_preserve_a_n (s : state) :
      state_get_a (step s) = state_get_a s /\
      state_get_n (step s) = state_get_n s.
    Proof.
      destruct_state s.
      unfold step, state_get_a, state_get_n.
      simplify_words.
      auto.
    Qed.

    Lemma gcd_even_even (a b : Z)
          (Ha : Z.odd a = false)
          (Hb : Z.odd b = false) :
      Z.gcd a b <> 1.
    Proof.
      intros Hgcd.
      rewrite even_mod_2 in Ha.
      rewrite even_mod_2 in Hb.
      rewrite Z.mod_divide in Ha by lia.
      rewrite Z.mod_divide in Hb by lia.
      pose proof (Z.gcd_greatest a b 2 Ha Hb) as H.
      rewrite Hgcd in H.
      apply Z.divide_1_r in H.
      lia.
    Qed.

    (** Finally, our correctness result. If [mod_inverse_consttime] returns
        something, it must be a modular inverse. If it does not, the inverse did
        not exist.

        Note the proof doesn't hold for [a = 0] or [n = 0], which should be
        handled by the caller. *)
    Theorem mod_inverse_consttime_spec
            (a n : Z)
            (Ha : 0 < a < 2^abits)
            (Hn : 0 < n < 2^nbits)
            (Hreduced : a < n) :
      match mod_inverse_consttime (to_word a) (to_word n) with
      | Some (Word ainv) =>
        0 <= ainv < n /\
        (ainv * a) mod n = 1
      | None => Z.gcd a n <> 1
      end.
    Proof.
      (* Tidy up the loop. *)
      unfold mod_inverse_consttime.
      simplify_words.
      rewrite !Z.mod_small by
          (repeat first [split | apply Z.pow_gt_1 | lia]).

      (* Discard the both even case. *)
      destruct (negb (Z.odd a) && negb (Z.odd n)) eqn:both_even;
        repeat bool_to_prop_once;
        [ destruct_head'_and; apply gcd_even_even; trivial | ].

      lazymatch goal with |- context [while ?t ?b ?l ?i] => pattern (while t b l i) end.
      eapply (while.by_invariant
                (fun '(s, i) =>
                   invariant s /\
                   u_v_prod s <= a * n / 2^i /\
                   0 <= i /\
                   state_get_a s = a /\
                   state_get_n s = n)
                (fun '(_, i) => Z.to_nat (abits + nbits - i))).
      { (* Invariant holds in the beginning. *)
        unfold invariant, u_v_prod.
        repeat split; try rewrite Z.div_1_r; try solve [trivial | lia]. }
      { intros [s i].
        intros [Hinv [Hprod [Hi [Hpreserve_a Hpreserve_n]]]].
        destruct (i <? abits + nbits) eqn:Hbranch; repeat bool_to_prop_once.
        { (* If the loop continued, the invariant is preserved. *)
          destruct_head'_and.
          repeat split.
          - apply step_invariant; trivial.
          - rewrite step_shrinks by trivial.
            rewrite Z.pow_add_r by lia.
            rewrite Z.pow_1_r.
            rewrite <- Z.div_div by (try apply Z.pow_nonzero; lia).
            apply Z.div_le_mono; lia.
          - lia.
          - rewrite <- Hpreserve_a; apply step_preserve_a_n.
          - rewrite <- Hpreserve_n; apply step_preserve_a_n. }
        { (* If the loop exited, the invariant implies the postcondition. *)
          destruct s as [[[[[[[[a'] [n']] [A]] [B]] [C]] [D]] [u]] [v]].
          unfold invariant, state_get_a, state_get_n, u_v_prod in *.
          rewrite Hpreserve_a in *; rewrite Hpreserve_n in *.
          clear dependent a'; clear dependent n'.

          destruct_head'_and.
          clear dependent C; clear dependent D.

          (* First, show [u = Z.gcd a n], by way of [v = 0]. *)
          assert (Hzero : u * v = 0).
          {
            assert (a * n / 2^i = 0).
            { apply (Z.pow_le_mono_r 2) in Hbranch; try lia.
              rewrite Z.pow_add_r in Hbranch by lia.
              apply Z.div_small; nia. }
            nia. }
          apply Z.mul_eq_0 in Hzero.
          destruct Hzero as [Hu | Hv]; try lia.
          rewrite Hv in *; clear dependent v.
          rewrite Z.gcd_0_r_nonneg in * by lia.
          match goal with
          | H : u = Z.gcd a n |- _ => rewrite H in *; clear dependent u
          end.

          destruct (Z.gcd a n =? 1) eqn:Hgcd; repeat bool_to_prop_once.
          { (* There is a mod inverse *)
            rewrite Hgcd in *.
            split; try lia.
            rewrite <- (Z.mod_add_full (A*a) (-B) n).
            rewrite <- (Z.mod_1_l n) by lia.
            f_equal; nia. }
          { (* No mod inverse *) trivial. } } }
      { (* fuel <= measure *)
        apply Z2Nat.inj_le; lia. }
      { (* measure decreases *)
        intros [_ i].
        destruct (i <? abits + nbits) eqn:H; repeat bool_to_prop_once.
        - apply Z2Nat.inj_lt; lia.
        - trivial. }
    Qed.

  End BinaryExtendedGCD.
End BinaryExtendedGCD.
