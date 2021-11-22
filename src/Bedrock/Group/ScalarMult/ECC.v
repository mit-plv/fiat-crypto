Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Loops.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Specs.ScalarField.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Algebra.Hierarchy.

Local Open Scope Z_scope.

Section S.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {scalar_field_parameters : ScalarFieldParameters}.
  Context {scalar_field_parameters_ok : ScalarFieldParameters_ok}.
  Context {field_representaton : FieldRepresentation}
  {scalar_representation : ScalarRepresentation}.
  Context {field_representation_ok : FieldRepresentation_ok}.
  Hint Resolve @relax_bounds : compiler.

  Section Gallina.

    Fixpoint exp_by_squaring (x : F M_pos) (n : positive) : F M_pos :=
      match n with
      | xH => x
      | xO xH => F.pow x 2
      | xI xH => let/n res := F.pow x 2 in F.mul x res
      | xO n' => let/n res := exp_by_squaring x n' in F.pow res 2
      | xI n' => let/n res := exp_by_squaring x n' in
                 let/n res := F.pow res 2 in
                 F.mul x res
      end.

    Ltac rewrite_Z :=
    lazymatch goal with
    | [|- ?a = ?b] =>
      let H := fresh "H" in
      let m := open_constr:(_) in
      enough (F.of_Z m (F.to_Z a) = F.of_Z m (F.to_Z b)) as H;
        [rewrite !F.of_Z_to_Z in H; assumption| f_equal]
        end.

    Ltac F_math :=
      rewrite !F.to_Z_mul.
    

    Ltac F_lia_orig :=
    try rewrite_Z;
    try F_math;
    try rewrite <- !PullPush.Z.mul_mod_l;
    try rewrite <- !PullPush.Z.mul_mod_r;
    try f_equal;
    try lia.

    Lemma solve_F_equality_via_Z lhs' rhs' (lhs rhs : F M_pos) 
    : F.to_Z lhs = lhs' mod Z.pos M_pos ->
      F.to_Z rhs = rhs' mod Z.pos M_pos ->
      lhs' = rhs' ->
      lhs = rhs.
  Proof.
    intros.
    rewrite <- (F.of_Z_to_Z lhs).
    rewrite <- (F.of_Z_to_Z rhs).
    intuition congruence.
  Qed.

  
  (*TODO: add remaining homomorphisms *)
  
  Lemma F_mul_to_Z a a' b b'
    : F.to_Z a = a' mod Z.pos M_pos ->
      F.to_Z b = b' mod Z.pos M_pos ->
      @F.to_Z M_pos (a * b) = (a' * b') mod Z.pos M_pos.
  Proof.
    intros H H0.
    rewrite F.to_Z_mul.
    rewrite H, H0.
    rewrite <- PullPush.Z.mul_mod_l.
    rewrite <- PullPush.Z.mul_mod_r.
    congruence.
  Qed.
  
  Lemma F_add_to_Z a a' b b'
    : F.to_Z a = a' mod Z.pos M_pos ->
      F.to_Z b = b' mod Z.pos M_pos ->
      @F.to_Z M_pos (a + b) = (a' + b') mod Z.pos M_pos.
  Proof.
    intros H H0.
    rewrite F.to_Z_add.
    rewrite H, H0.
    rewrite <- PullPush.Z.add_mod_l.
    rewrite <- PullPush.Z.add_mod_r.
    congruence.
  Qed.

  Lemma F_var_to_Z (x : F M_pos) : F.to_Z x = proj1_sig x mod Z.pos M_pos.
  Proof.
    destruct x; simpl; assumption.
  Qed.
  
  Lemma F_one_to_Z : @F.to_Z M_pos 1 = 1 mod Z.pos M_pos.
  Proof.
    reflexivity.
  Qed.

  
  Lemma F_const_to_Z c : F.to_Z (F.of_Z M_pos c) = c mod Z.pos M_pos.
  Proof.
    reflexivity.
  Qed.


Ltac F_convert_to_Z :=
  solve [repeat
           let e := lazymatch goal with |- F.to_Z ?x = _ => x end in
           tryif is_var e
           then simple eapply F_var_to_Z
           else first [ simple eapply F_mul_to_Z
                      | simple eapply F_add_to_Z
                      | simple eapply F_one_to_Z
                      | simple eapply F_const_to_Z]].

(*TODO: doesn't prepare hypotheses*)
Ltac F_zify :=
  intros;
  lazymatch goal with
  | [|- ?lhs = ?rhs] =>
    simple eapply solve_F_equality_via_Z;
    [F_convert_to_Z | F_convert_to_Z | ]
  end.

Ltac F_lia := F_zify; lia.


Create HintDb F_pow.
Hint Rewrite @F.pow_2_r : F_pow.
Hint Rewrite @F.pow_add_r : F_pow.
Hint Rewrite @F.pow_mul_l : F_pow.
Hint Rewrite <- @F.pow_pow_l : F_pow.
Hint Rewrite @F.pow_1_r : F_pow.
Hint Rewrite @F.pow_3_r : F_pow.

Lemma Pos2N_pos_xI n :
  N.pos n~1 = (2 * N.pos n + 1)%N.
Proof.
  lia.
Qed.

Lemma Pos2N_pos_xO n :
  N.pos n~0 = (2 * N.pos n)%N.
Proof.
  lia.
Qed.

Lemma F_mul_assoc (x1 x2 x3 : F M_pos):
  (x1 * x2 * x3)%F = (x1 * (x2 * x3))%F.
Proof.
  F_lia.
Qed.

    Lemma exp_by_squaring_correct :
     forall n x, exp_by_squaring x n = F.pow x (Npos n).
    Proof.
      induction n; intros; cbn [exp_by_squaring]; unfold nlet;
        rewrite (Pos2N_pos_xI n) || rewrite (Pos2N_pos_xO n) || idtac.
      all: try rewrite IHn.
      all: try destruct n eqn : H'; autorewrite with F_pow.
      all: F_lia_orig. (* FIXME: ask Dustin why F_lia doesn't work *)
    Qed.

    Lemma letn_equal :
      forall A B (val : A) (body_l body_r : A -> B) (var : string),
        (let x := val in body_l x = body_r x)
        -> (let/n x as var := val in body_l x) = (let/n y as var := val in body_r y).
    Proof.
      intros. assumption.
    Qed.

    Lemma letn_nested :
      forall A B C (a : C) (val1 : A) (body1 : A -> B) (body2 : B -> C) (var var' : string),
        a = (let/n x as var' := val1 in let/n y as var := body1 x in body2 y)
        -> a = (let/n y as var := let/n x as var' := val1 in body1 x in body2 y).
    Proof.
      intros. assumption.
    Qed.

    Lemma letn_paren_equal :
      forall A B (a : A) (val : A) (body_r : A -> B) (var : string) left,
        left = (let/n y as var := val in (a, body_r y))
        -> left = (a, let/n y as var := val in body_r y).
    Proof.
      intros.
      rewrite H. reflexivity.
    Qed.

    Ltac tac :=
      lazymatch goal with
      | [ |- let _ := _ in _ = _ ] =>
        intros
      | [ |- _ = let/n _ as _ := (let/n _ as _ := _ in _) in _] =>
        eapply letn_nested
      | [ |- _ = let/n _ as _ := _ in _] =>
        eapply letn_equal with (body_l := fun _ => _)
      | [ |- _ = (_, let/n _ as _ := _ in _)] =>
        eapply letn_paren_equal
      end.

    Definition exp_result x_ptr q_ptr xq_val : list word -> _ -> Prop :=
      fun _ => (FElem (Some tight_bounds) x_ptr (fst xq_val) * FElem (Some tight_bounds) q_ptr (snd xq_val))%sep.

    Fixpoint run_length_encoding (n : positive) : list (bool * nat) :=
      match n with
      | xH => [(true, 0)]
      | xO n' =>
        match (run_length_encoding n') with
        | (false, k) :: t => (false, k + 1) :: t
        | t => (false, 0) :: t
        end
      | xI n' =>
        match (run_length_encoding n') with
        | (true, k) :: t => (true, k + 1) :: t
        | t => (true, 0) :: t
        end
      end%nat.

    Fixpoint loop {A} (x : A) (k : nat) (f : A -> A) : A :=
      match k with
      | 0%nat => x
      | S k' =>
        let/n res := loop x k' f in
        let/n res := f res in
        res
      end.

    Definition exp_square_and_multiply (x : F M_pos) (x' : F M_pos) :=
      let/n res := F.pow x' 2 in
      F.mul res x.

    Definition exp_square (x' : F M_pos) :=
      F.pow x' 2.

    (* Computes x ^ (decoded n). *)
    Fixpoint exp_from_encoding_simple (x : F M_pos) (n : list (bool * nat)) : F M_pos :=
      match n with
      | [] =>
        1
      (* can add more cases for small k to be faster *)
      | (true, 0%nat) :: t =>
        let/n res := exp_from_encoding_simple x t in
        let/n res := F.pow res 2 in
        let/n res := F.mul x res in
        res
      | (true, k) :: t =>
        let/n res := exp_from_encoding_simple x t in
        let/n res := loop res (S k) (exp_square_and_multiply x) in
        res
      | (false, 0%nat) :: t =>
        let/n res := exp_from_encoding_simple x t in
        let/n res := F.pow res 2 in
        res
      | (false, k) :: t =>
        let/n res := exp_from_encoding_simple x t in
        let/n res := loop res (S k) (exp_square) in
        res
      end.

    Fixpoint exp_from_encoding (x : F M_pos) (n : list (bool * nat)) : F M_pos :=
      match n with
      | [] =>
        1
      | [(true, 0%nat)] =>
        x
      | [(true, k)] =>
        let/n res := loop 1%F (S k) (exp_square_and_multiply x) in
        res
      | [(false, 0%nat)] =>
        1
      | [(false, k)] =>
        let/n res := loop 1%F (S k) (exp_square) in
        res
      | (true, 0%nat) :: t =>
        let/n res := exp_from_encoding x t in
        let/n res := F.pow res 2 in
        let/n res := F.mul x res in
        res
      | (true, k) :: t =>
        let/n res := exp_from_encoding x t in
        let/n res := loop res (S k) (exp_square_and_multiply x) in
        res
      | (false, 0%nat) :: t =>
        let/n res := exp_from_encoding x t in
        let/n res := F.pow res 2 in
        res
      | (false, k) :: t =>
        let/n res := exp_from_encoding x t in
        let/n res := loop res (S k) (exp_square) in
        res
      end.
    

    Definition exp_by_squaring_encoded_simple (x : F M_pos) (n : positive) : F M_pos :=
      exp_from_encoding_simple x (run_length_encoding n).

    Definition exp_by_squaring_encoded (x : F M_pos) (n : positive) : F M_pos :=
      exp_from_encoding x (run_length_encoding n).
    
    Lemma run_length_encoding_nonempty:
      forall n, run_length_encoding n <> [].
    Proof.
      destruct n eqn : H'; simpl.
      + destruct (run_length_encoding p).
        { inversion 1. }
        destruct p0; destruct b; inversion 1.
      + destruct (run_length_encoding p).
        { inversion 1. }
        destruct p0; destruct b; inversion 1.
      + inversion 1.
    Qed.

   Lemma f_one : forall x : F M_pos,
        (x * 1)%F = x.
   Proof.
     intros.
     F_lia.
   Qed.

   Lemma one_f : forall x : F M_pos,
       (1 * x)%F = x.
   Proof.
     intros.
     F_lia.
   Qed.

    Lemma exp_by_squaring_encoded_simple_correct : 
      M <> 0 -> forall n x, exp_by_squaring_encoded_simple x n = F.pow x (N.pos n).
    Proof.
      intros. rewrite <- exp_by_squaring_correct; eauto.
      unfold exp_by_squaring_encoded_simple; induction n; simpl.
      - cbn -[loop].
        destruct (run_length_encoding n) eqn : Heq.
        + apply run_length_encoding_nonempty in Heq.
          inversion Heq.
        + destruct p. destruct b.
          { rewrite <- IHn.
          cbn. replace (n0 + 1)%nat with (S n0) by lia.
          unfold nlet; destruct n0.
            { cbn.
              destruct n eqn : H'; unfold nlet.
              { unfold exp_square_and_multiply.
                unfold nlet.
                F_lia_orig.
                rewrite <- Z.mul_comm.
                f_equal.
                F_lia_orig.
                f_equal.
                F_lia_orig.
              }
              { unfold exp_square_and_multiply.
                unfold nlet.
                F_lia_orig.
                rewrite <- Z.mul_comm.
                f_equal.
                F_lia_orig.
                f_equal.
                F_lia_orig.
              }
              {
              unfold run_length_encoding in Heq.
              inversion Heq.
              repeat eapply mod_equal.
              unfold exp_square_and_multiply; unfold nlet.
              unfold exp_from_encoding_simple.
              rewrite_Z.
              F_math.
              rewrite <- Z.mul_comm.
              replace (F.to_Z ((1 ^ 2 * x) ^ 2)) with (F.to_Z (x ^ 2)).
              reflexivity.
              f_equal.
              repeat rewrite F.pow_2_r.
              replace (1 * 1 * x)%F with x.
              reflexivity.
              rewrite f_one.
              rewrite one_f.
              reflexivity.
              }
            }
            cbn.
            destruct n eqn : H'; unfold nlet.
            { repeat eapply mod_equal.
              Z.push_pull_mod.
              unfold exp_square_and_multiply; unfold nlet.
              F_lia_orig.
            }
            { repeat eapply mod_equal.
              Z.push_pull_mod.
              unfold exp_square_and_multiply; unfold nlet.
              F_lia_orig.
            }
              {
              unfold run_length_encoding in Heq.
              inversion Heq.
              }
          }
          rewrite <- IHn.
          cbn.
          unfold nlet.
          destruct n0; destruct n eqn : H'; try reflexivity.
          { unfold run_length_encoding in Heq.
            Z.push_pull_mod.
            inversion Heq.
          }
          unfold run_length_encoding in Heq.
          inversion Heq.
      - rewrite <- IHn.
        cbn. 
        destruct n eqn : H'.
        { destruct (run_length_encoding p~1) as [|[[|] n0] t]; try reflexivity.
          simpl.
          replace (n0 + 1)%nat with (S n0) by lia.
          unfold nlet.
          cbn.
          unfold exp_square.
          destruct n0.
          { unfold loop.
            F_lia_orig.
          }
          F_lia_orig.
        }
        { destruct (run_length_encoding p~0) as [|[[|] n0] t]; try reflexivity.
          simpl.
          replace (n0 + 1)% nat with (S n0) by lia.
          unfold nlet.
          cbn.
          unfold exp_square.
          destruct n0.
          { unfold loop.
            F_lia_orig.
          }
          F_lia_orig.
        }
        unfold run_length_encoding.
        unfold exp_from_encoding_simple.
        unfold nlet.
        rewrite_Z.
        repeat rewrite F.pow_2_r.
        f_equal.
        rewrite associative.
        repeat rewrite one_f.
        repeat rewrite f_one.
        reflexivity.
      - unfold nlet.
        rewrite_Z.
        rewrite F.pow_2_r.
        f_equal.
        repeat rewrite f_one.
        reflexivity.
    Qed.

    
    Lemma exp_by_squaring_encoded_correct :
      M <> 0 -> forall n x, exp_by_squaring_encoded x n = F.pow x (N.pos n).
    Proof.
      intros. rewrite <- exp_by_squaring_encoded_simple_correct; eauto.
      unfold exp_by_squaring_encoded. unfold exp_by_squaring_encoded_simple.
      induction (run_length_encoding n).
      - cbn.
        reflexivity.
      - destruct a.
        destruct b; unfold exp_from_encoding; unfold exp_from_encoding_simple; fold exp_from_encoding; fold exp_from_encoding_simple; destruct n0; destruct l; unfold nlet; eauto.
        + unfold exp_from_encoding_simple.
          rewrite_Z.
          rewrite F.pow_2_r.
          f_equal.
          repeat rewrite f_one.
          reflexivity.
        + rewrite IHl. eauto.
        + rewrite IHl. eauto.
        + unfold exp_from_encoding_simple. rewrite_Z. f_equal. rewrite F.pow_2_r.
          rewrite f_one.
          reflexivity.
        + rewrite IHl.
          eauto.
        + rewrite IHl.
          eauto.
    Qed.

    Lemma loop_equals':
      forall {A} f (x : A) k,
        (ExitToken.new, loop x k f) =
      (ranged_for' 0 (Z.of_nat k)
       (fun (acc : A) (tok : ExitToken.t) (idx : Z)  _ =>
          (tok, f acc)) x).
    Proof.
      induction k.
      - simpl.
        unfold ranged_for'.
        rewrite ranged_for_break_exit; try reflexivity.
        lia.
      - cbn -[Z.of_nat].
        replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
        erewrite ranged_for'_unfold_r_nstop; try lia; try easy.
        all: rewrite <- IHk; reflexivity.
    Qed.
        
    Lemma loop_equals :
      forall {A} f (x : A) k,
        Z.of_nat k < 2 ^ width ->
        loop x k f =
        let/n from := 0 in
        let/n to := word.of_Z (Z.of_nat k) in
        ranged_for_u (word.of_Z from) to
                     (fun acc t _ _ =>
                        let/n out := f acc in (t, out)) x.
    Proof.
      intros.
      unfold nlet.
      unfold ranged_for_u in *.
      unfold ranged_for_w in *.
      unfold ranged_for in *.
      unfold w_body_tok.
      pose proof Nat2Z.is_nonneg k.
      repeat rewrite word.unsigned_of_Z_0.
      repeat rewrite word.unsigned_of_Z.
      repeat rewrite word.wrap_small by lia.
      rewrite <- loop_equals'.
      reflexivity.
    Qed.

   Hint Unfold exp_square : compiler_cleanup.

  End Gallina.


  Section Bedrock.

    Create HintDb lowering.

    Ltac lower_step :=
      lazymatch goal with
      | [ |- forall _, _ ] =>
        intros
      | [ |- let _ := _ in _ = _ ] =>
        intros
      | [ |- _ = let/n _ as _ := (let/n _ as _ := _ in _) in _] =>
        eapply letn_nested
      | [ |- _ = let/n _ as _ := _ in _] =>
        eapply letn_equal with (body_l := fun _ => _)
      | [ |- _ = (_, let/n _ as _ := _ in _)] =>
        eapply letn_paren_equal
      end.

    Ltac compile_try_copy_pointer :=
     lazymatch goal with
     | [ H : ?pred ?m |- WeakestPrecondition.cmd _ _ _ ?m ?l (_ ?term) ] =>
       match term with
       | nlet_eq [?var_] ?v _ =>
         match l with
         | context [map.put _ var_ ?ptr] =>
           match pred with
           | context [?Data_ ptr v] =>
             simple eapply compile_copy_pointer with (var := var_) (x_ptr0 := ptr) (Data := Data_)
           end
         end
       end
     end.


    Ltac compile_custom ::=
      progress (try (try simple eapply compile_dlet_as_nlet_eq;
                     try simple eapply compile_nlet_as_nlet_eq;
                     first [ simple eapply compile_square
                           | simple eapply compile_mul
                           | compile_try_copy_pointer]));
      intros.

    Hint Unfold exp_by_squaring : lowering.

    Ltac lower_setup :=
      autounfold with lowering;
      lazymatch goal with
        | [ H := _ |- _ ] =>
          subst H
      end.

    Ltac lower :=
      lower_setup;
      repeat lower_step;
      reflexivity.

    Derive rewritten SuchThat
           (forall x, rewritten x = (x, let/n res := exp_by_squaring x 6 in res))
           As rewrite.
    Proof.
      lower.
    Qed.
    
    Print rewritten.
    About rewritten.

    Definition exp_6 x := let/n res := exp_by_squaring x 6 in (x, res).
    About exp_6.

    Instance spec_of_exp_6 : spec_of "exp_6" :=
    fnspec! "exp_6"
          (x_ptr sq_ptr : word)
          / (x sq : F M_pos) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) x_ptr x
         * FElem (Some tight_bounds) sq_ptr sq * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ let (x, ret) := exp_6 x in
           (FElem (Some tight_bounds) x_ptr x
            * FElem (Some tight_bounds) sq_ptr ret  * R)%sep mem'}.

    Local Ltac ecancel_assumption ::= ecancel_assumption_impl.


    
    Derive exp_6_body SuchThat
         (defn! "exp_6" ("x", "res") { exp_6_body },
          implements exp_6 using [square; mul])
         As exp_6_body_correct.

    compile_setup.
    evar (rewritten : F M_pos -> F M_pos * F M_pos).


    (* lazymatch goal with
    | [ |- <{ Trace := _; Memory := _; Locals := _; Functions := _ }> _ <{ _ ?f }> ]
      => idtac f; assert (forall x, rewritten x = f)
    end. 
     lower. *)
    

    assert (forall x0 : F M_pos,
       rewritten x0 = (let/n res as "res" := exp_by_squaring x0 6 in
                       (x0, res))).
    lower.

    rewrite <- H3.
    subst rewritten.
    cbv beta.
    repeat compile_step.
    Qed.

    Print exp_6_body.

    Ltac compile_custom ::=
      progress ( try rewrite loop_equals;
                 try (try simple eapply compile_dlet_as_nlet_eq;
                      try simple eapply compile_nlet_as_nlet_eq;
                      first [ simple eapply compile_square
                            | simple eapply compile_mul
                            | compile_try_copy_pointer]));
      intros.

    Hint Unfold exp_by_squaring_encoded : lowering.
    Hint Unfold exp_from_encoding : lowering.
    Hint Unfold exp_by_squaring_encoded_simple : lowering.
    Hint Unfold exp_from_encoding_simple : lowering.
    Hint Unfold run_length_encoding : lowering.
    Hint Unfold exp_square_and_multiply : lowering.
    Hint Unfold loop : lowering.

    Derive rewritten_encoded SuchThat
           (forall x, rewritten_encoded x = (x, let/n res := exp_by_squaring_encoded x 15 in res))
           As rewrite'.
    Proof.
      lower_setup.
      change (0 + 1)%nat with 1%nat.
      repeat lower_step.
      reflexivity.
    Qed.
    
    Print rewritten_encoded.

    Definition exp_15 x := let/n res := exp_by_squaring_encoded x 15 in (x, res).
    About exp_15.

    Instance spec_of_exp_15 : spec_of "exp_15" :=
    fnspec! "exp_15"
          (x_ptr sq_ptr : word)
          / (x sq : F M_pos) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) x_ptr x
         * FElem (Some tight_bounds) sq_ptr sq * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ let (x, ret) := exp_15 x in
           (FElem (Some tight_bounds) x_ptr x
            * FElem (Some tight_bounds) sq_ptr ret  * R)%sep mem'}.

    Derive exp_15_body SuchThat
         (defn! "exp_11" ("x", "res") { exp_11_body },
          implements exp_15 using [square; mul])
         As exp_15_body_correct.

    compile_setup.
    evar (rewritten : F M_pos -> F M_pos * F M_pos).

    assert (forall x0 : F M_pos,
       rewritten x0 = (let/n res as "res" := exp_by_squaring_encoded x0 15 in
                       (x0, res))) as Heq.
    autounfold with lowering.
    change (0 + 1)%nat with 1%nat.
    lower_setup.
    repeat lower_step.
    reflexivity.
    
    rewrite <- Heq.
    subst rewritten.
    cbv beta.

    repeat compile_step.
    
    repeat compile_step.

    eauto.

    Qed.

    (* TODO: investigate squaring 1 *)

    Instance spec_of_exp_11_encoded : spec_of "exp_11_encoded" :=
    fnspec! "exp_11_encoded"
          (x_ptr sq_ptr : word)
          / (x sq : F M_pos) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) x_ptr x
         * FElem (Some tight_bounds) sq_ptr sq * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ let (x, ret) := rewritten_encoded x in
           (FElem (Some tight_bounds) x_ptr x
            * FElem (Some tight_bounds) sq_ptr ret  * R)%sep mem'}.

    
    Derive exp_11_body SuchThat
         (defn! "exp_11" ("x", "res") { exp_11_body },
          implements rewritten_encoded using [square; mul])
         As exp_11_body_correct.
    compile_setup.
    repeat repeat compile_step.

    *)
      

    Print rewrite.

    Derive rewritten' SuchThat
           (forall x, rewritten' x = (x, let/n res := exp_by_squaring_encoded x 11 in res))
           As rewrite_encoded_11.
    Proof.
      cbv beta iota delta [exp_by_squaring_encoded].
      subst rewritten'.
      intros.
      repeat tac.
      reflexivity.
    Qed.

    Print rewritten'.
    

  End Bedrock.

End S.
