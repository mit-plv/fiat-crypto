From Coq Require Import BinInt String List InitialRing.
From bedrock2 Require Import BasicC64Semantics WeakestPrecondition ProgramLogic NotationsCustomEntry ZnWords.
Import ListNotations ProgramLogic.Coercions SeparationLogic Array Scalars.
Require Import bedrock2Examples.full_sub.
From coqutil Require Import Tactics.Tactics WithBaseName.
Local Open Scope string_scope. Local Open Scope Z_scope.

Local Notation eval := (fold_right (fun (a : word) (s : Z) => a + 2^64*s) 0).
Local Notation array := (array scalar (word.of_Z 8)).

From Coq Require Import ZArith Lia.

Section FunctionalCtz.
    Local Open Scope Z_scope.
    Local Open Scope positive_scope.

    Fixpoint pos_ctz (p : positive) : nat := 
        match p with 
        | q ~ 0 => S (pos_ctz q)
        | _ => 0
        end.
    Close Scope positive_scope.

    Definition lctz (def : Z) (z : Z) : Z := 
        match z with 
        | Zpos z' => pos_ctz z'
        | _ => def
        end.

    (* Lemmas *)

    Lemma lctz_pos_double (def : Z) (z : Z) :
        z > 0 -> lctz def (2 * z) = 1 + lctz def z.
    Proof.
        intros H. destruct z as [ | p | p ]; inversion H.
        rewrite <- Z.double_spec. cbv [Z.double lctz].
        cbn [pos_ctz]. lia.
    Qed.

    Lemma lctz_pos_pow2 (def : Z) (z : Z) : 
        z > 0 -> 2 ^ (lctz def z) > 0.
    Proof.
        intros H. destruct z as [ | p | p]; inversion H.
        cbv [lctz]. lia.
    Qed.

    Lemma lctz_pos_mod (def : Z) (z : Z) : 
        z > 0 -> z mod 2 ^ lctz def z = 0.
    Proof.
        intros H. destruct z as [ | p | p]; inversion H.
        induction p as [p IHp | p IHp | ]; cbv [lctz] in *; cbn [pos_ctz] in *; 
        (* Trivial cases *)
        try (rewrite Z.pow_0_r, Zmod_1_r; trivial).
        rewrite <- Z.div_exact by lia.
        rewrite <- Z.div_exact in IHp by lia.
        fold (Z.double (Z.pos p)). rewrite Z.double_spec.
        replace (2^ S (pos_ctz p)) with (2 * 2^ (pos_ctz p)) by 
            (rewrite Nat2Z.inj_succ, <-Z.add_1_l, Z.pow_add_r; lia).
        rewrite Zdiv_mult_cancel_l; lia.
    Qed.
    
    Lemma lctz_pos_div (def : Z) (z : Z) : 
        z > 0 -> z / 2 ^ lctz def z mod 2 = 1.
    Proof.
        intros H. destruct z as [ | p | p]; inversion H.
        induction p as [p IHp | p IHp | ]; 
        cbv [lctz] in *; cbn [pos_ctz] in *.
        { 
            rewrite Z.pow_0_r, Z.div_1_r, Pos2Z.inj_xI, Z.add_comm, Z.mul_comm, Z_mod_plus_full. 
            trivial.
        }
        {   
            rewrite Pos2Z.inj_xO. 
            replace (2^ S (pos_ctz p)) with (2 * 2^ (pos_ctz p)) by 
                (rewrite Nat2Z.inj_succ, <-Z.add_1_l, Z.pow_add_r; lia).
            rewrite Zdiv_mult_cancel_l; lia. 
        }
        {   rewrite Z.pow_0_r, Z.div_1_r. trivial. }
    Qed.

    Lemma lctz_pos_spec (def : Z) (z : Z) : 
        z > 0 -> 
            exists k , k mod 2 = 1%Z /\ z = k * 2^(lctz def z).
    Proof.
        intros H. exists (z / (2^lctz def z)); split.
        { eapply lctz_pos_div; trivial. }
        {   rewrite Z.mul_comm.
            eapply Z_div_exact_2; try eapply lctz_pos_pow2; eauto.
            eapply lctz_pos_mod; eauto. }
    Qed.
End FunctionalCtz.


(** * Specification *)


#[export] Instance spec_of_br_ctz : spec_of "br_ctz" := 
    fnspec! "br_ctz" (value : word) ~> count,
    {
        requires t m := value <> word.of_Z 0;
        ensures T M := T = t /\ M = m /\ count = word.of_Z (lctz 64 value)
    }.

(** * Implementation *)
Definition br_ctz := func! (value) ~> count {
    tmp = value;
    count = $0;

    while tmp {
        count = count + $1;
        tmp = tmp << $1
    };
    count = count - $ 64
}.

(** * Specification Proof *)
Lemma br_ctz_ok : program_logic_goal_for_function! br_ctz.
Proof.
    repeat straightline.
    refine ((Loops.tailrec
    (* types of ghost variables*) 
                                  
    (HList.polymorphic_list.nil)
    (* program variables *) (["value";"count";"tmp"] : list String.string))
    (fun v t m value_ count tmp => PrimitivePair.pair.mk (* precondition *)
      (lctz 64 tmp = lctz 64 value + count)
    (fun            T M VALUE COUNT TMP => (* postcondition *)
      lctz 64 TMP = lctz 64 value))
    (fun n m => m < n <= total_bits + w) (* well_founded relation *)
    _ _ _ _ _ ); 
    Loops.loop_simpl.

