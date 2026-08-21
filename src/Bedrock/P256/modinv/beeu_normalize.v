From Coq Require Import BinInt String List InitialRing.
From bedrock2 Require Import BasicC64Semantics WeakestPrecondition ProgramLogic NotationsCustomEntry ZnWords ArrayCasts.
Import ListNotations ProgramLogic.Coercions SeparationLogic Array Scalars.
From coqutil Require Import Tactics.Tactics WithBaseName Map.SeparationLogic.
Require Import Util.ZRange.
Require Import P256.modinv.u320_sub.
From Coq Require Import Zmod ZArith.
Local Open Scope string_scope. Local Open Scope Z_scope.
Require Import Setoid.

Local Notation eval := (fold_right (fun (a : word) (s : Z) => a + 2^64*s) 0).
Local Notation array := (array scalar (word.of_Z 8)).

From Coq Require Import ZArith Lia.

#[export] Instance spec_of_beeu_normalize : spec_of "beeu_normalize" :=
    fnspec! "beeu_normalize" (p_y p_m : word) / (y MOD : list word) R, 
    {
        requires t m := 
            m =* array p_y y ⋆ array p_m MOD ⋆ R /\ 
            length y = 5%nat /\ length MOD = 5%nat /\ eval MOD > 0;
        ensures T M := exists (r : list word), 
            M =* array p_y r ⋆ array p_m MOD ⋆ R /\ length r = 5%nat /\ 
                Zmod.of_Z (eval MOD) (eval y) = Zmod.of_Z (eval MOD) (eval r) 
                /\ 0%nat <= (eval r) < (eval MOD)
    }
.

#[export] Instance spec_of_u320_set : spec_of "u320_set" := fnspec! "u320_set" (p_x p_y : word) / (x y : list word) R, 
    {
        requires t m := 
            m =* array p_x x ⋆ array p_y y ⋆ R /\ 
            length x = 5%nat /\ length y = 5%nat;
        ensures T M := T = t /\
            M =* array p_x y ⋆ array p_y y ⋆ R 
    }.

Local Ltac lists_into_elements := repeat match goal with
  | H : length ?l = ?n |- _ =>  constr_eq true ltac:(isnatcst n);
  let x := fresh l "0" in destruct l as [|x l]; inversion H; clear H end.

Definition u320_set := func! (p_x, p_y) {
    store(p_x, load(p_y));
    store(p_x + $8, load(p_y + $8));
    store(p_x + $8 + $8, load(p_y + $8 + $8));
    store(p_x + $8 + $8 + $8, load(p_y + $8 + $8 + $8));
    store(p_x + $8 + $8 + $8 + $8, load(p_y + $8 + $8 + $8 + $8))
}.

Lemma u320_set_ok : program_logic_goal_for_function! u320_set.
Proof.
    repeat straightline. lists_into_elements; cbn [array] in *; repeat straightline. ecancel_assumption.
Qed. 

Definition beeu_normalize := func! (p_y, p_m) {
    borrow = $0;
    stackalloc 40 as p_prev;

    u320_set(p_prev, p_y);
    unpack! borrow = u320_sub(p_y, p_m);

    while borrow == $0 {
        u320_set(p_prev, p_y);

        unpack! borrow = u320_sub(p_y, p_m)
    };

    u320_set(p_y, p_prev)
}.

Lemma Zmod_diff {m n : Z} : ((n - m) mod m) = n mod m.
Proof.
    rewrite Zminus_mod, Z_mod_same_full, Z.sub_0_r, Zmod_mod. eauto.
Qed.

Lemma array_to_bytes ptr ws :
    Lift1Prop.iff1 (array ptr ws) (@Array.array _ word _ mem _ ptsto (word.of_Z 1) ptr (ws2bs 8 ws)).
Proof.
    eapply (@bytes_of_words 64 _ word mem _ _).
Qed.

Lemma bytes_to_array ptr bs : 
    (length bs mod 8)%nat = 0%nat ->
    Lift1Prop.iff1 (@Array.array _ word _ mem _ ptsto (word.of_Z 1) ptr bs) (array ptr (bs2ws 8 bs)).
Proof. intros H. eapply (@words_of_bytes 64 _ word mem _ _).
    cbn. replace (PosDef.Pos.to_nat 8) with 8%nat by lia.
    lia.
Qed.

#[local] Ltac ensure_map m := lazymatch type of m with | @Interface.map.rep _ _ _ => true | _ => false end.
#[local] Ltac newest_memory_hyp := match goal with | H: ?G ?m |- _ =>
    match (ensure_map m) with true => H | false => fail end end.

#[local] Ltac alloc_array ptr st := 
    match goal with 
    | [H : Datatypes.length st = ?n |- _] => 
        let Hmem := newest_memory_hyp in 
        seprewrite_in_by (bytes_to_array ptr st) Hmem ltac:(rewrite H; eauto);
        let prev := fresh "prev" in
        let Heqprev := fresh "Heqprev" in
        remember (bs2ws 8 st) as prev eqn:Heqprev; 
        let m := eval cbv in (Z.to_nat (n / 8)) in
        assert (length prev = m) by (rewrite Heqprev, bs2ws_length; try rewrite !H; eauto);
        clear dependent st
    end.

#[local] Ltac dealloc_array ptr arr := 
    match goal with 
    | [H : Datatypes.length arr = ?n |- _] => 
        let Hmem := newest_memory_hyp in
        seprewrite_in (array_to_bytes ptr arr) Hmem;
        let m := eval cbv in (Z.to_nat (8 * n)) in 
            assert (length (ws2bs 8 arr) = m) by (lists_into_elements; eauto)
    end.

#[local] Ltac destruct_cond := match goal with 
        | [H : ?T |- _] => 
            match T with 
            | ?A -> False =>
                match A with 
                | context m [if (word.eqb ?x ?y) then _ else _] => 
                    let Heq := fresh "Heq" in
                    destruct (word.eqb x y) eqn:Heq; [| contradiction]; 
                    eapply Properties.word.eqb_true in Heq
                end
            | ?A => 
                match A with 
                | context m [if (word.eqb ?x ?y) then _ else _] => 
                    let Heq := fresh "Heq" in
                    destruct (word.eqb x y) eqn:Heq; [discriminate |];
                    eapply Properties.word.eqb_false in Heq
                end
            end
        end.


Lemma beeu_normalize_ok : program_logic_goal_for_function! beeu_normalize.
Proof.
    repeat straightline.

    alloc_array a stack.

    repeat (straightline_call; ssplit; try ecancel_assumption; eauto; repeat straightline).
    rename a into p_prev; rename y into prv; rename x0 into y.

    refine ((Loops.tailrec
        (* types of ghost variables*) (HList.polymorphic_list.cons _
                                    (HList.polymorphic_list.cons _
                                    (HList.polymorphic_list.cons _
                                    HList.polymorphic_list.nil)))
        (* program variables *) (["borrow"; "p_prev"; "p_y"; "p_m"] : list String.string))
        (fun v y_ prev_ R t m borrow p_prev p_y p_m => PrimitivePair.pair.mk (* precondition *)
        ( v = eval prev_  /\ m=* array p_y y_ ⋆ array p_m MOD ⋆ array p_prev prev_ ⋆ R 
      /\ length y_ = 5%nat /\ length MOD = 5%nat /\ length prev_ = 5%nat /\
      eval y_ -2^320*borrow = (eval prev_) - (eval MOD) /\ 
      Zmod.of_Z (eval MOD) (eval prev_) = Zmod.of_Z (eval MOD) (eval prv) /\
      0 <= (eval prev_))
        (fun            T M BORROW P_PREV P_Y P_M => (* postcondition *)
        T = t /\ P_PREV = p_prev /\ P_Y = p_y /\ P_M = p_m /\ exists Y PREV, 
        M =* array p_y Y ⋆ array p_prev PREV ⋆ array p_m MOD ⋆ R
        /\ length Y = 5%nat /\ length PREV = 5%nat /\  
        Zmod.of_Z (eval MOD) (eval PREV) = Zmod.of_Z (eval MOD) (eval prv) /\ 
        0 <= (eval PREV) < (eval MOD)))
        (fun n m => 0 <= n < m) (* well_founded relation *)
        _ _ _ _ _ _ _ _);
    Loops.loop_simpl.
    { repeat straightline. }
    { eapply Z.lt_wf. }
    { repeat straightline; ssplit; try ecancel_assumption; eauto; lists_into_elements; cbv [fold_right] in *. ZnWords. }
    { intros. repeat straightline; subst br. 
        { 
            repeat (straightline_call; intuition try ecancel_assumption; repeat straightline). 
            eexists _,_,_,_. repeat straightline; intuition try ecancel_assumption. 
            {
                
                destruct_cond.
                rewrite <-H24, <-!Zmod.unsigned_inj_iff, !Zmod.unsigned_of_Z. symmetry. 
                rewrite <-Zmod_diff. f_equal. ZnWords.
            }
            { lists_into_elements. cbv [fold_right] in *. ZnWords. } 
            { 
                split; repeat straightline; intuition try ecancel_assumption.
                1,2: lists_into_elements; cbv [fold_right] in *; destruct_cond; ZnWords. 
                eexists _, _. intuition try ecancel_assumption. 
            }
        }
        { eexists _, _. intuition try ecancel_assumption. lists_into_elements; cbv [fold_right length] in *.
        destruct_cond; ZnWords.  }
    }
    { 
        repeat straightline. straightline_call; intuition try ecancel_assumption. repeat straightline.
        dealloc_array p_prev x5.
        repeat straightline. eexists; intuition try ecancel_assumption; lists_into_elements; 
        cbv [fold_right length] in *; eauto; ZnWords.
    }
Qed.