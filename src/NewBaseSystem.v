Require Import Coq.ZArith.ZArith Coq.micromega.Psatz Coq.omega.Omega.
Require Import Coq.ZArith.BinIntDef.
Local Open Scope Z_scope.

Require Import Crypto.Tactics.Algebra_syntax.Nsatz.
Require Import Crypto.Util.Tactics Crypto.Util.Decidable Crypto.Util.LetIn.
Require Import Crypto.Util.ZUtil Crypto.Util.ListUtil Crypto.Util.Sigma.
Require Import Crypto.Util.CPSUtil Crypto.Util.Prod.

Require Import Coq.Lists.List. Import ListNotations.
Require Crypto.Util.Tuple. Local Notation tuple := Tuple.tuple.

Local Ltac prove_id :=
  repeat match goal with
         | _ => progress intros
         | _ => progress simpl
         | _ => progress cbv [Let_In]
         | _ => progress (autorewrite with uncps push_id in * )
         | _ => break_if
         | _ => break_match
         | _ => contradiction
         | _ => reflexivity
         | _ => nsatz
         | _ => solve [auto]
         end.

Create HintDb push_basesystem_eval discriminated.
Local Ltac prove_eval := 
  repeat match goal with
         | _ => progress intros
         | _ => progress simpl
         | _ => progress cbv [Let_In]
         | _ => progress (autorewrite with push_basesystem_eval uncps push_id cancel_pair in * )
         | _ => break_if
         | _ => break_match
         | _ => split 
         | H : _ /\ _ |- _ => destruct H
         | H : Some _ = Some _ |- _ => progress (inversion H; subst)
         | _ => discriminate
         | _ => reflexivity
         | _ => nsatz
         end.

Delimit Scope runtime_scope with RT.
Definition runtime_mul := Z.mul.
Global Notation "a * b" := (runtime_mul a%RT b%RT) : runtime_scope.
Definition runtime_add := Z.add.
Global Notation "a + b" := (runtime_add a%RT b%RT) : runtime_scope. 
Definition runtime_fst {A B} := @fst A B.
Definition runtime_snd {A B} := @snd A B.

Module B.
  Local Definition limb := (Z*Z)%type. (* position coefficient and run-time value *)
  Module Associational.
    Definition eval (p:list limb) : Z :=
      List.fold_right Z.add 0%Z (List.map (fun t => fst t * snd t) p).
    
    Lemma eval_nil : eval nil = 0. Proof. reflexivity. Qed.
    Lemma eval_cons p q : eval (p::q) = (fst p) * (snd p) + eval q. Proof. reflexivity. Qed.
    Lemma eval_app p q: eval (p++q) = eval p + eval q.
    Proof. induction p; simpl eval; rewrite ?eval_nil, ?eval_cons; nsatz. Qed.
    Hint Rewrite eval_nil eval_cons eval_app : push_basesystem_eval.

    Definition multerm (t t' : limb) : limb :=
      (fst t * fst t', (snd t * snd t')%RT).
    Definition mul_cps (p q:list limb) {T} (f : list limb->T) :=
      flat_map_cps (fun t => @map_cps _ _ (multerm t) q) p f.
    Definition mul (p q:list limb) := mul_cps p q id.
    Hint Opaque mul : uncps.
    Lemma eval_map_mul (a:limb) (q:list limb) : eval (List.map (multerm a) q) = fst a * snd a * eval q.
    Proof.
      induction q; cbv [multerm]; simpl List.map;
        autorewrite with push_basesystem_eval cancel_pair; nsatz.
    Qed. Hint Rewrite eval_map_mul : push_basesystem_eval.
    Lemma mul_cps_id p q: forall {T} f,
      @mul_cps p q T f = f (mul p q).
    Proof. cbv [mul_cps mul]; prove_id. Qed. Hint Rewrite mul_cps_id : uncps.
    Lemma eval_mul_noncps p q:
      eval (mul p q) = eval p * eval q.
    Proof.
      cbv [mul mul_cps]; induction p; prove_eval. Qed. Hint Rewrite eval_mul_noncps : push_basesystem_eval.

    Fixpoint split (s:Z) (xs:list limb)
             {T} (f :list limb*list limb->T) :=
      match xs with
      | nil => f (nil, nil)
      | cons x xs' =>
        split s xs'
              (fun sxs' =>
        if dec (fst x mod s = 0)
        then f (fst sxs',          cons (fst x / s, snd x) (snd sxs'))
        else f (cons x (fst sxs'), snd sxs'))
      end.
    Definition split_noncps s xs := split s xs id.
    Hint Opaque split_noncps : uncps.
    Lemma split_id s p: forall {T} f,
        @split s p T f = f (split_noncps s p).
    Proof.
      induction p;
        repeat match goal with
               | _ => rewrite IHp
               | _ => progress (cbv [split_noncps]; prove_id)
               end.
    Qed. Hint Rewrite split_id : uncps.
    Lemma eval_split_noncps s p (s_nonzero:s<>0):
      eval (fst (split_noncps s p)) + s*eval (snd (split_noncps s p))  = eval p.
    Proof.
      cbv [split_noncps];  induction p; prove_eval.
        match goal with H:_ |- _ =>
                        unique pose proof (Z_div_exact_full_2 _ _ s_nonzero H)
        end; nsatz.
    Qed. Hint Rewrite @eval_split_noncps using auto : push_basesystem_eval.

    Definition reduce_cps (s:Z) (c:list limb) (p:list limb)
               {T} (f : list limb->T) :=
      split s p (fun ab =>mul_cps c (snd ab) (fun rr =>f (fst ab ++ rr))).
    Definition reduce s c p := reduce_cps s c p id.
    Hint Opaque reduce : uncps.
    Lemma reduction_rule a b s c (modulus_nonzero:s-c<>0) :
      (a + s * b) mod (s - c) = (a + c * b) mod (s - c).
    Proof. replace (a + s * b) with ((a + c*b) + b*(s-c)) by nsatz.
           rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod; trivial. Qed.
    Lemma reduce_cps_id s c p {T} f:
      @reduce_cps s c p T f = f (reduce s c p).
    Proof. cbv [reduce_cps reduce]; prove_id. Qed. Hint Rewrite reduce_cps_id : uncps.
    Lemma eval_reduce s c p (s_nonzero:s<>0) (modulus_nonzero:s-eval c<>0):
      eval (reduce s c p) mod (s - eval c) = eval p mod (s - eval c).
    Proof.
      cbv [reduce reduce_cps]; prove_eval;
        rewrite <-reduction_rule by auto; prove_eval.
    Qed. Hint Rewrite eval_reduce : push_basesystem_eval.

    Section Carries.
      Context {modulo div:Z->Z->Z}.
      Context {div_mod : forall a b:Z, b <> 0 ->
                                       a = b * (div a b) + modulo a b}.

      Definition carryterm_cps (w fw:Z) (t:limb) {T} (f:list limb->T) :=
        if dec (fst t = w)
        then dlet d := div (snd t) fw in
             dlet m := modulo (snd t) fw in
             f ((w*fw, d) :: (w, m) :: @nil limb)
        else f [t].
      Definition carry_cps(w fw:Z) (p:list limb) {T} (f:list limb->T) :=
        flat_map_cps (carryterm_cps w fw) p f.
      Definition carryterm w fw t := carryterm_cps w fw t id.
      Hint Opaque carryterm : uncps.
      Definition carry w fw p := carry_cps w fw p id.
      Hint Opaque carry : uncps.
      Lemma carryterm_cps_id w fw t {T} f :
        @carryterm_cps w fw t T f
        = f (@carryterm w fw t).
      Proof. cbv [carryterm_cps carryterm Let_In]; prove_id. Qed. Hint Rewrite carryterm_cps_id : uncps.
      Lemma eval_carryterm w fw (t:limb) (fw_nonzero:fw<>0):
        eval (carryterm w fw t) = eval [t].
      Proof.
        cbv [carryterm_cps carryterm Let_In]; prove_eval.
        specialize (div_mod (snd t) fw fw_nonzero).
        nsatz.
      Qed. Hint Rewrite eval_carryterm using auto : push_basesystem_eval.
      Lemma carry_cps_id w fw p {T} f:
        @carry_cps w fw p T f = f (carry w fw p).
      Proof. cbv [carry_cps carry]; prove_id. Qed.
      Hint Rewrite carry_cps_id : uncps.
      Lemma eval_carry w fw p (fw_nonzero:fw<>0):
        eval (carry w fw p) = eval p.
      Proof. cbv [carry_cps carry]; induction p; prove_eval. Qed.
      Hint Rewrite eval_carry using auto : push_basesystem_eval.
    End Carries.

    Section Saturated.
      Context {word_max : Z} {word_max_pos : 1 < word_max} 
              {add : Z -> Z -> Z * Z}
              {add_correct : forall x y, fst (add x y) + word_max * snd (add x y) = x + y}
              {mul : Z -> Z -> Z * Z}
              {mul_correct : forall x y, fst (mul x y) + word_max * snd (mul x y) = x * y}
              {end_wt:Z} {end_wt_pos : 0 < end_wt}
      .

      Definition sat_multerm_cps (t t' : limb) {T} (f:list limb->T) :=
        dlet tt' := mul (snd t) (snd t') in
              f ((fst t*fst t', runtime_fst tt') :: (fst t*fst t'*word_max, runtime_snd tt') :: nil)%list.
      Definition sat_mul_cps (p q : list limb) {T} (f:list limb->T) := 
        flat_map_cps (fun t => @flat_map_cps _ _ (sat_multerm_cps t) q) p f.
      (* TODO (jgross): kind of an interesting behavior--it infers the type arguments like this but fails to check if I leave them implicit *)
      Definition sat_multerm t t' := sat_multerm_cps t t' id.
      Definition sat_mul p q := sat_mul_cps p q id.
      Hint Opaque sat_multerm sat_mul : uncps.
      Lemma sat_multerm_cps_id t t' : forall {T} (f:list limb->T),
       sat_multerm_cps t t' f = f (sat_multerm t t').
      Proof. reflexivity. Qed. Hint Rewrite sat_multerm_cps_id : uncps.
      Lemma eval_map_sat_multerm_cps t q :
        eval (flat_map (fun x => sat_multerm_cps t x id) q) = fst t * snd t * eval q.
      Proof.
        cbv [sat_multerm sat_multerm_cps Let_In runtime_fst runtime_snd];
        induction q; prove_eval;
          try match goal with |- context [mul ?a ?b] =>
                              specialize (mul_correct a b) end;
          nsatz.
      Qed. Hint Rewrite eval_map_sat_multerm_cps : push_basesystem_eval.
      Lemma sat_mul_cps_id p q {T} f : @sat_mul_cps p q T f = f (sat_mul p q).
      Proof. cbv [sat_mul_cps sat_mul]; prove_id. Qed. Hint Rewrite sat_mul_cps_id : uncps.
      Lemma eval_sat_mul p q : eval (sat_mul p q) = eval p * eval q.
      Proof. cbv [sat_mul_cps sat_mul]; induction p; prove_eval. Qed.
      Hint Rewrite eval_sat_mul : push_basesystem_eval.

    End Saturated.
  End Associational.
  Hint Rewrite
      @Associational.sat_mul_cps_id
      @Associational.sat_multerm_cps_id
      @Associational.carry_cps_id
      @Associational.carryterm_cps_id
      @Associational.reduce_cps_id
      @Associational.split_id
      @Associational.mul_cps_id : uncps.

  Module Positional.
    Section Positional.
      Import Associational.
      Context (weight : nat -> Z) (* [weight i] is the weight of position [i] *)
              (weight_0 : weight 0%nat = 1%Z)
              (weight_nonzero : forall i, weight i <> 0).

      (** Converting from positional to associational *)

      Definition to_associational_cps {n:nat} (xs:tuple Z n)
                 {T} (f:list limb->T) :=
        map_cps weight (seq 0 n)
                (fun r =>
                   to_list_cps n xs (fun rr => combine_cps r rr f)).
      Definition to_associational {n} xs := @to_associational_cps n xs _ id.
      Definition eval {n} x := @to_associational_cps n x _ Associational.eval.
      Lemma to_associational_cps_id {n} x {T} f:
        @to_associational_cps n x T f = f (to_associational x).
      Proof. cbv [to_associational_cps to_associational]; prove_id. Qed.
      Hint Rewrite @to_associational_cps_id : uncps.
      Lemma eval_to_associational {n} x :
        Associational.eval (@to_associational n x) = eval x.
      Proof. cbv [to_associational_cps eval to_associational]; prove_eval. Qed.
      Hint Rewrite @eval_to_associational : push_basesystem_eval.

      (** Converting from associational to positional *)

      Program Definition zeros n : tuple Z n := Tuple.from_list n (List.map (fun _ => 0) (List.seq 0 n)) _.
      Next Obligation. autorewrite with distr_length; reflexivity. Qed.
      Lemma eval_zeros n : eval (zeros n) = 0.
      Proof.
        cbv [eval Associational.eval to_associational_cps zeros];
          autorewrite with uncps; rewrite Tuple.to_list_from_list.
        generalize dependent (List.seq 0 n); intro xs; induction xs; simpl; nsatz.
      Qed. Hint Rewrite eval_zeros : push_basesystem_eval.

      Definition add_to_nth_cps {n} i x t {T} (f:tuple Z n->T) :=
        @on_tuple_cps _ _ 0 (update_nth_cps i (runtime_add x)) n n t _ f.
      Definition add_to_nth {n} i x t := @add_to_nth_cps n i x t _ id.
      Hint Opaque add_to_nth : uncps.
      Lemma add_to_nth_cps_id {n} i x xs {T} f:
        @add_to_nth_cps n i x xs T f = f (add_to_nth i x xs).
      Proof.
        cbv [add_to_nth_cps add_to_nth]; erewrite !on_tuple_cps_correct
          by (intros; autorewrite with uncps; reflexivity); prove_id.
        Unshelve.
        intros; subst. autorewrite with uncps push_id. distr_length.
      Qed. Hint Rewrite @add_to_nth_cps_id : uncps.
      Lemma eval_add_to_nth {n} (i:nat) (x:Z) (H:(i<n)%nat) (xs:tuple Z n):
        eval (@add_to_nth n i x xs) = weight i * x + eval xs.
      Proof.
        cbv [eval to_associational_cps add_to_nth add_to_nth_cps runtime_add].
        erewrite on_tuple_cps_correct by (intros; autorewrite with uncps; reflexivity).
        prove_eval.
        cbv [Tuple.on_tuple].
        rewrite !Tuple.to_list_from_list.
        autorewrite with uncps push_id.
        rewrite ListUtil.combine_update_nth_r at 1.
        rewrite <-(update_nth_id i (List.combine _ _)) at 2.
        rewrite <-!(ListUtil.splice_nth_equiv_update_nth_update _ _ (weight 0, 0)); cbv [ListUtil.splice_nth id];
          repeat match goal with
                 | _ => progress (apply Zminus_eq; ring_simplify)
                 | _ => progress autorewrite with push_basesystem_eval cancel_pair distr_length
                 | _ => progress rewrite <-?ListUtil.map_nth_default_always, ?map_fst_combine, ?List.firstn_all2, ?ListUtil.map_nth_default_always, ?nth_default_seq_inbouns, ?plus_O_n
                 end; trivial; lia.
        Unshelve.
        intros; subst. autorewrite with uncps push_id. distr_length.
      Qed. Hint Rewrite @eval_add_to_nth using omega : push_basesystem_eval.

      Fixpoint place_cps (t:limb) (i:nat) {T} (f:nat * Z->T) :=
        if dec (fst t mod weight i = 0)
        then f (i, let c := fst t / weight i in (c * snd t)%RT)
        else match i with S i' => place_cps t i' f | O => f (O, fst t * snd t)%RT end.
      Lemma place_cps_in_range (t:limb) (n:nat) : (fst (place_cps t n id) < S n)%nat.
      Proof. induction n; simpl; break_match; simpl; omega. Qed.
      Lemma weight_place_cps t i : weight (fst (place_cps t i id)) * snd (place_cps t i id) = fst t * snd t.
      Proof.
        induction i; cbv [id]; simpl place_cps; break_match;
          autorewrite with cancel_pair;
          try find_apply_lem_hyp Z_div_exact_full_2; nsatz || auto.
      Qed.
      Definition place t i := place_cps t i id.
      Hint Opaque place : uncps.
      Lemma place_cps_id t i {T} f :
        @place_cps t i T f = f (place t i).
      Proof. cbv [place]; induction i; prove_id. Qed.
      Hint Rewrite place_cps_id : uncps.
      Definition from_associational_cps n (p:list limb) {T} (f:tuple Z n->T):=
        fold_right_cps (fun t st => place_cps t (pred n) (fun p=> add_to_nth_cps (fst p) (snd p) st id)) (zeros n) p f.
      Definition from_associational n p := from_associational_cps n p id.
      Hint Opaque from_associational : uncps.
      Lemma from_associational_cps_id {n} p {T} f:
        @from_associational_cps n p T f = f (from_associational n p).
      Proof. cbv [from_associational_cps from_associational]; prove_id. Qed.
      Hint Rewrite @from_associational_cps_id : uncps.
      Lemma eval_from_associational {n} p (n_nonzero:n<>O):
        eval (from_associational n p) = Associational.eval p.
      Proof.
        cbv [from_associational_cps from_associational]; induction p;
          [|pose proof (place_cps_in_range a (pred n))]; prove_eval.
        cbv [place]; rewrite weight_place_cps. nsatz.
      Qed. Hint Rewrite @eval_from_associational using omega : push_basesystem_eval.

      Section Carries.
        Context {modulo div : Z->Z->Z}.
        Context {div_mod : forall a b:Z, b <> 0 ->
                                       a = b * (div a b) + modulo a b}.
      Definition carry_cps(index:nat) (p:list limb) {T} (f:list limb->T) :=
        @Associational.carry_cps modulo div (weight index) (weight (S index) / weight index) p T f.
      Definition carry i p := carry_cps i p id.
      Hint Opaque carry : uncps.
      Lemma carry_cps_id i p {T} f:
        @carry_cps i p T f = f (carry i p).
      Proof. cbv [carry_cps carry]; prove_id; rewrite carry_cps_id; reflexivity. Qed.
      Hint Rewrite carry_cps_id : uncps.
      Lemma eval_carry i p: weight (S i) / weight i <> 0 ->
        Associational.eval (carry i p) = Associational.eval p.
      Proof. cbv [carry_cps carry]; intros; eapply @eval_carry; eauto. Qed.
      Hint Rewrite @eval_carry : push_basesystem_eval.
      End Carries.
    End Positional.
  End Positional.
  Hint Rewrite
      @Associational.sat_mul_cps_id
      @Associational.sat_multerm_cps_id
      @Associational.carry_cps_id
      @Associational.carryterm_cps_id
      @Associational.reduce_cps_id
      @Associational.split_id
      @Associational.mul_cps_id
      @Positional.carry_cps_id
      @Positional.from_associational_cps_id
      @Positional.place_cps_id
      @Positional.add_to_nth_cps_id
      @Positional.to_associational_cps_id
    : uncps.
  Hint Rewrite
      @Associational.eval_sat_mul
      @Associational.eval_mul_noncps
      @Positional.eval_to_associational
      @Associational.eval_carry
      @Associational.eval_carryterm
      @Associational.eval_reduce
      @Associational.eval_split_noncps
      @Positional.eval_carry
      @Positional.eval_from_associational
      @Positional.eval_add_to_nth
    using (omega || assumption) : push_basesystem_eval.
End B.
  
Local Coercion Z.of_nat : nat >-> Z.
Import Coq.Lists.List.ListNotations. Local Open Scope list_scope.
Import B.

Ltac assert_preconditions :=
  repeat match goal with
         | |- context [Positional.from_associational_cps ?wt ?n] =>
           unique assert (wt 0%nat = 1) by (cbv; congruence)
         | |- context [Positional.from_associational_cps ?wt ?n] =>
           unique assert (forall i, wt i <> 0) by (intros; apply Z.pow_nonzero; try (cbv; congruence); solve [zero_bounds])
         | |- context [Positional.from_associational_cps ?wt ?n] =>
           unique assert (n <> 0%nat) by (cbv; congruence)
         | |- context [Positional.carry_cps?wt ?i] =>
           unique assert (wt (S i) / wt i <> 0) by (cbv; congruence)
         end.

Ltac op_simplify := 
  cbv - [runtime_add runtime_mul Let_In];
  cbv [runtime_add runtime_mul];
  repeat progress rewrite ?Z.mul_1_l, ?Z.mul_1_r, ?Z.add_0_l, ?Z.add_0_r.

Ltac prove_op sz x :=
  cbv [Tuple.tuple Tuple.tuple'] in *;
  repeat match goal with p : _ * Z |- _ => destruct p end;
  apply lift2_sig;
  eexists; cbv zeta beta; intros;
  match goal with |- Positional.eval ?wt _ = ?op (Positional.eval ?wt ?a) (Positional.eval ?wt ?b) =>
                  transitivity (Positional.eval wt (x wt a b))
  end; 
  [ apply f_equal; op_simplify; reflexivity
  | assert_preconditions;
    progress autorewrite with uncps push_id push_basesystem_eval;
    reflexivity ]
.

Section Ops.
  Context
    (modulo : Z -> Z -> Z)
    (div : Z -> Z -> Z)
    (div_mod : forall a b : Z, b <> 0 ->
                               a = b * div a b + modulo a b).
  Local Infix "^" := tuple : type_scope.

  Let wt := fun i : nat => 2^(25 * (i / 2) + 26 * ((i + 1) / 2)).
  Let sz := 10%nat.
  Let sz2 := Eval compute in ((sz * 2) - 1)%nat.

  (* shorthand for many carries in a row *)
  Definition chained_carries (w : nat -> Z) (p:list B.limb) (idxs : list nat)
             {T} (f:list B.limb->T) :=
    fold_right_cps2 (@Positional.carry_cps w modulo div) p idxs f.

  Definition addT :
    { add : (Z^sz -> Z^sz -> Z^sz)%type &
               forall a b : Z^sz,
                 let eval {n} := Positional.eval (n := n) wt in
                 eval (add a b) = eval a  + eval b }.
  Proof.
    prove_op sz (
        fun wt a b =>
        Positional.to_associational_cps (n := sz) wt a
          (fun r => Positional.to_associational_cps (n := sz) wt b
          (fun r0 => Positional.from_associational_cps wt sz (r ++ r0) id
        ))).
  Defined.
  

  Definition mulT :
    {mul : (Z^sz -> Z^sz -> Z^sz2)%type &
               forall a b : Z^sz,
                 let eval {n} := Positional.eval (n := n) wt in
                 eval (mul a b) = eval a  * eval b }.
  Proof.
    let x := (eval cbv [chained_carries seq fold_right_cps2 sz2] in
        (fun w a b =>
         Positional.to_associational_cps (n := sz) w a
           (fun r => Positional.to_associational_cps (n := sz) w b
           (fun r0 => Associational.mul_cps r r0
           (fun r1 => Positional.from_associational_cps w sz2 r1
           (fun r2 => Positional.to_associational_cps w r2
           (fun r3 => chained_carries w r3 (seq 0 sz2)
           (fun r13 => Positional.from_associational_cps w sz2 r13 id
             )))))))) in
    prove_op sz x.
  Time Defined. (* Finished transaction in 139.086 secs *) 

End Ops.

Eval cbv [projT1 addT lift2_sig proj1_sig] in (projT1 addT).
Eval cbv [projT1 mulT lift2_sig proj1_sig] in
    (fun m d div_mod => projT1 (mulT m d div_mod)).
