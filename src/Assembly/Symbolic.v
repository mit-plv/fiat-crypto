Require Crypto.Assembly.Parse.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Crypto.Util.Tuple.
Require Import Util.OptionList.
Require Import Crypto.Util.ErrorT.
Module Import List.
  Section IndexOf.
    Context [A] (f : A -> bool).
    Fixpoint indexof (l : list A) : option nat :=
      match l with
      | nil => None
      | cons a l =>
          if f a then Some 0
          else option_map S (indexof l )
      end.
    Lemma indexof_none l (H : indexof l = None) :
      forall i a, nth_error l i = Some a -> f a = false.
    Admitted.
    Lemma indexof_Some l i (H : indexof l = Some i) :
      exists a, nth_error l i = Some a /\ f a = true.
    Admitted.
    Lemma indexof_first l i (H : indexof l = Some i) :
      forall j a, j < i -> nth_error l j = Some a -> f a = false.
    Admitted.
  End IndexOf.


  Section FoldMap. (* map over a list in the state monad *)
    Context [A B S] (f : A -> S -> B * S).
    Fixpoint foldmap (l : list A) (s : S) : list B * S :=
      match l with
      | nil => (nil, s)
      | cons a l =>
          let bs_s := foldmap l s in
          let b_s := f a (snd bs_s) in
          (cons (fst b_s) (fst bs_s), snd b_s)
      end.
    Lemma foldmap_ind
      l s
      (P : list A -> list B -> S -> Prop)
      (Hnil : P nil nil s)
      (Hcons : forall (l : list A) (l' : list B) (s : S),
      P l l' s -> forall a, P (cons a l) (cons (fst (f a s)) l') (snd (f a s))) : P l (fst (foldmap l s)) (snd (foldmap l s)).
    Proof using Type. induction l; eauto; []; eapply Hcons; trivial. Qed.
  End FoldMap.
End List.

Require Coq.Sorting.Mergesort.
Module NOrder <: Orders.TotalLeBool.
  Local Open Scope N_scope.
  Definition t := N.
  Definition ltb := N.ltb.
  Definition leb := N.leb.
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb ltb]; intros a1 a2.
    repeat first [ rewrite !Bool.andb_true_iff
                 | rewrite !Bool.orb_true_iff
                 | rewrite !N.eqb_eq
                 | rewrite !N.ltb_lt
                 | rewrite !N.leb_le ].
    Lia.lia.
  Qed.
End NOrder.
Module NSort := Mergesort.Sort NOrder.
Notation sortN := NSort.sort.

Require Import Coq.Program.Equality.

Section Forall2.
  Lemma Forall2_flip {A B} {R : A -> B -> Prop} xs ys :
    Forall2 R xs ys -> Forall2 (fun y x => R x y) ys xs.
  Proof. induction 1; eauto. Qed.

  Lemma length_Forall2 [A B : Type] [xs ys] [P:A->B->Prop] : Forall2 P xs ys -> length xs = length ys.
  Proof. induction 1; cbn; eauto. Qed.

  Section weaken.
    Context {A B} {P Q:A->B->Prop} (H : forall (a : A) (b : B), P a b -> Q a b).
    Fixpoint Forall2_weaken args args' (pf : Forall2 P args args') : Forall2 Q args args' :=
      match pf with
      | Forall2_nil => Forall2_nil _
      | Forall2_cons _ _ _ _ Rxy k => Forall2_cons _ _ (H _ _ Rxy) (Forall2_weaken _ _ k)
      end.
  End weaken.
  Lemma Forall2_map_l {A' A B} (f : A' -> A) {R : A -> B -> Prop} (xs : list A') (ys : list B) :
    Forall2 R (map f xs) ys <-> Forall2 (fun x y => R (f x) y) xs ys.
  Proof.
    split; intros H; dependent induction H; try destruct xs; cbn in *;
      try congruence; eauto.
    { inversion x; subst; eauto. }
  Qed.
  Import RelationClasses.
  Instance Reflexive_forall2 [A] [R] : @Reflexive A R -> Reflexive (Forall2 R).
  Proof. intros ? l; induction l; eauto. Qed.
  Lemma Forall2_eq [A] (xs ys : list A) : Forall2 eq xs ys <-> xs = ys.
  Proof. split; induction 1; subst; eauto; reflexivity. Qed.
  Lemma Forall2_trans [A B C] [AB BC] [xs : list A] [ys : list B] :
    Forall2 AB xs ys -> forall [zs : list C], Forall2 BC ys zs ->
    Forall2 (fun x z => exists y, AB x y /\ BC y z) xs zs.
  Proof. induction 1; inversion 1; subst; econstructor; eauto. Qed.
End Forall2.

Require Import Coq.Strings.String Crypto.Util.Strings.Show.
Require Import Crypto.Assembly.Syntax.
Definition idx := N.
Local Set Boolean Equality Schemes.
Definition symbol := N.

Class OperationSize := operation_size : N.
Global Instance Show_OperationSize : Show OperationSize := show_N.

Section S.
Implicit Type s : OperationSize.
Variant op := old s (_:symbol) | oldold (_:REG*option nat) | const (_ : N) | add s | addcarry s | notaddcarry s | addoverflow s | neg s | shl s | shr s | sar s | rcr s | and s | or s | xor s | slice (lo sz : N) | mul s | mulhuu s | set_slice (lo sz : N) | selectznz (* | ... *) | bzhi s
  | addZ | mulZ | negZ | shlZ | shrZ | andZ | orZ.
End S.

Global Instance Show_op : Show op := fun o =>
  match o with
  | old s n => "old " ++ show s ++ " " ++ show n
  | oldold p => "oldold " ++ show p
  | const n => "const " ++ show n
  | add s => "add " ++ show s
  | addcarry s => "addcarry " ++ show s
  | notaddcarry s => "notaddcarry " ++ show s
  | addoverflow s => "addoverflow " ++ show s
  | neg s => "neg " ++ show s
  | shl s => "shl " ++ show s
  | shr s => "shr " ++ show s
  | sar s => "sar " ++ show s
  | rcr s => "rcr " ++ show s
  | and s => "and " ++ show s
  | or s => "or " ++ show s
  | xor s => "xor " ++ show s
  | bzhi s => "bzhi" ++ show s                 
  | slice lo sz => "slice " ++ show lo ++ " " ++ show sz
  | mul s => "mul " ++ show s
  | mulhuu s => "mulhuu " ++ show s
  | set_slice lo sz => "set_slice " ++ show lo ++ " " ++ show sz
  | selectznz => "selectznz"

             
  | addZ => "addZ"
  | mulZ => "mulZ"
  | negZ => "negZ"
  | shlZ => "shlZ"
  | shrZ => "shrZ"
  | andZ => "andZ"
  | orZ => "orZ"
  end%string.

Definition associative o := match o with add _|mul _|or _|and _=> true | _ => false end.
Definition commutative o := match o with add _|addcarry _|mul _|mulhuu _ => true | _ => false end.
Definition identity o := match o with add _|addcarry _ => Some 0%N | mul _|mulhuu _=>Some 1%N |_=> None end.

Definition node (A : Set) : Set := op * list A.
Global Instance Show_node {A : Set} [show_A : Show A] : Show (node A) := show_prod.

Local Unset Elimination Schemes.
Inductive expr : Set :=
| ExprRef (_ : idx)
| ExprApp (_ : node expr).
Local Set Elimination Schemes.
Section expr_ind.
  Context (P : expr -> Prop)
    (HRef : forall i, P (ExprRef i))
    (HApp : forall n, Forall P (snd n) -> P (ExprApp n)).
  Fixpoint expr_ind e {struct e} : P e :=
    match e with
    | ExprRef i => HRef i
    | ExprApp n => HApp _ (list_rect _ (Forall_nil _) (fun e _ H => Forall_cons e (expr_ind e) H) (snd n))
    end.
End expr_ind.
Definition invert_ExprRef (e : expr) : option idx :=
  match e with ExprRef i => Some i | _ => None end.
Definition Show_expr_body (Show_expr : Show expr) : Show expr
  := Eval cbv -[String.append show_N concat List.map Show_op] in
      fun e => match e with
               | ExprRef i => "ExprRef " ++ show i
               | ExprApp (o, e) => "ExprApp " ++ show (o, e)
               end%string.
Definition Show_expr : Show expr
  := Eval cbv -[String.append show_N concat List.map Show_op] in
      fix Show_expr e := Show_expr_body Show_expr e.
Global Existing Instance Show_expr.

Require Import Crypto.Util.Option Crypto.Util.Notations Coq.Lists.List.
Import ListNotations.

Section WithContext.
  Context (ctx : symbol -> option N).
  Definition interp_op o args :=
    let keep n x := N.land x (N.ones n) in
    let signed s n : Z := (Z.land (Z.shiftl 1 (Z.of_N s-1) + Z.of_N n) (Z.ones (Z.of_N s)) - Z.shiftl 1 (Z.of_N s-1))%Z in
    match o, args with
    | old s x, nil => match ctx x with Some v => Some (keep s v) | None => None end
    | add s, args => Some (keep s (List.fold_right N.add 0 args))
    | addoverflow s, args => Some (
        let v := List.fold_right Z.add 0%Z (List.map (signed s) args) in
        if Z.eqb v (Z.land v (Z.ones (Z.of_N s))) then 0 else 1)
    | xor s, args => Some (keep s (List.fold_right N.lxor 0 args))
    | neg s, [a] => Some (keep s (2^s - a))
    (* note: this case is real awkward, consider Z? *)
    | slice lo sz, [a] => Some (keep sz (N.shiftr a lo))
    (* shifts should not truncate shamt because fiat-crypto semantics does not *)
    | const z, nil => Some z
    (* note: incomplete *)
    | _, _ => None
    end%N.
End WithContext.
Definition interp0_op := interp_op (fun _ => None).

Definition node_beq [A : Set] (arg_eqb : A -> A -> bool) : node A -> node A -> bool :=
  Prod.prod_beq _ _ op_beq (ListUtil.list_beq _ arg_eqb).

Definition dag := list (node idx).

Section WithDag.
  Context (ctx : symbol -> option N) (dag : dag).
  Definition reveal_step reveal (i : idx) : expr :=
    match List.nth_error dag (N.to_nat i) with
    | None => (* undefined *) ExprRef i
    | Some (op, args) => ExprApp (op, List.map reveal args)
    end.
  Fixpoint reveal (n : nat) (i : idx) :=
    match n with
    | O => ExprRef i
    | S n => reveal_step (reveal n) i
    end.

  Definition reveal_node n '(op, args) :=
    ExprApp (op, List.map (reveal n) args).

  Local Unset Elimination Schemes.
  Inductive repr  : forall (i:N) (e : expr), Prop :=
  | RepApp i op args args'
    (_:List.nth_error dag (N.to_nat i) = Some (op, args))
    (_:List.Forall2 repr args args') : repr i (ExprApp (op, args')).

  Section repr_ind.
    Context (P : N -> expr -> Prop)
      (H : forall i op args args', nth_error dag (N.to_nat i) = Some (op, args) ->
        Forall2 (fun i e => repr i e /\ P i e) args args' -> P i (ExprApp (op, args'))).
    Fixpoint repr_ind i e (pf : repr i e) {struct pf} : P i e :=
       let '(RepApp _ _ _ _ A B) := pf in
       H _ _ _ _ A (Forall2_weaken (fun _ _ C => conj C (repr_ind _ _ C)) _ _ B).
  End repr_ind.

  Inductive reveals : expr -> expr -> Prop :=
  | RRef i op args args'
    (_:List.nth_error dag (N.to_nat i) = Some (op, args))
    (_:List.Forall2 (fun i e => reveals (ExprRef i) e) args args')
    : reveals (ExprRef i) (ExprApp (op, args'))
  | RApp op args args'
    (_:List.Forall2 reveals args args')
    : reveals (ExprApp (op, args)) (ExprApp (op, args')).

  Section reveals_ind.
    Context (P : expr -> expr -> Prop)
      (HRef : forall i op args args', nth_error dag (N.to_nat i) = Some (op, args) ->
        Forall2 (fun i e => reveals (ExprRef i) e /\ P (ExprRef i) e) args args' ->
        P (ExprRef i) (ExprApp (op, args')))
      (HApp : forall op args args',
        Forall2 (fun i e => reveals i e /\ P i e) args args' ->
        P (ExprApp (op, args)) (ExprApp (op, args'))).
    Fixpoint reveals_ind i e (pf : reveals i e) {struct pf} : P i e :=
      match pf with
      | RRef _ _ _ _ A B => HRef _ _ _ _ A (Forall2_weaken (fun _ _ C => conj C (reveals_ind _ _ C)) _ _ B)
      | RApp _ _ _ A => HApp _ _ _ (Forall2_weaken (fun _ _ B => conj B (reveals_ind _ _ B)) _ _ A)
      end.
  End reveals_ind.

  Inductive eval : expr -> N -> Prop :=
  | ERef i op args args' n
    (_:List.nth_error dag (N.to_nat i) = Some (op, args))
    (_:List.Forall2 eval (map ExprRef args) args')
    (_:interp_op ctx op args' = Some n)
    : eval (ExprRef i) n
  | EApp op args args' n
    (_:List.Forall2 eval args args')
    (_:interp_op ctx op args' = Some n)
    : eval (ExprApp (op, args)) n.

  Variant eval_node : node idx -> N -> Prop :=
  | ENod op args args' n
    (_:List.Forall2 eval (map ExprRef args) args')
    (_:interp_op ctx op args' = Some n)
    : eval_node (op, args) n.


  Section eval_ind.
    Context (P : expr -> N -> Prop)
      (HRef : forall i op args args' n, nth_error dag (N.to_nat i) = Some (op, args) ->
        Forall2 (fun e n => eval e n /\ P e n) (map ExprRef args) args' ->
        interp_op ctx op args' = Some n ->
        P (ExprRef i) n)
      (HApp : forall op args args' n,
        Forall2 (fun i e => eval i e /\ P i e) args args' ->
        interp_op ctx op args' = Some n ->
        P (ExprApp (op, args)) n).
    Fixpoint eval_ind i n (pf : eval i n) {struct pf} : P i n :=
      match pf with
      | ERef _ _ _ _ _ A B C => HRef _ _ _ _ _ A (Forall2_weaken (fun _ _ D => conj D (eval_ind _ _ D)) _ _ B) C
      | EApp _ _ _ _ A B => HApp _ _ _ _ (Forall2_weaken (fun _ _ C => conj C (eval_ind _ _ C)) _ _ A) B
      end.
  End eval_ind.

  Lemma eval_eval : forall e v1, eval e v1 -> forall v2, eval e v2 -> v1=v2.
  Proof using Type.
    induction 1; inversion 1; subst;
    enough (args' = args'0) by congruence;
    try replace args0 with args in * by congruence.
    { eapply Forall2_map_l in H0.
      eapply Forall2_flip in H0.
      eapply (proj1 (Forall2_map_l _ _ _)) in H5.
      epose proof Forall2_trans H0 H5 as HH.
      eapply Forall2_eq, Forall2_weaken, HH; cbv beta; clear; firstorder. }
    { eapply Forall2_flip in H.
      epose proof Forall2_trans H H4 as HH.
      eapply Forall2_eq, Forall2_weaken, HH; cbv beta; clear; firstorder. }
  Qed.

  Lemma repr_reveals : forall i e, reveals (ExprRef i) e -> repr i e.
  Proof using Type ctx.
    intros ? ? H.
    dependent induction H; econstructor; try eassumption.
    eapply Forall2_weaken; [|eauto]; cbn; intuition eauto.
  Qed.

  Lemma reveals_repr : forall i e, repr i e -> reveals (ExprRef i) e.
  Proof using Type ctx.
    induction 1; econstructor; try eassumption.
    eapply Forall2_weaken; [|eauto]; cbn; intuition eauto.
  Qed.

  Lemma reveal_exists_enough_fuel i e : repr i e -> exists n, reveal n i = e.
  Proof.
    induction 1.
    enough (exists n, map (reveal n) args = args') as [n Hn].
    { eexists (S n); cbn [reveal]; cbv [reveal_step]; rewrite H, Hn; trivial. }
    clear H.
    dependent induction H0.
    { cbn; eauto using O. }
    destruct H as [_ [n' Hn'] ].
    destruct IHForall2 as [n IH].
    exists (max n n').
    cbn [map]; f_equal.
    (* fuel weakening *)
  Admitted.

  Lemma reveals_reveal_repr : forall n i e', reveal n i = e' ->
    forall e, repr i e -> reveals e' e.
  Proof using Type ctx.
    induction n; cbn [reveal]; cbv [reveal_step]; intros; subst.
    { eauto using reveals_repr. }
    inversion H0; subst.
    rewrite H; econstructor.
    clear dependent i.
    induction H1; cbn; eauto.
  Qed.

  Lemma eval_reveal : forall n i, forall v, eval (ExprRef i) v ->
    forall e, reveal n i = e -> eval e v.
  Proof using Type.
    induction n; cbn [reveal]; cbv [reveal_step]; intros; subst; eauto; [].
    inversion H; subst; clear H.
    rewrite H1; econstructor; try eassumption; [].
    eapply (proj1 (Forall2_map_l _ _ _)) in H2.
    clear dependent i; clear dependent v.
    induction H2; cbn; eauto.
  Qed.

  Lemma eval_node_reveal_node : forall n v, eval_node n v ->
    forall f e, reveal_node f n = e -> eval e v.
  Proof using Type.
    cbv [reveal_node]; inversion 1; intros; subst.
    econstructor; eauto.
    eapply (proj1 (Forall2_map_l _ _ _)) in H0; eapply Forall2_map_l.
    eapply Forall2_weaken; try eassumption; []; cbv beta; intros.
    eapply eval_reveal; eauto.
  Qed.
End WithDag.

Definition merge_node (n : node idx) (d : dag) : idx * dag :=
  match List.indexof (node_beq N.eqb n) d with
  | Some i => (N.of_nat i, d)
  | None => (N.of_nat (length d), List.app d (cons n nil))
  end.
Fixpoint merge (e : expr) (d : dag) : idx * dag :=
  match e with
  | ExprRef i => (i, d)
  | ExprApp (op, args) =>
    let idxs_d := List.foldmap merge args d in
    let idxs := if commutative op
                then sortN (fst idxs_d)
                else (fst idxs_d) in
    merge_node (op, idxs) (snd idxs_d)
  end.

Lemma node_beq_sound e x : node_beq N.eqb e x = true -> e = x.
Admitted.

Lemma eval_weaken G d x e n : eval G d e n -> eval G (d ++ [x]) e n.
Proof.
  induction 1; subst; econstructor; eauto.
  { erewrite nth_error_app1; try eassumption; [].
    eapply ListUtil.nth_error_value_length; eassumption. }
  all : eapply Forall2_weaken; [|eassumption].
  { intuition eauto. eapply H2. }
  { intuition eauto. eapply H1. }
Qed.

Lemma interp_op_weaken_symbols G1 G2 o args
  (H : forall (s:symbol) v, G1 s = Some v -> G2 s = Some v)
  : forall v, interp_op G1 o args = Some v -> interp_op G2 o args = Some v.
Proof.
  cbv [interp_op option_map]; intros;
    repeat (BreakMatch.break_match || BreakMatch.break_match_hyps);
    inversion_option; subst;
    try congruence.
  all : eapply H in Heqo0; congruence.
Qed.

Lemma eval_weaken_symbols G1 G2 d e n
  (H : forall s v, G1 s = Some v -> G2 s = Some v)
  : eval G1 d e n -> eval G2 d e n.
Proof.
  induction 1; subst; econstructor;
    intuition eauto using interp_op_weaken_symbols.
  { eapply Forall2_weaken; [|eassumption]; intros ? ? (?&?); eauto. }
  { eapply Forall2_weaken; [|eassumption]; intros ? ? (?&?); eauto. }
Qed.

Lemma eval_eval0 d e n G : eval (fun _ => None) d e n -> eval G d e n.
Proof. eapply eval_weaken_symbols; congruence. Qed.

Lemma permute_commutative G op args n : commutative op = true ->
  interp_op G op args = Some n ->
  forall args', Permutation.Permutation args args' ->
  interp_op G op args' = Some n.
Admitted.

Definition dag_ok G (d : dag) := forall i _r, nth_error d (N.to_nat i) = Some _r -> exists v, eval G d (ExprRef i) v.

Lemma eval_merge_node :
  forall G d, dag_ok G d ->
  forall op args n, let e := (op, args) in
  eval G d (ExprApp (op, List.map ExprRef args)) n ->
  eval G (snd (merge_node e d)) (ExprRef (fst (merge_node e d))) n /\
  dag_ok G (snd (merge_node e d)) /\
  forall i e', eval G d i e' -> eval G (snd (merge_node e d)) i e'.
Proof.
  intros.
  cbv beta delta [merge_node].
  inversion H0; subst.
  case (indexof _ _) eqn:?; cbn; repeat split; eauto.
  { eapply indexof_Some in Heqo; case Heqo as (?&?&?).
    replace x with e in * by (eauto using node_beq_sound); clear H2. (* node_beq -> eq *)
    econstructor; rewrite ?Nnat.Nat2N.id; eauto. }
  { econstructor; eauto.
    { erewrite ?nth_error_app2, ?Nnat.Nat2N.id, Nat.sub_diag by Lia.lia.
      exact eq_refl. }
    eapply Forall2_weaken; [|eauto]; eauto using eval_weaken. }
  { cbv [dag_ok]; intros.
    case (lt_dec (N.to_nat i) (length d)) as [?|?];
      erewrite ?nth_error_app1, ?nth_error_app2 in H1 by Lia.lia.
      { case (H _ _ H1); eauto using eval_weaken. }
      { destruct (N.to_nat i - length d) eqn:?.
        2: { inversion H1. rewrite ListUtil.nth_error_nil_error in H4; inversion H4. }
        eexists. econstructor.
        replace (N.to_nat i) with (length d) by Lia.lia.
        { erewrite ?nth_error_app2, ?Nnat.Nat2N.id, Nat.sub_diag by Lia.lia.
          exact eq_refl. }
        { eapply Forall2_weaken; [|eauto]; eauto using eval_weaken. }
        eauto. } }
  { eauto using eval_weaken. }
Qed.

Require Import Crypto.Util.Tactics.SplitInContext.

Lemma eval_merge G :
  forall e n,
  forall d, dag_ok G d ->
  eval G d e n ->
  eval G (snd (merge e d)) (ExprRef (fst (merge e d))) n /\
  dag_ok G (snd (merge e d)) /\
  forall i e', eval G d i e' -> eval G (snd (merge e d)) i e'.
Proof.
  induction e; intros; eauto; [].
  rename n0 into v.

  set (merge _ _) as m; cbv beta iota delta [merge] in m; fold merge in m.
  destruct n as (op&args).
  repeat match goal with
    m := let x := ?A in @?B x |- _ =>
    let y := fresh x in
    set A as y;
    let m' := eval cbv beta in (B y) in
    change m' in (value of m)
  end.

  inversion H1; clear H1 ; subst.

  cbn [fst snd] in *.
  assert (dag_ok G (snd idxs_d) /\
    Forall2 (fun i v => eval G (snd idxs_d) (ExprRef i) v) (fst idxs_d) args' /\
    forall i e', eval G d i e' -> eval G (snd idxs_d) i e'
  ) as HH; [|destruct HH as(?&?&?)].
  { clear m idxs H6 v op; revert dependent d; revert dependent args'.
    induction H; cbn; intros; inversion H4; subst;
      split_and; pose proof @Forall2_weaken; typeclasses eauto 8 with core. }
  clearbody idxs_d.

  enough (eval G (snd idxs_d) (ExprApp (op, map ExprRef idxs)) v) by
    (unshelve edestruct ((eval_merge_node _ _ ltac:(eassumption) op) idxs v) as (?&?&?); eauto); clear m.

  pose proof length_Forall2 H4; pose proof length_Forall2 H2.

  cbn [fst snd] in *; destruct (commutative op) eqn:?; cycle 1; subst idxs.

  { econstructor; eauto.
    eapply ListUtil.Forall2_forall_iff; rewrite map_length; try congruence; [].
    intros i Hi.
    unshelve (epose proof (proj1 (ListUtil.Forall2_forall_iff _ _ _ _ _ _) H2 i _));
      shelve_unifiable; try congruence; [].
    rewrite ListUtil.map_nth_default_always. eapply H8. }

  pose proof NSort.Permuted_sort (fst idxs_d) as Hperm.
  eapply (Permutation.Permutation_Forall2 Hperm) in H2.
  case H2 as (argExprs&Hperm'&H2).
  eapply permute_commutative in H6; try eassumption; [].
  epose proof Permutation.Permutation_length Hperm.
  epose proof Permutation.Permutation_length Hperm'.

  { econstructor; eauto.
    eapply ListUtil.Forall2_forall_iff; rewrite map_length; try congruence; [|].
    { setoid_rewrite <-H8. setoid_rewrite <-H9. eassumption. }
    intros i Hi.
    unshelve (epose proof (proj1 (ListUtil.Forall2_forall_iff _ _ _ _ _ _) H2 i _));
      shelve_unifiable; try trivial; [|].
    { setoid_rewrite <-H8. setoid_rewrite <-H9. eassumption. }
    rewrite ListUtil.map_nth_default_always. eapply H10. }
  Unshelve. all : exact 0%N.
Qed.

Definition zconst s (z:Z) :=
  const (if z <? 0 then invert_Some (interp0_op (neg s) [Z.abs_N z]) else Z.to_N z)%Z.

Section WithContext.
  Context (ctx : symbol -> option N).
  Fixpoint interp_expr (e : expr) : option N :=
    match e with
    | ExprApp (o, arges) =>
        args <- Option.List.lift (List.map interp_expr arges);
        interp_op ctx o args
    | _ => None
    end%option.
End WithContext.
Definition interp0_expr := interp_expr (fun _ => None).

Lemma eval_interp_expr G e : forall d v, interp_expr G e = Some v -> eval G d e v.
Proof.
  induction e; cbn; try discriminate; intros.
  case n in *; cbn [fst snd] in *.
  destruct (Option.List.lift _) eqn:? in *; try discriminate.
  econstructor; try eassumption; [].
  clear dependent v.
  revert dependent l0.
  induction H; cbn in *.
  { inversion 1; subst; eauto. }
  destruct (interp_expr _) eqn:? in *; cbn in *; try discriminate; [].
  destruct (fold_right _ _ _) eqn:? in *; cbn in *; try discriminate; [].
  specialize (fun d => H d _ eq_refl).
  inversion 1; subst.
  econstructor; trivial; [].
  eapply IHForall; eassumption.
Qed.

Lemma le_land n m : (N.land n m <= m)%N.
Proof.
Admitted.

Module N.
Lemma testbit_ones n i : N.testbit (N.ones n) i = N.ltb i n.
Proof.
  pose proof N.ones_spec_iff n i.
  destruct (N.testbit _ _) eqn:? in*; destruct (N.ltb_spec i n); trivial.
  { pose proof (proj1 H eq_refl); Lia.lia. }
  { pose proof (proj2 H H0). inversion H1. }
Qed.
 
Lemma ones_min m n : N.ones (N.min m n) = N.land (N.ones m) (N.ones n).
Proof.
  eapply N.bits_inj_iff; intro i.
  rewrite N.land_spec.
  rewrite !N.testbit_ones.
  destruct (N.ltb_spec0 i (N.min m n));
  destruct (N.ltb_spec0 i m);
  destruct (N.ltb_spec0 i n);
  Lia.lia.
Qed.
End N.

Lemma land_ones_le n m : (n <= N.ones m -> N.land n (N.ones m) = n)%N.
Proof.
  intros; eapply N.bits_inj_iff; intro i.
  rewrite N.land_spec.
  epose proof N.ones_spec_iff m i.
  destruct (N.testbit (N.ones m) i);
    rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; intuition idtac.
  destruct (N.le_gt_cases m i); try intuition congruence; [].
  clear H1 H2.
  (*
  erewrite N.bits_above_log2; trivial.
  erewrite N.ones_equiv in H.
  assert (n < 2 ^ m)%N by admit; clear H.
  assert (n < 2 ^ i)%N by admit; clear H0.
  eapply N.log2_lt_pow2.
  Search N.log2 N.lt N.pow.
  Search N.ones N.pow.
  *)
Admitted.

Definition bound_expr e : option N := (* e <= r *)
  match e with
  | ExprApp (const v, _) => Some v
  | ExprApp ((old s _ | add s | mul s | shl s | shr s | sar s | neg s | mulhuu s | and s | or s | xor s), _) => Some (N.ones s)
  | ExprApp ((addcarry _ | notaddcarry _ | addoverflow _), _) => Some 1%N
  | _ => None
  end.

Lemma eval_bound_expr G e b : bound_expr e = Some b ->
  forall d v, eval G d e v -> (v <= b)%N.
Proof.
  cbv [bound_expr]; BreakMatch.break_match;
    inversion 2; intros; inversion_option; subst;
    cbv [interp_op] in *;
    BreakMatch.break_match_hyps; inversion_option; subst;
    rewrite ?N.land_ones, ?N.ones_equiv;
    try match goal with |- context [(?a mod ?b)%N] => pose proof N.mod_bound_pos a b ltac:(Lia.lia) end;
    try Lia.lia.
    assert (0 < 2^s)%N as HH by admit. pose proof (H HH). Lia.lia.
    assert (0 < 2^s)%N as HH by admit. pose proof (H HH). Lia.lia.
Admitted.

Definition isCst (e : expr) :=
  match e with ExprApp ((const _), _) => true | _ => false end.

Definition simplify_slice0 :=
  fun e => match e with
    ExprApp (slice 0 s, [(ExprApp ((addZ|mulZ|negZ|shlZ|shrZ|andZ|orZ) as o, args))]) =>
        ExprApp ((match o with addZ=>add s|mulZ=>mul s|negZ=>neg s|shlZ=>shl s|shrZ => shr s|andZ => and s| orZ => or s |_=>old 0%N 999999%N end), args)
      | _ => e end.
Definition simplify_slice_set_slice :=
  fun e => match e with
    ExprApp (slice lo1 s1, [ExprApp (set_slice lo2 s2, [_; e'])]) =>
      if andb (N.eqb lo1 lo2) (N.leb s1 s2) then e' else e | _ => e end.
Definition simplify_set_slice_set_slice :=
  fun e => match e with
    ExprApp (set_slice lo1 s1, [ExprApp (set_slice lo2 s2, [x; e']); y]) =>
      if andb (N.eqb lo1 lo2) (N.leb s2 s1) then ExprApp (set_slice lo1 s1, [x; y]) else e | _ => e end.
Definition simplify_truncate_small :=
  fun e => match e with
    ExprApp (slice 0%N s, [ExprApp (op, args) as e']) =>
      match bound_expr e' with Some b =>
      if N.leb b (N.ones s)
      then e'
      else e | _ => e end | _ => e end.




Definition simplify_and_ones1 :=
  fun e => match e with
        | ExprApp (and 64%N, [ExprApp (const 18446744073709551615, nil); y]) => y
        | _ => e end.

Definition simplify_and_ones2 :=
  fun e => match e with
        | ExprApp (and 64%N, [x; ExprApp (const 18446744073709551615, nil)]) => x    
        | _ => e end.

Definition simplify_bzhi :=
  fun e => match e with
        | ExprApp (bzhi s, [x; ExprApp (const 43, nil)]) => ExprApp (and s, [x;  ExprApp (const 8796093022207, nil)])
        | ExprApp (bzhi s, [x; ExprApp (const 44, nil)]) => ExprApp (and s, [x;  ExprApp (const 17592186044415, nil)])
        | ExprApp (bzhi s, [x; ExprApp (const 51, nil)]) => ExprApp (and s, [x;  ExprApp (const 2251799813685247, nil)])
        | ExprApp (bzhi s, [x; ExprApp (const 56, nil)]) => ExprApp (and s, [x;  ExprApp (const 72057594037927935, nil)])
        | ExprApp (bzhi s, [x; ExprApp (const 57, nil)]) => ExprApp (and s, [x;  ExprApp (const 144115188075855871, nil)])
        | ExprApp (bzhi s, [x; ExprApp (const 58, nil)]) => ExprApp (and s, [x;  ExprApp (const 288230376151711743, nil)])                   | _ => e end.

Definition simplify_expr : expr -> expr :=
  List.fold_left (fun e f => f e)
  [fun e => match interp0_expr e with
            | Some v => ExprApp (const v, nil)
            | _ => e end
  ;simplify_truncate_small
  ;simplify_slice0
  ;simplify_set_slice_set_slice
  ;simplify_slice_set_slice
  ;simplify_and_ones1
  ;simplify_and_ones2      
  ;simplify_bzhi
      
  ;fun e => match e with
    ExprApp (o, args) =>
    if associative o then
      ExprApp (o, List.flat_map (fun e' =>
        match e' with
        | ExprApp (o', args') => if op_beq o o' then args' else [e']
        | _ => [e'] end) args)
    else e | _ => e end
  ;fun e => match e with
    ExprApp (o, args) =>
    if commutative o then
    let csts_exprs := List.partition isCst args in
    match interp0_expr (ExprApp (o, fst csts_exprs)) with None => e | Some v =>
    ExprApp (o, ExprApp (const v, nil):: snd csts_exprs)
    end else e | _ => e end
  ;fun e => match e with
    ExprApp (slice 0 s, [a]) =>
      match bound_expr a with Some b =>
      if N.leb b (N.ones s)
      then a else e | _ => e end | _ => e end
  ;fun e => match e with
    ExprApp (o, args) =>
    match identity o with
    | Some i =>
        let args := List.filter (fun a => negb (option_beq N.eqb (interp0_expr a) (Some i))) args in
        match args with
        | nil => ExprApp (const i, nil)
        | cons a nil => a
        | _ => ExprApp (o, args)
        end
    | _ => e end | _ => e end
  ;fun e => match e with ExprApp (xor _,[x;y]) =>
    if expr_beq x y then ExprApp (const 0, nil) else e | _ => e end
                    
  ]%N%bool.
Definition simplify (dag : dag) (e : node idx) : expr :=
  simplify_expr (reveal_node dag 2 e).

Lemma eval_simplify_expr c d e v : eval c d e v -> eval c d (simplify_expr e) v.
Proof.
  intros H; cbv [simplify_expr].

  Strategy 10000 [simplify_slice0 simplify_slice_set_slice simplify_truncate_small simplify_and_ones1 simplify_and_ones2 simplify_bzhi].
  Local Opaque simplify_slice0 simplify_slice_set_slice simplify_truncate_small simplify_and_ones1 simplify_and_ones2 simplify_bzhi.
  repeat match goal with (* one goal per rewrite rule *)
  | |- context G [fold_left ?f (cons ?r ?rs) ?e] =>
    let re := fresh "e" in
    let e_re := eval cbv beta in (r e) in pose (e_re) as re;
    let g := context G [fold_left f rs re] in time change g;
    assert (eval c d re v); [ subst re | clearbody re;
        clear dependent e; rename re into e ]
  | |- context G [fold_left ?f nil ?e] => eassumption
  end.
  Local Transparent simplify_slice0 simplify_slice_set_slice simplify_truncate_small simplify_and_ones1 simplify_and_ones2 simplify_bzhi.
  all : cbv [simplify_slice0 simplify_slice_set_slice simplify_truncate_small simplify_and_ones1 simplify_and_ones2 simplify_bzhi] in *.

  all : repeat match goal with
               | _ => solve [trivial]
               | _ => progress cbn [fst snd interp_op option_map] in *
               | _ => progress inversion_option
               | H: interp0_expr _ = Some _ |- _ => eapply eval_interp_expr in H; instantiate (1:=d) in H
               | H: bound_expr _ = Some _ |- _ => eapply eval_bound_expr in H; eauto; [ ]
               | H : eval _ _ ?e _ |- _ => assert_fails (is_var e); inversion H; clear H; subst
               | H : Forall2 (eval _ _) ?es _ |- _ => assert_fails (is_var es); inversion H; clear H; subst

               | H : andb _ _ = true |- _ => eapply Bool.andb_prop in Heqb; case Heqb as (?&?)
               | H : N.eqb ?n _ = true |- _ => eapply N.eqb_eq in H; subst n
               | H : expr_beq ?a ?b = true |- _ => replace a with b in * by admit; clear H

               | H : (?x <=? ?y)%N = ?b |- _ => is_constructor b; destruct (N.leb_spec x y); (inversion H || clear H)
               | H : eval _ ?d ?e ?v1, G: eval _ ?d ?e ?v2 |- _ =>
                   assert_fails (constr_eq v1 v2);
                   eapply (eval_eval _ d e v1 H v2) in G
               | H : _ = ?v |- _ => is_var v; progress subst v
               | H : ?v = _ |- _ => is_var v; progress subst v
               | |- eval _ ?d ?e ?v =>
                   match goal with
                     H : eval _ d e ?v' |- _ =>
                         let Heq := fresh in
                         enough (Heq : v = v') by (rewrite Heq; exact H);
                         clear H; try clear e
                   end
               | _ => progress BreakMatch.break_match
               end.
  { econstructor; eauto; []; cbn [interp_op option_map].
    f_equal; eauto using eval_eval, eval_eval0. }
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  { econstructor; eauto; []; cbn [interp_op fold_right].
    rewrite N.lxor_0_r, N.lxor_nilpotent; trivial. }
Admitted.

Lemma eval_simplify G d n v : eval_node G d n v -> eval G d (simplify d n) v.
Proof. eauto using eval_simplify_expr, eval_node_reveal_node. Qed.

Definition reg_state := Tuple.tuple (option idx) 16.
Definition flag_state := Tuple.tuple (option idx) 6.
Definition mem_state := list (idx * idx).

Definition get_flag (st : flag_state) (f : FLAG) : option idx
  := let '(cfv, pfv, afv, zfv, sfv, ofv) := st in
     match f with
     | CF => cfv
     | PF => pfv
     | AF => afv
     | ZF => zfv
     | SF => sfv
     | OF => ofv
     end.
Definition set_flag_internal (st : flag_state) (f : FLAG) (v : option idx) : flag_state
  := let '(cfv, pfv, afv, zfv, sfv, ofv) := st in
     (match f with CF => v | _ => cfv end,
      match f with PF => v | _ => pfv end,
      match f with AF => v | _ => afv end,
      match f with ZF => v | _ => zfv end,
      match f with SF => v | _ => sfv end,
      match f with OF => v | _ => ofv end).
Definition set_flag (st : flag_state) (f : FLAG) (v : idx) : flag_state
  := set_flag_internal st f (Some v).
Definition havoc_flag (st : flag_state) (f : FLAG) : flag_state
  := set_flag_internal st f None.
Definition havoc_flags : flag_state
  := (None, None, None, None, None, None).

Definition get_reg (st : reg_state) (ri : nat) : option idx
  := Tuple.nth_default None ri st.
Definition set_reg (st : reg_state) ri (i : idx) : reg_state
  := Tuple.from_list_default None _ (ListUtil.set_nth
       ri
       (Some i)
       (Tuple.to_list _ st)).

Definition load (a : idx) (s : mem_state) : option idx :=
  option_map snd (find (fun p => fst p =? a)%N s).
Definition store (a v : idx) (s : mem_state) : option mem_state :=
  n <- indexof (fun p => fst p =? a)%N s;
  Some (ListUtil.update_nth n (fun ptsto => (fst ptsto, v)) s).

Record symbolic_state := { dag_state :> dag ; symbolic_reg_state :> reg_state ; symbolic_flag_state :> flag_state ; symbolic_mem_state :> mem_state }.
Definition update_dag_with (st : symbolic_state) (f : dag -> dag) : symbolic_state
  := {| dag_state := f st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_reg_with (st : symbolic_state) (f : reg_state -> reg_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := f st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_flag_with (st : symbolic_state) (f : flag_state -> flag_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := f st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_mem_with (st : symbolic_state) (f : mem_state -> mem_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := f st.(symbolic_mem_state) |}.

Global Instance show_reg_state : Show reg_state := fun st =>
  show (List.map (fun '(n, v) => (widest_register_of_index n, v)) (ListUtil.List.enumerate (Option.List.map id (Tuple.to_list _ st)))).

Global Instance show_flag_state : Show flag_state :=
  fun '(cfv, pfv, afv, zfv, sfv, ofv) => (
  "(*flag_state*)(CF="++show cfv
  ++" PF="++show pfv
  ++" AF="++show afv
  ++" ZF="++show zfv
  ++" SF="++show sfv
  ++" ZF="++show zfv
  ++" OF="++show ofv++")")%string.
Global Instance show_lines_dag : ShowLines dag := (fun d =>
  ["(*dag*)["]
  ++List.map (fun '(i, v) =>"(*"++show i ++"*) " ++ show v++";")%string (@ListUtil.List.enumerate (node idx) d)
  ++["]"])%list%string.
Global Instance show_lines_mem_state : ShowLines mem_state :=
  @show_lines_list _ ShowLines_of_Show.

Global Instance ShowLines_symbolic_state : ShowLines symbolic_state :=
 fun X : symbolic_state =>
 match X with
 | {|
     dag_state := ds;
     symbolic_reg_state := rs;
     symbolic_flag_state := fs;
     symbolic_mem_state := ms
   |} =>
   ["(*symbolic_state*) {|";
   "  dag_state :="] ++ show_lines ds ++ [";";
   ("  symbolic_reg_state := " ++ show rs ++ ";")%string;
   ("  symbolic_flag_state := " ++ show fs ++";")%string;
   "  symbolic_mem_state :="] ++show_lines ms ++ [";";
   "|}"]
 end%list%string.


Module error.
  Variant error :=
  | nth_error_dag (_ : nat)

  | get_flag (f : FLAG)
  | get_reg (r : REG)
  | load (a : idx)
  | store (a v : idx)
  | set_const (_ : CONST) (_ : idx)
  | expected_const (_ : idx)

  | unimplemented_instruction (_ : NormalInstruction)
  | ambiguous_operation_size (_ : NormalInstruction)

  | failed_to_unify (_ : list (expr * (option idx * option idx))).

  Global Instance Show_error : Show error := fun e =>
   match e with
   | nth_error_dag n => "error.nth_error_dag " ++ show n
   | get_flag f => "error.get_flag " ++ show f
   | get_reg r => "error.get_reg " ++ show r
   | load a => "error.load " ++ show a
   | store a v => "error.store " ++ show a ++ " " ++ show v
   | set_const c i => "error.set_const " ++ show c ++ " " ++ show i
   | expected_const i => "error.expected_const " ++ show i
   | unimplemented_instruction n => "error.unimplemented_instruction " ++ show n
   | ambiguous_operation_size n => "error.ambiguous_operation_size " ++ show n
   | failed_to_unify l => "error.failed_to_unify " ++ show l
   end%string.
End error.
Notation error := error.error.

Definition M T := symbolic_state -> ErrorT (error * symbolic_state) (T * symbolic_state).
Definition ret {A} (x : A) : M A :=
  fun s => Success (x, s).
Definition err {A} (e : error) : M A :=
  fun s => Error (e, s).
Definition some_or {A} (f : symbolic_state -> option A) (e : error) : M A :=
  fun st => match f st with Some x => Success (x, st) | None => Error (e, st) end.
Definition bind {A B} (x : M A) (f : A -> M B) : M B :=
  fun s => (x_s <- x s; f (fst x_s) (snd x_s))%error.
Declare Scope x86symex_scope.
Delimit Scope x86symex_scope with x86symex.
Bind Scope x86symex_scope with M.
Notation "x <- y ; f" := (bind y (fun x => f%x86symex)) : x86symex_scope.
Section MapM. (* map over a list in the state monad *)
  Context [A B] (f : A -> M B).
  Fixpoint mapM (l : list A) : M (list B) :=
    match l with
    | nil => ret nil
    | cons a l => b <- f a; bs <- mapM l; ret (cons b bs)
    end%x86symex.
End MapM.
Definition mapM_ [A B] (f: A -> M B) l : M unit := _ <- mapM f l; ret tt.

Definition GetFlag f : M idx :=
  some_or (fun s => get_flag s f) (error.get_flag f).
Definition GetReg64 ri : M idx :=
  some_or (fun st => get_reg st ri) (error.get_reg (widest_register_of_index ri)).
Definition Load64 (a : idx) : M idx := some_or (load a) (error.load a).
Definition SetFlag f i : M unit :=
  fun s => Success (tt, update_flag_with s (fun s => set_flag s f i)).
Definition HavocFlags : M unit :=
  fun s => Success (tt, update_flag_with s (fun _ => Tuple.repeat None 6)).
Definition SetReg64 rn i : M unit :=
  fun s => Success (tt, update_reg_with s (fun s => set_reg s rn i)).
Definition Store64 (a v : idx) : M unit :=
  ms <- some_or (store a v) (error.store a v);
  fun s => Success (tt, update_mem_with s (fun _ => ms)).
Definition Merge (e : expr) : M idx := fun s =>
  let i_dag := merge e s in
  Success (fst i_dag, update_dag_with s (fun _ => snd i_dag)).
Definition App (n : node idx) : M idx :=
  fun s => Merge (simplify s n) s.
Definition Reveal n (i : idx) : M expr :=
  fun s => Success (reveal s n i, s).
Definition RevealConst (i : idx) : M N :=
  x <- Reveal 1 i;
  match x with
  | ExprApp (const n, nil) => ret n
  | _ => err (error.expected_const i)
  end.

Definition GetReg r : M idx :=
  let '(rn, lo, sz) := index_and_shift_and_bitcount_of_reg r in
  v <- GetReg64 rn;
  App ((slice lo sz), [v]).
Definition SetReg r (v : idx) : M unit :=
  let '(rn, lo, sz) := index_and_shift_and_bitcount_of_reg r in
  if N.eqb sz 64
  then SetReg64 rn v (* works even if old value is unspecified *)
  else old <- GetReg64 rn;
       v <- App ((set_slice lo sz), [old; v]);
       SetReg64 rn v.

Class AddressSize := address_size : OperationSize.
Definition Address {sa : AddressSize} (a : MEM) : M idx :=
  base <- GetReg a.(mem_reg);
  index <- match a.(mem_extra_reg) with
           | Some r => GetReg r
           | None => App ((const 0), nil)
           end;
  offset <- App ((zconst sa (match a.(mem_offset) with
                             | Some s => s
                             | None => 0 end)), nil);
  bi <- App (add sa, [base; index]);
  App (add sa, [bi; offset]).

Definition Load {s : OperationSize} {sa : AddressSize} (a : MEM) : M idx :=
  addr <- Address a;
  v <- Load64 addr;
  if N.eqb s 64%N
  then ret v
  else App ((slice 0 (Syntax.operand_size a s)), [v]).

Definition Store {s : OperationSize} {sa : AddressSize} (a : MEM) v : M unit :=
  addr <- Address a;
  if N.eqb s 64%N
  then Store64 addr v
  else old <- Load64 addr;
       v <- App (set_slice 0 (Syntax.operand_size a s), [old; v])%N;
       Store64 addr v.

(* note: this could totally just handle truncation of constants if semanics handled it *)
Definition GetOperand {s : OperationSize} {sa : AddressSize} (o : ARG) : M idx :=
  match o with
  | Syntax.const a => App (zconst sa a, [])
  | mem a => Load a
  | reg r => GetReg r
  end.

Definition SetOperand {s : OperationSize} {sa : AddressSize} (o : ARG) (v : idx) : M unit :=
  match o with
  | Syntax.const a => err (error.set_const a v)
  | mem a => Store a v
  | reg a => SetReg a v
  end.

Local Unset Elimination Schemes.
Inductive pre_expr : Set :=
| PreARG (_ : ARG)
| PreFLG (_ : FLAG)
| PreApp (_ : op) (_ : list pre_expr).
(* note: need custom induction principle *)
Local Set Elimination Schemes.
Local Coercion PreARG : ARG >-> pre_expr.
Local Coercion PreFLG : FLAG >-> pre_expr.
Example __testPreARG_boring : ARG -> list pre_expr := fun x : ARG => @cons pre_expr x nil.
(*
Example __testPreARG : ARG -> list pre_expr := fun x : ARG => [x].
*)

Fixpoint Symeval {s : OperationSize} {sa : AddressSize} (e : pre_expr) : M idx :=
  match e with
  | PreARG o => GetOperand o
  | PreFLG f => GetFlag f
  | PreApp op args =>
      idxs <- mapM Symeval args;
      App (op, idxs)
  end.

Notation "f @ ( x , y , .. , z )" := (PreApp f (@cons pre_expr x (@cons pre_expr y .. (@cons pre_expr z nil) ..))) (at level 10) : x86symex_scope.
Definition SymexNormalInstruction (instr : NormalInstruction) : M unit :=
  let sa : AddressSize := 64%N in
  match Syntax.operation_size instr with Some s =>
  let s : OperationSize := s in
  match instr.(Syntax.op), instr.(args) with
  | (mov | movzx), [dst; src] => (* Note: unbundle when switching from N to Z *)
    v <- GetOperand src;
    SetOperand dst v
  | xchg, [a; b] => (* Note: unbundle when switching from N to Z *)
    va <- GetOperand a;
    vb <- GetOperand b;
    _ <- SetOperand a vb;
    SetOperand b va
  | cmovc, [dst; src] =>
    v <- Symeval (selectznz@(CF, dst, src));
    SetOperand dst v
  | cmovnz, [dst; src] =>
    v <- Symeval (selectznz@(ZF, src, dst));
    SetOperand dst v
  | seto, [dst] =>
    of <- GetFlag OF;
    SetOperand dst of
  | setc, [dst] =>
    cf <- GetFlag CF;
    SetOperand dst cf
  | Syntax.add, [dst; src] =>
    v <- Symeval (add s@(dst, src));
    c <- Symeval (addcarry s@(dst, src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    SetFlag CF c
  | Syntax.adc, [dst; src] =>
    v <- Symeval (add s@(dst, src, CF));
    c <- Symeval (addcarry s@(dst, src, CF));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    SetFlag CF c
  | (adcx|adox) as op, [dst; src] =>
    let f := match op with adcx => CF | _ => OF end in
    v <- Symeval (add s@(dst, src, f));
    c <- Symeval (addcarry s@(dst, src, f));
    _ <- SetOperand dst v;
    SetFlag f c
  | Syntax.sub, [dst; src] =>
    v <- Symeval (add s@(dst, PreApp (neg s) [PreARG src]));
    _ <- SetOperand dst v;
    HavocFlags
  | lea, [dst; mem src] =>
    a <- Address src;
    SetOperand dst a
  | imul, ([dst as src1; src2] | [dst; src1; src2]) =>
    v <- Symeval (mul s@(src1,src2));
    _ <- SetOperand dst v;
    HavocFlags
  | Syntax.xor, [dst; src] =>
    v <- Symeval (xor s@(dst,src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    zero <- Symeval (PreApp (const 0) nil);
    _ <- SetFlag CF zero;
    SetFlag OF zero
  | Syntax.and, [dst; src] =>
    v <- Symeval (and s@(dst,src));
    _ <- SetOperand dst v;
    HavocFlags
  | Syntax.bzhi, [dst; src; cnt] =>
    cnt <- GetOperand cnt;
    cnt <- RevealConst cnt;
    v <- Symeval (and s@(dst,PreApp (const (N.ones (N.land cnt (N.ones (N.log2 s))))) nil));
    _ <- SetOperand dst v;
    HavocFlags
  | mulx, [hi; lo; src2] =>
    let src1 : ARG := rdx in
    vl <- Symeval (mul s@(src1,src2));
    vh <- Symeval (mulhuu s@(src1,src2));
    _ <- SetOperand lo vl;
         SetOperand hi vh
   | Syntax.shr, [dst; cnt] =>
    v <- Symeval (shr s@(dst, cnt));
    _ <- SetOperand dst v;
    HavocFlags
   | Syntax.sar, [dst; cnt] =>
    x <- GetOperand dst;
    c <- GetOperand cnt; c <- Reveal 1 c;
    y <- Symeval (sar s@(dst, cnt));
    _ <- SetOperand dst y;
    _ <- HavocFlags;
    if match c with ExprApp (const 1%N, nil) => true | _ => false end
    then (
      cf <- App ((slice 0 1), cons (x) nil);
      _ <- SetFlag CF cf;
      zero <- Symeval (PreApp (const 0) nil); SetFlag OF zero)
    else ret tt
  | shrd, [lo as dst; hi; cnt] =>
    let cnt' := add s@(Z.of_N s, PreApp (neg s) [PreARG cnt]) in
    v <- Symeval (or s@(shr s@(lo, cnt), shl s@(hi, cnt')));
    _ <- SetOperand dst v;
    HavocFlags
  | inc, [dst] =>
    v <- Symeval (add s@(dst, PreARG 1%Z));
    o <- Symeval (addoverflow s@(dst, PreARG 1%Z));
    _ <- SetOperand dst v;
    cf <- GetFlag CF; _ <- HavocFlags;
    _ <- SetFlag CF cf; SetFlag OF o
  | dec, [dst] =>
    orig <- GetOperand dst; orig <- Reveal 1 orig;
    v <- Symeval (add s@(dst, PreApp (neg s) [PreARG 1%Z]));
    _ <- SetOperand dst v;
    cf <- GetFlag CF; _ <- HavocFlags; _ <- SetFlag CF cf;
    if match orig with ExprApp (const n, nil) => n =? 0 | _ => false end
    then zero <- Symeval (PreApp (const 0) nil); SetFlag OF zero else SetFlag CF cf
  | test, [a;b] =>
      _ <- HavocFlags;
    zero <- Symeval (PreApp (const 0) nil);
    _ <- SetFlag CF zero;
    SetFlag OF zero
      (* note: ZF *)
  | _, _ => err (error.unimplemented_instruction instr)
 end
  | _ =>
  match instr.(Syntax.op), instr.(args) with
  | clc, [] => zero <- @Symeval 1 _ (@PreApp (const 0) nil); SetFlag CF zero
  | Syntax.ret, [] => ret tt
  | _, _ => err (error.ambiguous_operation_size instr) end end%N%x86symex.

Definition SymexNormalInstructions := fun st is => mapM_ SymexNormalInstruction is st.

Definition invert_rawline l := match l.(rawline) with INSTR instr => Some instr | _ => None end.
Definition SymexLines st (lines : list Syntax.Line) :=
  SymexNormalInstructions st (Option.List.map invert_rawline lines).
