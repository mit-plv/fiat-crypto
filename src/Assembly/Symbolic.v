Require Crypto.Assembly.Parse.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Crypto.Util.Tuple.
Require Import Util.OptionList.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Testbit.

Require Import coqutil.Z.bitblast.

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
    Lemma indexof_Some l i (H : indexof l = Some i) :
      exists a, nth_error l i = Some a /\ f a = true.
    Proof.
      revert dependent i; induction l; cbn in *; try congruence; [].
      destruct (f a) eqn:?; cbn.
      { inversion 1; subst. eexists. split. exact eq_refl. eassumption. }
      { cbv [option_map]; destruct (indexof l) eqn:?; inversion 1; subst; eauto. }
    Qed.
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
Local Set Decidable Equality Schemes.
Definition symbol := N.

Class OperationSize := operation_size : N.
Global Instance Show_OperationSize : Show OperationSize := show_N.

Section S.
Implicit Type s : OperationSize.
Variant op := old s (_:symbol) | const (_ : Z) | add s | addcarry s | subborrow s | addoverflow s | neg s | shl s | shr s | sar s | rcr s | and s | or s | xor s | slice (lo sz : N) | mul s | set_slice (lo sz : N) | selectznz | iszero (* | ... *)
  | addZ | mulZ | negZ | shlZ | shrZ | andZ | orZ | xorZ | addcarryZ s | subborrowZ s.
Definition op_beq a b := if op_eq_dec a b then true else false.
End S.

Global Instance Show_op : Show op := fun o =>
  match o with
  | old s n => "old " ++ show s ++ " " ++ show n
  | const n => "const " ++ show n
  | add s => "add " ++ show s
  | addcarry s => "addcarry " ++ show s
  | subborrow s => "subborrow " ++ show s
  | addoverflow s => "addoverflow " ++ show s
  | neg s => "neg " ++ show s
  | shl s => "shl " ++ show s
  | shr s => "shr " ++ show s
  | sar s => "sar " ++ show s
  | rcr s => "rcr " ++ show s
  | and s => "and " ++ show s
  | or s => "or " ++ show s
  | xor s => "xor " ++ show s
  | slice lo sz => "slice " ++ show lo ++ " " ++ show sz
  | mul s => "mul " ++ show s
  | set_slice lo sz => "set_slice " ++ show lo ++ " " ++ show sz
  | selectznz => "selectznz"
  | iszero => "iszero"
  | addZ => "addZ"
  | mulZ => "mulZ"
  | negZ => "negZ"
  | shlZ => "shlZ"
  | shrZ => "shrZ"
  | andZ => "andZ"
  | orZ => "orZ"
  | xorZ => "xorZ"
  | addcarryZ s => "addcarryZ " ++ show s
  | subborrowZ s => "subborrowZ " ++ show s
  end%string.

Definition associative o := match o with add _|mul _|mulZ|or _|and _=> true | _ => false end.
Definition commutative o := match o with add _|addcarry _|addoverflow _|mul _|mulZ => true | _ => false end.
Definition identity o := match o with add _| mul N0=>None|mul _|mulZ=>Some 1%Z | and s => Some (Z.ones (Z.of_N s)) |_=> None end.

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

Lemma op_beq_spec a b : BoolSpec (a=b) (a<>b) (op_beq a b).
Proof. cbv [op_beq]; destruct (op_eq_dec a b); constructor; congruence. Qed.
Fixpoint expr_beq (X Y : expr) {struct X} : bool :=
  match X, Y with
  | ExprRef x, ExprRef x0 => N.eqb x x0
  | ExprApp x, ExprApp x0 =>
      Prod.prod_beq _ _ op_beq (ListUtil.list_beq expr expr_beq) x x0
  | _, _ => false
  end.
Lemma expr_beq_spec a b : BoolSpec (a=b) (a<>b) (expr_beq a b).
Proof.
  revert b; induction a, b; cbn.
  1: destruct (N.eqb_spec i i0); constructor; congruence.
  1,2: constructor; congruence.
  destruct n, n0; cbn.
  destruct (op_beq_spec o o0); cbn in *; [subst|constructor; congruence].
  revert l0; induction H, l0; cbn; try (constructor; congruence); [].
  destruct (H e); cbn; try (constructor; congruence); []; subst.
  destruct (IHForall l0); [left|right]; congruence.
Qed.
Lemma expr_beq_true a b : expr_beq a b = true -> a = b.
Proof. destruct (expr_beq_spec a b); congruence. Qed.

Require Import Crypto.Util.Option Crypto.Util.Notations Coq.Lists.List.
Import ListNotations.

Section WithContext.
  Context (ctx : symbol -> option Z).
  Definition signed s n : Z := (Z.land (Z.shiftl 1 (Z.of_N s-1) + n) (Z.ones (Z.of_N s)) - Z.shiftl 1 (Z.of_N s-1))%Z.
  Definition interp_op o (args : list Z) : option Z :=
    let keep n x := Z.land x (Z.ones (Z.of_N n)) in
    match o, args with
    | old s x, nil => match ctx x with Some v => Some (keep s v) | None => None end
    | const z, nil => Some z
    | add s, args => Some (keep s (List.fold_right Z.add 0 args))
    | addcarry s, args =>
        Some (Z.shiftr (List.fold_right Z.add 0 args) (Z.of_N s) mod 2)
    | subborrow s, cons a args' =>
        Some ((- Z.shiftr (a - List.fold_right Z.add 0 args') (Z.of_N s)) mod 2)
    | addoverflow s, args => Some (Z.b2z (negb (Z.eqb
      (signed s (keep s (List.fold_right Z.add 0 args)))
                         (List.fold_right Z.add 0%Z (List.map (signed s) args)))))
    | neg s, [a] => Some (keep s (- a))
    | shl s, [a; b] => Some (keep s (Z.shiftl a b))
    | shr s, [a; b] => Some (keep s (Z.shiftr a b))
    | sar s, [a; b] => Some (keep s (Z.shiftr (signed s a) b))
    | rcr s, [v1; cf; cnt] => Some (
        let v1c := Z.lor v1 (Z.shiftl cf (Z.of_N s)) in
        let l := Z.lor v1c (Z.shiftl v1 (1+Z.of_N s)) in
        keep s (Z.shiftr l cnt))
    | and s, args => Some (keep s (List.fold_right Z.land (-1) args))
    | or s, args => Some (keep s (List.fold_right Z.lor 0 args))
    | xor s, args => Some (keep s (List.fold_right Z.lxor 0 args))
    | slice lo sz, [a] => Some (keep sz (Z.shiftr a (Z.of_N lo)))
    | mul s, args => Some (keep s (List.fold_right Z.mul 1 args))
    | set_slice lo sz, [a; b] =>
        Some (Z.lor (Z.shiftl (keep sz b) (Z.of_N lo))
                    (Z.ldiff a (Z.shiftl (Z.ones (Z.of_N sz)) (Z.of_N lo))))
    | selectznz, [c; a; b] => Some (if Z.eqb c 0 then a else b)
    | iszero, [a] => Some (Z.b2z (Z.eqb a 0))
    | addZ, args => Some (List.fold_right Z.add 0 args)
    | mulZ, args => Some (List.fold_right Z.mul 1 args)
    | negZ, [a] => Some (Z.opp a)
    | shlZ, [a; b] => Some (Z.shiftl a b)
    | shrZ, [a; b] => Some (Z.shiftr a b)
    | andZ, args => Some (List.fold_right Z.land (-1) args)
    | orZ, args => Some (List.fold_right Z.lor 0 args)
    | xorZ, args => Some (List.fold_right Z.lxor 0 args)
    | addcarryZ s, args => Some (Z.shiftr (List.fold_right Z.add 0 args) (Z.of_N s))
    | subborrowZ s, cons a args' => Some (- Z.shiftr (a - List.fold_right Z.add 0 args') (Z.of_N s))
    | _, _ => None
    end%Z.
End WithContext.
Definition interp0_op := interp_op (fun _ => None).

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

Lemma interp_op_interp0_op o a v (H : interp0_op o a = Some v)
  : forall G, interp_op G o a = Some v.
Proof. intros; eapply interp_op_weaken_symbols in H; eauto; discriminate. Qed.

Definition node_beq [A : Set] (arg_eqb : A -> A -> bool) : node A -> node A -> bool :=
  Prod.prod_beq _ _ op_beq (ListUtil.list_beq _ arg_eqb).

Definition dag := list (node idx).

Section WithDag.
  Context (ctx : symbol -> option Z) (dag : dag).
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
  Inductive eval : expr -> Z -> Prop :=
  | ERef i op args args' n
    (_:List.nth_error dag (N.to_nat i) = Some (op, args))
    (_:List.Forall2 eval (map ExprRef args) args')
    (_:interp_op ctx op args' = Some n)
    : eval (ExprRef i) n
  | EApp op args args' n
    (_:List.Forall2 eval args args')
    (_:interp_op ctx op args' = Some n)
    : eval (ExprApp (op, args)) n.

  Variant eval_node : node idx -> Z -> Prop :=
  | ENod op args args' n
    (_:List.Forall2 eval (map ExprRef args) args')
    (_:interp_op ctx op args' = Some n)
    : eval_node (op, args) n.


  Section eval_ind.
    Context (P : expr -> Z -> Prop)
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

  Lemma eval_eval_Forall2 xs vxs (_ : Forall2 eval xs vxs)
    vys (_ : Forall2 eval xs vys) : vxs = vys.
  Proof.
    revert dependent vys; induction H; inversion 1; subst;
      eauto; eauto using f_equal2, IHForall2, eval_eval.
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
Proof.
  eapply Prod.internal_prod_dec_bl.
  { intros X Y; destruct (op_beq_spec X Y); congruence. }
  { intros X Y. eapply ListUtil.internal_list_dec_bl, N.eqb_eq. }
Qed.

Lemma eval_weaken G d x e n : eval G d e n -> eval G (d ++ [x]) e n.
Proof.
  induction 1; subst; econstructor; eauto.
  { erewrite nth_error_app1; try eassumption; [].
    eapply ListUtil.nth_error_value_length; eassumption. }
  all : eapply Forall2_weaken; [|eassumption].
  { intuition eauto. eapply H2. }
  { intuition eauto. eapply H1. }
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

Lemma permute_add xs ys : Permutation.Permutation xs ys -> fold_right Z.add Z0 xs = fold_right Z.add Z0 ys.
Proof. induction 1; cbn; try Lia.lia. Qed.
Lemma permute_mul xs ys : Permutation.Permutation xs ys -> fold_right Z.mul 1%Z xs = fold_right Z.mul 1%Z ys.
Proof. induction 1; cbn; try Lia.lia. Qed.
Lemma permute_commutative G op args n : commutative op = true ->
  interp_op G op args = Some n ->
  forall args', Permutation.Permutation args args' ->
  interp_op G op args' = Some n.
Proof.
  destruct op; inversion 1; cbn; intros ? ? Hp.
  { erewrite <-permute_add; eauto. }
  { erewrite <-permute_add; eauto. }
  { erewrite <-permute_add; eauto.
    erewrite <-(permute_add _ (map _ args')); eauto using Permutation.Permutation_map. }
  { erewrite <-permute_mul; eauto. }
  { erewrite <-permute_mul; eauto. }
Qed.

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
Require Import coqutil.Tactics.autoforward coqutil.Decidable coqutil.Tactics.Tactics.
Global Set Default Goal Selector "1".

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
  Unshelve. all : constructor.
Qed.

Definition zconst s (z:Z) := const (Z.land z (Z.ones (Z.of_N s)))%Z.

Section WithContext.
  Context (ctx : symbol -> option Z).
  Fixpoint interp_expr (e : expr) : option Z :=
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

Lemma eval_interp0_expr e v (H : interp0_expr e = Some v) : forall G d, eval G d e v.
Proof.
  cbv [interp0_expr]; intros.
  eapply eval_interp_expr, eval_weaken_symbols in H; [eassumption|congruence].
Qed.

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

Local Open Scope Z_scope.

Fixpoint bound_expr e : option Z := (* e <= r *)
  match e with
  | ExprApp (const v, _) => if Z.leb 0 v then Some v else None
  | ExprApp (add s, args) =>
      Some  match Option.List.lift (List.map bound_expr args) with
            | Some bounds => Z.min (List.fold_right Z.add 0%Z bounds) (Z.ones (Z.of_N s))
            | None => Z.ones (Z.of_N s)
            end
  | ExprApp (selectznz, [c;a;b]) =>
      match bound_expr a, bound_expr b with
      | Some a, Some b => Some (Z.max a b)
      | _, _ => None
      end
  | ExprApp (set_slice 0 w, [a;b]) =>
      match bound_expr a, bound_expr b with
      | Some a, Some b => Some (Z.lor
                                  (Z.land (Z.ones (Z.succ (Z.log2 b))) (Z.ones (Z.of_N w)))
                                  (Z.ldiff (Z.ones (Z.succ (Z.log2 a))) (Z.ones (Z.of_N w))))
      | _, _ => None
      end
  | ExprApp ((old s _ | slice _ s | mul s | shl s | shr s | sar s | neg s | and s | or s | xor s), _) => Some (Z.ones (Z.of_N s))
  | ExprApp ((addcarry _ | subborrow _ | addoverflow _ | iszero), _) => Some 1
  | _ => None
  end%Z.

Import coqutil.Tactics.Tactics.
Ltac t:= match goal with
  | _ => progress intros
  | H : eval _ _ (ExprApp _) _ |- _ => inversion H; clear H; subst
  | H : Forall _ (cons _ _) |- _ => inversion H; clear H; subst
  | H : Forall _ nil |- _ => inversion H; clear H; subst
  | H : Forall2 _ (cons _ _) _ |- _ => inversion H; clear H; subst
  | H : Forall2 _ nil _ |- _ => inversion H; clear H; subst
  | H : Forall2 _ _ (cons _ _) |- _ => inversion H; clear H; subst
  | H : Forall2 _ _ nil |- _ => inversion H; clear H; subst
  | H : _ = true |- _ => autoforward with typeclass_instances in H
  | H : forall b, _ |- _ => pose proof (H _ ltac:(eassumption) _ _ ltac:(eassumption)); clear H
  | H : eval _ ?d ?e ?v1, G: eval _ ?d ?e ?v2 |- _ =>
      assert_fails (constr_eq v1 v2);
      eapply (eval_eval _ d e v1 H v2) in G
  | _ => progress cbv [interp_op] in *
  | _ => progress cbn [fst snd] in *
  | _ => progress destruct_one_match
  | _ => progress Option.inversion_option
  | _ => progress subst
  end.

Lemma bound_sum' G d
  es (He : Forall (fun e => forall b, bound_expr e = Some b -> 
       forall (d : dag) (v : Z), eval G d e v -> (0 <= v <= b)%Z) es)
  : forall
  bs (Hb : Option.List.lift (map bound_expr es) = Some bs)
  vs (Hv : Forall2 (eval G d) es vs)
  , (0 <= fold_right Z.add 0 vs <= fold_right Z.add 0 bs)%Z.
Proof.
  induction He; cbn in *; repeat t.
  { cbv [fold_right]; Lia.lia. }
  destruct (bound_expr _) eqn:? in *; cbn in *; repeat t.
  destruct (fold_right (B:=option _) _) eqn:? in *; cbn in *; repeat t.
  specialize (IHHe _ ltac:(eassumption) _ ltac:(eassumption)); cbn.
  specialize (H _ ltac:(exact eq_refl) _ _ ltac:(eassumption)).
  Lia.lia.
Qed.


Lemma Z__ones_nonneg n (H : 0 <= n)  : 0 <= Z.ones n.
Proof. rewrite Z.ones_equiv. pose proof Z.pow_pos_nonneg 2 n ltac:(Lia.lia) ltac:(assumption); Lia.lia. Qed.

Require Import Util.ZRange.LandLorBounds.
Lemma eval_bound_expr G e b : bound_expr e = Some b ->
  forall d v, eval G d e v -> (0 <= v <= b)%Z.
Proof.
  revert b; induction e; simpl bound_expr; BreakMatch.break_match;
    inversion 2; intros; inversion_option; subst;
    try match goal with H : context [set_slice] |- _ => shelve end;
    cbv [interp_op] in *;
    BreakMatch.break_match_hyps; inversion_option; subst;
    rewrite ?Z.ldiff_ones_r, ?Z.land_ones, ?Z.ones_equiv;
    cbv [Z.b2z];
    try match goal with |- context [(?a mod ?b)%Z] => unshelve epose proof Z.mod_pos_bound a b ltac:(eapply Z.pow_pos_nonneg; Lia.lia) end;
    repeat t;
    try (Z.div_mod_to_equations; Lia.lia).
  { clear dependent args'0.
    epose proof bound_sum' _ ltac:(eassumption) _ ltac:(eassumption) _ ltac:(eassumption) _ ltac:(eassumption).
    split; try Lia.lia.
    eapply Z.min_glb_iff; split; try Lia.lia.
    etransitivity. eapply Zmod_le.
    all : try Lia.lia. }
  Unshelve. {
    repeat t.
    pose proof Z.log2_nonneg z; pose proof Z.log2_nonneg z0.
    rewrite !Z.shiftl_0_r.
    split.
    { eapply Z.lor_nonneg; split; try eapply Z.land_nonneg; try eapply Z.ldiff_nonneg; Lia.lia. }
    eapply Z.le_bitwise.
    { eapply Z.lor_nonneg; split; try eapply Z.land_nonneg; try eapply Z.ldiff_nonneg; Lia.lia. }
    { eapply Z.lor_nonneg; split; try eapply Z.land_nonneg; try eapply Z.ldiff_nonneg;
        left; try eapply Z__ones_nonneg; Lia.lia. }
    { intros i Hi.
      Z.rewrite_bitwise.
      destr (i <? Z.of_N sz);
        rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_l, ?Bool.orb_false_r.
      { clear -H Hi.
        destr (i <? Z.succ (Z.log2 z0)).
        { eapply Bool.le_implb, Bool.implb_true_r. }
        rewrite Z.bits_above_log2; cbn; trivial; try Lia.lia.
        destruct H as [? H]; eapply Z.log2_le_mono in H. Lia.lia. }
      { clear -H0 Hi.
        destr (i <? Z.succ (Z.log2 z)).
        { eapply Bool.le_implb, Bool.implb_true_r. }
        rewrite Z.bits_above_log2; cbn; trivial; try Lia.lia.
        destruct H0 as [? H0]; eapply Z.log2_le_mono in H0. Lia.lia. } } }
Qed.

Lemma bound_sum G d es 
  bs (Hb : Option.List.lift (map bound_expr es) = Some bs)
  vs (Hv : Forall2 (eval G d) es vs)
  : (0 <= fold_right Z.add 0 vs <= fold_right Z.add 0 bs)%Z.
Proof.
  eapply bound_sum' in Hb; eauto.
  eapply Forall_forall; intros.
  eapply eval_bound_expr; eauto.
Qed.


Definition isCst (e : expr) :=
  match e with ExprApp ((const _), _) => true | _ => false end.


Module Rewrite.
Class Ok r := rwok : forall G d e v, eval G d e v -> eval G d (r e) v.

Ltac resolve_match_using_hyp :=
  match goal with |- context[match ?x with _ => _ end] =>
  match goal with H : x = ?v |- _ =>
      let h := Head.head v in
      is_constructor h;
      rewrite H
  end end.

Ltac step := match goal with
  | |- Ok ?r => cbv [Ok r]; intros
  | _ => solve [trivial | contradiction]
  |  _ => resolve_match_using_hyp
  | _ => inversion_option_step

  | H : _ = ?v |- _ => is_var v; progress subst v
  | H : ?v = _ |- _ => is_var v; progress subst v

  | H : eval _ ?d ?e ?v1, G: eval _ ?d ?e ?v2 |- _ =>
      assert_fails (constr_eq v1 v2);
      eapply (eval_eval _ d e v1 H v2) in G
  | |- eval _ ?d ?e ?v =>
      match goal with
        H : eval _ d e ?v' |- _ =>
            let Heq := fresh in
            enough (Heq : v = v') by (rewrite Heq; exact H);
            try (clear H; clear e)
      end

  | H: interp_op _ (const _) nil = Some _ |- _ => inversion H; clear H; subst
  | H: interp0_op _ _ = Some _ |- _ => eapply interp_op_interp0_op in H
  | H: interp0_expr _ = Some _ |- _ => eapply eval_interp0_expr in H
  | H: bound_expr _ = Some _ |- _ => eapply eval_bound_expr in H; eauto; [ ]

  | H : (?x <=? ?y)%N = ?b |- _ => is_constructor b; destruct (N.leb_spec x y); (inversion H || clear H)
  | H : andb _ _ = true |- _ => eapply Bool.andb_prop in H; case H as (?&?)
  | H : N.eqb ?n _ = true |- _ => eapply N.eqb_eq in H; try subst n
  | H : Z.eqb ?n _ = true |- _ => eapply Z.eqb_eq in H; try subst n
  | H : expr_beq ?a ?b = true |- _ => replace a with b in * by (symmetry;exact (expr_beq_true a b H)); clear H
  | _ => progress destruct_one_match_hyp
  | _ => progress destruct_one_match

  | H : eval _ _ ?e _ |- _ => assert_fails (is_var e); inversion H; clear H; subst
  | H : Forall2 (eval _ _) (cons _ _) _ |- _ => inversion H; clear H; subst
  | H : Forall2 (eval _ _) _ (cons _ _) |- _ => inversion H; clear H; subst
  | H : Forall2 _ _ nil |- _ => inversion H; clear H; subst
  | H : Forall2 _ nil _ |- _ => inversion H; clear H; subst

  | _ => progress cbn [fst snd map option_map] in *
  end.

Ltac Econstructor :=
  match goal with
  | |- Forall2 (eval _ _) _ _ =>  econstructor
  | |- eval _ _ ?e _ => econstructor
  end.

Ltac t := repeat (step || Econstructor || eauto || (progress cbn [interp0_op interp_op] in * ) ).

Definition slice0 :=
  fun e => match e with
    ExprApp (slice 0 s, [(ExprApp ((addZ|mulZ|negZ|shlZ|shrZ|andZ|orZ|xorZ) as o, args))]) =>
        ExprApp ((match o with addZ=>add s|mulZ=>mul s|negZ=>neg s|shlZ=>shl s|shrZ => shr s|andZ => and s| orZ => or s|xorZ => xor s |_=>old 0%N 999999%N end), args)
      | _ => e end.
Global Instance slice0_ok : Ok slice0. Proof. t. Qed.

Definition slice01_addcarryZ :=
  fun e => match e with
    ExprApp (slice 0 1, [(ExprApp (addcarryZ s, args))]) =>
        ExprApp (addcarry s, args)
      | _ => e end.
Global Instance slice01_addcarryZ_ok : Ok slice01_addcarryZ.
Proof. t; rewrite ?Z.shiftr_0_r, ?Z.land_ones, ?Z.shiftr_div_pow2; trivial; Lia.lia. Qed.

Definition slice01_subborrowZ :=
  fun e => match e with
    ExprApp (slice 0 1, [(ExprApp (subborrowZ s, args))]) =>
        ExprApp (subborrow s, args)
      | _ => e end.
Global Instance slice01_subborrowZ_ok : Ok slice01_subborrowZ.
Proof. t; rewrite ?Z.shiftr_0_r, ?Z.land_ones, ?Z.shiftr_div_pow2; trivial; Lia.lia. Qed.

Definition slice_set_slice :=
  fun e => match e with
    ExprApp (slice 0 s1, [ExprApp (set_slice 0 s2, [_; e'])]) =>
      if N.leb s1 s2 then ExprApp (slice 0 s1, [e']) else e | _ => e end.
Global Instance slice_set_slice_ok : Ok slice_set_slice.
Proof. t. f_equal. Z.bitblast. Qed.

Definition set_slice_set_slice :=
  fun e => match e with
    ExprApp (set_slice lo1 s1, [ExprApp (set_slice lo2 s2, [x; e']); y]) =>
      if andb (N.eqb lo1 lo2) (N.leb s2 s1) then ExprApp (set_slice lo1 s1, [x; y]) else e | _ => e end.
Global Instance set_slice_set_slice_ok : Ok set_slice_set_slice.
Proof. t. f_equal. Z.bitblast. Qed.

Definition set_slice0_small :=
  fun e => match e with
    ExprApp (set_slice 0 s, [x; y]) =>
      match bound_expr x, bound_expr y with Some a, Some b =>
      if Z.leb a (Z.ones (Z.of_N s)) && Z.leb b (Z.ones (Z.of_N s)) then y
      else e | _, _ => e end | _ => e end%bool.
Global Instance set_slice0_small_ok : Ok set_slice0_small.
Proof.
  t.
  eapply Zle_bool_imp_le in H0; rewrite Z.ones_equiv in H0; eapply Z.lt_le_pred in H0.
  eapply Zle_bool_imp_le in H1; rewrite Z.ones_equiv in H1; eapply Z.lt_le_pred in H1.
  assert ((0 <= y < 2^Z.of_N sz)%Z) by Lia.lia; clear dependent z.
  assert ((0 <= y0 < 2^Z.of_N sz)%Z) by Lia.lia; clear dependent z0.
  rewrite ?Z.shiftl_0_r, Z.land_ones, Z.mod_small by Lia.lia.
  destruct (Z.eq_dec y 0); subst.
  { rewrite Z.ldiff_0_l, Z.lor_0_r; trivial. }
  rewrite Z.ldiff_ones_r_low, Z.lor_0_r; try Lia.lia.
  eapply Z.log2_lt_pow2; Lia.lia.
Qed.

Lemma indN: forall (P: N -> Prop),
    P 0%N ->                                 (* base case to prove *)
    (forall n: N, P n -> P (n + 1)%N) ->     (* inductive case to prove *)
    forall n, P n.                           (* conclusion to enjoy *)
Proof. setoid_rewrite N.add_1_r. exact N.peano_ind. Qed.

Ltac induct e := induction e using indN.
                  
Lemma helper'': forall sz, (2^Z.of_N sz>0)%Z.
  Proof. 
    induct sz; cbn in *; try Lia.lia.
    replace (2^Z.of_N (sz+1))%Z with (2 * 2^Z.of_N sz )%Z; try Lia.lia.
    replace (2^Z.of_N (sz+1))%Z with ( 2^ Z.succ (Z.of_N sz) )%Z.
    erewrite Z.pow_succ_r; eauto; Lia.lia.
    f_equal; Lia.lia.
  Qed.
  
Lemma helper': forall sz y,(y<= Z.pred (2^ Z.of_N sz))%Z -> (y <  (2 ^ Z.of_N sz ))%Z. 
Proof.
  intros; pose proof helper'' sz; replace( N.pred (2^ sz))%N with (2^sz-1)%N in H by Lia.lia; Lia.lia.
Qed.

Lemma le_ones: forall sz y,  (0 <= y )%Z -> (y<=Z.ones (Z.of_N sz))%Z -> Z.land y (Z.ones (Z.of_N sz)) = y.
Proof.
  intros.
  erewrite Z.land_ones.
  erewrite Z.ones_equiv in H0.
  eapply helper' in H0.
  eapply Z.mod_small; eauto. Lia.lia.
Qed.

Definition truncate_small :=
  fun e => match e with
    ExprApp (slice 0%N s, [e']) =>
      match bound_expr e' with Some b =>
      if Z.leb b (Z.ones (Z.of_N s))
      then e'
      else e | _ => e end | _ => e end.
Global Instance truncate_small_ok : Ok truncate_small. Proof. t; []. cbn in *; eapply le_ones; eauto. firstorder. Lia.lia. Qed.
 
Definition addcarry_bit :=
  fun e => match e with
    ExprApp (addcarry s, ([ExprApp (const a, nil);b])) =>
      if option_beq Z.eqb (bound_expr b) (Some 1) then
      match interp0_op (addcarry s) [a; 0], interp0_op (addcarry s) [a; 1] with
      | Some 0, Some 1 => b
      | Some 0, Some 0 => ExprApp (const 0, nil)
      | _, _ => e
      end else e | _ => e end%Z%bool.
Global Instance addcarry_bit_ok : Ok addcarry_bit.
Proof.
  repeat step;
    [instantiate (1:=G) in E0; instantiate (1:=G) in E1|];
    destruct (Reflect.reflect_eq_option (eqA:=Z.eqb) (bound_expr e) (Some 1%Z)) in E;
      try discriminate; repeat step;
    assert (y0 = 0 \/ y0 = 1)%Z as HH by Lia.lia; case HH as [|];
      subst; repeat step; repeat Econstructor; cbn; congruence.
Qed.

Definition addoverflow_bit :=
  fun e => match e with
    ExprApp (addoverflow s, ([ExprApp (const a, nil);b])) =>
      if option_beq Z.eqb (bound_expr b) (Some 1%Z) then
      match interp0_op (addoverflow s) [a; 0] , interp0_op (addoverflow s) [a; 1] with
      | Some 0, Some 1 => b
      | Some 0, Some 0 => ExprApp (const 0, nil)
      | _, _ => e
      end else e | _ => e end%Z%bool.
Global Instance addoverflow_bit_ok : Ok addoverflow_bit.
Proof.
  repeat step;
    [instantiate (1:=G) in E0; instantiate (1:=G) in E1|];
    destruct (Reflect.reflect_eq_option (eqA:=Z.eqb) (bound_expr e) (Some 1)%Z) in E;
      try discriminate; repeat step;
    assert (y0 = 0 \/ y0 = 1)%Z as HH by Lia.lia; case HH as [|];
      subst; repeat step; repeat Econstructor; cbn; congruence.
Qed.

Definition addbyte_small :=
  fun e => match e with
    ExprApp (add (8%N as s), args) =>
      match Option.List.lift (List.map bound_expr args) with
      | Some bounds =>
          if Z.leb (List.fold_right Z.add 0%Z bounds) (Z.ones (Z.of_N s))
          then ExprApp (add 64%N, args)
          else e | _ => e end | _ =>  e end.
Global Instance addbyte_small_ok : Ok addbyte_small.
Proof. 
  t; f_equal.
  eapply bound_sum in H2; eauto.
  rewrite Z.ones_equiv in E0; rewrite !Z.land_ones, !Z.mod_small; Lia.lia.
Qed.

Lemma shiftr_ones: forall s,  Z.shiftr (Z.ones (Z.of_N s)) (Z.of_N s) = 0%Z.
Proof.
  intros.
  erewrite Z.shiftr_div_pow2; eauto; try Lia.lia.
  eapply Z.div_small; eauto; try Lia.lia. pose proof helper'' s.  erewrite Z.ones_equiv. Lia.lia. Qed.
                    
Definition addcarry_small :=
  fun e => match e with
    ExprApp (addcarry s, args) =>
      match Option.List.lift (List.map bound_expr args) with
      | Some bounds =>
          if Z.leb (List.fold_right Z.add 0%Z bounds) (Z.ones (Z.of_N s))
          then (ExprApp (const 0, nil))
          else e | _ => e end | _ =>  e end.
Global Instance addcarry_small_ok : Ok addcarry_small.
Proof.
  t; f_equal.
  eapply bound_sum in H2; eauto.
  rewrite Z.ones_equiv in E0; rewrite Z.shiftr_div_pow2, Z.div_small; cbn; Lia.lia.
Qed.

Lemma signed_small s v (Hv : (0 <= v <= Z.ones (Z.of_N s-1))%Z) : signed s v = v.
Proof.
  destruct (N.eq_dec s 0); subst; cbv [signed].
  { rewrite Z.land_0_r. cbn in *; Lia.lia. }
  rewrite !Z.land_ones, !Z.shiftl_mul_pow2, ?Z.add_0_r, ?Z.mul_1_l by Lia.lia.
  rewrite Z.ones_equiv in Hv.
  rewrite Z.mod_small; try ring.
  enough (2 ^ Z.of_N s = 2 ^ (Z.of_N s - 1) + 2 ^ (Z.of_N s - 1))%Z; try Lia.lia.
  replace (Z.of_N s) with (1+(Z.of_N s-1))%Z at 1 by Lia.lia.
  rewrite Z.pow_add_r; try Lia.lia.
Qed.

Definition addoverflow_small :=
  fun e => match e with
    ExprApp (addoverflow s, ([_]|[_;_]|[_;_;_]) as args) =>
      match Option.List.lift (List.map bound_expr args) with
      | Some bounds =>
          if Z.leb (List.fold_right Z.add 0%Z bounds) (Z.ones (Z.of_N s-1))
          then (ExprApp (const 0, nil))
          else e | _ => e end | _ =>  e end.
Global Instance addoverflow_small_ok : Ok addoverflow_small.
Proof.
  t; cbv [Option.List.lift Option.bind fold_right] in *;
  BreakMatch.break_match_hyps; Option.inversion_option; t;
  epose proof Z.ones_equiv (Z.of_N s -1).
  all : rewrite Z.land_ones, !Z.mod_small, !signed_small, !Z.eqb_refl; trivial.
  all : try split; try Lia.lia.
  all : replace (Z.of_N s) with (1+(Z.of_N s-1))%Z at 1 by Lia.lia;
  rewrite Z.pow_add_r; try Lia.lia.
  all : destruct s; cbn in E0; Lia.lia.
Qed.

Definition constprop :=
  fun e => match interp0_expr e with
           | Some v => ExprApp (const v, nil)
           | _ => e end.
Global Instance constprop_ok : Ok constprop.
Proof. t. f_equal; eauto using eval_eval. Qed.

Lemma invert_interp_op_associative o : associative o = true ->
  forall G x xs v, interp_op G o (x :: xs) = Some v ->
  exists v', interp_op G o xs = Some v' /\
  interp_op G o [x; v'] = Some v.
Proof.
  destruct o; inversion 1; intros * HH; inversion HH; clear HH; subst; cbn;
    eexists; split; eauto; f_equal; try ring; try solve [Z.bitblast].
  { rewrite !Z.add_0_r, ?Z.land_ones; push_Zmod; pull_Zmod; Lia.lia. }
  { rewrite !Z.mul_1_r, ?Z.land_ones; push_Zmod; pull_Zmod; Lia.lia. }
Qed.

Lemma interp_op_associative_cons o : associative o = true ->
  forall G x xs ys v,
  interp_op G o xs = Some v -> interp_op G o ys = Some v ->
  interp_op G o (x :: xs) = interp_op G o (x :: ys).
Proof.
  destruct o; inversion 1;
    do 2 (intros * HH; inversion HH; clear HH; subst; cbn); f_equal.
  { rewrite ?Z.land_ones in *; push_Zmod; rewrite ?H1; pull_Zmod; Lia.lia. }
  { rewrite <-2Z.land_assoc; congruence. }
  { rewrite 2Z.land_lor_distr_l; congruence. }
  { rewrite ?Z.land_ones in *; push_Zmod; rewrite ?H1; pull_Zmod; Lia.lia. }
Qed.

Lemma interp_op_associative_app G o : associative o = true ->
  forall xs vxs, interp_op G o xs = Some vxs -> 
  forall ys vys, interp_op G o ys = Some vys ->
  interp_op G o (xs ++ ys) = interp_op G o [vxs; vys].
Proof.
  induction xs; destruct o; inversion H; cbn [app interp_op fold_right] in *;
    intros; Option.inversion_option; subst; f_equal;
    try ring; try solve [Z.bitblast].
  { rewrite ?Z.land_ones in *; push_Zmod; pull_Zmod; try Lia.lia; f_equal; ring. }
  { rewrite ?Z.land_ones in *; push_Zmod; pull_Zmod; try Lia.lia; f_equal; ring. }
  all : epose proof (IHxs _ eq_refl _ _ eq_refl) as HH;
        inversion HH as [HHH]; clear IHxs HH.
  { rewrite ?Z.land_ones in *; push_Zmod;
    rewrite ?HHH; push_Zmod; pull_Zmod; try Lia.lia. f_equal; ring. }
  { rewrite <-2Z.land_assoc. rewrite ?HHH. Z.bitblast. }
  { rewrite 2Z.land_lor_distr_l. rewrite ?HHH. Z.bitblast. }
  { rewrite ?Z.land_ones in *; push_Zmod;
    rewrite ?HHH; push_Zmod; pull_Zmod; try Lia.lia. f_equal; ring. }
  { rewrite ?HHH. ring. }
Qed.

Definition flatten_associative :=
  fun e => match e with
    ExprApp (o, args) =>
    if associative o then
      ExprApp (o, List.flat_map (fun e' =>
        match e' with
        | ExprApp (o', args') => if op_beq o o' then args' else [e']
        | _ => [e'] end) args)
    else e | _ => e end.
Global Instance flatten_associative_ok : Ok flatten_associative.
Proof.
  repeat step.
  revert dependent v; induction H2; cbn.
  { econstructor; eauto. }
  intros ? H4.
  pose proof H4.
  eapply invert_interp_op_associative in H4; eauto. destruct H4 as (?&?&?).
  specialize (IHForall2 _ ltac:(eassumption)).
  inversion IHForall2; subst.
  destruct x as [i|[o' args''] ].
  { econstructor. { econstructor. eauto. eauto. }
    erewrite interp_op_associative_cons; eauto. }
  { destruct (op_beq_spec o o'); subst; cycle 1.
    { econstructor. { econstructor. eauto. eauto. }
      erewrite interp_op_associative_cons; eauto. }
    inversion H; clear H; subst.
    econstructor; eauto using Forall2_app.
    erewrite interp_op_associative_app; eauto. }
Qed.

Definition consts_commutative :=
  fun e => match e with
    ExprApp (o, args) =>
    (* note: removing the next line makes tests fail *)
    if (match o with mul _ => true | _ => false end) then e else
    if commutative o then
    let csts_exprs := List.partition isCst args in
    if associative o
    then match interp0_expr (ExprApp (o, fst csts_exprs)) with
         | Some v => ExprApp (o, ExprApp (const v, nil):: snd csts_exprs)
         | _ => ExprApp (o, fst csts_exprs ++ snd csts_exprs)
         end
    else ExprApp (o, fst csts_exprs ++ snd csts_exprs)
    else e | _ => e end.

Lemma Permutation_partition {A} (l : list A) f :
    Permutation.Permutation l (fst (partition f l) ++ snd (partition f l)).
Proof.
  induction l; cbn; BreakMatch.break_match; cbn in *; eauto.
  etransitivity. econstructor. eassumption.
  eapply Permutation.Permutation_middle.
Qed.

Global Instance consts_commutative_ok : Ok consts_commutative.
Proof.
  step.
  destruct e; trivial.
  destruct n.
  destruct (match o with mul _ => true | _ => false end); trivial.
  destruct commutative eqn:?; trivial.
  inversion H; clear H; subst.
  epose proof Permutation_partition l isCst.
  eapply Permutation.Permutation_Forall2 in H2; [|eassumption].
  DestructHead.destruct_head'_ex; DestructHead.destruct_head'_and.
  epose proof permute_commutative  _ _ _ _ Heqb H4 _ H0.
  repeat Econstructor; eauto.
  destruct associative eqn:?; [|solve[repeat Econstructor; eauto] ].
  BreakMatch.break_match; [|solve[repeat Econstructor; eauto] ].

  set (fst (partition isCst l)) as csts in *; clearbody csts.
  set (snd (partition isCst l)) as exps in *; clearbody exps.
  clear dependent l. clear dependent args'. 
  move o at top; move Heqb0 at top; move Heqb at top.
  eapply eval_interp0_expr in Heqo0; instantiate (1:=d) in Heqo0; instantiate (1:=G) in Heqo0.

  eapply Forall2_app_inv_l in H1; destruct H1 as (?&?&?&?&?); subst.
  rename x0 into xs. rename x1 into ys.
  econstructor. { econstructor. econstructor. econstructor. exact eq_refl. eassumption. }

  inversion Heqo0; clear Heqo0; subst.
  eapply eval_eval_Forall2 in H; eauto; subst.
  clear dependent exps. clear dependent csts.
  clear -H2 H6 Heqb Heqb0.

  destruct o; try solve [inversion Heqb; inversion Heqb0]; clear Heqb Heqb0;
  inversion H6; inversion H2; clear H6 H2; subst; eapply (f_equal Some).
  all: rewrite fold_right_app, ListUtil.List.fold_right_cons.
  all : rewrite ?Z.land_ones; push_Zmod; pull_Zmod; try Lia.lia; f_equal.
  all : set (fold_right _ _ ys) as Y; clearbody Y.
  all : induction xs; cbn [fold_right]; eauto;
    try ring [IHxs]; try (symmetry in IHxs; ring [IHxs]); try ring.
Qed.

Definition neqconst i := fun a : expr => negb (option_beq Z.eqb (interp0_expr a) (Some i)).
Definition drop_identity :=
  fun e => match e with ExprApp (o, args) =>
    match identity o with
    | Some i =>
        let args := List.filter (neqconst i) args in
        match args with
        | nil => ExprApp (const i, nil)
        | _ => ExprApp (o, args)
        end
    | _ => e end | _ => e end.

Lemma eval_filter_identity_mulZ G d args v
  (Hv : eval G d (ExprApp (mulZ, args)) v)
  : eval G d (ExprApp (mulZ, filter (neqconst 1) args)) v.
Proof.
  inversion Hv; clear Hv; subst.
  revert dependent v; induction H1; cbn;
    intros * HH; inversion HH; subst.
  { repeat Econstructor; eauto. }
  cbv [neqconst];
  destruct (@Reflect.reflect_eq_option _ _ BinInt.Z.eqb_spec (interp0_expr x) (Some 1%Z)); cbn;
  match goal with |- context[filter ?x] => change x with (neqconst 1%Z) end.
  { epose proof eval_interp0_expr _ _ e G d as He; step; step; subst; clear H.
    cbn -[Z.mul] in HH; Option.inversion_option; subst.
    rewrite Z.mul_1_l.
    eapply IHForall2. exact eq_refl. }
  { clear n.
    cbn -[Z.mul] in HH; Option.inversion_option; subst.
    specialize (IHForall2 (fold_right Z.mul 1%Z l') eq_refl);
      inversion IHForall2; subst.
    repeat Econstructor; eauto.
    cbn [fold_right interp_op] in *; Option.inversion_option; f_equal. ring [H5]. }
Qed.

Lemma eval_filter_identity_mul G d s args v
  (Hv : eval G d (ExprApp (mul s, args)) v)
  : eval G d (ExprApp (mul s, filter (neqconst 1) args)) v.
Proof.
  inversion Hv; clear Hv; subst.
  revert dependent v; induction H1; cbn;
    intros * HH; inversion HH; subst.
  { repeat Econstructor; eauto. }
  cbv [neqconst];
  destruct (@Reflect.reflect_eq_option _ _ BinInt.Z.eqb_spec (interp0_expr x) (Some 1%Z)); cbn;
  match goal with |- context[filter ?x] => change x with (neqconst 1%Z) end.
  { epose proof eval_interp0_expr _ _ e G d as He; step; step; subst; clear H.
    cbn -[Z.mul] in HH; Option.inversion_option; subst.
    rewrite Z.mul_1_l.
    eapply IHForall2. exact eq_refl. }
  { clear n.
    cbn -[Z.mul] in HH; Option.inversion_option; subst.
    epose proof (IHForall2 _ eq_refl) as IH; inversion IH; subst.
    repeat Econstructor; eauto.
    cbn [fold_right interp_op] in *; Option.inversion_option; f_equal.
    rewrite !Z.land_ones in *; push_Zmod; rewrite ?H5; pull_Zmod; Lia.lia. }
Qed.

Lemma eval_filter_identity_add G d s args v
  (Hv : eval G d (ExprApp (add s, args)) v)
  : eval G d (ExprApp (add s, filter (neqconst 0) args)) v.
Proof.
  inversion Hv; clear Hv; subst.
  revert dependent v; induction H1; cbn;
    intros * HH; inversion HH; subst.
  { repeat Econstructor; eauto. }
  cbv [neqconst];
  destruct (@Reflect.reflect_eq_option _ _ BinInt.Z.eqb_spec (interp0_expr x) (Some 0%Z)); cbn;
  match goal with |- context[filter ?x] => change x with (neqconst 0%Z) end.
  { epose proof eval_interp0_expr _ _ e G d as He; step; step; subst; clear H.
    cbn -[Z.add] in HH; Option.inversion_option; subst.
    rewrite Z.add_0_l.
    eapply IHForall2. exact eq_refl. }
  { clear n.
    cbn -[Z.add] in HH; Option.inversion_option; subst.
    epose proof (IHForall2 _ eq_refl) as IH; inversion IH; subst.
    repeat Econstructor; eauto.
    cbn [fold_right interp_op] in *; Option.inversion_option; f_equal.
    rewrite !Z.land_ones in *; push_Zmod; rewrite ?H5; pull_Zmod; Lia.lia. }
Qed.

Lemma eval_filter_identity_and G d s args v
  (Hv : eval G d (ExprApp (and s, args)) v)
  : eval G d (ExprApp (and s, filter (neqconst (Z.ones (Z.of_N s))) args)) v.
Proof.
  inversion Hv; clear Hv; subst.
  revert dependent v; induction H1; cbn;
    intros * HH; inversion HH; subst.
  { repeat Econstructor; eauto. }
  cbv [neqconst];
  destruct (@Reflect.reflect_eq_option _ _ BinInt.Z.eqb_spec (interp0_expr x) (Some (Z.ones (Z.of_N s)))); cbn;
  match goal with |- context[filter ?x] => change x with (neqconst (Z.ones (Z.of_N s))) end.
  { epose proof eval_interp0_expr _ _ e G d as He; step; step; subst; clear H.
    rewrite Z.land_comm, Z.land_assoc, Z.land_diag, Z.land_comm.
    eapply IHForall2. exact eq_refl. }
  { clear n.
    cbn -[Z.land] in HH; Option.inversion_option; subst.
    epose proof (IHForall2 _ eq_refl) as IH; inversion IH; subst.
    repeat Econstructor; eauto.
    cbn [fold_right interp_op] in *; Option.inversion_option; f_equal.
    rewrite <-2Z.land_assoc. congruence. }
Qed.

Lemma eval_filter_identity G d o args v i (Hi : identity o = Some i)
  (Hv : eval G d (ExprApp (o, args)) v)
  : eval G d (ExprApp (o, filter (neqconst i) args)) v.
Proof.
  destruct o; inversion Hi;
    BreakMatch.break_match_hyps; Option.inversion_option; subst;
    eauto using eval_filter_identity_add, eval_filter_identity_mul, eval_filter_identity_mulZ, eval_filter_identity_and.
Qed.

Lemma signed_0 s : signed s 0 = 0%Z.
Proof.
  destruct (N.eq_dec s 0); subst; trivial.
  cbv [signed].
  rewrite !Z.land_ones, !Z.shiftl_mul_pow2, ?Z.add_0_r, ?Z.mul_1_l by Lia.lia.
  rewrite Z.mod_small; try ring.
  split; try (eapply Z.pow_lt_mono_r; Lia.lia).
  eapply Z.pow_nonneg; Lia.lia.
Qed.

Lemma interp_op_nil_is_identity o i (Hi : identity o = Some i)
  G : interp_op G o [] = Some i.
Proof.
  destruct o; inversion Hi; subst; unfold interp_op, fold_right; f_equal.
  { rewrite Z.land_m1_l; trivial. }
  { destruct s; inversion Hi; subst.
    rewrite Z.land_ones, Z.mod_small; try split; try Lia.lia; trivial.
    replace (Z.of_N (N.pos p)) with (1 + Z.of_N (N.pos p -1)%N)%Z by Lia.lia.
    rewrite Z.pow_add_r by Lia.lia.
    epose proof Z.pow_pos_nonneg 2 (Z.of_N (N.pos p - 1))%Z ltac:(Lia.lia) ltac:(Lia.lia).
    Lia.nia. }
Qed.

Global Instance drop_identity_0k : Ok drop_identity.
Proof.
  repeat (step; eauto; []).
  pose proof H as H'; eapply eval_filter_identity in H; try eassumption.
  destruct (filter _ _ ) eqn:? in *; eauto.
  repeat step. erewrite interp_op_nil_is_identity in * by eassumption; t.
Qed.

Definition opcarry_0_at1 :=
  fun e => match e with ExprApp ((addcarryZ s|addcarry s|addoverflow s) as op, cons x args') =>
  match interp0_expr x with
  | Some 0 => ExprApp (op, args')
  | _ => e end | _ => e end%Z.
Global Instance opcarry_0_at1_ok : Ok opcarry_0_at1.
Proof.
  t;
  try (eapply eval_eval in E; [|
    match goal with H : eval _ ?d _ _ |- _ => assert_fails (has_evar d); exact H end]);
  subst; cbn; repeat (rewrite ?Z.add_0_r, ?signed_0); f_equal.
Qed.

Definition opcarry_0_at2 :=
  fun e => match e with ExprApp ((subborrowZ s|subborrow s|addcarryZ s|addcarry s|addoverflow s) as op, cons x (cons y args')) =>
  match interp0_expr y with
  | Some 0 => ExprApp (op, cons x args')
  | __ => e end | _ => e end%Z.
Global Instance opcarry_0_at2_ok : Ok opcarry_0_at2.
Proof.
  t;
  try (eapply eval_eval in E; [|
    match goal with H : eval _ ?d _ _ |- _ => assert_fails (has_evar d); exact H end]);
  subst; cbn; repeat (rewrite ?Z.add_0_r, ?signed_0); f_equal.
Qed.

Definition opcarry_0_at3 :=
  fun e => match e with ExprApp ((subborrowZ s|subborrow s|addcarryZ s|addcarry s|addoverflow s) as op, cons x (cons y (cons z args'))) =>
  match interp0_expr z with
  | Some 0 => ExprApp (op, cons x (cons y args'))
  | _ => e end | _ => e end%Z.
Global Instance opcarry_0_at3_ok : Ok opcarry_0_at3.
Proof.
  t;
  try (eapply eval_eval in E; [|
    match goal with H : eval _ ?d _ _ |- _ => assert_fails (has_evar d); exact H end]);
  try (eapply eval_eval in E0; [|
    match goal with H : eval _ ?d _ _ |- _ => assert_fails (has_evar d); exact H end]);
  subst; cbn; repeat (rewrite ?Z.add_0_r, ?signed_0); f_equal.
Qed.

Definition xor_same :=
  fun e => match e with ExprApp (xor _,[x;y]) =>
    if expr_beq x y then ExprApp (const 0, nil) else e | _ => e end.
Global Instance xor_same_ok : Ok xor_same.
Proof.
  t; cbn [fold_right]. rewrite Z.lxor_0_r, Z.lxor_nilpotent; trivial.
Qed.

Definition expr : expr -> expr :=
  List.fold_left (fun e f => f e)
  [constprop
  ;slice0
  ;slice01_addcarryZ
  ;slice01_subborrowZ
  ;set_slice_set_slice
  ;slice_set_slice
  ;set_slice0_small 
  ;flatten_associative
  ;consts_commutative
  ;drop_identity
  ;opcarry_0_at1
  ;opcarry_0_at3
  ;opcarry_0_at2
  ;truncate_small
  ;addoverflow_bit
  ;addcarry_bit
  ;addcarry_small
  ;addoverflow_small
  ;addbyte_small
  ;xor_same 
  ].

Lemma eval_expr c d e v : eval c d e v -> eval c d (expr e) v.
Proof.
  intros H; cbv [expr fold_left].
  repeat lazymatch goal with
  | H : eval ?c ?d ?e _ |- context[?r ?e] =>
    let Hr := fresh in epose proof ((_:Ok r) _ _ _ _ H) as Hr; clear H
  end.
  eassumption.
Qed.
End Rewrite.

Definition simplify (dag : dag) (e : node idx) :=
  Rewrite.expr (reveal_node dag 3 e).

Lemma eval_simplify G d n v : eval_node G d n v -> eval G d (simplify d n) v.
Proof. eauto using Rewrite.eval_expr, eval_node_reveal_node. Qed.

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

  | unsupported_memory_access_size (_:N)
  | unimplemented_instruction (_ : NormalInstruction)
  | unsupported_line (_ : RawLine)
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
   | unsupported_memory_access_size n => "error.unsupported_memory_access_size " ++ show n
   | unimplemented_instruction n => "error.unimplemented_instruction " ++ show n
   | unsupported_line n => "error.unsupported_line " ++ show n
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
Definition PreserveFlag {T} (f : FLAG) (k : M T) : M T :=
  vf <- (fun s => Success (get_flag s f, s));
  x <- k;
  _ <- (fun s => Success (tt, update_flag_with s (fun s => set_flag_internal s f vf)));
  ret x.
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
Definition RevealConst (i : idx) : M Z :=
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
  then v <- App (slice 0 64, [v]);
       SetReg64 rn v (* works even if old value is unspecified *)
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
  offset <- App (match a.(mem_offset) with
                             | Some s => (zconst sa s, nil)
                             | None => (const 0, nil) end);
  bi <- App (add sa, [base; index]);
  App (add sa, [bi; offset]).

Definition Load {s : OperationSize} {sa : AddressSize} (a : MEM) : M idx :=
  if negb (orb (Syntax.operand_size a s =? 8 )( Syntax.operand_size a s =? 64))%N
  then err (error.unsupported_memory_access_size (Syntax.operand_size a s)) else
  addr <- Address a;
  v <- Load64 addr;
  App ((slice 0 (Syntax.operand_size a s)), [v]).

Definition Store {s : OperationSize} {sa : AddressSize} (a : MEM) v : M unit :=
  if negb (orb (Syntax.operand_size a s =? 8 )( Syntax.operand_size a s =? 64))%N
  then err (error.unsupported_memory_access_size (Syntax.operand_size a s)) else
  addr <- Address a;
  old <- Load64 addr;
  v <- App (slice 0 (Syntax.operand_size a s), [v]);
  v <- App (set_slice 0 (Syntax.operand_size a s), [old; v])%N;
  Store64 addr v.

(* note: this could totally just handle truncation of constants if semanics handled it *)
Definition GetOperand {s : OperationSize} {sa : AddressSize} (o : ARG) : M idx :=
  match o with
  | Syntax.const a => App (zconst s a, [])
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
| PreRef (_ : idx)
| PreApp (_ : op) (_ : list pre_expr).
(* note: need custom induction principle *)
Local Set Elimination Schemes.
Local Coercion PreARG : ARG >-> pre_expr.
Local Coercion PreFLG : FLAG >-> pre_expr.
Local Coercion PreRef : idx >-> pre_expr.
Example __testPreARG_boring : ARG -> list pre_expr := fun x : ARG => @cons pre_expr x nil.
(*
Example __testPreARG : ARG -> list pre_expr := fun x : ARG => [x].
*)

Fixpoint Symeval {s : OperationSize} {sa : AddressSize} (e : pre_expr) : M idx :=
  match e with
  | PreARG o => GetOperand o
  | PreFLG f => GetFlag f
  | PreRef i => ret i
  | PreApp op args =>
      idxs <- mapM Symeval args;
      App (op, idxs)
  end.

Definition rcrcnt s cnt : Z :=
  if N.eqb s 8 then Z.land cnt 0x1f mod 9 else
  if N.eqb s 16 then Z.land cnt 0x1f mod 17 else
  Z.land cnt (Z.of_N s-1).

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
    _ <- SetOperand b va;
    SetOperand a vb
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
    o <- Symeval (addoverflow s@(dst, src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    _ <- SetFlag CF c;
    SetFlag OF o
  | Syntax.adc, [dst; src] =>
    v <- Symeval (add s@(dst, src, CF));
    c <- Symeval (addcarry s@(dst, src, CF));
    o <- Symeval (addoverflow s@(dst, src, CF));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    _ <- SetFlag CF c;
    SetFlag OF o
  | (adcx|adox) as op, [dst; src] =>
    let f := match op with adcx => CF | _ => OF end in
    v <- Symeval (add s@(dst, src, f));
    c <- Symeval (addcarry s@(dst, src, f));
    _ <- SetOperand dst v;
    SetFlag f c
  | Syntax.sub, [dst; src] =>
    v <- Symeval (add       s@(dst, PreApp (neg s) [PreARG src]));
    c <- Symeval (subborrow s@(dst, src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    SetFlag CF c
  | Syntax.sbb, [dst; src] =>
    v <- Symeval (add         s@(dst, PreApp (neg s) [PreARG src], PreApp (neg s) [PreFLG CF]));
    c <- Symeval (subborrow s@(dst, src, CF));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    SetFlag CF c
  | lea, [reg dst; mem src] =>
    a <- Address src;
    SetOperand dst a
  | imul, ([dst as src1; src2] | [dst; src1; src2]) =>
    v <- Symeval (mulZ@(src1,src2));
    _ <- SetOperand dst v;
    HavocFlags
  | Syntax.xor, [dst; src] =>
    v <- Symeval (xorZ@(dst,src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    zero <- Symeval (PreApp (const 0) nil);
    _ <- SetFlag CF zero;
    SetFlag OF zero
  | Syntax.and, [dst; src] =>
    v <- Symeval (andZ@(dst,src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    zero <- Symeval (PreApp (const 0) nil); _ <- SetFlag CF zero; SetFlag OF zero
  | Syntax.bzhi, [dst; src; cnt] =>
    cnt <- GetOperand cnt;
    cnt <- RevealConst cnt;
    v <- Symeval (andZ@(src,PreApp (const (Z.ones (Z.land cnt (Z.ones 8)))) nil));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    zero <- App (const 0, nil); SetFlag OF zero
  | Syntax.rcr, [dst; cnt] =>
    x <- GetOperand dst;
    cf <- GetFlag CF;
    cnt <- GetOperand cnt; cnt <- RevealConst cnt; let cnt := rcrcnt s cnt in
    cntv <- App (const cnt, nil);
    y <- App (rcr s, [x; cf; cntv]);
    _ <- SetOperand dst y;
    _ <- HavocFlags;
    if (cnt =? 1)%Z
    then cf <- App ((slice 0 1), cons (x) nil); SetFlag CF cf
    else ret tt    
  | mulx, [hi; lo; src2] =>
    let src1 : ARG := rdx in
    v1 <- GetOperand src1;
    v2 <- GetOperand src2;
    v <- App (mulZ, [v1; v2]);
    s <- App (const (Z.of_N s), nil);
    vh <- App (shrZ, [v; s]);
    _ <- SetOperand lo v;
         SetOperand hi vh
  | Syntax.shr, [dst; cnt] =>
    let cnt := andZ@(cnt, (PreApp (const (Z.of_N s-1)%Z) nil)) in
    v <- Symeval (shr s@(dst, cnt));
    _ <- SetOperand dst v;
    HavocFlags
  | Syntax.sar, [dst; cnt] =>
    x <- GetOperand dst;
    let cnt := andZ@(cnt, (PreApp (const (Z.of_N s-1)%Z) nil)) in
    c <- Symeval cnt; rc <- Reveal 1 c;
    y <- App (sar s, [x; c]);
    _ <- SetOperand dst y;
    _ <- HavocFlags;
    if expr_beq rc (ExprApp (const 1%Z, nil))
    then (
      cf <- App ((slice 0 1), cons (x) nil);
      _ <- SetFlag CF cf;
      zero <- App (const 0, nil); SetFlag OF zero)
    else ret tt
  | shrd, [lo as dst; hi; cnt] =>
    let cnt := andZ@(cnt, (PreApp (const (Z.of_N s-1)%Z) nil)) in
    let cnt' := addZ@(Z.of_N s, PreApp negZ [cnt]) in
    v <- Symeval (or s@(shr s@(lo, cnt), shl s@(hi, cnt')));
    _ <- SetOperand dst v;
    HavocFlags
  | inc, [dst] =>
    v <- Symeval (add s@(dst, PreARG 1%Z));
    o <- Symeval (addoverflow s@(dst, PreARG 1%Z));
    _ <- SetOperand dst v;
    _ <- PreserveFlag CF HavocFlags;
    SetFlag OF o
  | dec, [dst] =>
    v <- Symeval (add s@(dst, PreARG (-1)%Z));
    o <- Symeval (addoverflow s@(dst, PreARG (-1)%Z));
    _ <- SetOperand dst v;
    _ <- PreserveFlag CF HavocFlags;
    SetFlag OF o
  | test, [ea;eb] =>
    a <- GetOperand ea;
    b <- GetOperand eb;
    zero <- App (const 0, nil);
    _ <- HavocFlags;
    _ <- SetFlag CF zero;
    _ <- SetFlag OF zero;
    if Equality.ARG_beq ea eb 
    then zf <- App (iszero, [a]); SetFlag ZF zf
    else ret tt
  | clc, [] => zero <- Merge (@ExprApp (const 0, nil)); SetFlag CF zero
  | _, _ => err (error.unimplemented_instruction instr)
 end
  | _ => err (error.ambiguous_operation_size instr) end%N%x86symex.

Definition SymexRawLine (rawline : RawLine) : M unit :=
  match rawline with
  | EMPTY
  | LABEL _
    => ret tt
  | INSTR instr
    => SymexNormalInstruction instr
  | SECTION _
  | GLOBAL _
      => err (error.unsupported_line rawline)
  end.

Definition SymexLine line := SymexRawLine line.(rawline).

Fixpoint SymexLines (lines : Lines) : M unit
  := match lines with
     | [] => ret tt
     | line :: lines
       => (st <- SymexLine line;
          SymexLines lines)
     end.
