Require Import NPeano NArith PArith Ndigits ZArith Znat.
Require Import List Listize Basics.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.Specific.GF1305.

Import ListNotations.

Lemma inj_and x y : Z.land (Z.of_N x) y = Z.of_N (N.land x (Z.to_N y)).
Proof.
Admitted.

Lemma inj_shiftr x y :
  Z.shiftr (Z.of_N x) y = Z.of_N (N.shiftr x (Z.to_N y)).
Proof.
Admitted.

Definition nateq {ins outs} (f: Curried Z Z ins outs) :=
  {g: Curried N N ins outs | forall (x: list N), length x = ins ->
    (curriedToListF 0%N g) x =
      map Z.to_N ((curriedToListF 0%Z f) (map Z.of_N x))}.

Definition nateq_kill_arg: forall {m n} (f: Curried Z Z (S m) n),
  (forall x, nateq (f x)) -> nateq f.
Proof. Admitted.

Definition nateq_break_cons: forall {m} (a: Z) (b: list Z),
    @nateq O 1 [a] ->
    @nateq O (S m) b ->
    @nateq O (S (S m)) (cons a b).
Proof. Admitted.

Definition nateq_nil: @nateq O O [].
Proof. Admitted.

Definition nateq_cut_let: forall {outs} (x: Z) (f: Z -> list Z),
    @nateq 1 outs f -> @nateq O 1 [x] ->
    @nateq O outs (Let_In x f).
Proof. Admitted.

Definition nateq_let_const: forall {T outs} (a: T) (f: T -> list Z),
    @nateq O outs (f a) -> @nateq O outs (Let_In a f).
Proof. Admitted.

Definition nateq_debool_andb: forall {outs} (a b: bool) (f: bool -> list Z),
    @nateq O outs (Let_In a (fun x => Let_In b (fun y => f (andb x y)))) ->
    @nateq O outs (Let_In (andb a b) f).
Proof. Admitted.

Definition nateq_debool_ltb: forall {outs} (x y: Z) (f: bool -> list Z),
    @nateq O outs (f true) -> @nateq O outs (f false) ->
    @nateq O 1 [x] -> @nateq O 1 [y] ->
    @nateq O outs (Let_In (x <? y)%Z f).
Proof. Admitted.

Definition nateq_debool_eqb: forall {outs} (x y: Z) (f: bool -> list Z),
    @nateq O outs (f true) -> @nateq O outs (f false) ->
    @nateq O 1 [x] -> @nateq O 1 [y] ->
    @nateq O outs (Let_In (x =? y)%Z f).
Proof. Admitted.

Ltac standardize_nateq :=
  repeat match goal with
  | [|- @nateq (S ?m) _ _] => apply nateq_kill_arg; intro
  | [|- @nateq O _ (Let_In true _)] => apply nateq_let_const
  | [|- @nateq O _ (Let_In false _)] => apply nateq_let_const
  | [|- @nateq O _ (Let_In (_ <? _)%Z _)] => apply nateq_debool_ltb
  | [|- @nateq O _ (Let_In (_ =? _)%Z _)] => apply nateq_debool_eqb
  | [|- @nateq O _ (Let_In (andb _ _) _)] => apply nateq_debool_andb
  | [|- @nateq O _ (Let_In _ _)] => apply nateq_cut_let
  | [|- @nateq O _ (cons _ _)] => apply nateq_break_cons
  end.

Ltac natize_iter :=
  match goal with
  | [ |- context [((Z.of_N ?x) + (Z.of_N ?y))%Z]] =>
    rewrite <- (N2Z.inj_add x y)

  | [ |- context [((Z.of_N ?x) + (Z.of_N ?y))%Z]] =>
    rewrite <- (N2Z.inj_sub x y)

  | [ |- context [((Z.of_N ?x) * (Z.of_N ?y))%Z]] =>
    rewrite <- (N2Z.inj_mul x y)

  | [ |- context [Z.land (Z.of_N ?x) ?y]] =>
    rewrite (inj_and x y)

  | [ |- context [Z.shiftr (Z.of_N ?x) ?y]] =>
    rewrite (inj_shiftr x y)

  | [ |- context [Z.to_N (Z.of_N ?x)]] =>
    rewrite N2Z.id
  end.

Opaque Z.shiftr Z.shiftl Z.land Z.eqb.

Ltac simpl' := cbn beta delta iota.

Ltac solve_nateq :=
  simpl'; standardize_nateq; simpl';
  try (
    let x := fresh in
    let Hlen := fresh in (

    eexists; intros x Hlen;
    list_destruct;
    repeat natize_iter;
    try reflexivity)).
