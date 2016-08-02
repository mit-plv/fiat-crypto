Require Import Omega.
Require Import Crypto.Util.Sigma Crypto.Tactics.VerdiTactics.
Unset Asymmetric Patterns.

Inductive type := Nat | Prod : type -> type -> type.

Section expr.
  Context {var : type -> Type}.
  Inductive expr : type -> Type :=
  | Const : nat -> expr Nat
  | Var : forall {t}, var t -> expr t
  | Plus : expr Nat -> expr Nat -> expr Nat
  | NatBinop : (nat->nat->nat) -> expr Nat -> expr Nat -> expr Nat
  | Let : forall {tx}, expr tx -> forall {tC}, (var tx -> expr tC) -> expr tC
  | Pair : forall {t1 t2}, expr t1 -> expr t2 -> expr (Prod t1 t2)
  | MatchPair : forall {t1 t2}, expr (Prod t1 t2) -> forall {tC}, (var t1 -> var t2 -> expr tC) -> expr tC
  .
End expr.
Arguments expr _ _ : clear implicits.
Definition Expr t := forall var, expr var t.

Fixpoint tinterp t :=
  match t with
  | Nat => nat
  | Prod a b => prod (tinterp a) (tinterp b)
  end.

Fixpoint interp {t} (e:expr tinterp t) : tinterp t :=
  match e in expr _ t return tinterp t with
  | Const n => n
  | Var n => n
  | Plus e1 e2 => interp e1 + interp e2
  | NatBinop op e1 e2 => op (interp e1) (interp e2)
  | Let ex eC => interp (eC (interp ex))
  | Pair e1 e2 => (interp e1, interp e2)
  | MatchPair ep eC => let (v1, v2) := interp ep in interp (eC v1 v2)
  end.

Eval simpl in interp (Let (Const 7) (fun a =>
                                       Let (Let (Plus (Var a) (Var a)) (fun b => Pair (Var b) (Var b)))
                                           (fun p => MatchPair (Var p) (fun x y =>  Plus (Var x) (Var y)))
                     )).

Section commute_plus.
  Context {var : type -> Type}.
  Fixpoint commute_plus {t} (e:expr var t) : expr var t :=
    match e in expr _ t return expr var t with
    | Plus e1 e2 => Plus (commute_plus e2) (commute_plus e1)
                         
    | Const n => Const n
    | Var n => Var n
    | NatBinop op e1 e2 => NatBinop op (commute_plus e1) (commute_plus e2)
    | Let ex eC => Let (commute_plus ex) (fun x => commute_plus (eC x))
    | Pair e1 e2 => Pair (commute_plus e1) (commute_plus e2)
    | MatchPair ep eC => MatchPair (commute_plus ep) (fun x y => commute_plus (eC x y))
    end.
End commute_plus.

Ltac cases E :=
  match type of E with
  | _ => is_var E; destruct E
  | {_} + {_} => destruct E
  | _ => let HeqE := fresh "Heq" in destruct E eqn:HeqE
  end.

Lemma commute_plus_correct : forall {t} (e:expr tinterp t), interp (commute_plus e) = interp e.
  induction e; simpl; try cases (interp e);
    repeat match goal with [H: _ |- _ ] => rewrite H end;
    intuition omega.
Qed.

Section unmatch_pair.
  Context {var : type -> Type}.
  Definition CoqPairIfPair {t1 t2} (ep : expr var (Prod t1 t2)) : option (expr var t1 * expr var t2)
   := match ep in expr _ t return option (match t with
                                          | Prod t1 t2 => (expr var t1 * expr var t2)
                                          | _ => False
                                          end) with
      | Pair e1 e2 => Some (e1, e2)
      | _ => None
      end.



  Fixpoint unmatch_pair {t} (e:expr var t) : expr var t :=
    match e in expr _ t return expr var t with
    | MatchPair ep eC
      => match CoqPairIfPair (unmatch_pair ep) with
         | Some (e1, e2) => Let e1 (fun v1 => (Let e2 (fun v2 => unmatch_pair (eC v1 v2))))
         | None => MatchPair (unmatch_pair ep) (fun x y => unmatch_pair (eC x y))
         end
    | Const n => Const n
    | Var n => Var n
    | Plus e1 e2 => Plus (unmatch_pair e1) (unmatch_pair e2)
    | NatBinop op e1 e2 => NatBinop op (unmatch_pair e1) (unmatch_pair e2)
    | Let ex eC => Let (unmatch_pair ex) (fun x => unmatch_pair (eC x))
    | Pair e1 e2 => Pair (unmatch_pair e1) (unmatch_pair e2)
    end.
End unmatch_pair.

Ltac simpl_lem_then_rewrite lem :=
  let t := type of lem in
  let t' := (eval simpl in t) in
  let lem' :=  constr:(lem:t') in
  rewrite lem'.

Lemma CoqPairIfPair_Some_helper {var} {t} (ep:expr var t) :
  match t return expr var t -> Prop with
  | Prod _ _ => fun ep => forall e1 e2, CoqPairIfPair ep = Some (e1, e2) <-> ep = Pair e1 e2
  | _ => fun _ => True
  end ep.
Proof.
  unfold CoqPairIfPair; destruct ep; try break_match;
    repeat (intuition congruence || match goal with [H:_ |- _] => apply (f_equal CoqPairIfPair) in H end).
Qed.

Lemma CoqPairIfPair_Some {var} {t1 t2} (ep:expr var (Prod t1 t2)) e1 e2 :
    CoqPairIfPair ep = Some (e1, e2) <-> ep = Pair e1 e2.
Proof.
  simpl_lem_then_rewrite (CoqPairIfPair_Some_helper ep); reflexivity.
Qed.

Lemma unmatch_pair_correct : forall {t} (e:expr tinterp t), interp (unmatch_pair e) = interp e.
  induction e; simpl;
    try cases (interp e);
    repeat break_match; simpl;
    try find_apply_lem_hyp @CoqPairIfPair_Some;
    repeat match goal with
           | _ => solve [intuition]
           | _ => progress simpl @interp in *
           | [H: _ |- _ ] => rewrite H
           | [H: _, H': _ |- _ ] => rewrite H in H'
           | [H: (_, _) = (_, _) |- _ ] => inversion H; subst
           end.
Qed.