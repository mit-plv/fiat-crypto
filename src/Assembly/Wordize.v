
Require Export Bedrock.Word Bedrock.Nomega.
Require Import NArith PArith Ndigits Compare_dec Arith.
Require Import ProofIrrelevance Ring List.
Require Export MultiBoundedWord QhasmCommon.

Import ListNotations.

(* The base type of an n-vector of words *)
Inductive wvec: nat -> nat -> Type :=
  | VO: forall {n}, wvec n O
  | VS: forall {n k}, word n -> wvec n k -> wvec n (S k).

Definition vgets {n k} (v: wvec n (S k)): (word n) * (wvec n k).
  inversion v as [| n' k' w v']; refine (w, v').
Defined.

Definition vfunO {n} {T} (f: word n -> T): wvec n 1 -> T :=
  fun v => f (fst (vgets v)).

Definition vfunS {n k} {T} (f: wvec n k -> word n -> T): wvec n (S k) -> T :=
  fun v => match (vgets v) with | (w, v') => f v' w end.

(* The base type of an n-vector of bounded Ns *)
Inductive nvec: nat -> list N -> Type :=
  | NO: nvec O nil
  | NS: forall {k bs} b x, N.le x b -> nvec k bs -> nvec (S k) (cons b bs).

Definition ngets {k b bs} (v: nvec (S k) (cons b bs)): N * N * (nvec k bs).
  inversion v as [| k' bs' b' x p v']; refine (x, b', v').
Defined.

Definition nfunO {T b} (f: {x: N | N.le x b} -> T): nvec 1 [b] -> T.
  intro v; inversion v as [| k' bs' b' x p v']; refine (f (exist _ x p)).
Defined.

Definition nfunS {T k b bs} (f: nvec k bs -> {x: N | N.le x b} -> T):
    nvec (S k) (cons b bs) -> T.
  intro v; inversion v as [| k' bs' b' x p v']; refine (f v' (exist _ x p)).
Defined.

(* Conversion from nvec functions to wvec functions *)
Inductive nweq: forall {n k bs}, nvec k bs -> wvec n k -> Prop :=
  | nweqO: forall {n}, nweq NO (@VO n)
  | nweqS: forall {n b k bs' x p}
             (nv: nvec k bs') (wv: wvec n k),
      nweq nv wv -> nweq (NS b x p nv) (VS (NToWord n x) wv).

(* new word operations *)
Definition dmult {n} (a b: word n): (word n) * (word n) :=
  let d := NToWord (n + n) ((wordToN a) * (wordToN b))%N in
  (split1 n n d, split2 n n d).

Definition addWithCarry {n} (a b: word n): (word n) * bool :=
  let r := NToWord (S n) ((wordToN a) + (wordToN b))%N in
  (wtl r, whd r).

(* N to word lemmas *)
Lemma nw_plus: forall n x y,
    (n >= 1)%nat
  -> (x <= Npow2 (pred n))%N
  -> (y <= Npow2 (pred n))%N
  -> NToWord n (x + y)%N = (NToWord n x) ^+ (NToWord n y).
Admitted.

Lemma nw_awc: forall n x y,
    (n >= 1)%nat
  -> (x <= Npow2 (pred n))%N
  -> (y <= Npow2 (pred n))%N
  -> NToWord n (x + y)%N = fst (addWithCarry (NToWord n x) (NToWord n y)).
Admitted.

Lemma nw_dmult: forall n x y,
    (n >= 2)%nat
  -> (x <= Npow2 (n / 2)%nat)%N
  -> (y <= Npow2 (n / 2)%nat)%N
  -> NToWord n (x * y)%N = snd (dmult (NToWord n x) (NToWord n y)).
Admitted.

Lemma nw_mult: forall n x y,
    (n >= 2)%nat
  -> (x <= Npow2 (n / 2)%nat)%N
  -> (y <= Npow2 (n / 2)%nat)%N
  -> NToWord n (x * y)%N = wmult (NToWord n x) (NToWord n y).
Admitted.

Definition nwadd {T b} (f: forall x, N.le x b -> T): {x | N.le x b} -> T :=
  nweq na wa ->
  nweq nb wb ->
  nweq na wb
  fun s => (f (proj1_sig s) (proj2_sig s)).

(* Full Conversion example: steps are
    - Function over {x: N | N.le x b}.
    - Function over nvec.
    - Function over wvec.
    - Pseudo
 *)

Lemma nexample: forall b0 b1,
  (forall x0 x1, N.le x0 b0 -> N.le x1 b1 -> N) ->
  (nvec 2 [b0; b1] -> N).
Proof.
  intros b0 b1 f.
  apply nfunS; repeat apply (@nfunS ({x: N | N.le x _} -> N)).
  intros z s1 s0;
    destruct s0 as [s0x s0p];
    destruct s1 as [s1x s1p].
  refine (f s0x s1x s0p s1p).
Defined.
