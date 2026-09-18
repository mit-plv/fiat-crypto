From Stdlib Require Export ZmodDef ZstarDef.
From Stdlib Require Import NArith ZArith ZModOffset Lia.
From Stdlib Require Import Bool.Bool Lists.List.
Require Import Crypto.Util.Factoring.
Import ListNotations.
Local Open Scope Z_scope.
Local Coercion Zmod.unsigned : Zmod.Zmod >-> Z.
Local Coercion Z.pos : positive >-> Z.
Local Coercion N.pos : positive >-> N.
Local Coercion Z.of_N : N >-> Z.

Import ZmodDef.Zmod.

(** ** Square roots modulo primes *)

Section WithAB.
Context {m} (phi_m : positive) (a b : Zmod m).
Local Infix "*" := mul.
Local Infix "^" := pow.
Local Fixpoint chase_sqrt (apow : positive) (bpow : N) :=
  match apow with
  | xO apow => if Zmod.eqb (a^apow * b^N.div2 bpow) one
               then chase_sqrt apow (N.div2 bpow)
               else chase_sqrt apow (N.div2 bpow + N.div2 phi_m)%N
  | xI apow => a^Pos.succ apow * b ^ N.div2 bpow
  | xH =>      a               * b ^ N.div2 bpow
  end.
End WithAB.

Local Definition sqrtp_given_nonsquare {p} (a nonsquare : Zmod p) :=
  @chase_sqrt p (Pos.pred (Z.to_pos p)) a nonsquare (Z.to_pos (Z.div2 (Z.pred p))) 0.

(* NOTE: this definition is intended to be replacable with one that does not compute [elements m] *)
Local Definition find {m} f := find f (elements m).

Definition nonsquare p : Zmod p :=
  match find (fun b => eqb (pow b ((p-1)/2)) (opp (@one p))) with
  | Some b => b
  | None => one
  end.

Definition sqrtsp {p} (a : Zmod p) : option (Zmod p * Zmod p) :=
  let x := sqrtp_given_nonsquare a (nonsquare p) in
  if eqb (pow x 2) a then Some (abs x, opp (abs x)) else None.

Definition sqrtspl {p} (a : Zmod p) := 
  match sqrtsp a with
  | None => []
  | Some (x, y) => [x; y]
  end.

Definition sqrtp {p} (a : Zmod p) : Zmod p := hd zero (sqrtspl a).

(** ** Square roots modulo powers of 2 *)

Local Fixpoint sqrtp2odd' (n : nat) (a : Z) : Z :=
  Z.land (Z.ones (Z.of_nat n))
  match n with
  |0%nat|1%nat|2%nat|3%nat => 1
  |S n => let x := sqrtp2odd' n a in
          let k := Z.shiftr (x^2-a) (Z.of_nat n) in
          x + Z.shiftl k (Z.pred (Z.of_nat n))
  end.

Definition sqrtsp2odd {k : Z} (a : bits k) : option ((_ * _) * (_ * _)) :=
  if Z.land a (Z.ones 3) =? 1
  then Some (
    let x := of_Z (2^k) (sqrtp2odd' (Z.to_nat k) a) in
    let y := add x (of_Z (2^k) (Z.shiftl 1 (k-1))) in
    let p := (abs x, opp (abs x)) in
    let q := (abs y, opp (abs y)) in
    if fst p <? fst q then (p,q) else (q, p))
  else None.

Definition sqrtsp2nz {k} (a : bits k) : option ((_ * _) * (_ * _)) :=
  let v := val 2 (Z.to_pos a) in
  if N.odd v then None
  else match sqrtsp2odd (sru a v) with 
  | None => None
  | Some ((a,b), (c,d)) =>
    let s := N.div2 v in
    Some ((slu a s, slu b s), (slu c s, slu d s))
  end.

Definition sqrtsp2nzl {k} (a : bits k) :=
  match sqrtsp2nz a with 
  | Some ((a,b), (c,d)) => [a; b; c; d]
  | None => nil
  end.

(* slow *)
Definition sqrtsp2z k : list (bits k) :=
  List.filter (fun x => eqb (pow x 2) zero) (elements (2^k)).
(*
Compute List.forallb (fun n => let n := Z.of_nat n in
(2^(n/2) =? Z.of_nat (length (sqrtp2z n)))
) (seq 1 12).
*)

Definition sqrtsp2 {k} (a : bits k) : list (bits k) :=
  if Zmod.eqb zero a then sqrtsp2z k else sqrtsp2nzl a.

Definition sqrtp2 {k} (a : bits k) : bits k :=
  if Zmod.eqb zero a then zero else hd zero (sqrtsp2 a).

(** ** Square roots modulo powers of odd primes *)

Section WithP.
  Context (p : Z).
  Context (sqrt_p_a : Z).
  Local Fixpoint liftSqrtPop (lgk : nat) (a : Z) : Z :=
    match lgk with
    | O => sqrt_p_a
    | S lgk' =>
        let q := p^two_power_nat lgk' in
        let x := liftSqrtPop lgk' (a mod q) in
        x + ((x^2 - a)/q * Z.invmod (-2*x) q) mod q * q
    end.
End WithP.

Definition sqrtspop {p k} (a : Zmod (p^k)) : option (Zmod (p^k) * Zmod (p^k)) :=
  if Zmod.eqb zero a then Some (zero, zero) else
  let v := val (Z.to_pos p) (Z.to_pos a) in
  if N.odd v then None else
  let a := a / p^v in
  match sqrtsp (Zmod.of_Z p a) with
  | None => None
  | Some (x, y) =>
      let r := Zmod.of_Z (p^k) (p^N.div2 v) in
      let lift x := Zmod.of_Z _ (liftSqrtPop p x (Z.to_nat (Z.log2_up k)) a) in
      Some (mul r (lift x), mul r (lift y))
  end.

Definition sqrtspopl {p k} (a : Zmod (p^k)) : list (Zmod (p^k)) :=
  match sqrtspop a with
  | Some (x, y) => [x; y]
  | None => []
  end.

Definition sqrtspp {p k} : Zmod (p^k) -> list (Zmod (p^k)) :=
  match Z.eq_dec 2 p with
  | left eq_2_p => match eq_2_p with eq_refl => sqrtsp2 end
  | right _ => sqrtspopl
  end.

Definition sqrtpp {p k} (a : Zmod (p^k)) := hd zero (sqrtspp a).

Definition combinecongs (congs : list (Z * Z)) :=
  fold_right (fun '(r1, m1) '(r2, m2) => (Zcong.Z.combinecong m1 m2 r1 r2, m1*m2)) (0, 1) congs.

Definition sqrtmod' a m : Z :=
  fst (combinecongs (map (fun '(p, k) =>
    (Zmod.to_Z (sqrtpp (Zmod.of_Z (Z.pos p^Z.pos k) a)), p^k))
  (ppfactor m))).
Definition sqrtmod a m :=
  let r := sqrtmod' a m in 
  if r * r mod m =? a then r else 0.

Definition sqrtsmod a m : list Z :=
  let rs :=
  ((map (fun '(p, k) =>
    (map Zmod.to_Z (sqrtspp (Zmod.of_Z (Z.pos p^Z.pos k) a)), p^k))
  (ppfactor m))) in
  fst (List.fold_right (fun '(xs, m) '(ys, M) =>
  (map (uncurry (Z.combinecong m M)) (list_prod xs ys), m*M)
  ) ([0], 1) rs).

Compute let m := (3*5*7)%positive in 
        let a := 4 in
        let sqrts := sqrtsmod a m in
        (forallb (fun x => (x*x mod m =? a mod m)) sqrts, sqrts).

Compute let m := (11)%positive in 
        map (fun a => let a := Z.of_nat a in
        let sqrts := sqrtsmod a m in
        (forallb (fun x => (x*x mod m =? a mod m)) sqrts, sqrts))
        (seq 0 (Pos.to_nat m)).

Compute ppfactor 11.

Compute let m := (11)%positive in 
        map (fun a => let a := Z.of_nat a in
        let sqrts := map Zmod.to_Z (sqrtspl (Zmod.of_Z m a)) in
        (a, forallb (fun x => (x*x mod m =? a mod m)) sqrts, sqrts))
        (seq 0 (Pos.to_nat m)).

Compute let m := (11)%positive in 
        map (fun a => let a := Z.of_nat a in
        (a, filter (fun x => let x := Z.of_nat x in (x*x mod m =? a mod m)) (seq 0 (Pos.to_nat m))))
        (seq 0 (Pos.to_nat m)).

Compute sqrtp_given_nonsquare (Zmod.of_Z 11 1) (Zmod.of_Z _ 2).

Definition Zstar_sqrtp {p} (a : Zstar.Zstar p) : Zstar.Zstar p := Zstar.of_Zmod (sqrtp (Zstar.to_Zmod a)).

Definition Zstar_sqrtpp {p k} (a : Zstar.Zstar (p^k)) := Zstar.of_Zmod (sqrtpp (Zstar.to_Zmod a)).
