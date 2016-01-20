
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)


Require Import ZArith Znumtheory Zpow_facts.
Require Import CyclicAxioms DoubleCyclic BigN Cyclic31 Int31.
Require Import W.
Require Import Mod_op.
Require Import ZEll.
Require Import Bits.
Import CyclicAxioms DoubleType DoubleBase.


Set Implicit Arguments.

Open Scope Z_scope.


Record ex: Set := mkEx {
  vN : positive;
  vS : positive;
  vR:  List.list (positive * positive);
  vA:  Z;
  vB:  Z;
  vx:  Z;
  vy:  Z
}.

Coercion Local Zpos : positive >-> Z.

Record ex_spec (exx: ex): Prop := mkExS {
  n2_div: ~(2 | exx.(vN));
  n_pos: 2 < exx.(vN);
 lprime: 
  forall p : positive * positive, List.In p (vR exx) -> prime (fst p);
   lbig:
    4 * vN exx < (Zmullp (vR exx) - 1) ^ 2;
   inC:
    vy exx ^ 2 mod vN exx = (vx exx ^ 3 + vA exx * vx exx + vB exx) mod vN exx
}.

Section NEll.

Variable exx: ex.
Variable exxs: ex_spec exx.

Variable zZ: Type.
Variable op: ZnZ.Ops zZ.
Variable op_spec: ZnZ.Specs op.
Definition z2Z z :=  ZnZ.to_Z z.
Definition zN := snd (ZnZ.of_pos exx.(vN)).
Variable mop: mod_op zZ.
Variable mop_spec: mod_spec op zN mop.
Variable N_small:  exx.(vN) < base (ZnZ.digits op).

Lemma z2ZN: z2Z zN = exx.(vN).
apply (@ZnZ.of_Z_correct _ _ op_spec exx.(vN)); split; auto with zarith.
Qed.

Definition Z2z z :=
 match z mod exx.(vN) with
 | Zpos p => snd (ZnZ.of_pos p)
 | _ => ZnZ.zero
 end.

Definition S := exx.(vS).
Definition R := exx.(vR).
Definition A := Z2z exx.(vA).
Definition B := Z2z exx.(vB).
Definition xx := Z2z exx.(vx).
Definition yy := Z2z exx.(vy).
Definition c3 := Z2z 3.
Definition c2 := Z2z 2.
Definition c1 := Z2z 1.
Definition c0 := Z2z 0.

Inductive nelt: Type :=
  nzero | ntriple: zZ -> zZ -> zZ  -> nelt.

Definition pp := ntriple xx yy c1.

Definition nplus x y := mop.(add_mod) x y.
Definition nmul x y :=  mop.(mul_mod) x y.
Definition nsub x y :=  mop.(sub_mod) x y.
Definition neq x y := match ZnZ.compare x y with Eq => true | _ => false end.

Notation "x ++ y " := (nplus x y).
Notation "x -- y" := (nsub x y) (at level 50, left associativity).
Notation "x ** y" := (nmul x y) (at level 40, left associativity).
Notation "x ?= y" := (neq x y).

Definition ndouble: zZ -> nelt -> (nelt * zZ):= fun (sc: zZ) (p1: nelt) =>
 match p1 with
  nzero => (p1, sc)
 | (ntriple x1 y1 z1) =>
    if (y1 ?= c0) then (nzero, z1 ** sc) else
     (* we do 2p *)
    let m' := c3 ** x1 ** x1 ++ A ** z1 ** z1 in
    let l' := c2 ** y1 ** z1 in
    let m'2 := m' ** m' in
    let l'2 := l' ** l' in
    let l'3 := l'2 ** l' in
    let x3 := m'2 ** z1 -- c2 ** x1 ** l'2 in
    (ntriple
          (l' ** x3)
          (l'2 ** (m' ** x1 -- y1 ** l') -- m' ** x3)
          (z1 ** l'3), sc)
  end.


Definition nadd := fun (sc: zZ) (p1 p2: nelt) =>
 match p1, p2 with
  nzero, _ => (p2, sc)
 | _ , nzero => (p1, sc)
 | (ntriple x1 y1 z1), (ntriple x2 y2 z2) =>
  let d1 := x2 ** z1 in
  let d2 := x1 ** z2 in
  let l := d1 -- d2 in
  let dl := d1 ++ d2 in
  let m := y2 ** z1 -- y1 ** z2 in
  if (l ?= c0) then
   (* we have p1 = p2 o p1 = -p2 *)
   if (m ?= c0) then
    if (y1 ?= c0) then (nzero, z1 ** z2 ** sc) else
     (* we do 2p *)
    let m' := c3 ** x1 ** x1 ++ A ** z1 ** z1 in
    let l' := c2 ** y1 ** z1 in
    let m'2 := m' ** m' in
    let l'2 := l' ** l' in
    let l'3 := l'2 ** l' in
    let x3 := m'2 ** z1 -- c2 ** x1 ** l'2 in
    (ntriple
          (l' ** x3)
          (l'2 ** (m' ** x1 -- y1 ** l') -- m' ** x3)
          (z1 ** l'3), z2 ** sc)
    else (* p - p *)  (nzero, m ** z1 ** z2 ** sc)
  else
     let l2 := l ** l in
     let l3 := l2 ** l in
     let m2 := m ** m in
     let x3 := z1 ** z2 ** m2 -- l2 ** dl in
      (ntriple (l ** x3)
             (z2 ** l2 ** (m ** x1 -- y1 ** l) -- m ** x3)
             (z1 ** z2 ** l3), sc)
  end.


Definition nopp p := 
  match p with nzero => p | (ntriple x1 y1 z1) => (ntriple x1 (c0 -- y1) z1) end.

Fixpoint scalb (sc: zZ) (b:bool) (a: nelt) (p: positive) {struct p}:
 nelt * zZ :=
 match p with
   xH => if b then ndouble sc a else (a,sc)
 | xO p1 => let (a1, sc1) := scalb sc false a p1 in
              if b then 
                let (a2, sc2) := ndouble sc1 a1 in
                nadd sc2 a a2
              else ndouble sc1 a1
 | xI p1 => let (a1, sc1) := scalb sc true a p1 in
              if b then  ndouble sc1 a1
              else
              let (a2, sc2) := ndouble sc1 a1 in 
              nadd sc2 (nopp a) a2
 end.

Definition scal sc a p := scalb sc false a p.


Definition scal_list sc a l :=
  List.fold_left 
  (fun (asc: nelt * zZ) p1 => let (a,sc) := asc in scal sc a p1) l (a,sc).

Fixpoint scalL (sc:zZ) (a: nelt) (l: List.list positive) {struct l}: (nelt * zZ) :=
   match l with
     List.nil => (a,sc)
   | List.cons n l1 =>
        let (a1, sc1) := scal sc a n in
        let (a2, sc2) := scal_list sc1 a l1 in
          match a2 with
             nzero => (nzero, c0)
          |  ntriple _ _ z => scalL (sc2 ** z) a1 l1
          end
   end.

Definition zpow sc p n :=
  let (p,sc') := scal sc p n in
  (p, ZnZ.to_Z (ZnZ.gcd sc' zN)).

Definition e2E n := 
  match n with 
    nzero => ZEll.nzero
  | ntriple x1 y1 z1 => ZEll.ntriple (z2Z x1) (z2Z y1) (z2Z z1)
  end.


Definition wft t :=  z2Z t = (z2Z t) mod (z2Z zN).

Lemma vN_pos: 0 < exx.(vN).
red; simpl; auto.
Qed.

Hint Resolve vN_pos.

Lemma nplusz: forall x y, wft x -> wft y -> 
      z2Z (x ++ y) = ZEll.nplus (vN exx) (z2Z x) (z2Z y).
Proof.
intros x y Hx Hy.
unfold z2Z, nplus.
rewrite (mop_spec.(add_mod_spec) _ _ _ _ Hx Hy); auto.
rewrite <- z2ZN; auto.
Qed.

Lemma nplusw: forall x y, wft x -> wft y ->  wft (x ++ y).
Proof.
intros x y Hx Hy.
unfold wft.
pattern (z2Z (x ++ y)) at 2; rewrite (nplusz Hx Hy).
unfold ZEll.nplus; rewrite z2ZN.
rewrite Zmod_mod; auto.
apply (nplusz Hx Hy).
Qed.

Lemma nsubz: forall x y, wft x -> wft y -> 
      z2Z (x -- y) = ZEll.nsub (vN exx) (z2Z x) (z2Z y).
Proof.
intros x y Hx Hy.
unfold z2Z, nsub.
rewrite (mop_spec.(sub_mod_spec) _ _ _ _ Hx Hy); auto.
rewrite <- z2ZN; auto.
Qed.

Lemma nsubw: forall x y, wft x -> wft y ->  wft (x -- y).
Proof.
intros x y Hx Hy.
unfold wft.
pattern (z2Z (x -- y)) at 2; rewrite (nsubz Hx Hy).
unfold ZEll.nsub; rewrite z2ZN.
rewrite Zmod_mod; auto.
apply (nsubz Hx Hy).
Qed.

Lemma nmulz: forall x y, wft x -> wft y -> 
      z2Z (x ** y) = ZEll.nmul (vN exx) (z2Z x) (z2Z y).
Proof.
intros x y Hx Hy.
unfold z2Z, nmul.
rewrite (mop_spec.(mul_mod_spec) _ _ _ _ Hx Hy); auto.
rewrite <- z2ZN; auto.
Qed.

Lemma nmulw: forall x y, wft x -> wft y ->  wft (x ** y).
Proof.
intros x y Hx Hy.
unfold wft.
pattern (z2Z (x ** y)) at 2; rewrite (nmulz Hx Hy).
unfold ZEll.nmul; rewrite z2ZN.
rewrite Zmod_mod; auto.
apply (nmulz Hx Hy).
Qed.

Hint Resolve nmulw nplusw nsubw.


Definition wfe p := match p with
  ntriple x y z => wft x /\ wft y /\ wft z
| _ => True
end.

Lemma z2Zx: forall x, z2Z (Z2z x) = x mod exx.(vN).
unfold Z2z; intros x.
generalize (Z_mod_lt x exx.(vN)).
case_eq (x mod exx.(vN)).
intros _ _.
simpl; unfold z2Z; rewrite ZnZ.spec_0; auto.
intros p Hp HH; case HH; auto with zarith; clear HH.
intros _ HH1.
case (ZnZ.spec_to_Z zN).
generalize  z2ZN; unfold z2Z; intros HH; rewrite HH; auto.
intros _ H0.
set (v := ZnZ.of_pos p); generalize HH1.
rewrite (ZnZ.spec_of_pos p); fold v.
case (fst v).
  simpl; auto.
intros p1 H1.
contradict H0; apply Zle_not_lt.
apply Zlt_le_weak; apply Zle_lt_trans with (2:= H1).
apply Zle_trans with (1 * base (ZnZ.digits op) + 0); auto with zarith.
apply Zplus_le_compat; auto.
apply Zmult_gt_0_le_compat_r; auto with zarith.
  case (ZnZ.spec_to_Z (snd v)); auto with zarith.
  case p1; red; simpl; intros; discriminate.
  case (ZnZ.spec_to_Z (snd v)); auto with zarith.
intros p Hp; case (Z_mod_lt x exx.(vN)); auto with zarith.
rewrite Hp; intros HH; case HH; auto.
Qed.


Lemma z2Zx1: forall x, z2Z (Z2z x) = z2Z (Z2z x) mod z2Z zN.
Proof.
unfold Z2z; intros x.
generalize (Z_mod_lt x exx.(vN)).
case_eq (x mod exx.(vN)).
intros _ _.
simpl; unfold z2Z; rewrite ZnZ.spec_0; auto.
intros p H1 H2.
case (ZnZ.spec_to_Z zN).
generalize  z2ZN; unfold z2Z; intros HH; rewrite HH; auto.
intros _ H0.
case H2; auto with zarith; clear H2; intros _ H2.
rewrite Zmod_small; auto.
set (v := ZnZ.of_pos p).
split.
  case (ZnZ.spec_to_Z (snd v)); auto.
generalize H2; rewrite (ZnZ.spec_of_pos p); fold v.
case (fst v).
  simpl; auto.
intros p1 H.
contradict H0; apply Zle_not_lt.
apply Zlt_le_weak; apply Zle_lt_trans with (2:= H).
apply Zle_trans with (1 * base (ZnZ.digits op) + 0); auto with zarith.
apply Zplus_le_compat; auto.
apply Zmult_gt_0_le_compat_r; auto with zarith.
  case (ZnZ.spec_to_Z (snd v)); auto with zarith.
  case p1; red; simpl; intros; discriminate.
  case (ZnZ.spec_to_Z (snd v)); auto with zarith.
intros p Hp; case (Z_mod_lt x exx.(vN)); auto with zarith.
rewrite Hp; intros HH; case HH; auto.
Qed.


Lemma c0w: wft c0.
Proof.
red; unfold c0; apply z2Zx1.
Qed.

Lemma c2w: wft c2.
Proof.
red; unfold c2; apply z2Zx1.
Qed.

Lemma c3w: wft c3.
Proof.
red; unfold c3; apply z2Zx1.
Qed.

Lemma Aw: wft A.
Proof.
red; unfold A; apply z2Zx1.
Qed.

Hint Resolve c0w c2w c3w Aw.

Ltac nw :=
  repeat (apply nplusw || apply nsubw || apply nmulw || apply c2w ||
          apply c3w || apply Aw); auto.


Lemma nadd_wf: forall x y sc,
  wfe x -> wfe y -> wft sc ->
  wfe (fst (nadd sc x y)) /\  wft (snd (nadd sc x y)).
Proof.
intros x; case x; clear; auto.
intros x1 y1 z1 y; case y; clear; auto.
  intros x2 y2 z2 sc (wfx1,(wfy1, wfz1)) (wfx2,(wfy2, wfz2)) wfsc; 
    simpl; auto.
   case neq.
    2: repeat split; simpl; nw.
   case neq.
    2: repeat split; simpl; nw.
   case neq.
   repeat split; simpl; nw; auto.
   repeat split; simpl; nw; auto.
Qed.

 Lemma ztest: forall x y,
     x ?= y =Zeq_bool (z2Z x) (z2Z y).
 Proof.
 intros x y.
 unfold neq.
 rewrite (ZnZ.spec_compare x y); case Zcompare_spec; intros HH;
 match goal with H: context[x] |- _ =>
   generalize H; clear H; intros HH1
 end.
 symmetry; apply GZnZ.Zeq_iok; auto.
 case_eq (Zeq_bool (z2Z x) (z2Z y)); intros H1; auto;
   generalize HH1; generalize (Zeq_bool_eq _ _ H1); unfold z2Z;
   intros HH; rewrite HH; auto with zarith.
 case_eq (Zeq_bool (z2Z x) (z2Z y)); intros H1; auto;
   generalize HH1; generalize (Zeq_bool_eq _ _ H1); unfold z2Z;
   intros HH; rewrite HH; auto with zarith.
 Qed.

 Lemma zc0: z2Z c0 = 0.
 Proof.
 unfold z2Z, c0, z2Z; simpl.
 generalize ZnZ.spec_0; auto.
 Qed.


Ltac iftac t := 
  match t with 
   context[if ?x ?= ?y then _ else _] =>
      case_eq (x ?= y)
  end.

Ltac ftac := match goal with
  |- context[?x = ?y] => (iftac x); 
    let H := fresh "tmp" in 
     (try rewrite ztest; try rewrite zc0; intros H;
      repeat ((rewrite nmulz in H || rewrite nplusz in H || rewrite nsubz in H); auto);
      try (rewrite H; clear H))
    end.

Require Import Zmod.

Lemma c2ww: forall x, ZEll.nmul (vN exx) 2 x = ZEll.nmul (vN exx) (z2Z c2) x.
intros x; unfold ZEll.nmul.
unfold c2; rewrite z2Zx; rewrite Zmodml; auto.
Qed.
Lemma c3ww: forall x, ZEll.nmul (vN exx) 3 x = ZEll.nmul (vN exx) (z2Z c3) x.
intros x; unfold ZEll.nmul.
unfold c3; rewrite z2Zx; rewrite Zmodml; auto.
Qed.

Lemma Aww: forall x, ZEll.nmul (vN exx) exx.(vA) x = ZEll.nmul (vN exx) (z2Z A) x.
intros x; unfold ZEll.nmul.
unfold A; rewrite z2Zx; rewrite Zmodml; auto.
Qed.

Lemma nadd_correct: forall x y sc,
  wfe x -> wfe y -> wft sc ->
  e2E (fst (nadd sc x y)) = fst (ZEll.nadd exx.(vN) exx.(vA) (z2Z sc) (e2E x) (e2E y) )/\
  z2Z (snd (nadd sc x y)) = snd (ZEll.nadd exx.(vN) exx.(vA) (z2Z sc) (e2E x) (e2E y)).
Proof.
intros x; case x; clear; auto.
intros x1 y1 z1 y; case y; clear; auto.
  intros x2 y2 z2 sc (wfx1,(wfy1, wfz1)) (wfx2,(wfy2, wfz2)) wfsc; simpl.
  ftac.
  ftac.
  ftac.
  simpl; split; auto.
  repeat ((rewrite nmulz || rewrite nplusz || rewrite nsubz); auto).
  simpl; split; auto.
  repeat ((rewrite nmulz || rewrite nplusz || rewrite nsubz||
           rewrite c2ww || rewrite c3ww || rewrite Aww); try nw; auto).
  rewrite nmulz; auto.
  simpl; split; auto.
  repeat ((rewrite nmulz || rewrite nplusz || rewrite nsubz); auto).
  simpl; split; auto.
  repeat ((rewrite nmulz || rewrite nplusz || rewrite nsubz ||
           rewrite c2ww || rewrite c3ww || rewrite Aww); try nw; auto).
  Qed.

 Lemma ndouble_wf: forall x sc,
  wfe x -> wft sc ->
  wfe (fst (ndouble sc x)) /\  wft (snd (ndouble sc x)).
Proof.
intros x; case x; clear; auto.
intros x1 y1 z1 sc (wfx1,(wfy1, wfz1)) wfsc; 
    simpl; auto.
  repeat (case neq; repeat split; simpl; nw; auto).
Qed.


Lemma ndouble_correct: forall x sc,
  wfe x -> wft sc ->
  e2E (fst (ndouble sc x)) = fst (ZEll.ndouble exx.(vN) exx.(vA) (z2Z sc) (e2E x))/\
  z2Z (snd (ndouble sc x)) = snd (ZEll.ndouble exx.(vN) exx.(vA) (z2Z sc) (e2E x)).
Proof.
intros x; case x; clear; auto.
  intros x1 y1 z1 sc (wfx1,(wfy1, wfz1))  wfsc; simpl.
  ftac.
  simpl; split; auto.
  repeat ((rewrite nmulz || rewrite nplusz || rewrite nsubz); auto).
  simpl; split; auto.
  repeat ((rewrite nmulz || rewrite nplusz || rewrite nsubz ||
           rewrite c2ww || rewrite c3ww || rewrite Aww); try nw; auto).
  Qed.

Lemma nopp_wf: forall x, wfe x -> wfe (nopp x).
Proof.
intros x; case x; simpl nopp; auto.
intros x1 y1 z1 [H1 [H2 H3]]; repeat split; auto.
Qed.

Lemma scalb_wf: forall n b x sc,
  wfe x -> wft sc ->
  wfe (fst (scalb sc b x n)) /\  wft (snd (scalb sc b x n)).
Proof.
intros n; elim n; unfold scalb; fold scalb; auto.
  intros n1 Hrec b x sc H H1.
    case (Hrec true x sc H H1).
    case scalb; simpl fst; simpl snd.
    intros a1 sc1 H2 H3.
    case (ndouble_wf _ H2 H3); auto;
    case ndouble; simpl fst; simpl snd; intros x2 sc2 H4 H5.
    case b; auto.
    case (nadd_wf _ _ (nopp_wf _ H) H4 H5); auto;
    case ndouble; simpl fst; simpl snd; intros x2 sc2 H4 H5.
  intros n1 Hrec b x sc H H1.
    case (Hrec false x sc H H1).
    case scalb; simpl fst; simpl snd.
    intros a1 sc1 H2 H3.
    case (ndouble_wf _ H2 H3); auto;
    case ndouble; simpl fst; simpl snd; intros x2 sc2 H4 H5.
    case b; auto.
    case (nadd_wf _ _ H H4 H5); auto;
    case ndouble; simpl fst; simpl snd; intros x2 sc2 H4 H5.
intros b x sc H H1; case b; auto.
case (ndouble_wf _ H H1); auto.
Qed.


Lemma scal_wf: forall n x sc,
  wfe x -> wft sc ->
  wfe (fst (scal sc x n)) /\  wft (snd (scal sc x n)).
Proof.
intros n; exact (scalb_wf n false).
Qed.

Lemma nopp_correct: forall x,
  wfe x -> e2E x = ZEll.nopp exx.(vN) (e2E (nopp x)).
Proof.
intros x; case x; simpl; auto.
intros x1 y1 z1 [H1 [H2 H3]]; apply f_equal3 with (f := ZEll.ntriple); auto.
rewrite nsubz; auto.
rewrite zc0.
unfold ZEll.nsub, ninv; simpl.
apply sym_equal.
rewrite <- (Z_mod_plus) with (b := -(-z2Z y1 /exx.(vN))); auto with zarith.
rewrite <- Zopp_mult_distr_l.
rewrite <- Zopp_plus_distr.
rewrite Zmult_comm; rewrite Zplus_comm.
rewrite <- Z_div_mod_eq; auto with zarith.
rewrite Zopp_involutive; rewrite <- z2ZN.
apply sym_equal; auto.
Qed.

Lemma scalb_correct: forall n b x sc,
  wfe x -> wft sc ->
  e2E (fst (scalb sc b x n)) = fst (ZEll.scalb exx.(vN) exx.(vA) (z2Z sc) b (e2E x) n)/\
  z2Z (snd (scalb sc b x n)) = snd (ZEll.scalb exx.(vN) exx.(vA) (z2Z sc) b (e2E x) n).
Proof.
intros n; elim n; clear; auto.
intros p Hrec b x sc H1 H2.
  case b; unfold scalb; fold scalb.
    generalize (scalb_wf p true x H1 H2);
    generalize (Hrec true _ _ H1 H2); case scalb; simpl.
    case ZEll.scalb; intros r1 rc1; simpl.
    intros a2 sc2 (H3, H4) (H5, H6); subst r1 rc1.
    apply ndouble_correct; auto.
    generalize (scalb_wf p true x H1 H2);
    generalize (Hrec true _ _ H1 H2); case scalb; simpl.
    case ZEll.scalb; intros r1 rc1; simpl.
    intros a2 sc2 (H3, H4) (H5, H6); subst r1 rc1.
    generalize (ndouble_wf _ H5 H6); 
      generalize (ndouble_correct _ H5 H6); case ndouble; simpl.
    case ZEll.ndouble; intros r1 rc1; simpl.
    intros a3 sc3 (H7,H8) (H9,H10); subst r1 rc1.
    replace (ZEll.nopp (vN exx) (e2E x)) with
      (e2E (nopp x)).
    apply nadd_correct; auto. 
    generalize H1; case x; auto.
    intros x1 y1 z1 [HH1 [HH2 HH3]]; split; auto.
    rewrite nopp_correct; auto.
    apply f_equal2 with (f := ZEll.nopp); auto.
    generalize H1; case x; simpl; auto; clear x H1.
    intros x1 y1 z1 [HH1 [HH2 HH3]]; 
      apply f_equal3 with (f := ZEll.ntriple); auto.
    repeat rewrite nsubz; auto.
    rewrite zc0.
    unfold ZEll.nsub; simpl.
    rewrite <- (Z_mod_plus) with (b := -(-z2Z y1 /exx.(vN))); auto with zarith.
    rewrite <- Zopp_mult_distr_l.
    rewrite <- Zopp_plus_distr.
    rewrite Zmult_comm; rewrite Zplus_comm.
    rewrite <- Z_div_mod_eq; auto with zarith.
    rewrite Zopp_involutive; rewrite <- z2ZN.
    apply sym_equal; auto.
    generalize H1; case x; auto.
    intros x1 y1 z1 [HH1 [HH2 HH3]]; split; auto.
intros p Hrec b x sc H1 H2.
  case b; unfold scalb; fold scalb.
    generalize (scalb_wf p false x H1 H2);
    generalize (Hrec false _ _ H1 H2); case scalb; simpl.
    case ZEll.scalb; intros r1 rc1; simpl.
    intros a2 sc2 (H3, H4) (H5, H6); subst r1 rc1.
    generalize (ndouble_wf _ H5 H6); 
      generalize (ndouble_correct _ H5 H6); case ndouble; simpl.
    case ZEll.ndouble; intros r1 rc1; simpl.
    intros a3 sc3 (H7,H8) (H9,H10); subst r1 rc1.
    replace (ZEll.nopp (vN exx) (e2E x)) with
      (e2E (nopp x)).
    apply nadd_correct; auto.
    rewrite nopp_correct; auto.
    apply f_equal2 with (f := ZEll.nopp); auto.
    generalize H1; case x; simpl; auto; clear x H1.
    intros x1 y1 z1 [HH1 [HH2 HH3]]; 
      apply f_equal3 with (f := ZEll.ntriple); auto.
    repeat rewrite nsubz; auto.
    rewrite zc0.
    unfold ZEll.nsub; simpl.
    rewrite <- (Z_mod_plus) with (b := -(-z2Z y1 /exx.(vN))); auto with zarith.
    rewrite <- Zopp_mult_distr_l.
    rewrite <- Zopp_plus_distr.
    rewrite Zmult_comm; rewrite Zplus_comm.
    rewrite <- Z_div_mod_eq; auto with zarith.
    rewrite Zopp_involutive; rewrite <- z2ZN.
    apply sym_equal; auto.
    generalize H1; case x; auto.
    intros x1 y1 z1 [HH1 [HH2 HH3]]; split; auto.
    generalize (scalb_wf p false x H1 H2);
    generalize (Hrec false _ _ H1 H2); case scalb; simpl.
    case ZEll.scalb; intros r1 rc1; simpl.
    intros a2 sc2 (H3, H4) (H5, H6); subst r1 rc1.
    apply ndouble_correct; auto.
intros b x sc H H1.
case b; simpl; auto.
apply ndouble_correct; auto.
Qed.


Lemma scal_correct: forall n x sc,
  wfe x -> wft sc ->
  e2E (fst (scal sc x n)) = fst (ZEll.scal exx.(vN) exx.(vA) (z2Z sc) (e2E x) n)/\
  z2Z (snd (scal sc x n)) = snd (ZEll.scal exx.(vN) exx.(vA) (z2Z sc) (e2E x) n).
Proof.
intros n; exact (scalb_correct n false).
Qed. 

Lemma scal_list_correct: forall l x sc,
  wfe x -> wft sc ->
  e2E (fst (scal_list sc x l)) = fst (ZEll.scal_list exx.(vN) exx.(vA) (z2Z sc) (e2E x) l)/\
  z2Z (snd (scal_list sc x l)) = snd (ZEll.scal_list exx.(vN) exx.(vA) (z2Z sc) (e2E x) l).
Proof.
intros l1; elim l1; simpl; auto.
unfold scal_list, ZEll.scal_list; simpl; intros a l2 Hrec x sc H1 H2.
generalize (scal_correct a _ H1 H2) (scal_wf a _ H1 H2); case scal.
case ZEll.scal; intros r1 rsc1; simpl.
simpl; intros a1 sc1 (H3, H4) (H5, H6); subst r1 rsc1; auto.
Qed.

Lemma scal_list_wf: forall l x sc,
  wfe x -> wft sc ->
  wfe (fst (scal_list sc x l)) /\  wft (snd (scal_list sc x l)).
Proof.
intros l1; elim l1; simpl; auto.
unfold scal_list; intros a l Hrec x sc H1 H2; simpl.
generalize (@scal_wf a _ _ H1 H2); 
  case (scal sc x a); simpl; intros x1 sc1 [H3 H4]; auto.
Qed.

Lemma scalL_wf: forall l x sc,
  wfe x -> wft sc ->
  wfe (fst (scalL sc x l)) /\  wft (snd (scalL sc x l)).
Proof.
intros l1; elim l1; simpl; auto.
intros a l2 Hrec x sc H1 H2.
generalize (scal_wf a _ H1 H2); case scal; simpl.
intros a1 sc1 (H3, H4); auto.
generalize (scal_list_wf l2 _ H1 H4); case scal_list; simpl.
intros a2 sc2; case a2; simpl; auto.
intros x1 y1 z1 ((V1, (V2, V3)), V4); apply Hrec; auto.
Qed. 

Lemma scalL_correct: forall l x sc,
  wfe x -> wft sc ->
  e2E (fst (scalL sc x l)) = fst (ZEll.scalL exx.(vN) exx.(vA) (z2Z sc) (e2E x) l)/\
  z2Z (snd (scalL sc x l)) = snd (ZEll.scalL exx.(vN) exx.(vA) (z2Z sc) (e2E x) l).
Proof.
intros l1; elim l1; simpl; auto.
intros a l2 Hrec x sc H1 H2.
generalize (scal_wf a _ H1 H2) (scal_correct a _ H1 H2); case scal; simpl.
case ZEll.scal; intros r1 rsc1; simpl.
intros a1 sc1 (H3, H4) (H5, H6); subst r1 rsc1.
generalize (scal_list_wf l2 _ H1 H4) (scal_list_correct l2 _ H1 H4); case scal_list; simpl.
case ZEll.scal_list; intros r1 rsc1; simpl.
intros a2 sc2 (H7, H8) (H9, H10); subst r1 rsc1.
generalize H7; clear H7; case a2; simpl; auto.
rewrite zc0; auto.
intros x1 y1 z1 (V1, (V2, V3)); auto.
generalize (nmulw H8 V3) (nmulz H8 V3); intros V4 V5; rewrite <- V5.
apply Hrec; auto.
Qed.

Lemma f4 : wft (Z2z 4).
Proof.
red; apply z2Zx1.
Qed.

Lemma f27 : wft (Z2z 27).
Proof.
red; apply z2Zx1.
Qed.

Lemma Bw : wft B.
Proof.
red; unfold B; apply z2Zx1.
Qed.

Hint Resolve f4 f27 Bw.

Lemma mww: forall x y, ZEll.nmul (vN exx) (x mod (vN exx) ) y = ZEll.nmul (vN exx) x y.
intros x  y; unfold ZEll.nmul; rewrite Zmodml; auto.
Qed.

Lemma wwA: forall x, ZEll.nmul (vN exx) x exx.(vA) = ZEll.nmul (vN exx) x (z2Z A).
intros x; unfold ZEll.nmul.
unfold A; rewrite z2Zx; rewrite Zmodmr; auto.
Qed.

Lemma wwB: forall x, ZEll.nmul (vN exx) x exx.(vB) = ZEll.nmul (vN exx) x (z2Z B).
intros x; unfold ZEll.nmul.
unfold B; rewrite z2Zx; rewrite Zmodmr; auto.
Qed.

 Lemma  scalL_prime: 
  let a := ntriple (Z2z (exx.(vx))) (Z2z (exx.(vy))) c1 in
  let isc := (Z2z 4) ** A ** A ** A  ++ (Z2z 27) ** B ** B in
  let (a1, sc1) := scal isc a exx.(vS) in
  let (S1,R1) := psplit exx.(vR) in
  let (a2, sc2) := scal sc1 a1 S1 in
  let (a3, sc3) := scalL sc2 a2 R1 in
    match a3 with
     nzero => if (Zeq_bool (Zgcd (z2Z sc3) exx.(vN)) 1) then prime exx.(vN)
              else True
   | _ => True
   end.
  Proof.
  intros a isc.
  case_eq (scal isc a (vS exx)); intros a1 sc1 Ha1.
  case_eq (psplit (vR exx)); intros S1 R1 HS1.
  case_eq (scal sc1 a1 S1); intros a2 sc2 Ha2.
  case_eq (scalL sc2 a2 R1); intros a3 sc3; case a3; auto.
  intros Ha3; case_eq (Zeq_bool (Zgcd (z2Z sc3) (vN exx)) 1); auto.
  intros H1.
  assert (F0: 
     (vy exx mod vN exx) ^ 2 mod vN exx =
       ((vx exx mod vN exx) ^ 3 + vA exx * (vx exx mod vN exx) +
        vB exx) mod vN exx).
      generalize exxs.(inC).
      simpl; unfold Zpower_pos; simpl.
      repeat rewrite Zmult_1_r.
      intros HH.
      match goal with |- ?t1 = ?t2 => rmod t1; auto end.
      rewrite HH.
      rewrite Zplus_mod; auto; symmetry; rewrite Zplus_mod; auto; symmetry.
      apply f_equal2 with (f := Zmod); auto.
      apply f_equal2 with (f := Zplus); auto.
      rewrite Zplus_mod; auto; symmetry; rewrite Zplus_mod; auto; symmetry.
      apply f_equal2 with (f := Zmod); auto.
      apply f_equal2 with (f := Zplus); auto.
      rewrite Zmult_mod; auto; symmetry; rewrite Zmult_mod; auto; symmetry.
      apply f_equal2 with (f := Zmod); auto.
      apply f_equal2 with (f := Zmult); auto.
      rewrite Zmod_mod; auto.
      match goal with |- ?t1 = ?t2 => rmod t2; auto end.
      rewrite Zmult_mod; auto; symmetry; rewrite Zmult_mod; auto; symmetry.
      apply f_equal2 with (f := Zmod); auto.
      rewrite Zmod_mod; auto.
   generalize (@ZEll.scalL_prime exx.(vN) 
               (exx.(vx) mod exx.(vN))
               (exx.(vy) mod exx.(vN))
               exx.(vA)
               exx.(vB) 
               exxs.(n_pos) exxs.(n2_div) exx.(vR) 
               exxs.(lprime) exx.(vS) exxs.(lbig) F0); simpl.
generalize (@scal_wf (vS exx) a isc) (@scal_correct (vS exx) a isc).
unfold isc.
rewrite nplusz; auto; try nw; auto.
repeat rewrite nmulz; auto; try nw; auto.
  repeat rewrite z2Zx.
repeat rewrite wwA || rewrite wwB|| rewrite mww.
replace (e2E a) with (ZEll.ntriple (vx exx mod vN exx) (vy exx mod vN exx) 1).
case ZEll.scal.
fold isc; rewrite HS1; rewrite Ha1; simpl; auto.
intros r1 rsc1 HH1 HH2.
case HH1; clear HH1.
  unfold c1; repeat split; red; try apply z2Zx1.
  unfold isc; nw.
case HH2; clear HH2.
  unfold c1; repeat split; red; try apply z2Zx1.
  unfold isc; nw.
intros U1 U2 W1 W2; subst r1 rsc1.
generalize (@scal_wf S1 a1 sc1) (@scal_correct S1 a1 sc1).
case ZEll.scal.
intros r1 rsc1 HH1 HH2.
case HH1; clear HH1; auto.
case HH2; clear HH2; auto.
rewrite Ha2; simpl.
intros U1 U2 W3 W4; subst r1 rsc1.
generalize (@scalL_wf R1 a2 sc2) (@scalL_correct R1 a2 sc2).
case ZEll.scalL.
intros n; case n; auto.
rewrite Ha3; simpl.
intros rsc1 HH1 HH2.
case HH1; clear HH1; auto.
case HH2; clear HH2; auto.
intros _ U2 _ W5; subst rsc1.
rewrite H1; auto.
intros x1 y1 z1 sc4; rewrite Ha3; simpl; auto.
intros _ HH; case HH; auto.
intros; discriminate.
unfold a; simpl.
unfold c1; repeat rewrite z2Zx.
rewrite (Zmod_small 1); auto.
generalize exxs.(n_pos).
auto with zarith.
Qed.

End NEll.

Fixpoint plength (p: positive) : positive :=
  match p with
    xH => xH
  | xO p1 => Psucc (plength p1)
  | xI p1 => Psucc (plength p1)
  end.

Theorem plength_correct: forall p, (Zpos p < 2 ^ Zpos (plength p))%Z.
assert (F: (forall p, 2 ^ (Zpos (Psucc p)) = 2 * 2 ^ Zpos p)%Z).
intros p; replace (Zpos (Psucc p)) with (1 + Zpos p)%Z.
rewrite Zpower_exp; auto with zarith.
rewrite Zpos_succ_morphism; unfold Zsucc; auto with zarith.
intros p; elim p; simpl plength; auto.
intros p1 Hp1; rewrite F; repeat rewrite Zpos_xI.
assert (tmp: (forall p, 2 * p = p + p)%Z);
  try repeat rewrite tmp; auto with zarith.
intros p1 Hp1; rewrite F; rewrite (Zpos_xO p1).
assert (tmp: (forall p, 2 * p = p + p)%Z);
  try repeat rewrite tmp; auto with zarith.
rewrite Zpower_1_r; auto with zarith.
Qed.

Theorem plength_pred_correct: forall p, (Zpos p <= 2 ^ Zpos (plength (Ppred p)))
%Z.
intros p; case (Psucc_pred p); intros H1.
subst; simpl plength.
rewrite Zpower_1_r; auto with zarith.
pattern p at 1; rewrite <- H1.
rewrite Zpos_succ_morphism; unfold Zsucc; auto with zarith.
generalize (plength_correct (Ppred p)); auto with zarith.
Qed.

Definition pheight p := plength (Ppred (plength (Ppred p))).

Theorem pheight_correct: forall p, (Zpos p <= 2 ^ (2 ^ (Zpos (pheight p))))%Z.
intros p; apply Zle_trans with (1 := (plength_pred_correct p)).
apply Zpower_le_monotone; auto with zarith.
split; auto with zarith.
unfold pheight; apply plength_pred_correct.
Qed.

Definition isM2 p := 
  match p with
    xH   => false
|    xO _ => false
|     _ => true
end.

Lemma isM2_correct: forall p,
  if isM2 p then ~(Zdivide 2 p) /\ 2 < p else True.
Proof.
intros p; case p; simpl; auto; clear p.
intros p1; split; auto.
intros HH; inversion_clear HH.
generalize H; rewrite Zmult_comm.
case x; simpl; intros; discriminate.
case p1; red; simpl; auto.
Qed.

Definition ell_test (N S: positive) (l: List.list (positive * positive))
                      (A B x y: Z) :=
  let op := cmk_op (Peano.pred (nat_of_P (get_height 31 (plength N)))) in
  let mop := make_mod_op op (ZnZ.of_Z N) in
    if isM2 N then
    match (4 * N) ?= (ZEll.Zmullp l - 1) ^ 2  with
      Lt => 
       match y ^ 2 mod N ?= (x ^ 3 + A * x + B) mod N with
       Eq => 
          let ex := mkEx N S l A B x y in
          let a := ntriple (Z2z ex op x) (Z2z ex op y) (Z2z ex op 1)  in
          let A := (Z2z  ex op A) in
          let B := (Z2z  ex op B) in
          let d4 := (Z2z  ex op 4) in
          let d27 := (Z2z  ex op 27) in
          let da := mop.(add_mod) in
          let dm := mop.(mul_mod) in
          let isc := (da (dm (dm  (dm d4 A) A) A) (dm (dm d27 B) B)) in
          let (a1, sc1) := scal ex op mop isc a S in
          let (S1,R1) := ZEll.psplit l in
          let (a2, sc2) := scal ex op mop sc1 a1 S1 in
          let (a3, sc3) := scalL ex op mop sc2 a2 R1 in
          match a3 with
           nzero => if (Zeq_bool (Zgcd (z2Z op sc3) N) 1) then true
                    else false
          | _ => false
          end
      | _  => false
       end
    | _  => false
    end 
    else false.

Lemma Zcompare_correct: forall x y,
  match x ?= y with Eq => x = y | Gt => x > y | Lt => x < y end.
Proof.
intros x y; unfold Zlt, Zgt; generalize (Zcompare_Eq_eq x y); case Zcompare; auto.
Qed.

Lemma ell_test_correct: forall (N S: positive) (l: List.list (positive * positive))
                      (A B x y: Z),
  (forall p, List.In p l -> prime (fst p)) -> 
  if ell_test N S l A B x y then prime N else True.
intros N S1 l A1 B1 x y H; unfold ell_test.
generalize (isM2_correct N); case isM2; auto.
intros (H1, H2).
match goal with |- context[?x ?= ?y] =>
  generalize (Zcompare_correct x y); case Zcompare; auto
end; intros H3.
match goal with |- context[?x ?= ?y] =>
  generalize (Zcompare_correct x y); case Zcompare; auto
end; intros H4.
set (n := Peano.pred (nat_of_P (get_height 31 (plength N)))).
set (op := cmk_op n).
set (mop := make_mod_op op (ZnZ.of_Z N)).
set (exx := mkEx N S1 l A1 B1 x y).
set (op_spec := cmk_spec n).
assert (exxs: ex_spec exx).
  constructor; auto.
assert (H0: N < base (ZnZ.digits op)).
  apply Zlt_le_trans with (1 := plength_correct N).
  unfold op, base.
  rewrite cmk_op_digits.
  apply Zpower_le_monotone; split; auto with zarith.
  generalize (get_height_correct 31 (plength N)); unfold n.
  set (p := plength N).
  replace (Z_of_nat (Peano.pred (nat_of_P (get_height 31 p)))) with
       ((Zpos (get_height 31 p) - 1) ); auto with zarith.
  rewrite pred_of_minus; rewrite inj_minus1; auto with zarith.
  rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; auto with zarith.
  generalize (lt_O_nat_of_P (get_height 31 p)); auto with zarith.
assert (mspec: mod_spec op (zN exx op) mop).
  unfold mop; apply make_mod_spec; auto.
  rewrite ZnZ.of_Z_correct; auto with zarith.
generalize (@scalL_prime exx exxs _ op (cmk_spec n) mop mspec H0).
lazy zeta.
unfold c1, A, B,  nplus, nmul; 
  simpl exx.(vA); simpl exx.(vB); simpl exx.(vx); simpl exx.(vy);
  simpl exx.(vS); simpl exx.(vR); simpl exx.(vN).
case scal; intros a1 sc1.
case ZEll.psplit; intros S2 R2.
case scal; intros a2 sc2.
case scalL; intros a3 sc3.
case a3; auto.
case Zeq_bool; auto.
Qed.

Time Eval vm_compute in (ell_test
  329719147332060395689499
  8209062
  (List.cons (40165264598163841%positive,1%positive) List.nil)
  (-94080)
  9834496
  0
  3136).


Time Eval vm_compute in (ell_test
  1384435372850622112932804334308326689651568940268408537
  13077052794
  (List.cons (105867537178241517538435987563198410444088809%positive, 1%positive) List.nil)
  (-677530058123796416781392907869501000001421915645008494)
  0
  (-169382514530949104195348226967375250000355478911252124)
  1045670343788723904542107880373576189650857982445904291
).
