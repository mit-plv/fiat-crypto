From Coq Require Import BinPosDef.
Require Import Spec.ModularArithmetic.
Local Open Scope positive_scope.

Notation p := (2^255-19).
Notation l := (2^252 + 27742317777372353535851937790883648493).
Notation l2 := (2^253 - 55484635554744707071703875581767296995).
Notation order := (8*l).
Notation twist_order := (4*l2).

Lemma orders_match : (2*(p + 1) - order = twist_order)%Z. Proof. exact eq_refl. Qed.

From Coq Require Import Znumtheory List. Import ListNotations. 
From Coqprime.PrimalityTest Require Import Pocklington PocklingtonCertificat.

Lemma prime_p : prime p.
Proof.
  simple refine (Pocklington_refl (Pock_certif _ 2
    [(74058212732561358302231226437062788676166966415465897661863160754340907, 1); (2, 2)] 1)
  [ Pock_certif 74058212732561358302231226437062788676166966415465897661863160754340907 2
    [(31757755568855353, 1); (57467, 1); (353, 1); (2, 1)] 2028478494862525422475606;
  Pock_certif 31757755568855353 10 [(223, 1); (107, 1); (3, 1); (2, 3)] 539560;
  Pock_certif 57467 2 [(59, 1); (2, 1)] 14;
  Pock_certif 353 3 [(2, 5)] 1;
  Pock_certif 223 3 [(3, 1); (2, 1)] 1;
  Pock_certif 107 2 [(53, 1); (2, 1)] 1;
  Pock_certif 59 2 [(29, 1); (2, 1)] 1;
  Pock_certif 53 2 [(2, 2)] 4;
  Pock_certif 29 2 [(2, 2)] 1;
  Proof_certif 3 prime_3;
  Proof_certif 2 prime_2
  ] _).
  native_cast_no_check (@eq_refl bool true).
Qed. (* 1s *)

Lemma prime_l : prime l.
Proof.
  simple refine (Pocklington_simple_computational l 276602624281642239937218680557139826668747 2
  (Pocklington_refl(Pock_certif _ 2 [(19757330305831588566944191468367130476339, 1); (2, 1)] 1)
  [Pock_certif 19757330305831588566944191468367130476339 2     [(213441916511, 1); (269, 1); (2, 1)] 150181583887270;
  Pock_certif 213441916511 13 [(292386187, 1); (2, 1)] 1;
  Pock_certif 292386187 2 [(307, 1); (2, 1)] 961;
  Pock_certif 307 5 [(3, 1); (2, 1)] 1;
  Pock_certif 269 2 [(67, 1); (2, 2)] 1; Pock_certif 67 2 [(3, 1); (2, 1)] 1;
  Proof_certif 3 prime_3; Proof_certif 2 prime_2] _)
  _ _ _ _ _ _ _ _).
  1: native_cast_no_check (@eq_refl bool true).
  all : native_compute; exact eq_refl.
Qed. (* 1.3s *)

Lemma prime_l2 : prime l2.
Proof.
  simple refine (Pocklington_refl (Pock_certif _ 2
    [(27413359092552162435694767700453926735143482401279781, 1); (2, 2)] 1)
  [Pock_certif 27413359092552162435694767700453926735143482401279781 2
    [(104719073621178708975837602950775180438320278101, 1); (2, 2)] 1;
  Pock_certif 104719073621178708975837602950775180438320278101 2
    [(203852586375664218368381551393371968928013, 1); (2, 2)] 1;
  Pock_certif 203852586375664218368381551393371968928013 2
    [(1013266244677, 1); (743104567, 1); (2, 2)] 1;
  Pock_certif 1013266244677 2 [(383, 1); (7, 1); (2, 2)] 7406;
  Pock_certif 743104567 3 [(3637, 1); (2, 1)] 322;
  Pock_certif 3637 2 [(3, 1); (2, 2)] 11;
  Pock_certif 383 5 [(191, 1); (2, 1)] 1;
  Pock_certif 191 7 [(5, 1); (2, 1)] 1; Pock_certif 7 3 [(2, 1)] 1;
  Pock_certif 5 2 [(2, 2)] 1;
  Proof_certif 3 prime_3; 
  Proof_certif 2 prime_2] _).
  native_cast_no_check (@eq_refl bool true).
Time Qed. (* 1s *)

Local Notation F := (F p).

Require PrimeFieldTheorems.

Lemma field : @Hierarchy.field F eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div.
Proof. apply PrimeFieldTheorems.F.field_modulo, prime_p. Qed.
Lemma char_ge_3 : @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul 3.
Proof. eapply Hierarchy.char_ge_weaken; try apply ModularArithmeticTheorems.F.char_gt; Decidable.vm_decide. Qed.

Require Import Spec.CompleteEdwardsCurve.
Module E.
  Definition a : F := F.opp 1.
  Definition d : F := F.div (F.opp (F.of_Z _ 121665)) (F.of_Z _ 121666).

  Lemma nonzero_a : a <> F.zero. Proof. Decidable.vm_decide. Qed.
  Lemma square_a : exists sqrt_a, F.mul sqrt_a sqrt_a = a.
  Proof. epose (@PrimeFieldTheorems.F.Decidable_square p prime_p eq_refl); Decidable.vm_decide. Qed.
  Lemma nonsquare_d : forall x, F.mul x x <> d.
  Proof. epose (@PrimeFieldTheorems.F.Decidable_square p prime_p eq_refl); Decidable.vm_decide. Qed.

  Definition point := @E.point F eq F.one F.add F.mul a d.
  Definition add := E.add(field:=field)(char_ge_3:=char_ge_3)(a:=a)(d:=d)
    (nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d).
  Definition zero := E.zero(field:=field)(a:=a)(d:=d)(nonzero_a:=nonzero_a).
  Definition B : E.point.
    refine (
    exist _ (F.of_Z _ 15112221349535400772501151409588531511454012693041857206046113283949847762202, F.div (F.of_Z _ 4) (F.of_Z _ 5)) _).
    Decidable.vm_decide.
  Defined.
End E.

Require Import Spec.MontgomeryCurve.
Module M.
  Definition a : F := F.of_Z _ 486662.
  Definition b : F := F.one.
  Definition a24 : F := ((a - F.of_Z _ 2) / F.of_Z _ 4)%F.
  Definition point := @M.point F eq F.add F.mul a b.
  Definition B : point :=
    exist _ (inl (F.of_Z _ 9, F.of_Z _ 14781619447589544791020593568409986887264606134616475288964881837755586237401)) eq_refl.

  Lemma a2m4_nonzero : F.sub (F.mul a a) (F.of_Z _ 4) <> F.zero. Decidable.vm_decide. Qed.
  Lemma a2m4_nonsq : ~(exists r, F.mul r r = F.sub (F.mul a a) (F.of_Z _ 4)).
  Proof. epose (@PrimeFieldTheorems.F.Decidable_square p prime_p eq_refl); Decidable.vm_decide. Qed.
  Lemma b_nonzero : b <> F.zero. Decidable.vm_decide. Qed.

  Definition add := (M.add(field:=field)(char_ge_3:=char_ge_3)(a:=a)(b_nonzero:=b_nonzero)).
  Definition opp := (M.opp(field:=field)(a:=a)(b_nonzero:=b_nonzero)).
  Definition X0 := (M.X0(Feq:=eq)(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(b:=b)).
  Definition scalarmult := (@ScalarMult.scalarmult_ref _ add M.zero opp).
End M.

Definition clamp k := let s := k/8 mod 2^251 in 8*(2^251 + s).
