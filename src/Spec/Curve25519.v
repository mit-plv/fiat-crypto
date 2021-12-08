Require Import Coq.PArith.BinPosDef.
Require Import Spec.ModularArithmetic.
Local Open Scope positive_scope.

Notation p := (2^255-19).
Notation l := (2^252 + 27742317777372353535851937790883648493).
Notation l2 := (2^253 - 55484635554744707071703875581767296995).
Notation order := (8*l).
Notation twist_order := (4*l2).

Lemma orders_match : (2*(p + 1) - order = twist_order)%Z. Proof. exact eq_refl. Qed.

Require Import Coq.ZArith.Znumtheory Coq.Lists.List. Import ListNotations. 
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
