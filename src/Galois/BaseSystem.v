Require Import List.
Require Import ZArith.ZArith.

Local Open Scope Z.
Local Open Scope list_scope.

Module Type BaseCoefs.
  (* lists coefficients of digits and the digits themselves always have the
  * LEAST significant position first. *)
  Definition coefs : Type := list Z.

  Parameter bs : coefs.
  Axiom bs_good :
    forall i j,
    let b := nth_default 0 bs in
    exists r,
    b i * b j = r * b (i+j)%nat.
End BaseCoefs.

Module BaseSystem (Import B:BaseCoefs).
  Definition digits : Type := list Z.

  Definition accumulate p acc := fst p * snd p + acc.
  Definition decode u  := fold_right accumulate 0 (combine u bs).

	Fixpoint add (us vs:digits) : digits :=
		match us,vs with
			| u::us', v::vs' => (u+v)::(add us' vs')
			| _, nil => us
			| _, _ => vs
		end.
  Local Infix ".+" := add (at level 50).

  Lemma add_rep : forall us vs, decode (add us vs) = decode us + decode vs.
  Proof.
    unfold decode, accumulate.
    induction bs; destruct us; destruct vs; auto; simpl; try rewrite IHc; ring.
  Qed.

  (* mul' is a valid multiplication algorithm if b_i = b_1^i *)
  Fixpoint mul' (us vs:digits) : digits :=
		match us,vs with
			| u::us', v::vs' => u*v :: map (Z.mul u) vs' .+ mul' us' vs
			| _, _ => nil
		end.

  (* UPNEXT: multiplication for arbitrary good bs *)
End BaseSystem.
