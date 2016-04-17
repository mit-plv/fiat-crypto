
Require Import ZArith NArith NPeano.
Require Import QhasmCommon.
Require Export Bedrock.Word.

Module Util.

    Inductive Either A B := | xleft: A -> Either A B | xright: B -> Either A B.

    Definition indexToNat {lim: nat} (i: Index lim): nat := proj1_sig i.
    Coercion indexToNat : Index >-> nat.

    (* Float Manipulations *)

    Definition getFractionalBits {n} (reg: FReg n): nat :=
      if (Nat.eq_dec n 32) then 23 else
      if (Nat.eq_dec n 64) then 52 else 0.

    Definition getFloatInstance {n} (reg: FReg n): Float n (getFractionalBits reg).
      refine match reg with
      | regFloat32 _ => (eq_rect _ id Float32 _ _)
      | regFloat64 _ => (eq_rect _ id Float64 _ _)
      end; abstract intuition.
    Defined.

    (* Magical Bitwise Manipulations *)

    (* Force w to be m bits long, by truncation or zero-extension *)
    Definition trunc {n} (m: nat) (w: word n): word m.
      destruct (lt_eq_lt_dec n m) as [s|s]; try destruct s as [s|s].

    - replace m with (n + (m - n)) by abstract intuition.
        refine (zext w (m - n)).

    - rewrite <- s; assumption.

    - replace n with (m + (n - m)) in w by abstract intuition.
        refine (split1 m (n-m) w).
    Defined.

    (* Get the index-th m-bit block of w *)
    Definition getIndex {n} (w: word n) (m index: nat): word m.
      replace n with
        ((min n (m * index)) + (n - (min n (m * index))))%nat
        in w by abstract (
        assert ((min n (m * index)) <= n)%nat
            by apply Nat.le_min_l;
        intuition).

      refine
        (trunc m
        (split2 (min n (m * index)) (n - min n (m * index)) w)).
    Defined.

    (* set the index-th m-bit block of w to s *)
    Definition setInPlace {n m} (w: word n) (s: word m) (index: nat): word n :=
      (w ^& (wnot (trunc n (combine (wones m) (wzero (index * m)%nat)))))
         ^| (trunc n (combine s (wzero (index * m)%nat))).

    (* Iterating Stack Operations *)
    Lemma getStackWords_spec: forall {n} (x: Stack n), n = 32 * (getStackWords x).
    Proof. intros; destruct x; simpl; intuition. Qed.

    Definition segmentStackWord {n} (x: Stack n) (w: word n): word (32 * (getStackWords x)).
      intros; destruct x; simpl; intuition.
    Defined.

    Definition desegmentStackWord {n} (x: Stack n) (w: word (32 * (getStackWords x))): word n.
      intros; destruct x; simpl; intuition.
    Defined.

 End Util.
