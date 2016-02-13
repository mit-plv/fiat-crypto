Require Import Znumtheory BinInt BinNums.
Require Import Eqdep_dec.
Require Import EqdepFacts.

Lemma Z_mod_mod x m : x mod m = (x mod m) mod m.
  symmetry.
  destruct (BinInt.Z.eq_dec m 0).
  - subst; rewrite !Zdiv.Zmod_0_r; reflexivity.
  - apply BinInt.Z.mod_mod; assumption.
Qed.

Lemma exist_reduced_eq: forall (m : Z) (a b : Z), a = b -> forall pfa pfb,
    exist (fun z : Z => z = z mod m) a pfa =
    exist (fun z : Z => z = z mod m) b pfb.
Proof.
Admitted.

Definition opp_impl:
  forall {m : BinNums.Z},
    {opp0 : {z : BinNums.Z | z = z mod m} -> {z : BinNums.Z | z = z mod m} |
     forall x : {z : BinNums.Z | z = z mod m},
       exist (fun z : BinNums.Z => z = z mod m)
             ((proj1_sig x + proj1_sig (opp0 x)) mod m)
             (Z_mod_mod (proj1_sig x + proj1_sig (opp0 x)) m) =
       exist (fun z : BinNums.Z => z = z mod m) (0 mod m) (Z_mod_mod 0 m)}.
  intro m.
  refine (exist _ (fun x => exist _ ((m-proj1_sig x) mod m) _) _); intros.

  destruct x;
  simpl;
  apply exist_reduced_eq;
  rewrite Zdiv.Zplus_mod_idemp_r;
  replace (x + (m - x)) with m by omega;
  apply Zdiv.Z_mod_same_full.

  Grab Existential Variables.
  destruct x; simpl.
  rewrite Zdiv.Zmod_mod; reflexivity.
Defined.