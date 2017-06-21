Require Coq.ZArith.ZArith.

Lemma unit_eq (x y:unit) : x = y. destruct x, y; reflexivity. Qed.
Hint Resolve unit_eq.

Hint Extern 0 (_ = _ :> bool) => (
  match goal with
  | [H:Bool.eqb ?a ?b = true |- ?a = ?b ] => apply (proj1 (Bool.eqb_true_iff _ _) H)
  | [H:Bool.eqb ?b ?a = true |- ?a = ?b ] => symmetry; apply (proj1 (Bool.eqb_true_iff _ _) H)
  end).

Hint Extern 0 (_ = _ :> nat) => (
  match goal with
  | [H:Nat.eqb ?a ?b = true |- ?a = ?b ] => apply (proj1 (PeanoNat.Nat.eqb_eq _ _) H)
  | [H:Nat.eqb ?b ?a = true |- ?a = ?b ] => symmetry; apply (proj1 (PeanoNat.Nat.eqb_eq _ _) H)
  end).

Hint Extern 0 (_ <= _) => (
  match goal with
  | [H:Nat.ltb ?a ?b = true |- ?a < ?b ] => apply (proj1 (PeanoNat.Nat.ltb_lt _ _) H)
  end).

Hint Extern 0 (_ <= _) => (
  match goal with
  | [H:Nat.leb ?a ?b = true |- ?a <= ?b ] => apply (proj1 (PeanoNat.Nat.leb_le _ _) H)
  end).

Hint Extern 0 (_ = _ :> BinNums.N) => (
  match goal with
  | [H:BinNat.N.eqb ?a ?b = true |- ?a = ?b ] => apply (proj1 (BinNat.N.eqb_eq _ _) H)
  | [H:BinNat.N.eqb ?b ?a = true |- ?a = ?b ] => symmetry; apply (proj1 (BinNat.N.eqb_eq _ _) H)
  end).
Hint Extern 0 (_ = _ :> BinInt.Z) => (
  match goal with
  | [H:BinInt.Z.eqb ?a ?b = true |- ?a = ?b ] => apply (proj1 (BinInt.Z.eqb_eq _ _) H)
  | [H:BinInt.Z.eqb ?a ?b = true |- ?b = ?a ] => symmetry; apply (proj1 (BinInt.Z.eqb_eq _ _) H)
  end).
Hint Extern 0 (BinInt.Z.lt _ _) => (
  match goal with
  | [H:BinInt.Z.ltb ?a ?b = true |- BinInt.Z.lt ?a ?b ] => apply (proj1 (BinInt.Z.ltb_lt _ _) H)
  | [H:BinInt.Z.gtb ?b ?a = true |- BinInt.Z.lt ?a ?b ] => apply (proj1 (BinInt.Z.gtb_lt _ _) H)
  end).
Hint Extern 0 (BinInt.Z.le _ _) => (
  match goal with
  | [H:BinInt.Z.leb ?a ?b = true |- BinInt.Z.le ?a ?b ] => apply (proj1 (BinInt.Z.leb_le _ _) H)
  | [H:BinInt.Z.geb ?b ?a = true |- BinInt.Z.le ?a ?b ] => apply (proj1 (BinInt.Z.geb_le _ _) H)
  end).

Hint Extern 0 (_ = _ :> BinPos.positive) => (
  match goal with
  | [H:BinPos.Pos.eqb ?a ?b = true |- ?a = ?b ] => apply (proj1 (BinPos.Pos.eqb_eq _ _) H)
  | [H:BinPos.Pos.eqb ?a ?b = true |- ?b = ?a ] => symmetry; apply (proj1 (BinPos.Pos.eqb_eq _ _) H)
  end).
Hint Extern 0 (BinPos.Pos.lt _ _) => (
  match goal with
  | [H:BinPos.Pos.ltb ?a ?b = true |- BinPos.Pos.lt ?a ?b ] => apply (proj1 (BinPos.Pos.ltb_lt _ _) H)
  end).
Hint Extern 0 (BinPos.Pos.le _ _) => (
  match goal with
  | [H:BinPos.Pos.leb ?a ?b = true |- BinPos.Pos.le ?a ?b ] => apply (proj1 (BinPos.Pos.leb_le _ _) H)
  end).