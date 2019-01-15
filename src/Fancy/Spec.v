Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.

(* Condition code flags *)
Module CC.
  Inductive code : Type :=
  | C : code
  | M : code
  | L : code
  | Z : code
  .

  Record state :=
    { cc_c : bool; cc_m : bool; cc_l : bool; cc_z : bool }.

  Definition code_dec (x y : code) : {x = y} + {x <> y}.
  Proof. destruct x, y; try apply (left eq_refl); right; congruence. Defined.

  Definition update (to_write : list code) (result : BinInt.Z) (cc_spec : code -> BinInt.Z -> bool) (old_state : state)
    : state :=
    {|
      cc_c := if (In_dec code_dec C to_write)
              then cc_spec C result
              else old_state.(cc_c);
      cc_m := if (In_dec code_dec M to_write)
              then cc_spec M result
              else old_state.(cc_m);
      cc_l := if (In_dec code_dec L to_write)
              then cc_spec L result
              else old_state.(cc_l);
      cc_z := if (In_dec code_dec Z to_write)
              then cc_spec Z result
              else old_state.(cc_z)
    |}.

End CC.

Section Language.
  Record instruction :=
    {
      num_source_regs : nat;
      writes_conditions : list CC.code;
      spec : tuple Z num_source_regs -> CC.state -> Z
    }.

  Section expr.
    Context {name : Type} (name_eqb : name -> name -> bool) (wordmax : Z) (cc_spec : CC.code -> Z -> bool).

    Inductive expr :=
    | Ret : name -> expr
    | Instr (i : instruction)
            (rd : name) (* destination register *)
            (args : tuple name i.(num_source_regs)) (* source registers *)
            (cont : expr) (* next line *)
      : expr
    .

    Fixpoint interp (e : expr) (cc : CC.state) (ctx : name -> Z) : Z :=
      match e with
      | Ret n => ctx n
      | Instr i rd args cont =>
        let result := i.(spec) (Tuple.map ctx args) cc in
        let new_cc := CC.update i.(writes_conditions) result cc_spec cc in
        let new_ctx := (fun n => if name_eqb n rd then result mod wordmax else ctx n) in
        interp cont new_cc new_ctx
      end.
  End expr.
End Language.

Section Instructions.
  Import CC.

  Definition cc_spec (x : CC.code) (result : BinInt.Z) : bool :=
    match x with
    | C => Z.testbit result 256 (* carry bit *)
    | M => Z.testbit result 255 (* most significant bit *)
    | L => Z.testbit result 0   (* least significant bit *)
    | Z => result =? 0          (* whether equal to zero *)
    end.

  Definition lower128 x := (Z.land x (Z.ones 128)).
  Definition upper128 x := (Z.shiftr x 128).
  Local Notation "x '[C]'" := (if x.(cc_c) then 1 else 0) (at level 20).
  Local Notation "x '[M]'" := (if x.(cc_m) then 1 else 0) (at level 20).
  Local Notation "x '[L]'" := (if x.(cc_l) then 1 else 0) (at level 20).
  Local Notation "x '[Z]'" := (if x.(cc_z) then 1 else 0) (at level 20).
  Local Notation "'int'" := (BinInt.Z).
  Local Notation "x << y" := ((Z.shiftl x y) mod (2^256)) : Z_scope. (* truncating left shift *)
  Local Notation "x >> y" := (Z.shiftr x y) : Z_scope.


  (* Note: In the specification document, argument order gets a bit
    confusing. Like here, r0 is always the first argument "source 0"
    and r1 the second. But the specification of MUL128LU is:
            (R[RS1][127:0] * R[RS0][255:128])

    while the specification of SUB is:
          (R[RS0] - shift(R[RS1], imm))

    In the SUB case, r0 is really treated the first argument, but in
    MUL128LU the order seems to be reversed; rather than low-high, we
    take the high part of the first argument r0 and the low parts of
    r1. This is also true for MUL128UL. *)

  Definition ADD (imm : int) : instruction :=
    {|
      num_source_regs := 2;
      writes_conditions := [C; M; L; Z];
      spec := (fun '(r0, r1) cc =>
                 r0 + (r1 << imm))
    |}.

  Definition ADDC (imm : int) : instruction :=
    {|
      num_source_regs := 2;
      writes_conditions := [C; M; L; Z];
      spec := (fun '(r0, r1) cc =>
                 r0 + (r1 << imm) + cc[C])
    |}.

  Definition SUB (imm : int) : instruction :=
    {|
      num_source_regs := 2;
      writes_conditions := [C; M; L; Z];
      spec := (fun '(r0, r1) cc =>
                 r0 - (r1 << imm))
    |}.

  Definition SUBC (imm : int) : instruction :=
    {|
      num_source_regs := 2;
      writes_conditions := [C; M; L; Z];
      spec := (fun '(r0, r1) cc =>
                 r0 - (r1 << imm) - cc[C])
    |}.


  Definition MUL128LL : instruction :=
    {|
      num_source_regs := 2;
      writes_conditions := [M; L; Z];
      spec := (fun '(r0, r1) cc =>
                 (lower128 r0) * (lower128 r1))
    |}.

  Definition MUL128LU : instruction :=
    {|
      num_source_regs := 2;
      writes_conditions := [M; L; Z];
      spec := (fun '(r0, r1) cc =>
                 (lower128 r1) * (upper128 r0)) (* see note *)
    |}.

  Definition MUL128UL : instruction :=
    {|
      num_source_regs := 2;
      writes_conditions := [M; L; Z];
      spec := (fun '(r0, r1) cc =>
                 (upper128 r1) * (lower128 r0)) (* see note *)
    |}.

  Definition MUL128UU : instruction :=
    {|
      num_source_regs := 2;
      writes_conditions := [M; L; Z];
      spec := (fun '(r0, r1) cc =>
                 (upper128 r0) * (upper128 r1))
    |}.

  (* Note : Unlike the other operations, the output of RSHI is
    truncated in the specification. This is not strictly necessary,
    since the interpretation function truncates the output
    anyway. However, it is useful to make the definition line up
    exactly with Z.rshi. *)
  Definition RSHI (imm : int) : instruction :=
    {|
      num_source_regs := 2;
      writes_conditions := [M; L; Z];
      spec := (fun '(r0, r1) cc =>
                 (((2^256 * r0) + r1) >> imm) mod (2^256))
    |}.

  Definition SELC : instruction :=
    {|
      num_source_regs := 2;
      writes_conditions := [];
      spec := (fun '(r0, r1) cc =>
                 if cc[C] =? 1 then r0 else r1)
    |}.

  Definition SELM : instruction :=
    {|
      num_source_regs := 2;
      writes_conditions := [];
      spec := (fun '(r0, r1) cc =>
                 if cc[M] =? 1 then r0 else r1)
    |}.

  Definition SELL : instruction :=
    {|
      num_source_regs := 2;
      writes_conditions := [];
      spec := (fun '(r0, r1) cc =>
                 if cc[L] =? 1 then r0 else r1)
    |}.

  (* TODO : treat the MOD register specially, like CC *)
  Definition ADDM : instruction :=
    {|
      num_source_regs := 3;
      writes_conditions := [M; L; Z];
      spec := (fun '(r0, r1, MOD) cc =>
                 let ra := r0 + r1 in
                 if ra >=? MOD
                 then ra - MOD
                 else ra)
    |}.

End Instructions.

Module Registers.
  Inductive register : Type :=
  | r0 : register
  | r1 : register
  | r2 : register
  | r3 : register
  | r4 : register
  | r5 : register
  | r6 : register
  | r7 : register
  | r8 : register
  | r9 : register
  | r10 : register
  | r11 : register
  | r12 : register
  | r13 : register
  | r14 : register
  | r15 : register
  | r16 : register
  | r17 : register
  | r18 : register
  | r19 : register
  | r20 : register
  | r21 : register
  | r22 : register
  | r23 : register
  | r24 : register
  | r25 : register
  | r26 : register
  | r27 : register
  | r28 : register
  | r29 : register
  | r30 : register
  | RegZero : register (* r31 *)
  | RegMod : register
  .

  Definition reg_dec (x y : register) : {x = y} + {x <> y}.
  Proof. destruct x, y; try (apply left; congruence); right; congruence. Defined.
  Definition reg_eqb x y := if reg_dec x y then true else false.

  Lemma reg_eqb_neq x y : x <> y -> reg_eqb x y = false.
  Proof. cbv [reg_eqb]; break_match; congruence. Qed.
  Lemma reg_eqb_refl x : reg_eqb x x = true.
  Proof. cbv [reg_eqb]; break_match; congruence. Qed.
End Registers.