Require Export Coq.ZArith.BinInt.
Require Export Coq.Lists.List.
Require Export Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.TagList.
Require Crypto.Util.Tuple.

Local Set Primitive Projections.

Module Export Notations := RawCurveParameters.Notations.

Module TAG. (* namespacing *)
  Inductive tags := CP | sz | bitwidth | s | c | carry_chains | a24 | coef_div_modulus | goldilocks | montgomery | upper_bound_of_exponent | allowable_bit_widths | freeze_allowable_bit_widths | modinv_fuel.
End TAG.

Module Export CurveParameters.
  Local Notation eval p :=
    (List.fold_right Z.add 0%Z (List.map (fun t => fst t * snd t) p)).

  Ltac do_compute v :=
    let v' := (eval vm_compute in v) in v'.
  Notation compute v
    := (ltac:(let v' := do_compute v in exact v'))
         (only parsing).
  Local Notation defaulted opt_v default
    := (match opt_v with
        | Some v => v
        | None => default
        end)
         (only parsing).
  Record CurveParameters :=
    {
      sz : nat;
      bitwidth : Z;
      s : Z;
      c : list limb;
      carry_chains : list (list nat);
      a24 : Z;
      coef_div_modulus : nat;

      goldilocks : bool;
      montgomery : bool;

      mul_code : option (Z^sz -> Z^sz -> Z^sz);
      square_code : option (Z^sz -> Z^sz);
      upper_bound_of_exponent : Z -> Z;
      allowable_bit_widths : list nat;
      freeze_allowable_bit_widths : list nat;
      modinv_fuel : nat
    }.

  Declare Reduction cbv_CurveParameters
    := cbv [sz
              bitwidth
              s
              c
              carry_chains
              a24
              coef_div_modulus
              goldilocks
              montgomery
              mul_code
              square_code
              upper_bound_of_exponent
              allowable_bit_widths
              freeze_allowable_bit_widths
              modinv_fuel].

  Ltac default_mul CP :=
    lazymatch (eval hnf in (mul_code CP)) with
    | None => reflexivity
    | Some ?mul_code
      => instantiate (1:=mul_code)
    end.
  Ltac default_square CP :=
    lazymatch (eval hnf in (square_code CP)) with
    | None => reflexivity
    | Some ?square_code
      => instantiate (1:=square_code)
    end.

  Local Notation list_8_if_not_exists ls :=
    (if existsb (Nat.eqb 8) ls
     then nil
     else [8]%nat)
      (only parsing).

  Definition fill_defaults_CurveParameters (CP : RawCurveParameters.CurveParameters)
    : CurveParameters
    := Eval cbv_RawCurveParameters in
        let sz := RawCurveParameters.sz CP in
        let bitwidth := RawCurveParameters.bitwidth CP in
        let montgomery := RawCurveParameters.montgomery CP in
        let s := RawCurveParameters.s CP in
        let c := RawCurveParameters.c CP in
        let goldilocks :=
            defaulted
              (RawCurveParameters.goldilocks CP)
              (let k := Z.log2 s / 2 in
               (s - eval c) =? (2^(2*k) - 2^k - 1)) in
        let allowable_bit_widths
            := defaulted
                 (RawCurveParameters.allowable_bit_widths CP)
                 ((if montgomery
                   then [8]
                   else nil)
                    ++ (Z.to_nat bitwidth :: 2*Z.to_nat bitwidth :: nil))%nat in

        {|
          sz := sz;
          bitwidth := bitwidth;
          s := s;
          c := c;
          carry_chains := defaulted (RawCurveParameters.carry_chains CP) [seq 0 (pred sz); [0; 1]]%nat;
          a24 := defaulted (RawCurveParameters.a24 CP) 0;
          coef_div_modulus := defaulted (RawCurveParameters.coef_div_modulus CP) 0%nat;

          goldilocks := goldilocks;
          montgomery := montgomery;

          mul_code := RawCurveParameters.mul_code CP;
          square_code := RawCurveParameters.square_code CP;
          upper_bound_of_exponent
          := defaulted (RawCurveParameters.upper_bound_of_exponent CP)
                       (if montgomery
                        then (fun exp => (2^exp - 1)%Z)
                        else (fun exp => (2^exp + 2^(exp-3))%Z));
          (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)

          allowable_bit_widths := allowable_bit_widths;
          freeze_allowable_bit_widths
          := defaulted
               (RawCurveParameters.freeze_extra_allowable_bit_widths CP)
               (list_8_if_not_exists allowable_bit_widths)
               ++ allowable_bit_widths;
          modinv_fuel := defaulted (RawCurveParameters.modinv_fuel CP) 10%nat
        |}.

  Ltac get_fill_CurveParameters CP :=
    let CP := (eval hnf in CP) in
    let v := (eval cbv [fill_defaults_CurveParameters] in
                 (fill_defaults_CurveParameters CP)) in
    let v := (eval cbv_CurveParameters in v) in
    let v := (eval cbv_RawCurveParameters in v) in
    lazymatch v with
    | ({|
          sz := ?sz';
          bitwidth := ?bitwidth';
          s := ?s';
          c := ?c';
          carry_chains := ?carry_chains';
          a24 := ?a24';
          coef_div_modulus := ?coef_div_modulus';
          goldilocks := ?goldilocks';
          montgomery := ?montgomery';
          mul_code := ?mul_code';
          square_code := ?square_code';
          upper_bound_of_exponent := ?upper_bound_of_exponent';
          allowable_bit_widths := ?allowable_bit_widths';
          freeze_allowable_bit_widths := ?freeze_allowable_bit_widths';
          modinv_fuel := ?modinv_fuel'
        |})
      => let sz' := do_compute sz' in
         let bitwidth' := do_compute bitwidth' in
         let carry_chains' := do_compute carry_chains' in
         let goldilocks' := do_compute goldilocks' in
         let montgomery' := do_compute montgomery' in
         let allowable_bit_widths' := do_compute allowable_bit_widths' in
         let freeze_allowable_bit_widths' := do_compute freeze_allowable_bit_widths' in
         let modinv_fuel' := do_compute modinv_fuel' in
         constr:({|
                    sz := sz';
                    bitwidth := bitwidth';
                    s := s';
                    c := c';
                    carry_chains := carry_chains';
                    a24 := a24';
                    coef_div_modulus := coef_div_modulus';
                    goldilocks := goldilocks';
                    montgomery := montgomery';
                    mul_code := mul_code';
                    square_code := square_code';
                    upper_bound_of_exponent := upper_bound_of_exponent';
                    allowable_bit_widths := allowable_bit_widths';
                    freeze_allowable_bit_widths := freeze_allowable_bit_widths';
                    modinv_fuel := modinv_fuel'
                  |})
    end.
  (*existsb Nat.eqb List.app seq pred Z_add_red Z_sub_red Z_mul_red Z_div_red Z_pow_red Z_eqb_red
                     Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul orb andb] in*)
  Notation fill_CurveParameters CP := ltac:(let v := get_fill_CurveParameters CP in exact v) (only parsing).

  Ltac internal_pose_of_CP CP proj id :=
    let P_proj := (eval cbv_CurveParameters in (proj CP)) in
    cache_term P_proj id.
  Ltac pose_sz CP sz :=
    internal_pose_of_CP CP CurveParameters.sz sz.
  Ltac pose_bitwidth CP bitwidth :=
    internal_pose_of_CP CP CurveParameters.bitwidth bitwidth.
  Ltac pose_s CP s := (* don't want to compute, e.g., [2^255] *)
    internal_pose_of_CP CP CurveParameters.s s.
  Ltac pose_c CP c :=
    internal_pose_of_CP CP CurveParameters.c c.
  Ltac pose_carry_chains CP carry_chains :=
    internal_pose_of_CP CP CurveParameters.carry_chains carry_chains.
  Ltac pose_a24 CP a24 :=
    internal_pose_of_CP CP CurveParameters.a24 a24.
  Ltac pose_coef_div_modulus CP coef_div_modulus :=
    internal_pose_of_CP CP CurveParameters.coef_div_modulus coef_div_modulus.
  Ltac pose_goldilocks CP goldilocks :=
    internal_pose_of_CP CP CurveParameters.goldilocks goldilocks.
  Ltac pose_montgomery CP montgomery :=
    internal_pose_of_CP CP CurveParameters.montgomery montgomery.
  Ltac pose_allowable_bit_widths CP allowable_bit_widths :=
    internal_pose_of_CP CP CurveParameters.allowable_bit_widths allowable_bit_widths.
  Ltac pose_freeze_allowable_bit_widths CP freeze_allowable_bit_widths :=
    internal_pose_of_CP CP CurveParameters.freeze_allowable_bit_widths freeze_allowable_bit_widths.
  Ltac pose_upper_bound_of_exponent CP upper_bound_of_exponent :=
    internal_pose_of_CP CP CurveParameters.upper_bound_of_exponent upper_bound_of_exponent.
  Ltac pose_modinv_fuel CP modinv_fuel :=
    internal_pose_of_CP CP CurveParameters.modinv_fuel modinv_fuel.

  (* Everything below this line autogenerated by remake_packages.py *)
  Ltac add_sz pkg :=
    let CP := Tag.get pkg TAG.CP in
    let sz := fresh "sz" in
    let sz := pose_sz CP sz in
    Tag.update pkg TAG.sz sz.

  Ltac add_bitwidth pkg :=
    let CP := Tag.get pkg TAG.CP in
    let bitwidth := fresh "bitwidth" in
    let bitwidth := pose_bitwidth CP bitwidth in
    Tag.update pkg TAG.bitwidth bitwidth.

  Ltac add_s pkg :=
    let CP := Tag.get pkg TAG.CP in
    let s := fresh "s" in
    let s := pose_s CP s in
    Tag.update pkg TAG.s s.

  Ltac add_c pkg :=
    let CP := Tag.get pkg TAG.CP in
    let c := fresh "c" in
    let c := pose_c CP c in
    Tag.update pkg TAG.c c.

  Ltac add_carry_chains pkg :=
    let CP := Tag.get pkg TAG.CP in
    let carry_chains := fresh "carry_chains" in
    let carry_chains := pose_carry_chains CP carry_chains in
    Tag.update pkg TAG.carry_chains carry_chains.

  Ltac add_a24 pkg :=
    let CP := Tag.get pkg TAG.CP in
    let a24 := fresh "a24" in
    let a24 := pose_a24 CP a24 in
    Tag.update pkg TAG.a24 a24.

  Ltac add_coef_div_modulus pkg :=
    let CP := Tag.get pkg TAG.CP in
    let coef_div_modulus := fresh "coef_div_modulus" in
    let coef_div_modulus := pose_coef_div_modulus CP coef_div_modulus in
    Tag.update pkg TAG.coef_div_modulus coef_div_modulus.

  Ltac add_goldilocks pkg :=
    let CP := Tag.get pkg TAG.CP in
    let goldilocks := fresh "goldilocks" in
    let goldilocks := pose_goldilocks CP goldilocks in
    Tag.update pkg TAG.goldilocks goldilocks.

  Ltac add_montgomery pkg :=
    let CP := Tag.get pkg TAG.CP in
    let montgomery := fresh "montgomery" in
    let montgomery := pose_montgomery CP montgomery in
    Tag.update pkg TAG.montgomery montgomery.

  Ltac add_allowable_bit_widths pkg :=
    let CP := Tag.get pkg TAG.CP in
    let allowable_bit_widths := fresh "allowable_bit_widths" in
    let allowable_bit_widths := pose_allowable_bit_widths CP allowable_bit_widths in
    Tag.update pkg TAG.allowable_bit_widths allowable_bit_widths.

  Ltac add_freeze_allowable_bit_widths pkg :=
    let CP := Tag.get pkg TAG.CP in
    let freeze_allowable_bit_widths := fresh "freeze_allowable_bit_widths" in
    let freeze_allowable_bit_widths := pose_freeze_allowable_bit_widths CP freeze_allowable_bit_widths in
    Tag.update pkg TAG.freeze_allowable_bit_widths freeze_allowable_bit_widths.

  Ltac add_upper_bound_of_exponent pkg :=
    let CP := Tag.get pkg TAG.CP in
    let upper_bound_of_exponent := fresh "upper_bound_of_exponent" in
    let upper_bound_of_exponent := pose_upper_bound_of_exponent CP upper_bound_of_exponent in
    Tag.update pkg TAG.upper_bound_of_exponent upper_bound_of_exponent.

  Ltac add_modinv_fuel pkg :=
    let CP := Tag.get pkg TAG.CP in
    let modinv_fuel := fresh "modinv_fuel" in
    let modinv_fuel := pose_modinv_fuel CP modinv_fuel in
    Tag.update pkg TAG.modinv_fuel modinv_fuel.

  Ltac add_CurveParameters_package pkg :=
    let pkg := add_sz pkg in
    let pkg := add_bitwidth pkg in
    let pkg := add_s pkg in
    let pkg := add_c pkg in
    let pkg := add_carry_chains pkg in
    let pkg := add_a24 pkg in
    let pkg := add_coef_div_modulus pkg in
    let pkg := add_goldilocks pkg in
    let pkg := add_montgomery pkg in
    let pkg := add_allowable_bit_widths pkg in
    let pkg := add_freeze_allowable_bit_widths pkg in
    let pkg := add_upper_bound_of_exponent pkg in
    let pkg := add_modinv_fuel pkg in
    Tag.strip_local pkg.
End CurveParameters.
