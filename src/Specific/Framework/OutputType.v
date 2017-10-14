Require Import Coq.ZArith.BinIntDef.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Util.Notations.
Import CurveParameters.Notations.

Local Coercion Z.to_nat : Z >-> nat.
Local Notation interp_flat_type := (interp_flat_type interp_base_type).

Section gen.
  Context (curve : RawCurveParameters.CurveParameters).

  Section gen_base_type.
    Context (b : base_type).

    Definition m := Z.to_pos (curve.(s) - Associational.eval curve.(c))%Z.
    Definition rT := ((Tbase b)^curve.(sz))%ctype.
    Definition T' := (interp_flat_type rT).
    Definition RT := (Unit -> rT)%ctype.
    Definition wt := (wt_gen m curve.(sz)).
    Definition encode : F m -> Expr RT
      := fun v var
         => Abs
              (fun _
               => SmartPairf
                    (flat_interp_untuple
                       (T:=Tbase _)
                       (Tuple.map
                          (fun v => Op (OpConst v) TT)
                          (@Positional.Fencode wt curve.(sz) m modulo div v)))).
    Definition decode : T' -> F m
      := fun v => @Positional.Fdecode
                    wt (curve.(sz)) m
                    (Tuple.map interpToZ (flat_interp_tuple (T:=Tbase _) v)).
  End gen_base_type.

  Local Notation TW := (TWord (Z.log2_up curve.(bitwidth))).
  Local Notation RTZ := (RT TZ).
  Local Notation rTZ := (rT TZ).
  Local Notation RTW := (RT TW).
  Local Notation rTW := (rT TW).

  Record SynthesisOutput :=
    {
      zeroZ : Expr RTZ;
      oneZ : Expr RTZ;
      addZ : Expr (rTZ * rTZ -> rTZ); (* does not include carry *)
      subZ : Expr (rTZ * rTZ -> rTZ); (* does not include carry *)
      carry_mulZ : Expr (rTZ * rTZ -> rTZ); (* includes carry *)
      carry_squareZ : Expr (rTZ -> rTZ); (* includes carry *)
      oppZ : Expr (rTZ -> rTZ); (* does not include carry *)
      carryZ : Expr (rTZ -> rTZ);
      carry_addZ : Expr (rTZ * rTZ -> rTZ)
      := (carryZ ∘ addZ)%expr;
      carry_subZ : Expr (rTZ * rTZ -> rTZ)
      := (carryZ ∘ subZ)%expr;
      carry_oppZ : Expr (rTZ -> rTZ)
      := (carryZ ∘ oppZ)%expr;

      zeroW : Expr RTW;
      oneW : Expr RTW;
      carry_addW : Expr (rTW * rTW -> rTW); (* includes carry *)
      carry_subW : Expr (rTW * rTW -> rTW); (* includes carry *)
      carry_mulW : Expr (rTW * rTW -> rTW); (* includes carry *)
      carry_squareW : Expr (rTW -> rTW); (* includes carry *)
      carry_oppW : Expr (rTW -> rTW); (* does not include carry *)

      PZ : T' TZ -> Prop;
      PW : T' TW -> Prop
      := fun v => PZ (tuple_map (A:=Tbase TW) (B:=Tbase TZ) (SmartVarfMap (@interpToZ)) v);

      encodeZ_valid : forall v, _;
      encodeZ_sig := fun v => exist PZ (Interp (encode TZ v) tt) (encodeZ_valid v);
      encodeZ_correct : forall v, decode TZ (Interp (encode TZ v) tt) = v;

      decodeZ_sig := fun v : sig PZ => decode TZ (proj1_sig v);

      zeroZ_correct : zeroZ = encode _ 0%F; (* which equality to use here? *)
      oneZ_correct : oneZ = encode _ 1%F; (* which equality to use here? *)
      zeroZ_sig := encodeZ_sig 0%F;
      oneZ_sig := encodeZ_sig 1%F;

      oppZ_valid : forall x, PZ x -> PZ (Interp carry_oppZ x);
      oppZ_sig := fun x => exist PZ _ (@oppZ_valid (proj1_sig x) (proj2_sig x));

      addZ_valid : forall x y, PZ x -> PZ y -> PZ (Interp carry_addZ (x, y));
      addZ_sig := fun x y => exist PZ _ (@addZ_valid (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y));

      subZ_valid : forall x y, PZ x -> PZ y -> PZ (Interp carry_subZ (x, y));
      subZ_sig := fun x y => exist PZ _ (@subZ_valid (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y));

      mulZ_valid : forall x y, PZ x -> PZ y -> PZ (Interp carry_mulZ (x, y));
      mulZ_sig := fun x y => exist PZ _ (@mulZ_valid (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y));

      squareZ_correct : forall x, PZ x -> Interp carry_squareZ x = Interp carry_mulZ (x, x);


      encodeW_valid : forall v, _;
      encodeW_sig := fun v => exist PW (Interp (encode TW v) tt) (encodeW_valid v);
      encodeW_correct : forall v, decode TW (Interp (encode TW v) tt) = v;

      decodeW_sig := fun v : sig PW => decode TW (proj1_sig v);

      zeroW_correct : zeroW = encode _ 0%F; (* which equality to use here? *)
      oneW_correct : oneW = encode _ 1%F; (* which equality to use here? *)
      zeroW_sig := encodeW_sig 0%F;
      oneW_sig := encodeW_sig 1%F;

      oppW_valid : forall x, PW x -> PW (Interp carry_oppW x);
      oppW_sig := fun x => exist PW _ (@oppW_valid (proj1_sig x) (proj2_sig x));

      addW_valid : forall x y, PW x -> PW y -> PW (Interp carry_addW (x, y));
      addW_sig := fun x y => exist PW _ (@addW_valid (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y));

      subW_valid : forall x y, PW x -> PW y -> PW (Interp carry_subW (x, y));
      subW_sig := fun x y => exist PW _ (@subW_valid (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y));

      mulW_valid : forall x y, PW x -> PW y -> PW (Interp carry_mulW (x, y));
      mulW_sig := fun x y => exist PW _ (@mulW_valid (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y));

      squareW_correct : forall x, PW x -> Interp carry_squareW x = Interp carry_mulW (x, x);

      T_Z := { v : T' TZ | PZ v };
      eqTZ : T_Z -> T_Z -> Prop
      := fun x y => eq (decode _ (proj1_sig x)) (decode _ (proj1_sig y));
      ringZ : @Hierarchy.ring
                T_Z eqTZ zeroZ_sig oneZ_sig oppZ_sig addZ_sig subZ_sig mulZ_sig;
      encodeZ_homomorphism
      : @Ring.is_homomorphism
          (F m) eq 1%F F.add F.mul
          T_Z eqTZ oneZ_sig addZ_sig mulZ_sig
          encodeZ_sig;
      decodeZ_homomorphism
      : @Ring.is_homomorphism
          T_Z eqTZ oneZ_sig addZ_sig mulZ_sig
          (F m) eq 1%F F.add F.mul
          decodeZ_sig;

      T_W := { v : T' TW | PW v };
      eqTW : T_W -> T_W -> Prop
      := fun x y => eq (decode _ (proj1_sig x)) (decode _ (proj1_sig y));
      ringW : @Hierarchy.ring
                T_W eqTW zeroW_sig oneW_sig oppW_sig addW_sig subW_sig mulW_sig;
      encodeW_homomorphism
      : @Ring.is_homomorphism
          (F m) eq 1%F F.add F.mul
          T_W eqTW oneW_sig addW_sig mulW_sig
          encodeW_sig;
      decodeW_homomorphism
      : @Ring.is_homomorphism
          T_W eqTW oneW_sig addW_sig mulW_sig
          (F m) eq 1%F F.add F.mul
          decodeW_sig
    }.
End gen.
