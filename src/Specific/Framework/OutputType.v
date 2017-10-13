Require Import Coq.ZArith.BinIntDef.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Util.Notations.
Import CurveParameters.Notations.

Local Coercion Z.to_nat : Z >-> nat.
Local Notation interp_flat_type := (interp_flat_type interp_base_type).

Section gen.
  Context (curve : RawCurveParameters.CurveParameters)
          (b : base_type).

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

  Record SynthesisOutputOn :=
    {
      zero : Expr RT;
      one : Expr RT;
      add : Expr (rT * rT -> rT); (* does not include carry *)
      sub : Expr (rT * rT -> rT); (* does not include carry *)
      mul : Expr (rT * rT -> rT); (* includes carry *)
      square : Expr (rT -> rT); (* includes carry *)
      opp : Expr (rT -> rT); (* does not include carry *)
      carry : Expr (rT -> rT);
      carry_add : Expr (rT * rT -> rT)
      := (carry ∘ add)%expr;
      carry_sub : Expr (rT * rT -> rT)
      := (carry ∘ sub)%expr;
      carry_opp : Expr (rT -> rT)
      := (carry ∘ opp)%expr;

      P : T' -> Prop;

      encode_valid : forall v, _;
      encode_sig := fun v => exist P (Interp (encode v) tt) (encode_valid v);
      encode_correct : forall v, decode (Interp (encode v) tt) = v;

      decode_sig := fun v : sig P => decode (proj1_sig v);

      zero_correct : zero = encode 0%F; (* which equality to use here? *)
      one_correct : one = encode 1%F; (* which equality to use here? *)
      zero_sig := encode_sig 0%F;
      one_sig := encode_sig 1%F;

      opp_valid : forall x, P x -> P (Interp carry_opp x);
      opp_sig := fun x => exist P _ (@opp_valid (proj1_sig x) (proj2_sig x));

      add_valid : forall x y, P x -> P y -> P (Interp carry_add (x, y));
      add_sig := fun x y => exist P _ (@add_valid (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y));

      sub_valid : forall x y, P x -> P y -> P (Interp carry_sub (x, y));
      sub_sig := fun x y => exist P _ (@sub_valid (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y));

      mul_valid : forall x y, P x -> P y -> P (Interp mul (x, y));
      mul_sig := fun x y => exist P _ (@mul_valid (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y));

      square_correct : forall x, P x -> Interp square x = Interp mul (x, x);

      T := { v : T' | P v };
      eqT : T -> T -> Prop
      := fun x y => eq (decode (proj1_sig x)) (decode (proj1_sig y));
      ring : @Hierarchy.ring
               T eqT zero_sig one_sig opp_sig add_sig sub_sig mul_sig;
      encode_homomorphism
      : @Ring.is_homomorphism
          (F m) eq 1%F F.add F.mul
          T eqT one_sig add_sig mul_sig
          encode_sig;
      decode_homomorphism
      : @Ring.is_homomorphism
          T eqT one_sig add_sig mul_sig
          (F m) eq 1%F F.add F.mul
          decode_sig
    }.
End gen.


Record SynthesisOutput (curve : RawCurveParameters.CurveParameters) :=
  {
    onZ : SynthesisOutputOn curve TZ;
    onWord : SynthesisOutputOn curve (TWord (Z.log2_up curve.(bitwidth)))
  }.
