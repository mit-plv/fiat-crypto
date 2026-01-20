Require Import bedrock2.Array.
Require Import bedrock2.bottom_up_simpl.
Require Import bedrock2.FE310CSemantics.
Require Import bedrock2.Loops.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Semantics.
Require Import bedrock2.SepAutoArray.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ZnWords.
Require Import compiler.MMIO.
Require Import compiler.Pipeline.
Require Import compiler.Symbols.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
From coqutil.Tactics Require Import Tactics letexists eabstract rdelta reference_to_string ident_of_string.
Require Import coqutil.Word.Bitwidth32.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Naive.
From Coq Require Import Init.Byte.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import ZArith.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.End2End.X25519.Field25519.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Curves.Edwards.XYZT.Basic.
Require Import Curves.Edwards.XYZT.Precomputed.
Require Import Curves.Edwards.XYZT.Readdition.
Require Import Lia.
Require Crypto.Bedrock.Field.Synthesis.New.Signature.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Import LittleEndianList.
Import ListNotations.
Import ProgramLogic.Coercions.
Import WeakestPrecondition.

Local Existing Instance field_parameters.
Local Existing Instance frep25519.
Local Existing Instance frep25519_ok.

(* Size of a field element in bytes. This is the same as computing eval in felem_size_bytes, but we want a notation instead of definition. *)
Local Notation felem_size := 40.

(* Notations help treat curve points like C structs. To avoid notation clashes, projective coordinates are capitalized. *)

(* Member access notation for projective points: (X, Y, Z, Ta, Tb). *)
Local Notation "A .X" := (A) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Y" := (expr.op Syntax.bopname.add A (felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Z" := (expr.op Syntax.bopname.add A (felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Ta" := (expr.op Syntax.bopname.add A (felem_size + felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Tb" := (expr.op Syntax.bopname.add A (felem_size + felem_size + felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).

(* Member access notation for precomputed points: (half_ypx, half_ymx, xyd). *)
Local Notation "A .half_ypx" := (A) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .half_ymx" := (expr.op Syntax.bopname.add A (felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .xyd" := (expr.op Syntax.bopname.add A (felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).

(* Member access notation for cached points: (half_YmX, half_YpX, Z, Td). *)
Local Notation "A .half_YmX" := (A) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .half_YpX" := (expr.op Syntax.bopname.add A (felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Z" := (expr.op Syntax.bopname.add A (felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Td" := (expr.op Syntax.bopname.add A (felem_size + felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).

(* Adds a precomputed point p_b to projective point p_a and puts the result in p_out. *)
Definition add_precomputed := func! (p_out, p_a, p_b) {
  stackalloc felem_size as YpX1;
  fe25519_add(YpX1, p_a.Y, p_a.X);
  stackalloc felem_size as YmX1;
  fe25519_sub(YmX1, p_a.Y, p_a.X);
  stackalloc felem_size as A;
  fe25519_mul(A, YmX1, p_b.half_ymx);
  stackalloc felem_size as B;
  fe25519_mul(B, YpX1, p_b.half_ypx);
  stackalloc felem_size as T1;
  fe25519_mul(T1, p_a.Ta, p_a.Tb);
  stackalloc felem_size as C;
  fe25519_mul(C, p_b.xyd, T1);
  fe25519_sub(p_out.Ta, B, A);
  stackalloc felem_size as F;
  fe25519_sub(F, p_a.Z, C);
  stackalloc felem_size as G;
  fe25519_add(G, p_a.Z, C);
  fe25519_add(p_out.Tb, B, A);
  fe25519_mul(p_out.X, p_out.Ta, F);
  fe25519_mul(p_out.Y, G, p_out.Tb);
  fe25519_mul(p_out.Z, F, G)
}.

(* Doubles a projective point. Equivalent of m1double in src/Curves/Edwards/XYZT/Basic.v *)
Definition double := func! (p_out, p_a) {
  stackalloc felem_size as trX;
  fe25519_square(trX, p_a.X);
  stackalloc felem_size as trZ;
  fe25519_square(trZ, p_a.Y);
  stackalloc felem_size as t0;
  fe25519_square(t0, p_a.Z);
  stackalloc felem_size as trT;
  fe25519_carry_add(trT, t0, t0);
  stackalloc felem_size as rY;
  fe25519_add(rY, p_a.X, p_a.Y);
  fe25519_square(t0, rY);
  fe25519_carry_add(p_out.Tb, trZ, trX);
  stackalloc felem_size as cZ;
  fe25519_carry_sub(cZ, trZ, trX);
  fe25519_sub(p_out.Ta, t0, p_out.Tb);
  stackalloc felem_size as cT;
  fe25519_sub(cT, trT, cZ);
  fe25519_mul(p_out.X, p_out.Ta, cT);
  fe25519_mul(p_out.Y, p_out.Tb, cZ);
  fe25519_mul(p_out.Z, cZ, cT)
}.

(* Converts a projective point p_a to a cached point p_out to prepare it for readdition.
   Uses the field's parameter d, which is passed as p_d for now. *)
Definition to_cached := func! (p_out, p_a, p_d) {
  fe25519_sub(p_out.half_YmX, p_a.Y, p_a.X);
  fe25519_half(p_out.half_YmX, p_out.half_YmX); (* An implementation doesn't exist yet, work with spec for now. *)
  fe25519_add(p_out.half_YpX, p_a.Y, p_a.X);
  fe25519_half(p_out.half_YpX, p_out.half_YpX);
  fe25519_mul(p_out.Td, p_a.Ta, p_a.Tb);
  fe25519_mul(p_out.Td, p_out.Td, p_d);
  fe25519_copy(p_out.Z, p_a.Z)
}.

(* Equivalent of m1_readd in src/Curves/Edwards/XYZT/Readdition.v
   Adds a projective point p_a and cached point p_c and stores the result as projective point in p_out. *)
Definition readd := func! (p_out, p_a, p_c) {
  stackalloc felem_size as A;
  fe25519_sub(A, p_a.Y, p_a.X);
  fe25519_mul(A, A, p_c.half_YmX);
  stackalloc felem_size as B;
  fe25519_add(B, p_a.Y, p_a.X);
  fe25519_mul(B, B, p_c.half_YpX);
  stackalloc felem_size as C;
  fe25519_mul(C, p_a.Ta, p_a.Tb);
  fe25519_mul(C, C, p_c.Td);
  stackalloc felem_size as D;
  fe25519_mul(D, p_a.Z, p_c.Z);
  fe25519_sub(p_out.Ta, B, A);
  stackalloc felem_size as F;
  fe25519_sub(F, D, C);
  stackalloc felem_size as G;
  fe25519_add(G, D, C);
  fe25519_add(p_out.Tb, B, A);
  fe25519_mul(p_out.X, p_out.Ta, F);
  fe25519_mul(p_out.Y, G, p_out.Tb);
  fe25519_mul(p_out.Z, F, G)
}.

Section WithParameters.
  Context {two_lt_M: 2 < M_pos}.
  (* TODO: Can we provide actual values/proofs for these, rather than just sticking them in the context? *)
  Context {char_ge_3 : @Ring.char_ge (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub F.mul
    (BinNat.N.succ_pos BinNat.N.two)}.
  Context {field:@Algebra.Hierarchy.field (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}.
  Context {a d: F M_pos}
          {nonzero_a : a <> F.zero}
          {square_a : exists sqrt_a, (F.mul sqrt_a sqrt_a) = a}
          {nonsquare_d : forall x, (F.mul x x) <> d}.
  Context {a_eq_minus1:a = F.opp F.one} {twice_d} {k_eq_2d:twice_d = (F.add d d)} {nonzero_d: d<>F.zero}.

Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).

Local Notation FElem := (FElem(FieldRepresentation:=frep25519)).
Local Notation felem_size_in_bytes := (felem_size_in_bytes(FieldRepresentation:=frep25519)).
Local Notation bounded_by := (bounded_by(FieldRepresentation:=frep25519)).
Local Notation word := (Naive.word 32).
Local Notation felem := (felem(FieldRepresentation:=frep25519)).
Local Notation point := (Extended.point(Feq:=Logic.eq)(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(d:=d)).
Local Notation cached := (cached(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(d:=d)(Feq:=Logic.eq)
  (Fsub:=F.sub)(Fdiv:=F.div)).
Local Notation precomputed_point := (precomputed_point(Feq:=Logic.eq)(a:=a)(d:=d)(Fone:=F.one)
  (Fadd:=F.add)(Fmul:=F.mul)(Fsub:=F.sub)).
Local Notation cached_coordinates := (cached_coordinates(Fzero:=F.zero)(Fadd:=F.add)(Fdiv:=F.div)
  (Fmul:=F.mul)(Fsub:=F.sub)(Feq:=Logic.eq)(a:=a)(d:=d)).
Local Notation precomputed_coordinates := (precomputed_coordinates(Fone:=F.one)(Fadd:=F.add)
  (Fmul:=F.mul)(Fsub:=F.sub)(Feq:=Logic.eq)(a:=a)(d:=d)).
Local Notation m1double :=
  (Extended.m1double(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
           (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
           (field:=field)(char_ge_3:=char_ge_3)(Feq_dec:=F.eq_dec)
           (a:=a)(d:=d)(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)
           (a_eq_minus1:=a_eq_minus1)(twice_d:=twice_d)(k_eq_2d:=k_eq_2d)).
Local Notation m1_prep :=
  (m1_prep(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
                  (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
                  (field:=field)(char_ge_3:=char_ge_3)(Feq_dec:=F.eq_dec)
                  (a:=a)(d:=d)(nonzero_a:=nonzero_a)(a_eq_minus1:=a_eq_minus1)
                  (twice_d:=twice_d)(k_eq_2d:=k_eq_2d)(nonzero_d:=nonzero_d)).
Local Notation m1_readd :=
  (m1_readd(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
           (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
           (field:=field)(char_ge_3:=char_ge_3)(Feq_dec:=F.eq_dec)
           (a:=a)(d:=d)(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)
           (a_eq_minus1:=a_eq_minus1)(twice_d:=twice_d)(k_eq_2d:=k_eq_2d)(nonzero_d:=nonzero_d)).
Local Notation m1add_precomputed_coordinates :=
  (m1add_precomputed_coordinates(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
           (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
           (field:=field)(char_ge_3:=char_ge_3)(Feq_dec:=F.eq_dec)
           (a:=a)(d:=d)(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)
           (a_eq_minus1:=a_eq_minus1)).

Local Notation "p .+ n" := (word.add p (word.of_Z n)) (at level 50, format "p .+ n", left associativity).

Local Notation "a <> b" := (not (a = b)) : type_scope. Local Notation "0" := F.zero.
Local Notation "1" := F.one. Local Infix "+" := F.add. Local Infix "*" := F.mul.
Local Infix "-" := F.sub. Local Infix "/" := F.div. Local Notation "x ^ 2" := (x*x).

Definition valid_projective_coords (X Y Z Ta Tb : felem):=
    ((a * (feval X)^2*(feval Z)^2 + (feval Y)^2*(feval Z)^2 = ((feval Z)^2)^2 + d * (feval X)^2 * (feval Y)^2)%F /\
    ((feval X) * (feval Y) = (feval Z) * (feval Ta) * (feval Tb))%F /\
    ((feval Z) <> 0)%F).
Definition projective_coords := { c | let '(X,Y,Z,Ta,Tb) := c in
    valid_projective_coords X Y Z Ta Tb /\
    bounded_by tight_bounds X /\ bounded_by tight_bounds Y /\ bounded_by tight_bounds Z /\
    bounded_by loose_bounds Ta /\ bounded_by loose_bounds Tb }.
Definition feval_projective_coords (c : projective_coords) :=
  let '(X, Y, Z, Ta, Tb) := proj1_sig c in (feval X, feval Y, feval Z, feval Ta, feval Tb).
Definition coords_to_point (c : projective_coords) : point.
  refine (exist _ (feval_projective_coords c) _).
  abstract (destruct_head' projective_coords;
    cbv [proj1_sig feval_projective_coords valid_projective_coords] in *;
    destruct_head' prod; destruct_head' and; ssplit; assumption).
  Defined.
Lemma point_implies_coords_valid (p : point) (X Y Z Ta Tb : felem):
  proj1_sig p = (feval X, feval Y, feval Z, feval Ta, feval Tb) -> valid_projective_coords X Y Z Ta Tb.
    intros.
    cbv[proj1_sig] in *. destruct_head' @Extended.point. destruct_head' prod. Prod.inversion_prod; subst.
    assumption.
Qed.

Definition valid_precomputed_coords (half_ypx half_ymx xyd : felem) :=
    let x := (feval half_ypx) - (feval half_ymx) in
    let y := (feval half_ypx) + (feval half_ymx) in
    (a*x^2 + y^2 = 1 + d*x^2*y^2)
    /\ (feval xyd) = x * y * d.
Definition precomputed_coords := { c | let '(half_ypx, half_ymx, xyd) := c in
                            valid_precomputed_coords half_ypx half_ymx xyd /\
                            bounded_by loose_bounds half_ymx /\ bounded_by loose_bounds half_ypx /\
                            bounded_by loose_bounds xyd }.
Definition feval_precomputed_coords (c : precomputed_coords) :=
  let '(half_ypx, half_ymx, xyd) := proj1_sig c in (feval half_ypx, feval half_ymx, feval xyd).
Definition precomputed_coords_to_precomputed (c : precomputed_coords) : precomputed_point.
  refine (exist _ (feval_precomputed_coords c) _).
  abstract (destruct_head' precomputed_coords; destruct_head' prod;
  destruct_head' and; cbv [feval_precomputed_coords valid_precomputed_coords proj1_sig] in *; assumption).
Defined.
Lemma precomputed_implies_coords_valid (p : precomputed_point) (half_ypx half_ymx xyd : felem):
  proj1_sig p = (feval half_ypx, feval half_ymx, feval xyd) -> valid_precomputed_coords half_ypx half_ymx xyd.
    intros.
    cbv[proj1_sig valid_precomputed_coords] in *. destruct_head' @Precomputed.precomputed_point.
    destruct_head' prod. Prod.inversion_prod; subst.
    assumption.
Qed.

Definition valid_cached_coords (half_YmX half_YpX Z Td : felem):=
  let X := (feval half_YpX) - (feval half_YmX) in
  let Y := (feval half_YpX) + (feval half_YmX) in
  let T := (feval Td) / d in
  let Z := (feval Z) in
    a * X^2*Z^2 + Y^2*Z^2 = (Z^2)^2 + d * X^2 * Y^2 /\
    X * Y = Z * T /\
    Z <> 0.
Definition cached_coords := { c | let '(half_YmX, half_YpX, Z, Td) := c in
                            valid_cached_coords half_YmX half_YpX Z Td /\
                            bounded_by loose_bounds half_YmX /\ bounded_by loose_bounds half_YpX /\
                            bounded_by loose_bounds Z /\ bounded_by loose_bounds Td }.
Definition feval_cached_coords (c : cached_coords) :=
  let '(half_YmX, half_YpX, Z, Td) := proj1_sig c in (feval half_YmX, feval half_YpX, feval Z, feval Td).
Definition cached_coords_to_cached (c : cached_coords) : cached.
  refine (exist _ (feval_cached_coords c) _).
  abstract (destruct_head' cached_coords; destruct_head' prod;
  destruct_head' and;
    cbv [valid_cached_coords proj1_sig] in *; assumption).
Defined.
Lemma cached_implies_coords_valid (c : cached) (half_YmX half_YpX Z Td : felem):
  proj1_sig c = (feval half_YmX, feval half_YpX, feval Z, feval Td) -> valid_cached_coords half_YmX half_YpX Z Td.
    intros.
    cbv[proj1_sig valid_cached_coords] in *. destruct_head' @Readdition.cached.
    destruct_head' prod. Prod.inversion_prod; subst.
    assumption.
Qed.

(* Extended projective points. *)
Local Notation "c 'p5@' p" := (let '(X,Y,Z,Ta,Tb) := proj1_sig c in sep (sep (sep (sep
                              (FElem (p) X)
                              (FElem (p .+ felem_size) Y))
                              (FElem (p .+ (felem_size + felem_size)) Z))
                              (FElem (p .+ (felem_size + felem_size + felem_size)) Ta))
                              (FElem (p .+ (felem_size + felem_size + felem_size + felem_size)) Tb))
                              (at level 10, format "c 'p5@' p").
(* Cached points. *)
Local Notation "c 'p4@' p" := (let '(half_ymx, half_ypx ,z,td) := proj1_sig c in sep (sep (sep
                              (FElem (p) half_ymx)
                              (FElem (p .+ felem_size) half_ypx))
                              (FElem (p .+ (felem_size + felem_size)) z))
                              (FElem (p .+ (felem_size + felem_size + felem_size)) td))
                              (at level 10, format "c 'p4@' p").
(* Precomputed points. *)
Local Notation "c 'p3@' p" := (let '(half_ymx, half_ypx, xyd) := proj1_sig c in sep (sep
                              (FElem (p) half_ymx)
                              (FElem (p .+ felem_size) half_ypx))
                              (FElem (p .+ (felem_size + felem_size)) xyd))
                              (at level 10, format "c 'p3@' p").

Instance spec_of_fe25519_half : spec_of "fe25519_half" :=
  fnspec! "fe25519_half"
    (result_location input_location: word) / (old_result input: felem)
    (R: _ -> Prop),
  { requires t m :=
    bounded_by loose_bounds input /\
    (exists Ra, m =* (FElem input_location input) * Ra) /\
    m =* (FElem result_location old_result) * R;
    ensures t' m' :=
      t = t' /\
      exists result : felem,
        bounded_by tight_bounds result /\
        feval result = F.div (feval input) (F.add F.one F.one) /\
        m' =* (FElem result_location result)  * R}.

Global Instance spec_of_add_precomputed : spec_of "add_precomputed" :=
  fnspec! "add_precomputed"
    (p_out p_a p_b: word) /
    (a: projective_coords) (b: precomputed_coords) (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a p5@ p_a * b p3@ p_b * R/\
        Datatypes.length out = Z.to_nat (5 * felem_size);
      ensures t' m' :=
        t = t' /\
        exists a_plus_b : projective_coords,
          m' =* a_plus_b p5@ p_out * a p5@ p_a * b p3@ p_b * R /\
          proj1_sig (m1add_precomputed_coordinates (coords_to_point a) (precomputed_coords_to_precomputed b))
             = feval_projective_coords a_plus_b
    }.

Global Instance spec_of_double : spec_of "double" :=
  fnspec! "double"
    (p_out p_a: word) /
    (a: projective_coords) (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a p5@ p_a * R /\
        Datatypes.length out = Z.to_nat (5 * felem_size);
      ensures t' m' :=
        t = t' /\
        exists a_double: projective_coords,
          m' =* a_double p5@ p_out * a p5@ p_a * R /\
          proj1_sig (m1double (coords_to_point a)) = feval_projective_coords a_double
    }.


Global Instance spec_of_to_cached: spec_of "to_cached" :=
  fnspec! "to_cached"
    (p_out p_a p_d: word) /
    (a: projective_coords) (d1: felem) (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a p5@ p_a * FElem p_d d1 * R /\
        Datatypes.length out = Z.to_nat (4 * felem_size) /\
        d = feval d1 /\
        bounded_by tight_bounds d1;
      ensures t' m' :=
        t = t' /\
        exists a_cached: cached_coords,
          m' =* a_cached p4@ p_out * a p5@ p_a * FElem p_d d1 * R /\
          proj1_sig (m1_prep (coords_to_point a)) = feval_cached_coords a_cached
  }.

Global Instance spec_of_readd : spec_of "readd" :=
  fnspec! "readd"
    (p_out p_a p_c: word) /
    (a: projective_coords) (c: cached_coords) (out : list byte) (R : _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a p5@ p_a * c p4@ p_c * R /\
        Datatypes.length out = Z.to_nat (5 * felem_size);
      ensures t' m' :=
        t = t' /\
        exists a_plus_c: projective_coords,
          m' =* a_plus_c p5@ p_out * a p5@ p_a * c p4@ p_c * R /\
          proj1_sig (m1_readd (coords_to_point a) (cached_coords_to_cached c))
            = feval_projective_coords a_plus_c
  }.

Local Instance spec_of_fe25519_square : spec_of "fe25519_square" := Field.spec_of_UnOp un_square.
Local Instance spec_of_fe25519_mul : spec_of "fe25519_mul" := Field.spec_of_BinOp bin_mul.
Local Instance spec_of_fe25519_add : spec_of "fe25519_add" := Field.spec_of_BinOp bin_add.
Local Instance spec_of_fe25519_carry_add : spec_of "fe25519_carry_add" := Field.spec_of_BinOp bin_carry_add.
Local Instance spec_of_fe25519_sub : spec_of "fe25519_sub" := Field.spec_of_BinOp bin_sub.
Local Instance spec_of_fe25519_carry_sub : spec_of "fe25519_carry_sub" := Field.spec_of_BinOp bin_carry_sub.
Local Instance spec_of_fe25519_from_word : spec_of "fe25519_from_word" := Field.spec_of_from_word.
Local Instance spec_of_fe26619_copy: spec_of "fe25519_copy" := Field.spec_of_felem_copy.

Local Arguments word.rep : simpl never.
Local Arguments word.wrap : simpl never.
Local Arguments word.unsigned : simpl never.
Local Arguments word.of_Z : simpl never.
Local Arguments word.add : simpl never.

Local Arguments feval : simpl never.

Local Ltac destruct_points :=
  repeat match goal with
    | _ => progress destruct_head' projective_coords
    | _ => progress destruct_head' precomputed_coords
    | _ => progress destruct_head' cached_coords
    | _ => progress destruct_head' prod
    | _ => progress destruct_head' and
    | _ => progress lazy beta match zeta delta [precomputed_coordinates cached_coordinates proj1_sig] in *
  end.

Local Ltac cbv_bounds H :=
  cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds] in H;
  cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds].

Local Ltac solve_bounds :=
  repeat match goal with
  | H: bounded_by loose_bounds ?x |- bounded_by loose_bounds ?x => apply H
  | H: bounded_by tight_bounds ?x |- bounded_by tight_bounds ?x => apply H
  | H: bounded_by tight_bounds ?x |- bounded_by loose_bounds ?x => apply relax_bounds
  | H: bounded_by _ ?x |- bounded_by _ ?x => cbv_bounds H
  end.

 Ltac skipn_firstn_length :=
    change felem_size_in_bytes with 40 in *; listZnWords.

Ltac split_stack_at_n_in stack p n H := rewrite <- (firstn_skipn n stack) in H;
  rewrite (map.of_list_word_at_app_n _ _ _ n) in H; try skipn_firstn_length;
  let D := fresh in
  unshelve(epose (sep_eq_putmany _ _ (map.adjacent_arrays_disjoint_n p (firstn n stack) (skipn n stack) n _ _)) as D);
  try skipn_firstn_length; seprewrite_in D H; rewrite ?skipn_skipn in H; bottom_up_simpl_in_hyp H; clear D.

Local Ltac solve_length :=
  try lia;
  match goal with
    | |- Datatypes.length _ = _ =>
      solve [rewrite ?ws2bs_felem_length; try lia;
          change felem_size_in_bytes with 40 in *; try listZnWords; lia]
  end.

Local Ltac solve_mem :=
  repeat match goal with
    | |- exists _ : _ -> Prop, _%sep _ => eexists
    | H: ?P%sep ?m |- ?G%sep ?m => progress ecancel_assumption_preprocess_with solve_length
    | H : _ %sep ?m |- _ %sep ?m => bottom_up_simpl_in_goal
    | |- _%sep _ => ecancel_assumption
  end.

Local Ltac single_step :=
  repeat straightline; straightline_call; ssplit; try solve_mem; try solve_bounds; try solve_length.

Ltac solve_deallocation := dealloc_preprocess; repeat straightline.

Ltac split_output_stack stack_var ptr_var num_points :=
  match goal with
  | H : context[stack_var $@ ptr_var] |- _ =>
    split_stack_at_n_in stack_var ptr_var 40%nat H;
    split_stack_at_n_in (skipn 40 stack_var) (ptr_var.+40) 40%nat H;
    split_stack_at_n_in (skipn 80 stack_var) (ptr_var.+80) 40%nat H;
    match num_points with
    | 4 => idtac
    | 5 =>
      split_stack_at_n_in (skipn 120 stack_var) (ptr_var.+120) 40%nat H
    end
  end.

Lemma to_cached_ok: program_logic_goal_for_function! to_cached.
Proof.
  (* Without this, resolution of cbv stalls out Qed. *)
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub
      bin_carry_sub un_outbounds bin_outbounds].

  repeat straightline.
  pose proof (cached_implies_coords_valid (m1_prep (coords_to_point a0))) as HPost.
  destruct_points.
  split_output_stack out p_out 4.
  repeat straightline.

  repeat single_step.

  repeat straightline.
  lazy delta [cached_coords].
  unshelve eexists.
  eexists (_, _, _, _).
  2: split; [solve_mem|].
  ssplit; try solve_bounds.
  apply HPost.
  all:(
    cbv [coords_to_point feval_projective_coords feval_cached_coords proj1_sig m1_prep bin_model bin_mul bin_add
      bin_carry_add bin_sub] in *;
    congruence).
Qed.

Lemma add_precomputed_ok : program_logic_goal_for_function! add_precomputed.
Proof.
  (* Without this, resolution of cbv stalls out Qed. *)
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub
      un_outbounds bin_outbounds].

  do 4 straightline.
  pose proof (point_implies_coords_valid (m1add_precomputed_coordinates (coords_to_point a0)
    (precomputed_coords_to_precomputed b))) as HPost.
  destruct_points.
  split_output_stack out p_out 5.
  repeat straightline.

  Time repeat single_step. (* Avoid performance regressions: Keep this around 90s*)

  repeat straightline.
  solve_deallocation.

  cbv [proj1_sig m1add_precomputed_coordinates bin_model bin_add bin_mul bin_sub coords_to_point
      feval_projective_coords precomputed_coords_to_precomputed feval_precomputed_coords] in *.
  unshelve eexists.
  eexists (_, _, _, _, _).
  2: split; [solve_mem|].
  ssplit; try solve_bounds.
  apply HPost.
  all:(congruence).
Qed.

Lemma double_ok : program_logic_goal_for_function! double.
Proof.
  (* Without this, resolution of cbv stalls out Qed. *)
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub
      bin_carry_sub un_outbounds bin_outbounds].

  do 3 straightline.
  pose proof (point_implies_coords_valid (m1double (coords_to_point a0))) as HPost.
  destruct_points.
  split_output_stack out p_out 5.
  repeat straightline.

  repeat single_step.

  (* Solve the postconditions *)
  repeat straightline.
  solve_deallocation.
  cbv [coords_to_point feval_projective_coords projective_coords
    proj1_sig m1double bin_model bin_add bin_mul bin_sub bin_carry_add
    bin_sub bin_carry_sub un_model un_square] in *.
  unshelve eexists.
  eexists (_, _, _, _, _).
  2: split; [solve_mem|].
  ssplit; try solve_bounds.
  apply HPost.
  all:(Prod.inversion_prod; rewrite F.pow_2_r in *; congruence).
Qed.

Lemma readd_ok : program_logic_goal_for_function! readd.
Proof.
  (* Without this, resolution of cbv stalls out Qed. *)
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add
      bin_sub bin_carry_sub un_outbounds bin_outbounds].

  do 4 straightline.
  pose proof (point_implies_coords_valid (m1_readd (coords_to_point a0) (cached_coords_to_cached c))) as HPost.
  destruct_points.
  split_output_stack out p_out 5.
  repeat straightline.

  repeat single_step.

  repeat straightline.
  solve_deallocation.
  cbv [m1_readd proj1_sig coords_to_point feval_projective_coords feval_cached_coords
      cached_coords_to_cached bin_model bin_mul bin_add bin_carry_add bin_sub] in *.
  unshelve eexists.
  eexists (_, _, _, _, _).
  2: split; [solve_mem|].
  ssplit; try solve_bounds.
  apply HPost.
  all:(Prod.inversion_prod; congruence).
Qed.

End WithParameters.
