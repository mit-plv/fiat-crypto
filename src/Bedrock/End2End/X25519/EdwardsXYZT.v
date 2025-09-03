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
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
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
Local Notation "A .X" := (expr.op Syntax.bopname.add A (0)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Y" := (expr.op Syntax.bopname.add A (felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Z" := (expr.op Syntax.bopname.add A (felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Ta" := (expr.op Syntax.bopname.add A (felem_size + felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Tb" := (expr.op Syntax.bopname.add A (felem_size + felem_size + felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).

(* Member access notation for precomputed points: (half_ypx, half_ymx, xyd). *)
Local Notation "A .half_ypx" := (expr.op Syntax.bopname.add A (0)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .half_ymx" := (expr.op Syntax.bopname.add A (felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .xyd" := (expr.op Syntax.bopname.add A (felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).

(* Member access notation for cached points: (half_YmX, half_YpX, Z, Td). *)
Local Notation "A .half_YmX" := (expr.op Syntax.bopname.add A (0)) (in custom bedrock_expr at level 2, left associativity, only parsing).
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
  Context {char_ge_3 : (@Ring.char_ge (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos BinNat.N.two))}.
  Context {field:@Algebra.Hierarchy.field (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}.
  Context {a d: F M_pos}
          {nonzero_a : a <> F.zero}
          {square_a : exists sqrt_a, (F.mul sqrt_a sqrt_a) = a}
          {nonsquare_d : forall x, (F.mul x x) <> d}.
  Context {a_eq_minus1:a = F.opp F.one} {twice_d} {k_eq_2d:twice_d = (F.add d d)} {nonzero_d: d<>F.zero}.

Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).

Local Notation FElem := (FElem(FieldRepresentation:=frep25519)).
Local Notation bounded_by := (bounded_by(FieldRepresentation:=frep25519)).
Local Notation word := (Naive.word 32).
Local Notation felem := (felem(FieldRepresentation:=frep25519)).
Local Notation point := (point(Feq:=Logic.eq)(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(d:=d)).
Local Notation cached := (cached(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(d:=d)).
Local Notation coordinates := (coordinates(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(Feq:=Logic.eq)(a:=a)(d:=d)).
Local Notation cached_coordinates := (cached_coordinates(Fzero:=F.zero)(Fadd:=F.add)(Fdiv:=F.div)(Fmul:=F.mul)(Fsub:=F.sub)(Feq:=Logic.eq)(a:=a)(d:=d)).
Local Notation precomputed_coordinates := (precomputed_coordinates(Fone:=F.one)(Fadd:=F.add)(Fmul:=F.mul)(Fsub:=F.sub)(Feq:=Logic.eq)(a:=a)(d:=d)).
Local Notation m1double :=
  (m1double(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
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

Definition projective_repr P := { p | let '(x,y,z,ta,tb) := p in
                            coordinates P = (feval x, feval y, feval z, feval ta, feval tb) /\
                            bounded_by tight_bounds x /\ bounded_by tight_bounds y /\ bounded_by tight_bounds z /\
                              bounded_by loose_bounds ta /\ bounded_by loose_bounds tb }.
Local Notation "c 'p5@' p" := (let '(x,y,z,ta,tb) := proj1_sig c in sep (sep (sep (sep (FElem (p .+ 0) x) (FElem (p .+ felem_size) y)) 
                              (FElem (p .+ (felem_size + felem_size)) z)) (FElem (p .+ (felem_size + felem_size + felem_size)) ta))
                              (FElem (p .+ (felem_size + felem_size + felem_size + felem_size)) tb)) (at level 10, format "c 'p5@' p").


Definition precomputed_repr (P : precomputed_point) := { p | let '(half_ymx, half_ypx, xyd) := p in
                            precomputed_coordinates P = (feval half_ymx, feval half_ypx, feval xyd) /\
                            bounded_by loose_bounds half_ymx /\ bounded_by loose_bounds half_ypx /\ bounded_by loose_bounds xyd }.
Local Notation "c 'p3@' p" := (let '(half_ymx, half_ypx, xyd) := proj1_sig c in sep (sep (FElem (p .+ 0) half_ymx) (FElem (p .+ felem_size) half_ypx))
                              (FElem (p .+ (felem_size + felem_size)) xyd)) (at level 10, format "c 'p3@' p").

Definition cached_repr (P : cached) := { p | let '(half_ymx, half_ypx,z,td) := p in
                            cached_coordinates P = (feval half_ymx, feval half_ypx, feval z, feval td) /\
                            bounded_by loose_bounds half_ymx /\ bounded_by loose_bounds half_ypx /\bounded_by loose_bounds z /\ bounded_by loose_bounds td }.
Local Notation "c 'p4@' p" := (let '(half_ymx, half_ypx,z,td) := proj1_sig c in sep (sep (sep (FElem (p .+ 0) half_ymx) (FElem (p .+ felem_size) half_ypx))
                              (FElem (p .+ (felem_size + felem_size)) z)) (FElem (p .+ (felem_size + felem_size + felem_size)) td)) (at level 10, format "c 'p4@' p").

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
      exists result,
        bounded_by tight_bounds result /\
        feval result = F.div (feval input) (F.add F.one F.one) /\
        m' =* (FElem result_location result)  * R}.

Global Instance spec_of_add_precomputed : spec_of "add_precomputed" :=
  fnspec! "add_precomputed"
    (p_out p_a p_b: word) / (a: point) (b: precomputed_point) (a_repr: projective_repr a) (b_repr: precomputed_repr b) (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a_repr p5@ p_a * b_repr p3@ p_b * R/\
        Datatypes.length out = Z.to_nat (5 * felem_size); 
      ensures t' m' :=
        t = t' /\
        exists a_plus_b : projective_repr (m1add_precomputed_coordinates a b),
          m' =* a_plus_b p5@ p_out * a_repr p5@ p_a * b_repr p3@ p_b * R
    }.
(*
Global Instance spec_of_double : spec_of "double" :=
  fnspec! "double"
    (p_out p_a: word) /
    (a: point) (a_repr: projective_repr a) (R: _ -> Prop), {
      requires t m :=
        m =* Placeholder5 p_out * a_repr p5@ p_a * R;
      ensures t' m' := 
        t = t' /\
        exists a_double: projective_repr (m1double a),
          m' =* a_double p5@ p_out * a_repr p5@ p_a * R
    }.

Global Instance spec_of_to_cached: spec_of "to_cached" :=
  fnspec! "to_cached"
    (p_out p_a p_d: word) /
    (a: point) (a_repr: projective_repr a) (d1: felem) (R: _ -> Prop), {
      requires t m :=
        m =* Placeholder4 p_out * a_repr p5@ p_a * FElem p_d d1 * R /\
        d = feval d1 /\
        bounded_by tight_bounds d1;
      ensures t' m' :=
        t = t' /\
        exists a_cached: cached_repr (m1_prep a),
          m' =* a_cached p4@ p_out * a_repr p5@ p_a * FElem p_d d1 * R
  }.

Global Instance spec_of_readd : spec_of "readd" :=
  fnspec! "readd"
    (p_out p_a p_c: word) /
    (a: point) (c: cached) (a_repr: projective_repr a) (c_repr: cached_repr c) (R : _ -> Prop), {
      requires t m :=
        m =* Placeholder5 p_out * a_repr p5@ p_a * c_repr p4@ p_c * R;
      ensures t' m' :=
        t = t' /\
        exists a_plus_c: projective_repr (m1_readd a c),
          m' =* a_plus_c p5@ p_out * a_repr p5@ p_a * c_repr p4@ p_c * R
    }.
*)
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
    | _ => progress destruct_head' @Readdition.cached
    | _ => progress destruct_head' cached_repr
    | _ => progress destruct_head' @Basic.point
    | _ => progress destruct_head' projective_repr
    | _ => progress destruct_head' @precomputed_point
    | _ => progress destruct_head' precomputed_repr
    | _ => progress destruct_head' prod
    | _ => progress destruct_head' and
    | _ => progress lazy beta match zeta delta [coordinates precomputed_coordinates cached_coordinates proj1_sig] in *
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
    replace (felem_size_in_bytes (FieldRepresentation:=frep25519)) with 40 in *; [ | lazy; reflexivity ]; (* get rid of felem_size_in_byte, if any *)
    rewrite ?List.length_firstn, ?List.length_skipn; lia. (* listZnWords will probably work*)

Ltac split_stack_at_n_in stack p n H := rewrite <- (firstn_skipn n stack) in H;
  rewrite (map.of_list_word_at_app_n _ _ _ n) in H; try skipn_firstn_length;
  let D := fresh in unshelve(epose (sep_eq_putmany _ _ (map.adjacent_arrays_disjoint_n p (firstn n stack) (skipn n stack) n _ _)) as D); try skipn_firstn_length;
  seprewrite_in D H; rewrite ?skipn_skipn in H; bottom_up_simpl_in_hyp H; clear D.

  (* For the conversion steps below, I could add a strategy to ecancel_assumption_impl. *)
Local Ltac solve_mem :=
  repeat match goal with
  | |- exists _ : _ -> Prop, _%sep _ => eexists
  | |- _%sep _ => ecancel_assumption_impl
  (*| H: ?P%sep ?m |- ?G%sep ?m =>  (* Convert from array1 to placeholder *)
    match P with context[array ptsto (word.of_Z 1) ?p ?stack] =>
    match G with context[Placeholder ?p _] =>
    match goal with L: Datatypes.length stack = _ |- _ =>
      seprewrite_in (iff1_sym (Placeholder_iff_array1 p _ L)) H
    end end end *)
  (*| H: ?P%sep ?m |- ?G%sep ?m =>  (* Solve Placeholder goals when a fixed size list is given *)
    match P with context[map.of_list_word_at ?p ?stack] =>
    match G with context[Placeholder ?p _] =>
      solve [ cbv [Placeholder]; extract_ex1_and_emp_in_goal; bottom_up_simpl_in_goal_nop_ok; split; [ecancel_assumption | skipn_firstn_length] ]
    end end*)
  | |- context[?a + ?b] => match isZcst a with  (* todo can I get rid of these now that I know bottom up simpl*)
        | false => fail
        | true => match (isZcst b) with
            | false => fail
            | true => let c := eval cbv in (a + b) in change (a + b) with c (* Simplify addition of constants. *)
          end
      end
  | H: ?P%sep _ |- _ => match P with context[?a + ?b] => match isZcst a with 
          | false => fail
          | true => match (isZcst b) with
              | false => fail
              | true => let c := eval cbv in (a + b) in change (a + b) with c in H
          end
        end 
      end
  end.

Ltac unfold_felem_size_in_bytes := 
  let s := eval lazy in felem_size_in_bytes in change felem_size_in_bytes with s in *.

(* array1 to Placeholder *)
Hint Extern 1 (Lift1Prop.impl1 (array ptsto (word.of_Z 1) ?p ?stack) (Placeholder ?p _)) => (
    unshelve(erewrite <- (Placeholder_iff_array1 p _ _)); [ (unfold_felem_size_in_bytes; ZnWords) | apply impl1_refl]) : ecancel_impl.
Hint Extern 1 (Lift1Prop.impl1 (map.of_list_word_at ?p ?stack) (Placeholder ?p _)) => (
  cbv [Placeholder]; extract_ex1_and_emp_in_goal; bottom_up_simpl_in_goal_nop_ok; split; [ecancel_assumption | skipn_firstn_length]) : ecancel_impl.

Local Ltac single_step :=
  repeat straightline; straightline_call; ssplit; try solve_mem; try solve_bounds.

(* Attempts to find anybytes terms in the goal and rewrites the first corresponding stack hypothesis to byte representation.
   straightline only supports deallocation for byte representation at the moment. *)
Ltac solve_deallocation :=
  lazy [FElem] in *;
  match goal with
    H: ?P%sep _ |- ?G =>
      repeat match G with context[anybytes ?p _ _] =>
        match P with context[Bignum.Bignum felem_size_in_words p ?v] =>
          seprewrite_in (Bignum.Bignum_to_bytes felem_size_in_words p) H
        end
      end;
      extract_ex1_and_emp_in H
  end;
  repeat straightline.

Lemma add_precomputed_ok : program_logic_goal_for_function! add_precomputed.
Proof.
  (* Without this, resolution of cbv stalls out Qed. *)
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds].

  do 4 straightline.

  (* Split the output into 5 points. *)
  split_stack_at_n_in out p_out 40%nat H12.
  split_stack_at_n_in (skipn 40 out) (p_out.+40) 40%nat H12.
  split_stack_at_n_in (skipn 80 out) (p_out.+80) 40%nat H12. 
  split_stack_at_n_in (skipn 120 out) (p_out.+120) 40%nat H12. 

  repeat straightline.
  destruct_points.

  repeat single_step.

  use_sep_assumption_impl. cancel.
  cancel_seps_at_indices_by_implication 7%nat 0%nat.
  (* todo resolve these and then add the corresponding hint, maybe a lemma to Field.v*)
   cbv [Placeholder]. let m H := fresh in intros m H. extract_ex1_and_emp_in_goal. bottom_up_simpl_in_goal_nop_ok; split; [ecancel_assumption | skipn_firstn_length].

  repeat straightline.
  solve_deallocation.

  lazy beta match zeta delta [m1add_precomputed_coordinates projective_repr precomputed_coordinates coordinates proj1_sig].
  unshelve eexists.
  eexists (_, _, _, _, _).
  2: {
    bottom_up_simpl_in_hyp H86.
    bottom_up_simpl_in_goal.
    replace (p_out.+0) with p_out; [|ZnWords]. (* bottom_up_simpl didn't do this for me. *)
    ecancel_assumption.
  }
  ssplit; try solve_bounds.
  lazy [bin_model bin_add bin_mul bin_sub] in *. congruence.
Qed.

Lemma to_cached_ok: program_logic_goal_for_function! to_cached.
Proof.
  (* Without this, resolution of cbv stalls out Qed. *)
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds].

  straightline.
  destruct_points.

  repeat single_step.
  repeat straightline.

  lazy delta [cached_repr].
  unshelve eexists.
  eexists (_, _, _, _). 2: solve_mem.
  lazy match zeta beta delta [bin_model bin_mul bin_add bin_carry_add bin_sub cached_coordinates coordinates proj1_sig m1_prep] in *.
  ssplit; try solve_bounds.
  congruence.
Qed.

Lemma double_ok : program_logic_goal_for_function! double.
Proof.
  (* Without this, resolution of cbv stalls out Qed. *)
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds].

  straightline.
  destruct_points.

  repeat single_step.

  (* Solve the postconditions *)
  repeat straightline.
  solve_deallocation.
  lazy beta match zeta delta [projective_repr coordinates proj1_sig m1double bin_model bin_add bin_mul bin_sub bin_carry_add bin_sub bin_carry_sub un_model un_square] in *.
  unshelve eexists.
  eexists (_, _, _, _, _).
  2: solve_mem.
  ssplit; try solve_bounds.
  rewrite F.pow_2_r in *.
  Prod.inversion_prod. congruence.
Qed.

Lemma readd_ok : program_logic_goal_for_function! readd.
Proof.
  (* Without this, resolution of cbv stalls out Qed. *)
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds].

  straightline.
  destruct_points.

  repeat single_step. repeat straightline.

  solve_deallocation.

  unshelve eexists.
  eexists (_, _, _, _, _). 2: solve_mem.
  lazy match beta zeta delta [m1_readd coordinates proj1_sig bin_model bin_mul bin_add bin_carry_add bin_sub] in *.
  ssplit; try solve_bounds.
  Prod.inversion_prod. congruence.
Qed.

End WithParameters.
