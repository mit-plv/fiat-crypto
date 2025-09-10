Require Import bedrock2.Array.
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
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.OfListWord.
From coqutil.Tactics Require Import Tactics letexists eabstract rdelta reference_to_string ident_of_string.
Require Import coqutil.Word.Bitwidth64.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Group.ScalarMult.CSwap.
Require Import Crypto.Bedrock.Secp256k1.Field256k1.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Util.Decidable.
Require Import Curves.Weierstrass.Jacobian.Jacobian.
Require Import Curves.Weierstrass.Jacobian.CoZ.
Require Import Lia.
Require Crypto.Bedrock.Field.Synthesis.New.Signature.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Import LittleEndianList.
Import ListNotations.
Import ProgramLogic.Coercions.
Import WeakestPrecondition.
Import BasicC64Semantics.

Local Existing Instance field_parameters.
Local Existing Instance frep256k1.
Local Existing Instance frep256k1_ok.

Definition secp256k1_jopp :=
  func! (OX, OY, OZ, X, Y, Z) {
    secp256k1_felem_copy(OX, X);
    secp256k1_opp(OY, Y);
    secp256k1_felem_copy(OZ, Z)
}.

Definition secp256k1_make_co_z :=
  func! (OX, OY, X, Y, Z) {
    stackalloc 32 as T;
    secp256k1_square(T, Z);
    secp256k1_mul(OX, X, T);
    secp256k1_mul(T, T, Z);
    secp256k1_mul(OY, Y, T)
}.

(* TODO: Can we optimize away the felem_copy? *)
Definition secp256k1_zaddu :=
  func! (OX1, OY1, OX2, OY2, OZ, X1, Y1, X2, Y2, Z) {
    stackalloc 32 as T1;
    stackalloc 32 as T2;
    stackalloc 32 as T4;
    stackalloc 32 as T5;
    stackalloc 32 as T6;
    secp256k1_sub(T6, X1, X2);     (* let t6 := t1 - t4 in *)
    secp256k1_mul(OZ, Z, T6);     (* let t3 := t3 * t6 in *)
    secp256k1_square(T6, T6);      (* let t6 := t6^2 in *)
    secp256k1_mul(T1, X1, T6);     (* let t1 := t1 * t6 in *)
    secp256k1_mul(T6, T6, X2);     (* let t6 := t6 * t4 in *)
    secp256k1_sub(T5, Y1, Y2);     (* let t5 := t2 - t5 in *)
    secp256k1_square(T4, T5);      (* let t4 := t5^2 in *)
    secp256k1_sub(T4, T4, T1);     (* let t4 := t4 - t1 in *)
    secp256k1_sub(T4, T4, T6);     (* let t4 := t4 - t6 in *)
    secp256k1_sub(T6, T1, T6);     (* let t6 := t1 - t6 in *)
    secp256k1_mul(T2, Y1, T6);     (* let t2 := t2 * t6 in *)
    secp256k1_sub(T6, T1, T4);     (* let t6 := t1 - t4 in *)
    secp256k1_mul(T5, T5, T6);     (* let t5 := t5 * t6 in *)
    secp256k1_sub(T5, T5, T2);     (* let t5 := t5 - t2 in *)
    secp256k1_felem_copy(OX1, T4); (* ((t4, t5, t3), (t1, t2, t3)) *)
    secp256k1_felem_copy(OY1, T5);
    secp256k1_felem_copy(OX2, T1);
    secp256k1_felem_copy(OY2, T2)
}.

(* TODO: Can we optimize away the felem_copy? *)
Definition secp256k1_zaddc :=
  func! (OX1, OY1, OX2, OY2, OZ, X1, Y1, X2, Y2, Z) {
    stackalloc 32 as T1;
    stackalloc 32 as T2;
    stackalloc 32 as T4;
    stackalloc 32 as T5;
    stackalloc 32 as T6;
    secp256k1_sub(T6, X1, X2);     (* let t6 := t1 - t4 in *)
    secp256k1_mul(OZ, Z, T6);     (* let t3 := t3 * t6 in *)
    secp256k1_square(T6, T6);      (* let t6 := t6^2 in *)
    stackalloc 32 as T7;
    secp256k1_mul(T7, X1, T6);     (* let t7 := t1 * t6 in *)
    secp256k1_mul(T6, T6, X2);     (* let t6 := t6 * t4 in *)
    secp256k1_add(T1, Y1, Y2);     (* let t1 := t2 + t5 in *)
    secp256k1_square(T4, T1);      (* let t4 := t1^2 in *)
    secp256k1_sub(T4, T4, T7);     (* let t4 := t4 - t7 in *)
    secp256k1_sub(T4, T4, T6);     (* let t4 := t4 - t6 in *)
    secp256k1_sub(T1, Y1, Y2);     (* let t1 := t2 - t5 in *)
    secp256k1_square(T1, T1);      (* let t1 := t1^2 in *)
    secp256k1_sub(T1, T1, T7);     (* let t1 := t1 - t7 in *)
    secp256k1_sub(T1, T1, T6);     (* let t1 := t1 - t6 in *)
    secp256k1_sub(T6, T6, T7);     (* let t6 := t6 - t7 in *)
    secp256k1_mul(T6, T6, Y1);     (* let t6 := t6 * t2 in *)
    secp256k1_sub(T2, Y1, Y2);     (* let t2 := t2 - t5 in *)
    secp256k1_add(T5, Y2, Y2);     (* let t5 := t5 + t5 in *)
    secp256k1_add(T5, T2, T5);     (* let t5 := t2 + t5 in *)
    secp256k1_sub(T7, T7, T4);     (* let t7 := t7 - t4 in *)
    secp256k1_mul(T5, T5, T7);     (* let t5 := t5 * t7 in *)
    secp256k1_add(T5, T5, T6);     (* let t5 := t5 + t6 in *)
    secp256k1_add(T7, T4, T7);     (* let t7 := t4 + t7 in *)
    secp256k1_sub(T7, T7, T1);     (* let t7 := t7 - t1 in *)
    secp256k1_mul(T2, T2, T7);     (* let t2 := t2 * t7 in *)
    secp256k1_add(T2, T2, T6);     (* let t2 := t2 + t6 in *)
    secp256k1_felem_copy(OX1, T1); (* ((t1, t2, t3), (t4, t5, t3)) *)
    secp256k1_felem_copy(OY1, T2);
    secp256k1_felem_copy(OX2, T4);
    secp256k1_felem_copy(OY2, T5)
}.

(* Specialized with a=0 *)
Definition secp256k1_dblu :=
  func! (OX1, OY1, OX2, OY2, OZ, X1, Y1) {
    stackalloc 32 as T1;
    stackalloc 32 as T2;
    secp256k1_add(OZ, Y1, Y1);     (* let t3 := t2 + t2 in *)
    secp256k1_square(T2, Y1);      (* let t2 := t2^2 in *)
    stackalloc 32 as T4;
    secp256k1_add(T4, X1, T2);     (* let t4 := t1 + t2 in *)
    secp256k1_square(T4, T4);      (* let t4 := t4^2 in *)
    stackalloc 32 as T5;
    secp256k1_square(T5, X1);      (* let t5 := t1^2 in *)
    secp256k1_sub(T4, T4, T5);     (* let t4 := t4 - t5 in *)
    secp256k1_square(T2, T2);      (* let t2 := t2^2 in *)
    secp256k1_sub(T4, T4, T2);     (* let t4 := t4 - t2 in *)
    secp256k1_add(T1, T4, T4);     (* let t1 := t4 + t4 in *)
    (* secp256k1_add(T0, T0, T5); *)     (* let t0 := t0 + t5 in *)
    stackalloc 32 as T0;
    secp256k1_felem_copy(T0, T5);  (* a = 0 for secp256k1 *)
    secp256k1_add(T5, T5, T5);     (* let t5 := t5 + t5 in *)
    secp256k1_add(T0, T0, T5);     (* let t0 := t0 + t5 in *)
    secp256k1_square(T4, T0);      (* let t4 := t0^2 in *)
    secp256k1_add(T5, T1, T1);     (* let t5 := t1 + t1 in *)
    secp256k1_sub(T4, T4, T5);     (* let t4 := t4 - t5 in *)
    secp256k1_add(T2, T2, T2);
    secp256k1_add(T2, T2, T2);
    secp256k1_add(T2, T2, T2);     (* let t2 := 8 * t2 in *)
    secp256k1_sub(T5, T1, T4);     (* let t5 := t1 - t4 in *)
    secp256k1_mul(T5, T5, T0);     (* let t5 := t5 * t0 in *)
    secp256k1_sub(T5, T5, T2);     (* let t5 := t5 - t2 in *)
    secp256k1_felem_copy(OX1, T4); (* ((t4, t5, t3), (t1, t2, t3)) *)
    secp256k1_felem_copy(OY1, T5);
    secp256k1_felem_copy(OX2, T1);
    secp256k1_felem_copy(OY2, T2)
}.

(* TODO: it should be possible to not use any temp field registers *)
Definition secp256k1_tplu :=
  func! (OX1, OY1, OX2, OY2, OZ, X1, Y1) {
    stackalloc 32 as T1;
    stackalloc 32 as T2;
    stackalloc 32 as T3;
    stackalloc 32 as T4;
    stackalloc 32 as T5;
    secp256k1_dblu(T1, T2, T3, T4, T5, X1, Y1);
    secp256k1_zaddu(OX1, OY1, OX2, OY2, OZ, T3, T4, T1, T2, T5)
}.

Definition secp256k1_zdau :=
  func! (X1, Y1, X2, Y2, Z) {
    stackalloc 32 as T1;
    stackalloc 32 as T2;
    stackalloc 32 as T4;
    stackalloc 32 as T5;
    stackalloc 32 as T6;
    secp256k1_sub(T6, X1, X2);     (* let t6 := t1 - t4 in *)
    stackalloc 32 as T7;
    secp256k1_square(T7, T6);      (* let t7 := t6^2 in *)
    secp256k1_mul(T1, X1, T7);     (* let t1 := t1 * t7 in *)
    secp256k1_mul(T4, X2, T7);     (* let t4 := t4 * t7 in *)
    secp256k1_sub(T5, Y1, Y2);     (* let t5 := t2 - t5 in *)
    stackalloc 32 as T8;
    secp256k1_sub(T8, T1, T4);     (* let t8 := t1 - t4 in *)
    secp256k1_mul(T2, Y1, T8);     (* let t2 := t2 * t8 in *)
    secp256k1_add(T2, T2, T2);     (* let t2 := t2 + t2 in *)
    secp256k1_square(T8, T5);      (* let t8 := t5^2 in *)
    secp256k1_sub(T4, T8, T4);     (* let t4 := t8 - t4 in *)
    secp256k1_sub(T4, T4, T1);     (* let t4 := t4 - t1 in *)
    secp256k1_sub(T4, T4, T1);     (* let t4 := t4 - t1 in *)
    secp256k1_add(T6, T4, T6);     (* let t6 := t4 + t6 in *)
    secp256k1_square(T6, T6);      (* let t6 := t6^2 in *)
    secp256k1_sub(T6, T6, T7);     (* let t6 := t6 - t7 in *)
    secp256k1_sub(T5, T5, T4);     (* let t5 := t5 - t4 in *)
    secp256k1_square(T5, T5);      (* let t5 := t5^2 in *)
    secp256k1_sub(T5, T5, T8);     (* let t5 := t5 - t8 in *)
    secp256k1_sub(T5, T5, T2);     (* let t5 := t5 - t2 in *)
    secp256k1_square(T7, T4);      (* let t7 := t4^2 in *)
    secp256k1_sub(T5, T5, T7);     (* let t5 := t5 - t7 in *)
    secp256k1_add(T8, T7, T7);     (* let t8 := t7 + t7 in *)
    secp256k1_add(T8, T8, T8);     (* let t8 := t8 + t8 in *)
    secp256k1_sub(T6, T6, T7);     (* let t6 := t6 - t7 in *)
    secp256k1_mul(Z, Z, T6);     (* let t3 := t3 * t6 in *)
    secp256k1_mul(T6, T1, T8);     (* let t6 := t1 * t8 in *)
    secp256k1_add(T1, T1, T4);     (* let t1 := t1 + t4 in *)
    secp256k1_mul(T8, T8, T1);     (* let t8 := t8 * t1 in *)
    secp256k1_add(T7, T2, T5);     (* let t7 := t2 + t5 in *)
    secp256k1_sub(T2, T5, T2);     (* let t2 := t5 - t2 in *)
    secp256k1_sub(T1, T8, T6);     (* let t1 := t8 - t6 in *)
    secp256k1_mul(T5, T5, T1);     (* let t5 := t5 * t1 in *)
    secp256k1_add(T6, T6, T8);     (* let t6 := t6 + t8 in *)
    secp256k1_square(T1, T2);      (* let t1 := t2^2 in *)
    secp256k1_sub(X1, T1, T6);     (* let t1 := t1 - t6 in *)
    secp256k1_sub(T4, T8, X1);     (* let t4 := t8 - t1 in *)
    secp256k1_mul(T2, T2, T4);     (* let t2 := t2 * t4 in *)
    secp256k1_sub(Y1, T2, T5);     (* let t2 := t2 - t5 in *)
    secp256k1_square(T4, T7);      (* let t4 := t7^2 in *)
    secp256k1_sub(X2, T4, T6);     (* let t4 := t4 - t6 in *)
    secp256k1_sub(T8, T8, X2);     (* let t8 := t8 - t4 in *)
    secp256k1_mul(T7, T7, T8);     (* let t7 := t7 * t8 in *)
    secp256k1_sub(Y2, T7, T5)     (* let t5 := t7 - t5 in *)
}.

Definition secp256k1_felem_cswap := CSwap.felem_cswap(word:=Naive.word64)(field_parameters:=field_parameters)(field_representaton:=frep256k1).

(* Compute ToCString.c_func ("secp256k1_zaddu", secp256k1_zaddu). *)
(* Compute ToCString.c_func ("secp256k1_felem_cswap", secp256k1_felem_cswap). *)

Section WithParameters.
  Context {two_lt_M: 2 < M_pos}.
  Context {char_ge_3 : (@Ring.char_ge (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos BinNat.N.two))}.
  Context {field:@Algebra.Hierarchy.field (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}.
  Context {a b : F M_pos}.
  Context {zero_a : id a = F.zero}
          {seven_b : id b = F.of_Z _ 7}.

  Local Coercion F.to_Z : F >-> Z.
  Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
  Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").

  Local Notation FElem := (FElem(FieldRepresentation:=frep256k1)).
  Local Notation word := (Naive.word 64).
  Local Notation felem := (felem(FieldRepresentation:=frep256k1)).
  Local Notation point := (Jacobian.point(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(b:=b)(Feq_dec:=F.eq_dec)).
  Local Notation co_z := (Jacobian.co_z(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(b:=b)(Feq_dec:=F.eq_dec)).
  Local Notation z_of := (Jacobian.z_of(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(b:=b)(Feq_dec:=F.eq_dec)).
  Local Notation jopp :=
    (Jacobian.opp(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
       (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
       (a:=a)(b:=b)(field:=field)(Feq_dec:=F.eq_dec)).
  Local Notation make_co_z :=
    (Jacobian.make_co_z(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
       (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
       (a:=a)(b:=b)(field:=field)(Feq_dec:=F.eq_dec)).
  Local Notation zaddu :=
    (Jacobian.zaddu(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
       (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
       (a:=a)(b:=b)(field:=field)(Feq_dec:=F.eq_dec)).
  Local Notation zaddc :=
    (Jacobian.zaddc(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
       (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
       (a:=a)(b:=b)(field:=field)(Feq_dec:=F.eq_dec)).
  Local Notation dblu :=
    (Jacobian.dblu(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
       (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
       (a:=a)(b:=b)(field:=field)(Feq_dec:=F.eq_dec)).
  Local Notation tplu :=
    (Jacobian.tplu(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
       (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
       (a:=a)(b:=b)(field:=field)(Feq_dec:=F.eq_dec)).
  Local Notation zdau :=
    (Jacobian.zdau(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
       (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
       (a:=a)(b:=b)(field:=field)(Feq_dec:=F.eq_dec)).

  Global Instance spec_of_jopp : spec_of "secp256k1_jopp" :=
    fnspec! "secp256k1_jopp"
      (OXK OYK OZK XK YK ZK : word) / (OX OY OZ X Y Z : felem) (P : point)
      (R : _ -> Prop),
    { requires t m :=
        proj1_sig P = ((feval X), (feval Y), (feval Z)) /\
        bounded_by loose_bounds X /\
        bounded_by loose_bounds Y /\
        bounded_by loose_bounds Z /\
        m =* (FElem OXK OX) * (FElem OYK OY) * (FElem OZK OZ) *
             (FElem XK X) * (FElem YK Y) * (FElem ZK Z) * R;
      ensures t' m' :=
        t = t' /\
        exists OX' OY' OZ',
        proj1_sig (jopp P) = ((feval OX'), (feval OY'), (feval OZ')) /\
        bounded_by tight_bounds OX' /\
        bounded_by tight_bounds OY' /\
        bounded_by tight_bounds OZ' /\
        m' =* (FElem OXK OX') * (FElem OYK OY') * (FElem OZK OZ') *
              (FElem XK X) * (FElem YK Y) * (FElem ZK Z) * R
    }.

  Global Instance spec_of_make_co_z : spec_of "secp256k1_make_co_z" :=
    fnspec! "secp256k1_make_co_z"
      (OXK OYK XK YK ZK : word) / (OX OY X Y Z : felem)
      (P Q : point) (HQaff: z_of Q = 1%F) (R : _ -> Prop),
    { requires t m :=
        (exists x y, proj1_sig P = (x, y, (feval Z))) /\
        (exists z, proj1_sig Q = ((feval X), (feval Y), z)) /\
        bounded_by loose_bounds X /\
        bounded_by loose_bounds Y /\
        bounded_by loose_bounds Z /\
        m =* (FElem OXK OX) * (FElem OYK OY) *
             (FElem XK X) * (FElem YK Y) * (FElem ZK Z) * R;
      ensures t' m' :=
        t = t' /\
        exists OX' OY',
        proj1_sig (snd (make_co_z P Q HQaff)) = ((feval OX'), (feval OY'), (feval Z)) /\
        bounded_by tight_bounds OX' /\
        bounded_by tight_bounds OY' /\
        m' =* (FElem OXK OX') * (FElem OYK OY') *
              (FElem XK X) * (FElem YK Y) * (FElem ZK Z) * R
    }.

  Global Instance spec_of_zaddu : spec_of "secp256k1_zaddu" :=
    fnspec! "secp256k1_zaddu"
      (OX1K OY1K OX2K OY2K OZK X1K Y1K X2K Y2K ZK : word) /
      (OX1 OY1 OX2 OY2 OZ X1 Y1 X2 Y2 Z : felem) (P Q : point)
      (HPQ : co_z P Q) (R : _ -> Prop),
    { requires t m :=
        proj1_sig P = ((feval X1), (feval Y1), (feval Z)) /\
        proj1_sig Q = ((feval X2), (feval Y2), (feval Z)) /\
        bounded_by loose_bounds X1 /\
        bounded_by loose_bounds Y1 /\
        bounded_by loose_bounds X2 /\
        bounded_by loose_bounds Y2 /\
        bounded_by loose_bounds Z /\
        m =* (FElem OX1K OX1) * (FElem OY1K OY1) *
             (FElem OX2K OX2) * (FElem OY2K OY2) * (FElem OZK OZ) *
             (FElem X1K X1) * (FElem Y1K Y1) *
             (FElem X2K X2) * (FElem Y2K Y2) * (FElem ZK Z) * R;
      ensures t' m' :=
        t = t' /\
        exists OX1' OY1' OX2' OY2' OZ',
        proj1_sig (fst (zaddu P Q HPQ)) = ((feval OX1'), (feval OY1'), (feval OZ')) /\
        proj1_sig (snd (zaddu P Q HPQ)) = ((feval OX2'), (feval OY2'), (feval OZ')) /\
        bounded_by tight_bounds OX1' /\
        bounded_by tight_bounds OY1' /\
        bounded_by tight_bounds OX2' /\
        bounded_by tight_bounds OY2' /\
        bounded_by tight_bounds OZ' /\
        m' =* (FElem OX1K OX1') * (FElem OY1K OY1') *
              (FElem OX2K OX2') * (FElem OY2K OY2') * (FElem OZK OZ') *
              (FElem X1K X1) * (FElem Y1K Y1) *
              (FElem X2K X2) * (FElem Y2K Y2) * (FElem ZK Z) * R
    }.

  Global Instance spec_of_zaddc : spec_of "secp256k1_zaddc" :=
    fnspec! "secp256k1_zaddc"
      (OX1K OY1K OX2K OY2K OZK X1K Y1K X2K Y2K ZK : word) /
      (OX1 OY1 OX2 OY2 OZ X1 Y1 X2 Y2 Z : felem) (P Q : point)
      (HPQ : co_z P Q) (R : _ -> Prop),
    { requires t m :=
        proj1_sig P = ((feval X1), (feval Y1), (feval Z)) /\
        proj1_sig Q = ((feval X2), (feval Y2), (feval Z)) /\
        bounded_by loose_bounds X1 /\
        bounded_by loose_bounds Y1 /\
        bounded_by loose_bounds X2 /\
        bounded_by loose_bounds Y2 /\
        bounded_by loose_bounds Z /\
        m =* (FElem OX1K OX1) * (FElem OY1K OY1) *
             (FElem OX2K OX2) * (FElem OY2K OY2) * (FElem OZK OZ) *
             (FElem X1K X1) * (FElem Y1K Y1) *
             (FElem X2K X2) * (FElem Y2K Y2) * (FElem ZK Z) * R;
      ensures t' m' :=
        t = t' /\
        exists OX1' OY1' OX2' OY2' OZ',
        proj1_sig (fst (zaddc P Q HPQ)) = ((feval OX1'), (feval OY1'), (feval OZ')) /\
        proj1_sig (snd (zaddc P Q HPQ)) = ((feval OX2'), (feval OY2'), (feval OZ')) /\
        bounded_by tight_bounds OX1' /\
        bounded_by tight_bounds OY1' /\
        bounded_by tight_bounds OX2' /\
        bounded_by tight_bounds OY2' /\
        bounded_by tight_bounds OZ' /\
        m' =* (FElem OX1K OX1') * (FElem OY1K OY1') *
              (FElem OX2K OX2') * (FElem OY2K OY2') * (FElem OZK OZ') *
              (FElem X1K X1) * (FElem Y1K Y1) *
              (FElem X2K X2) * (FElem Y2K Y2) * (FElem ZK Z) * R
    }.

  Global Instance spec_of_dblu: spec_of "secp256k1_dblu" :=
    fnspec! "secp256k1_dblu"
      (OX1K OY1K OX2K OY2K OZK X1K Y1K : word) /
      (OX1 OY1 OX2 OY2 OZ X1 Y1 : felem) (P : point)
      (HPaff : z_of P = F.one) (R : _ -> Prop),
    { requires t m :=
        (exists z, proj1_sig P = ((feval X1), (feval Y1), z)) /\
        bounded_by loose_bounds X1 /\
        bounded_by loose_bounds Y1 /\
        m =* (FElem OX1K OX1) * (FElem OY1K OY1) *
             (FElem OX2K OX2) * (FElem OY2K OY2) * (FElem OZK OZ) *
             (FElem X1K X1) * (FElem Y1K Y1) * R;
      ensures t' m' :=
        t = t' /\
        exists OX1' OY1' OX2' OY2' OZ',
        proj1_sig (fst (dblu P HPaff)) = ((feval OX1'), (feval OY1'), (feval OZ')) /\
        proj1_sig (snd (dblu P HPaff)) = ((feval OX2'), (feval OY2'), (feval OZ')) /\
        bounded_by tight_bounds OX1' /\
        bounded_by tight_bounds OY1' /\
        bounded_by tight_bounds OX2' /\
        bounded_by tight_bounds OY2' /\
        bounded_by tight_bounds OZ' /\
        m' =* (FElem OX1K OX1') * (FElem OY1K OY1') *
              (FElem OX2K OX2') * (FElem OY2K OY2') * (FElem OZK OZ') *
              (FElem X1K X1) * (FElem Y1K Y1) * R
    }.

  Global Instance spec_of_tplu : spec_of "secp256k1_tplu" :=
    fnspec! "secp256k1_tplu"
      (OX1K OY1K OX2K OY2K OZK X1K Y1K : word) /
      (OX1 OY1 OX2 OY2 OZ X1 Y1 : felem) (P : point)
      (HPaff : z_of P = F.one) (R : _ -> Prop),
    { requires t m :=
        (exists z, proj1_sig P = ((feval X1), (feval Y1), z)) /\
        bounded_by loose_bounds X1 /\
        bounded_by loose_bounds Y1 /\
        m =* (FElem OX1K OX1) * (FElem OY1K OY1) *
             (FElem OX2K OX2) * (FElem OY2K OY2) * (FElem OZK OZ) *
             (FElem X1K X1) * (FElem Y1K Y1) * R;
      ensures t' m' :=
        t = t' /\
        exists OX1' OY1' OX2' OY2' OZ',
        proj1_sig (fst (tplu P HPaff)) = ((feval OX1'), (feval OY1'), (feval OZ')) /\
        proj1_sig (snd (tplu P HPaff)) = ((feval OX2'), (feval OY2'), (feval OZ')) /\
        bounded_by tight_bounds OX1' /\
        bounded_by tight_bounds OY1' /\
        bounded_by tight_bounds OX2' /\
        bounded_by tight_bounds OY2' /\
        bounded_by tight_bounds OZ' /\
        m' =* (FElem OX1K OX1') * (FElem OY1K OY1') *
              (FElem OX2K OX2') * (FElem OY2K OY2') * (FElem OZK OZ') *
              (FElem X1K X1) * (FElem Y1K Y1) * R
    }.

  Global Instance spec_of_zdau : spec_of "secp256k1_zdau" :=
    fnspec! "secp256k1_zdau"
      (X1K Y1K X2K Y2K ZK : word) /
      (X1 Y1 X2 Y2 Z : felem) (P Q : point)
      (HPQ : co_z P Q) (R : _ -> Prop),
    { requires t m :=
        proj1_sig P = ((feval X1), (feval Y1), (feval Z)) /\
        proj1_sig Q = ((feval X2), (feval Y2), (feval Z)) /\
        bounded_by loose_bounds X1 /\
        bounded_by loose_bounds Y1 /\
        bounded_by loose_bounds X2 /\
        bounded_by loose_bounds Y2 /\
        bounded_by loose_bounds Z /\
        m =* (FElem X1K X1) * (FElem Y1K Y1) *
             (FElem X2K X2) * (FElem Y2K Y2) * (FElem ZK Z) * R;
      ensures t' m' :=
        t = t' /\
        exists OX1 OY1 OX2 OY2 OZ,
        proj1_sig (fst (zdau P Q HPQ)) = ((feval OX1), (feval OY1), (feval OZ)) /\
        proj1_sig (snd (zdau P Q HPQ)) = ((feval OX2), (feval OY2), (feval OZ)) /\
        bounded_by tight_bounds OX1 /\
        bounded_by tight_bounds OY1 /\
        bounded_by tight_bounds OX2 /\
        bounded_by tight_bounds OY2 /\
        bounded_by tight_bounds OZ /\
        m' =* (FElem X1K OX1) * (FElem Y1K OY1) *
              (FElem X2K OX2) * (FElem Y2K OY2) * (FElem ZK OZ) * R
    }.

  Local Instance spec_of_secp256k1_opp : spec_of "secp256k1_opp" := Field.spec_of_UnOp un_opp.
  Local Instance spec_of_secp256k1_square : spec_of "secp256k1_square" := Field.spec_of_UnOp un_square.
  Local Instance spec_of_secp256k1_mul : spec_of "secp256k1_mul" := Field.spec_of_BinOp bin_mul.
  Local Instance spec_of_secp256k1_add : spec_of "secp256k1_add" := Field.spec_of_BinOp bin_add.
  Local Instance spec_of_secp256k1_sub : spec_of "secp256k1_sub" := Field.spec_of_BinOp bin_sub.
  Local Instance spec_of_secp256k1_felem_copy : spec_of "secp256k1_felem_copy" := Field.spec_of_felem_copy.

  Local Arguments word.rep : simpl never.
  Local Arguments word.wrap : simpl never.
  Local Arguments word.unsigned : simpl never.
  Local Arguments word.of_Z : simpl never.

  Local Ltac solve_mem :=
    repeat match goal with
      | |- exists _ : _ -> Prop, _%sep _ => eexists
      | |- _%sep _ => ecancel_assumption_impl
      end.

  Local Ltac cbv_bounds H :=
    cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds] in H;
    cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds].

  Local Ltac solve_bounds :=
    match goal with
      | H: bounded_by _ ?x |- bounded_by _ ?x => apply H
      end.

  Local Ltac solve_stack :=
    (* Rewrites the `stack$@a` term in H to use a Bignum instead *)
    cbv [FElem];
    match goal with
    | H: _%sep ?m |- (Bignum.Bignum felem_size_in_words ?a _ * _)%sep ?m =>
        seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 4 a) H
    end;
    [> transitivity 32%nat; trivial | ];
    (* proves the memory matches up *)
    use_sep_assumption; cancel; cancel_seps_at_indices 0%nat 0%nat; cbn; [> trivial | eapply RelationClasses.reflexivity].

  Local Ltac single_step :=
    repeat straightline; straightline_call; ssplit; try solve_mem; try solve_bounds; try solve_stack.

  Lemma secp256k1_jopp_ok : program_logic_goal_for_function! secp256k1_jopp.
  Proof.
    Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds].

    do 3 single_step.
    repeat straightline.

    exists X, x, Z; ssplit. 2-4:solve_bounds.
    cbv [bin_model bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_model un_square] in *.
    cbv match beta delta [jopp proj1_sig fst snd].
    destruct P; cbv [proj1_sig] in H2.
    rewrite H2; cbv match zeta. rewrite H10. reflexivity.

    ecancel_assumption.
  Qed.

  Add Ring Private_ring : (F.ring_theory M_pos) (morphism (F.ring_morph M_pos), constants [F.is_constant]).

  Lemma secp256k1_make_co_z_ok : program_logic_goal_for_function! secp256k1_make_co_z.
  Proof.
    Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds].

    do 4 single_step.
    repeat straightline.

    cbv [FElem] in *.
    match goal with
    | |- context [anybytes ?a _ _] =>
        match goal with
        | H: _ ?a' |- context [map.split ?a' _ _] =>
            seprewrite_in (@Bignum.Bignum_to_bytes _ _ _ _ _ _ felem_size_in_words a) H
        end
    end.
    extract_ex1_and_emp_in H26.

    repeat straightline.
    exists x3, x5; ssplit. 2-3:solve_bounds.
    cbv [bin_model bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_model un_square] in *.
    cbv match beta delta [make_co_z proj1_sig fst snd].
    destruct P; destruct Q; cbv [proj1_sig] in H3, H4.
    rewrite H3, H4; cbv match zeta.
    repeat match goal with
           | H: feval ?x = _ |- context [feval ?x] => rewrite H
           end.
    rewrite F.pow_2_r in *; repeat (apply pair_equal_spec; split); ring.

    ecancel_assumption.
  Qed.

  Lemma secp256k1_zaddu_ok : program_logic_goal_for_function! secp256k1_zaddu.
  Proof.
    Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds].

    do 14 single_step.
    do 4 single_step.

    repeat straightline.
    (* Rewrites the FElems for the stack to be about bytes instead *)
    cbv [FElem] in *.
    repeat match goal with
    | |- context [anybytes ?a _ _] =>
        match goal with
        | H: _ ?a' |- context [map.split ?a' _ _] =>
            seprewrite_in (@Bignum.Bignum_to_bytes _ _ _ _ _ _ felem_size_in_words a) H
        end
    end.
    extract_ex1_and_emp_in H92.

    (* Solve stack/memory stuff *)
    repeat straightline.

    (* Post-conditions *)
    exists x7,x12,x2,x9,x0; ssplit. 3-7:solve_bounds.
    (* Correctness: result matches Gallina *)
    1,2: cbv [bin_model bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_model un_square] in *.
    1,2: cbv match beta delta [zaddu proj1_sig fst snd].
    1,2: destruct P; destruct Q; cbv [proj1_sig] in H17, H18.
    1,2: rewrite H17, H18; cbv match zeta.
    1,2: rewrite F.pow_2_r in *; congruence.

    ecancel_assumption.
  Qed.

  Lemma secp256k1_zaddc_ok: program_logic_goal_for_function! secp256k1_zaddc.
  Proof.
    Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds].

    do 25 single_step.
    do 4 single_step.

    repeat straightline.
    cbv [FElem] in *.
    repeat match goal with
    | |- context [anybytes ?a _ _] =>
        match goal with
        | H: _ ?a' |- context [map.split ?a' _ _] =>
            seprewrite_in (@Bignum.Bignum_to_bytes _ _ _ _ _ _ felem_size_in_words a) H
        end
    end.
    extract_ex1_and_emp_in H140.

    repeat straightline.
    exists x11,x23,x7,x19,x0; ssplit. 3-7:solve_bounds.
    1,2: cbv [bin_model bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_model un_square] in *.
    1,2: cbv match beta delta [zaddc proj1_sig fst snd].
    1,2: destruct P; destruct Q; cbv [proj1_sig] in H28, H29.
    1,2: rewrite H28, H29; cbv match zeta.
    1,2: rewrite F.pow_2_r in *; congruence.

    ecancel_assumption.
  Qed.

  Lemma secp256k1_dblu_ok: program_logic_goal_for_function! secp256k1_dblu.
  Proof.
    Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds].
    repeat single_step.

    repeat straightline.
    cbv [FElem] in *.
    repeat match goal with
    | |- context [anybytes ?a _ _] =>
        match goal with
        | H: _ ?a' |- context [map.split ?a' _ _] =>
            seprewrite_in (@Bignum.Bignum_to_bytes _ _ _ _ _ _ felem_size_in_words a) H
        end
    end.
    extract_ex1_and_emp_in H114.

    repeat straightline.
    exists x13,x19,x8,x16,x0; ssplit. 3-7:solve_bounds.
    1,2: cbv [bin_model bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_model un_square] in *.
    1,2: cbv match beta delta [dblu proj1_sig fst snd].
    1,2: destruct P; cbv [proj1_sig] in H24.
    1,2: rewrite H24; cbv match zeta.
    1,2: rewrite F.pow_2_r in *; cbv [id] in zero_a; subst a; repeat (apply pair_equal_spec; split); try congruence.
    1,2,3: repeat match goal with
                  | H: feval ?x = _ |- context [feval ?x] => rewrite H
                  end; ring.

    ecancel_assumption.
  Qed.

  Lemma secp256k1_tplu_ok: program_logic_goal_for_function! secp256k1_tplu.
  Proof.
    Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds].

    repeat straightline.
    eapply Proper_call; cycle -1; [eapply H|try eabstract (solve [ Morphisms.solve_proper ])..]; [ .. | intros ? ? ? ? ].
    ssplit; [eexists; eassumption|..]; try eassumption.
    repeat match goal with
    | H: context [array ptsto _ ?a _] |- context [FElem ?a _] =>
        seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 4 a) H; [trivial|]
    end.
    multimatch goal with
    | |- _ ?m1 =>
        multimatch goal with
        | H:_ ?m2
          |- _ =>
            syntactic_unify._syntactic_unify_deltavar m1 m2;
            refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H
        end
    end; cancel.
    cancel_seps_at_indices 4%nat 0%nat; [reflexivity|].
    cancel_seps_at_indices 3%nat 0%nat; [reflexivity|].
    cancel_seps_at_indices 2%nat 0%nat; [reflexivity|].
    cancel_seps_at_indices 1%nat 0%nat; [reflexivity|].
    cancel_seps_at_indices 0%nat 0%nat; [reflexivity|].
    solve [ecancel].

    repeat straightline.
    eapply Proper_call; cycle -1; [eapply H0|try eabstract (solve [ Morphisms.solve_proper ])..]; [ .. | intros ? ? ? ? ].
    ssplit; [exact H28|exact H27|..]; try solve_bounds.
    ecancel_assumption.

    repeat straightline.
    cbv [FElem] in *.
    repeat match goal with
    | |- context [anybytes ?a _ _] =>
        match goal with
        | H: _ ?a' |- context [map.split ?a' _ _] =>
            seprewrite_in (@Bignum.Bignum_to_bytes _ _ _ _ _ _ felem_size_in_words a) H
        end
    end.
    extract_ex1_and_emp_in H42.

    repeat straightline.
    exists x5,x6,x7,x8,x9; ssplit. 3-7:solve_bounds.
    exact H35. exact H36.

    ecancel_assumption.
  Qed.

  Lemma secp256k1_zdau_ok: program_logic_goal_for_function! secp256k1_zdau.
  Proof.
    Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds].

    do 43 single_step.

    repeat straightline.
    cbv [FElem] in *.
    repeat match goal with
    | |- context [anybytes ?a _ _] =>
        match goal with
        | H: _ ?a' |- context [map.split ?a' _ _] =>
            seprewrite_in (@Bignum.Bignum_to_bytes _ _ _ _ _ _ felem_size_in_words a) H
        end
    end.
    extract_ex1_and_emp_in H208.

    repeat straightline.
    exists x33,x36,x38,x41,x23; ssplit. 3-7:solve_bounds.
    1,2: cbv [bin_model bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_model un_square] in *.
    1,2: cbv match beta delta [zdau proj1_sig fst snd].
    1,2: destruct P; destruct Q; cbv [proj1_sig] in H42, H43.
    1,2: rewrite H42, H43; cbv match zeta.
    1,2: rewrite F.pow_2_r in *; congruence.

    ecancel_assumption.
  Qed.

End WithParameters.

(* Require Import bedrock2.ToCString. *)
(* Require Import coqutil.Macros.WithBaseName. *)
(* Definition funcs := *)
(*   List.app *)
(*   [ secp256k1_opp; *)
(*     secp256k1_mul; *)
(*     secp256k1_add; *)
(*     secp256k1_sub; *)
(*     secp256k1_square; *)
(*     secp256k1_to_bytes; *)
(*     secp256k1_from_bytes; *)
(*     secp256k1_from_mont; *)
(*     secp256k1_to_mont; *)
(*     secp256k1_select_znz] *)
(*   &[,secp256k1_jopp; *)
(*      secp256k1_make_co_z; *)
(*      secp256k1_felem_cswap; *)
(*      secp256k1_zaddu; *)
(*      secp256k1_zaddc; *)
(*      secp256k1_dblu; *)
(*      secp256k1_tplu; *)
(*      secp256k1_zdau]. *)

(* Compute (ToCString.c_module funcs). *)
