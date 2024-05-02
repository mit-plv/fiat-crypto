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
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Group.ScalarMult.CSwap.
Require Import Crypto.Bedrock.End2End.Secp256k1.Field256k1.
Require Import Crypto.Bedrock.End2End.Secp256k1.JacobianCoZ.
Require Import Crypto.Bedrock.End2End.Secp256k1.Addchain.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Util.Decidable.
Require Import Curves.Weierstrass.Jacobian.Jacobian.
Require Import Curves.Weierstrass.Jacobian.CoZ.
Require Import Curves.Weierstrass.Jacobian.ScalarMult.
Require Import Lia.
Require Crypto.Bedrock.Field.Synthesis.New.Signature.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Import LittleEndianList.
Import ListNotations.
Import ProgramLogic.Coercions.
Import WeakestPrecondition.

Local Existing Instance field_parameters.
Local Instance frep256k1 : Field.FieldRepresentation := field_representation Field256k1.m.
Local Existing Instance frep256k1_ok.

Definition secp256k1_laddermul :=
  func! (oX, oY, k, X, Y) {
    i = coq:(2);
    swap = (load1(k+coq:(1)>>coq:(3))>>(coq:(1)&coq:(7)))&coq:(1);
    stackalloc 32 as X0;
    stackalloc 32 as Y0;
    stackalloc 32 as X1;
    stackalloc 32 as Y1;
    stackalloc 32 as Z;
    stackalloc 32 as oZ;
    secp256k1_tplu(X1, Y1, X0, Y0, Z, X, Y);
    secp256k1_felem_cswap(swap, X0, X1);
    secp256k1_felem_cswap(swap, Y0, Y1);
    while (i < coq:(256)) {
      swap = (load1(k+i>>coq:(3))>>(i&coq:(7)))&coq:(1);
      secp256k1_felem_cswap(swap, X0, X1);
      secp256k1_felem_cswap(swap, Y0, Y1);
      secp256k1_zdau(X1, Y1, X0, Y0, Z);
      secp256k1_felem_cswap(swap, X0, X1);
      secp256k1_felem_cswap(swap, Y0, Y1);
      i = i+coq:(1)
    };
    stackalloc 32 as tX;
    stackalloc 32 as tY;
    secp256k1_make_co_z(tX, tY, X, Y, Z);
    secp256k1_opp(tY, tY);
    secp256k1_zaddu(X1, Y1, oX, oY, oZ, X0, Y0, tX, tY, Z);
    swap = (load1(k+coq:(0)>>coq:(3))>>(coq:(0)&coq:(7)))&coq:(1);
    secp256k1_felem_cswap(swap, oX, X1);
    secp256k1_felem_cswap(swap, oY, Y1);
    secp256k1_inv(Z, oZ);
    secp256k1_mul(oX, oX, Z);
    secp256k1_mul(oY, oY, Z)
}.

Require Import bedrock2.ToCString.
Require Import coqutil.Macros.WithBaseName.
Definition funcs :=
  List.app
  [ secp256k1_opp;
    secp256k1_mul;
    secp256k1_add;
    secp256k1_sub;
    secp256k1_square;
    secp256k1_to_bytes;
    secp256k1_from_bytes;
    secp256k1_from_mont;
    secp256k1_to_mont;
    secp256k1_select_znz]
  &[,secp256k1_make_co_z;
     secp256k1_felem_cswap;
     secp256k1_zaddu;
     secp256k1_dblu;
     secp256k1_tplu;
     secp256k1_zdau;
     secp256k1_inv;
     secp256k1_laddermul].

Compute (ToCString.c_module funcs).

