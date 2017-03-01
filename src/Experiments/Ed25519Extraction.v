Require Import Crypto.Experiments.Ed25519.
Require Import Crypto.Spec.MxDH.
Import Decidable BinNat BinInt ZArith_dec.

Extraction Language Haskell.
Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Unset Extraction AccessOpaque.

(** Eq *)

Extraction Implicit eq_rect   [ x y ].
Extraction Implicit eq_rect_r [ x y ].
Extraction Implicit eq_rec    [ x y ].
Extraction Implicit eq_rec_r  [ x y ].

Extract Inlined Constant eq_rect   => "".
Extract Inlined Constant eq_rect_r => "".
Extract Inlined Constant eq_rec    => "".
Extract Inlined Constant eq_rec_r  => "".

(** Ord *)

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].

(** Bool, sumbool, Decidable *)

Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive Bool.reflect => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inlined Constant Bool.iff_reflect => "".
Extraction Inline Crypto.Util.Decidable.Decidable Crypto.Util.Decidable.dec.

(* Extract Inlined Constant Equality.bool_beq => *)
(*   "((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)". *)
Extract Inlined Constant Bool.bool_dec     =>
  "((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)".

Extract Inlined Constant Sumbool.sumbool_of_bool => "".

Extract Inlined Constant negb => "Prelude.not".
Extract Inlined Constant orb  => "(Prelude.||)".
Extract Inlined Constant andb => "(Prelude.&&)".
Extract Inlined Constant xorb => "Data.Bits.xor".

(** Comparisons *)

Extract Inductive comparison => "Prelude.Ordering" [ "Prelude.EQ" "Prelude.LT" "Prelude.GT" ].
Extract Inductive CompareSpecT => "Prelude.Ordering" [ "Prelude.EQ" "Prelude.LT" "Prelude.GT" ].

(** Maybe *)

Extract Inductive option => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

(** Either *)

Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].

(** List *)

Extract Inductive list => "[]" ["[]" "(:)"].

Extract Inlined Constant app             => "(Prelude.++)".
Extract Inlined Constant List.map        => "Prelude.map".
Extract         Constant List.fold_left  => "\f l z -> Data.List.foldl f z l".
Extract Inlined Constant List.fold_right => "Data.List.foldr".
Extract Inlined Constant List.find       => "Data.List.find".
Extract Inlined Constant List.length     => "Data.List.genericLength".

(** Tuple *)

Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive sigT => "(,)" ["(,)"].

Extract Inlined Constant fst    => "Prelude.fst".
Extract Inlined Constant snd    => "Prelude.snd".
Extract Inlined Constant projT1 => "Prelude.fst".
Extract Inlined Constant projT2 => "Prelude.snd".

Extract Inlined Constant proj1_sig => "".

(** Unit *)

Extract Inductive unit => "()" ["()"].

(** nat *)

Require Import Crypto.Experiments.ExtrHaskellNats.

(** positive *)
Require Import BinPos.

Extract Inductive positive => "Prelude.Integer" [
  "(\x -> 2 Prelude.* x Prelude.+ 1)"
  "(\x -> 2 Prelude.* x)"
  "1" ]
  "(\fI fO fH n -> {- match_on_positive -}
                   if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))".

Extract Inlined Constant Pos.succ => "(1 Prelude.+)".
Extract Inlined Constant Pos.add => "(Prelude.+)".
Extract Inlined Constant Pos.mul => "(Prelude.*)".
Extract Inlined Constant Pos.pow => "(Prelude.^)".
Extract Inlined Constant Pos.max => "Prelude.max".
Extract Inlined Constant Pos.min => "Prelude.min".
Extract Inlined Constant Pos.gcd => "Prelude.gcd".
Extract Inlined Constant Pos.land => "(Data.Bits..&.)".
Extract Inlined Constant Pos.lor => "(Data.Bits..|.)".
Extract Inlined Constant Pos.compare => "Prelude.compare".
Extract Inlined Constant Pos.ltb => "(Prelude.<)".
Extract Inlined Constant Pos.leb => "(Prelude.<=)".
Extract Inlined Constant Pos.eq_dec => "(Prelude.==)".
Extract Inlined Constant Pos.eqb => "(Prelude.==)".

(* XXX: unsound -- overflow in fromIntegral *)
Extract Constant Pos.shiftr => "(\w n -> Data.Bits.shiftR w (Prelude.fromIntegral n))".
Extract Constant Pos.shiftl => "(\w n -> Data.Bits.shiftL w (Prelude.fromIntegral n))".
Extract Constant Pos.testbit => "(\w n -> Data.Bits.testBit w (Prelude.fromIntegral n))".

Extract Constant Pos.pred => "(\n -> Prelude.max 1 (Prelude.pred n))".
Extract Constant Pos.sub => "(\n m -> Prelude.max 1 (n Prelude.- m))".

(** N *)

Extract Inlined Constant N.succ => "(1 Prelude.+)".
Extract Inlined Constant N.add => "(Prelude.+)".
Extract Inlined Constant N.mul => "(Prelude.*)".
Extract Inlined Constant N.pow => "(Prelude.^)".
Extract Inlined Constant N.max => "Prelude.max".
Extract Inlined Constant N.min => "Prelude.min".
Extract Inlined Constant N.gcd => "Prelude.gcd".
Extract Inlined Constant N.lcm => "Prelude.lcm".
Extract Inlined Constant N.land => "(Data.Bits..&.)".
Extract Inlined Constant N.lor => "(Data.Bits..|.)".
Extract Inlined Constant N.lxor => "Data.Bits.xor".
Extract Inlined Constant N.compare => "Prelude.compare".
Extract Inlined Constant N.eq_dec => "(Prelude.==)".
Extract Inlined Constant N.ltb => "(Prelude.<)".
Extract Inlined Constant N.leb => "(Prelude.<=)".
Extract Inlined Constant N.eq_dec => "(Prelude.==)".
Extract Inlined Constant N.odd => "Prelude.odd".
Extract Inlined Constant N.even => "Prelude.even".

(* XXX: unsound -- overflow in fromIntegral *)
Extract Constant N.shiftr => "(\w n -> Data.Bits.shiftR w (Prelude.fromIntegral n))".
Extract Constant N.shiftl => "(\w n -> Data.Bits.shiftL w (Prelude.fromIntegral n))".
Extract Constant N.testbit => "(\w n -> Data.Bits.testBit w (Prelude.fromIntegral n))".
Extract Constant N.testbit_nat => "(\w n -> Data.Bits.testBit w (Prelude.fromIntegral n))".

Extract Constant N.pred => "(\n -> Prelude.max 0 (Prelude.pred n))".
Extract Constant N.sub => "(\n m -> Prelude.max 0 (n Prelude.- m))".
Extract Constant N.div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant N.modulo => "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".

Extract Inductive N => "Prelude.Integer" [ "0" "(\x -> x)" ]
  "(\fO fS n -> {- match_on_N -} if n Prelude.== 0 then fO () else fS n)".

(** Z *)
Require Import ZArith.BinInt.

Extract Inductive Z => "Prelude.Integer" [ "0" "(\x -> x)" "Prelude.negate" ]
  "(\fO fP fN n -> {- match_on_Z -}
                   if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))".

Extract Inlined Constant Z.succ => "(1 Prelude.+)".
Extract Inlined Constant Z.add => "(Prelude.+)".
Extract Inlined Constant Z.sub => "(Prelude.-)".
Extract Inlined Constant Z.opp => "Prelude.negate".
Extract Inlined Constant Z.mul => "(Prelude.*)".
Extract Inlined Constant Z.pow => "(Prelude.^)".
Extract Inlined Constant Z.pow_pos => "(Prelude.^)".
Extract Inlined Constant Z.max => "Prelude.max".
Extract Inlined Constant Z.min => "Prelude.min".
Extract Inlined Constant Z.lcm => "Prelude.lcm".
Extract Inlined Constant Z.land => "(Data.Bits..&.)".
Extract Inlined Constant Z.pred => "Prelude.pred".
Extract Inlined Constant Z.land => "(Data.Bits..&.)".
Extract Inlined Constant Z.lor => "(Data.Bits..|.)".
Extract Inlined Constant Z.lxor => "Data.Bits.xor".
Extract Inlined Constant Z.compare => "Prelude.compare".
Extract Inlined Constant Z.eq_dec => "(Prelude.==)".
Extract Inlined Constant Z_ge_lt_dec => "(Prelude.>=)".
Extract Inlined Constant Z_gt_le_dec => "(Prelude.>)".
Extract Inlined Constant Z.ltb => "(Prelude.<)".
Extract Inlined Constant Z.leb => "(Prelude.<=)".
Extract Inlined Constant Z.gtb => "(Prelude.>)".
Extract Inlined Constant Z.geb => "(Prelude.>=)".
Extract Inlined Constant Z.odd => "Prelude.odd".
Extract Inlined Constant Z.even => "Prelude.even".

(* XXX: unsound -- overflow in fromIntegral *)
Extract Constant Z.shiftr => "(\w n -> Data.Bits.shiftR w (Prelude.fromIntegral n))".
Extract Constant Z.shiftl => "(\w n -> Data.Bits.shiftL w (Prelude.fromIntegral n))".
Extract Constant Z.testbit => "(\w n -> Data.Bits.testBit w (Prelude.fromIntegral n))".

Extract Constant Z.div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant Z.modulo => "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".

(** Conversions *)

Extract Inlined Constant Z.of_N => "".
Extract Inlined Constant Z.to_N => "".
Extract Inlined Constant N.to_nat => "".
Extract Inlined Constant N.of_nat => "".
Extract Inlined Constant Z.to_nat => "".
Extract Inlined Constant Z.of_nat => "".
Extract Inlined Constant Z.abs_N => "Prelude.abs".
Extract Inlined Constant Z.abs_nat => "Prelude.abs".
Extract Inlined Constant Pos.pred_N => "Prelude.pred".
Extract Inlined Constant Pos.lxor => "Data.Bits.xor".

(** Word *)
(* do not annotate every bit of a word with the number of bits after it *)
Extraction Implicit Word.WS [ 2 ].
Extraction Implicit Word.weqb [ 1 ].
Extraction Implicit Word.whd [ 1 ].
Extraction Implicit Word.wtl [ 1 ].
Extraction Implicit Word.bitwp [ 2 ].
Extraction Implicit Word.wand [ 1 ].
Extraction Implicit Word.wor [ 1 ].
Extraction Implicit Word.wxor [ 1 ].
Extraction Implicit Word.wordToN [ 1 ].
Extraction Implicit Word.wordToNat [ 1 ].
Extraction Implicit Word.combine [ 1 3 ].
Extraction Implicit Word.split1 [ 2 ].
Extraction Implicit Word.split2 [ 2 ].
Extraction Implicit WordUtil.cast_word [1 2 3].
Extraction Implicit WordUtil.wfirstn [ 2 4 ].
Extraction Inline WordUtil.cast_word.
Extract Inductive Word.word => "[Prelude.Bool]" [ "[]" "(:)" ]
  "(\fWO fWS w -> {- match_on_word -} case w of {[] -> fWO (); (b:w') -> fWS b w' } )".

(** Let_In *)
Extraction Inline LetIn.Let_In.

(* Word64 *)
Import Crypto.Reflection.Z.Interpretations64.
Extract Inlined Constant WordW.wordW => "Data.Word.Word64".
Extract Inlined Constant GF25519BoundedCommon.word64 => "Data.Word.Word64".
Extract Inlined Constant GF25519BoundedCommon.w64eqb => "(Prelude.==)".
Extract Inlined Constant WordW.wordWToZ => "Prelude.fromIntegral".
Extract Inlined Constant WordW.ZToWordW => "Prelude.fromIntegral".
Extract Inlined Constant GF25519BoundedCommon.word64ToZ => "Prelude.fromIntegral".
Extract Inlined Constant GF25519BoundedCommon.NToWord64 => "Prelude.fromIntegral".
Extract Inlined Constant GF25519BoundedCommon.ZToWord64 => "Prelude.fromIntegral".
Extract Inlined Constant WordW.add => "(Prelude.+)".
Extract Inlined Constant WordW.mul => "(Prelude.*)".
Extract Inlined Constant WordW.sub => "(Prelude.-)".
Extract Inlined Constant WordW.land => "(Data.Bits..&.)".
Extract Inlined Constant WordW.lor => "(Data.Bits..|.)".
Extract Inlined Constant WordW.neg => "(\_ w -> Prelude.negate w)". (* FIXME: reification: drop arg1 *)
Extract Inlined Constant WordW.shr => "(\w n -> Data.Bits.shiftR w (Prelude.fromIntegral n))".
Extract Inlined Constant WordW.shl => "(\w n -> Data.Bits.shiftL w (Prelude.fromIntegral n))".
Extract Inlined Constant WordW.cmovle => "(\x y r1 r2 -> if x Prelude.<= y then r1 else r2)".
Extract Inlined Constant WordW.cmovne => "(\x y r1 r2 -> if x Prelude.== y then r1 else r2)".

(* inlining, primarily to reduce polymorphism *)
Extraction Inline dec_eq_Z dec_eq_N dec_eq_sig_hprop.
Extraction Inline Ed25519.Erep Ed25519.SRep Ed25519.ZNWord Ed25519.WordNZ.
Extraction Inline GF25519BoundedCommon.fe25519.
Extraction Inline EdDSARepChange.sign EdDSARepChange.splitSecretPrngCurve.
Extraction Inline Crypto.Util.IterAssocOp.iter_op Crypto.Util.IterAssocOp.test_and_op.
Extraction Inline CompleteEdwardsCurve.E.coordinates CompleteEdwardsCurve.E.zero.
Extraction Inline GF25519BoundedCommon.proj_word GF25519BoundedCommon.Build_bounded_word GF25519BoundedCommon.Build_bounded_word'.
Extraction Inline GF25519BoundedCommon.app_wire_digits GF25519BoundedCommon.wire_digit_bounds_exp.
Extraction Inline Crypto.Util.HList.mapt' Crypto.Util.HList.mapt Crypto.Util.Tuple.map.

Extraction Inline GF25519BoundedCommon.exist_fe25519 GF25519BoundedCommon.exist_fe25519W GF25519BoundedCommon.proj1_fe25519W.
Extraction Inline Crypto.Specific.GF25519Bounded.mulW Crypto.Specific.GF25519Bounded.addW Crypto.Specific.GF25519Bounded.subW.
(*done-at-haskell-level: Extraction Inline Crypto.Specific.GF25519Bounded.mul Crypto.Specific.GF25519Bounded.add Crypto.Specific.GF25519Bounded.sub Crypto.Specific.GF25519Bounded.inv Crypto.Specific.GF25519Bounded.sqrt. *)

Extraction Implicit Ed25519.SHA512 [ 1 ].
Extract Constant Ed25519.SHA512 =>
"let { b2i b = case b of { Prelude.True -> 1 ; Prelude.False -> 0 } } in
 let { leBitsToBytes [] = [] :: [Data.Word.Word8] ;
       leBitsToBytes (a:b:c:d:e:f:g:h:bs) = (b2i a Data.Bits..|. (b2i b `Data.Bits.shiftL` 1) Data.Bits..|. (b2i c `Data.Bits.shiftL` 2) Data.Bits..|. (b2i d `Data.Bits.shiftL` 3) Data.Bits..|. (b2i e `Data.Bits.shiftL` 4) Data.Bits..|. (b2i f `Data.Bits.shiftL` 5) Data.Bits..|. (b2i g `Data.Bits.shiftL` 6) Data.Bits..|. (b2i h `Data.Bits.shiftL` 7)) : leBitsToBytes bs ;
       leBitsToBytes bs = Prelude.error ('b':'s':'l':[]) } in
 let { bytesToLEBits [] = [] :: [Prelude.Bool] ;
       bytesToLEBits (x:xs) = (x `Data.Bits.testBit` 0) : (x `Data.Bits.testBit` 1) : (x `Data.Bits.testBit` 2) : (x `Data.Bits.testBit` 3) : (x `Data.Bits.testBit` 4) : (x `Data.Bits.testBit` 5) : (x `Data.Bits.testBit` 6) : (x `Data.Bits.testBit` 7) : bytesToLEBits xs } in
 (bytesToLEBits Prelude.. B.unpack Prelude.. SHA.bytestringDigest Prelude.. SHA.sha512 Prelude.. B.pack Prelude.. leBitsToBytes)".

Extraction Inline MxDH.ladderstep MxDH.montladder.

Extraction "src/Experiments/X25519_noimports.hs" Crypto.Experiments.Ed25519.x25519.
