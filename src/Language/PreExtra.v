(** Definitions for use in pre-reified rewriter rules *)
Require Import Coq.ZArith.BinInt.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.Notations.
Require Rewriter.Util.Bool.
Require Rewriter.Util.Option.
Require Rewriter.Util.Prod.
Require Rewriter.Util.NatUtil.
Require Rewriter.Util.ListUtil.
Require Export Rewriter.Language.Pre.
Require Crypto.Util.PrimitiveHList.
Local Open Scope bool_scope.
Local Open Scope Z_scope.

Module ident.
  Section cast.
    Definition is_more_pos_than_neg (r : zrange) (v : BinInt.Z) : bool
      := ((Z.abs (lower r) <? Z.abs (upper r)) (* if more of the range is above 0 than below 0 *)
          || ((lower r =? upper r) && (0 <=? lower r))
          || ((Z.abs (lower r) =? Z.abs (upper r)) && (0 <=? v))).

    (** We ensure that [ident.cast] is symmetric under [Z.opp], as
        this makes some rewrite rules much, much easier to prove. *)
    (** XXX TODO: Come up with a good way of proving boundedness for
          the abstract interpreter, now that we no longer can even
          guarantee that we have the same behavior independent of
          overflow behavior. *)
    Let cast_outside_of_range (r : zrange) (v : BinInt.Z) : BinInt.Z
      := ((v - lower r) mod (upper r - lower r + 1)) + lower r.

    Definition cast (r : zrange) (x : BinInt.Z)
      := let r := ZRange.normalize r in
         if (lower r <=? x) && (x <=? upper r)
         then x
         else if is_more_pos_than_neg r x
              then cast_outside_of_range r x
              else -cast_outside_of_range (-r) (-x).
    Definition cast2 (r : zrange * zrange) (x : BinInt.Z * BinInt.Z)
      := (cast (Datatypes.fst r) (Datatypes.fst x),
          cast (Datatypes.snd r) (Datatypes.snd x)).
  End cast.

  Section comment.
    Definition comment {A} (x : A) := tt.
    (** Version of [comment] which does not keep its arguments alive in the final output *)
    Definition comment_no_keep {A} (x : A) := tt.
  End comment.

  Module fancy.
    Module with_wordmax.
      Section with_wordmax.
        Context (log2wordmax : BinInt.Z).
        Let wordmax := 2 ^ log2wordmax.
        Let half_bits := log2wordmax / 2.
        Let wordmax_half_bits := 2 ^ half_bits.

        Local Notation low x := (Z.land x (wordmax_half_bits - 1)).
        Local Notation high x := (x >> half_bits).
        Local Notation shift x imm := ((x << imm) mod wordmax).

        Definition add (imm : Z) : Z * Z -> Z * Z
          := fun x => Z.add_get_carry_full wordmax (fst x) (shift (snd x) imm).
        Definition addc (imm : Z) : Z * Z * Z -> Z * Z
          := fun x => Z.add_with_get_carry_full wordmax (fst (fst x)) (snd (fst x)) (shift (snd x) imm).
        Definition sub (imm : Z) : Z * Z -> Z * Z
          := fun x => Z.sub_get_borrow_full wordmax (fst x) (shift (snd x) imm).
        Definition subb (imm : Z) : Z * Z * Z -> Z * Z
          := fun x => Z.sub_with_get_borrow_full wordmax (fst (fst x)) (snd (fst x)) (shift (snd x) imm).
        Definition mulll : Z * Z -> Z
          := fun x => low (fst x) * low (snd x).
        Definition mullh : Z * Z -> Z
          := fun x => low (fst x) * high (snd x).
        Definition mulhl : Z * Z -> Z
          := fun x => high (fst x) * low (snd x).
        Definition mulhh : Z * Z -> Z
          := fun x => high (fst x) * high (snd x).
        Definition selm : Z * Z * Z -> Z
          := fun x => Z.zselect (Z.cc_m wordmax (fst (fst x))) (snd (fst x)) (snd x).
        Definition rshi (n : Z) : Z * Z -> Z
          := fun x => Z.rshi wordmax (fst x) (snd x) n.
      End with_wordmax.
    End with_wordmax.


    Definition add : (Z * Z) * (Z * Z) -> Z * Z
      := Eval cbv [with_wordmax.add] in fun x => with_wordmax.add (fst (fst x)) (snd (fst x)) (snd x).
    Definition addc : (Z * Z) * (Z * Z * Z) -> Z * Z
      := Eval cbv [with_wordmax.addc] in fun x => with_wordmax.addc (fst (fst x)) (snd (fst x)) (snd x).
    Definition sub : (Z * Z) * (Z * Z) -> Z * Z
      := Eval cbv [with_wordmax.sub] in fun x => with_wordmax.sub (fst (fst x)) (snd (fst x)) (snd x).
    Definition subb : (Z * Z) * (Z * Z * Z) -> Z * Z
      := Eval cbv [with_wordmax.subb] in fun x => with_wordmax.subb (fst (fst x)) (snd (fst x)) (snd x).
    Definition mulll : Z * (Z * Z) -> Z
      := Eval cbv [with_wordmax.mulll] in fun x => with_wordmax.mulll (fst x) (snd x).
    Definition mullh : Z * (Z * Z) -> Z
      := Eval cbv [with_wordmax.mullh] in fun x => with_wordmax.mullh (fst x) (snd x).
    Definition mulhl : Z * (Z * Z) -> Z
      := Eval cbv [with_wordmax.mulhl] in fun x => with_wordmax.mulhl (fst x) (snd x).
    Definition mulhh : Z * (Z * Z) -> Z
      := Eval cbv [with_wordmax.mulhh] in fun x => with_wordmax.mulhh (fst x) (snd x).
    Definition selm : Z * (Z * Z * Z) -> Z
      := Eval cbv [with_wordmax.selm] in fun x => with_wordmax.selm (fst x) (snd x).
    Definition rshi : (Z * Z) * (Z * Z) -> Z
      := Eval cbv [with_wordmax.rshi] in fun x => with_wordmax.rshi (fst (fst x)) (snd (fst x)) (snd x).

    Definition selc : Z * Z * Z -> Z
      := fun x => Z.zselect (fst (fst x)) (snd (fst x)) (snd x).
    Definition sell : Z * Z * Z -> Z
      := fun x => Z.zselect (Z.land (fst (fst x)) 1) (snd (fst x)) (snd x).
    Definition addm : Z * Z * Z -> Z
      := fun x => Z.add_modulo (fst (fst x)) (snd (fst x)) (snd x).

    Declare Reduction cbv_fancy := cbv [ident.fancy.add ident.fancy.addc ident.fancy.addm ident.fancy.mulhh ident.fancy.mulhl ident.fancy.mullh ident.fancy.mulll ident.fancy.rshi ident.fancy.selc ident.fancy.sell ident.fancy.selm ident.fancy.sub ident.fancy.subb].
    Ltac cbv_fancy := cbv [ident.fancy.add ident.fancy.addc ident.fancy.addm ident.fancy.mulhh ident.fancy.mulhl ident.fancy.mullh ident.fancy.mulll ident.fancy.rshi ident.fancy.selc ident.fancy.sell ident.fancy.selm ident.fancy.sub ident.fancy.subb].
    Ltac cbv_fancy_in_all := cbv [ident.fancy.add ident.fancy.addc ident.fancy.addm ident.fancy.mulhh ident.fancy.mulhl ident.fancy.mullh ident.fancy.mulll ident.fancy.rshi ident.fancy.selc ident.fancy.sell ident.fancy.selm ident.fancy.sub ident.fancy.subb] in *.
  End fancy.
End ident.

Global Opaque ident.cast. (* This should never be unfolded except in [Language.Wf] *)
Global Opaque ident.comment.
Global Opaque ident.comment_no_keep.

Notation prod_rect_nodep := Rewriter.Util.Prod.prod_rect_nodep (only parsing).
Notation nat_rect_arrow_nodep := Rewriter.Util.NatUtil.nat_rect_arrow_nodep (only parsing).
Notation list_rect_arrow_nodep := Rewriter.Util.ListUtil.list_rect_arrow_nodep (only parsing).
Notation bool_rect_nodep := Rewriter.Util.Bool.bool_rect_nodep (only parsing).

Module Thunked.
  Notation bool_rect := Rewriter.Util.Bool.Thunked.bool_rect (only parsing).
  Notation list_rect := Rewriter.Util.ListUtil.Thunked.list_rect (only parsing).
  Notation list_case := Rewriter.Util.ListUtil.Thunked.list_case (only parsing).
  Notation nat_rect := Rewriter.Util.NatUtil.Thunked.nat_rect (only parsing).
  Notation option_rect := Rewriter.Util.Option.Thunked.option_rect (only parsing).
End Thunked.
