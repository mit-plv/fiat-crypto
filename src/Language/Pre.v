(** Definitions for use in pre-reified rewriter rules *)
Require Import Coq.ZArith.BinInt.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Local Open Scope bool_scope.
Local Open Scope Z_scope.

Module ident.
  Definition literal {T} (v : T) := v.
  Definition eagerly {T} (v : T) := v.
  Definition gets_inlined (real_val : bool) {T} (v : T) : bool := real_val.

  Section cast.
    Context (cast_outside_of_range : zrange -> BinInt.Z -> BinInt.Z).

    Definition is_more_pos_than_neg (r : zrange) (v : BinInt.Z) : bool
      := ((Z.abs (lower r) <? Z.abs (upper r)) (* if more of the range is above 0 than below 0 *)
          || ((lower r =? upper r) && (0 <=? lower r))
          || ((Z.abs (lower r) =? Z.abs (upper r)) && (0 <=? v))).

    (** We ensure that [ident.cast] is symmetric under [Z.opp], as
            this makes some rewrite rules much, much easier to
            prove. *)
    Let cast_outside_of_range' (r : zrange) (v : BinInt.Z) : BinInt.Z
      := ((cast_outside_of_range r v - lower r) mod (upper r - lower r + 1)) + lower r.

    Definition cast (r : zrange) (x : BinInt.Z)
      := let r := ZRange.normalize r in
         if (lower r <=? x) && (x <=? upper r)
         then x
         else if is_more_pos_than_neg r x
              then cast_outside_of_range' r x
              else -cast_outside_of_range' (-r) (-x).
    Definition cast2 (r : zrange * zrange) (x : BinInt.Z * BinInt.Z)
      := (cast (Datatypes.fst r) (Datatypes.fst x),
          cast (Datatypes.snd r) (Datatypes.snd x)).
  End cast.

  Definition cast_outside_of_range (r : zrange) (v : BinInt.Z) : BinInt.Z.
  Proof. exact v. Qed.

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

  Module Thunked.
    Definition bool_rect P (t f : Datatypes.unit -> P) (b : bool) : P
      := Datatypes.bool_rect (fun _ => P) (t tt) (f tt) b.
    Definition list_rect {A} P (N : Datatypes.unit -> P) (C : A -> list A -> P -> P) (ls : list A) : P
      := Datatypes.list_rect (fun _ => P) (N tt) C ls.
    Definition list_case {A} P (N : Datatypes.unit -> P) (C : A -> list A -> P) (ls : list A) : P
      := ListUtil.list_case (fun _ => P) (N tt) C ls.
    Definition nat_rect P (O_case : unit -> P) (S_case : nat -> P -> P) (n : nat) : P
      := Datatypes.nat_rect (fun _ => P) (O_case tt) S_case n.
    Definition option_rect {A} P (S_case : A -> P) (N_case : unit -> P) (o : option A) : P
      := Datatypes.option_rect (fun _ => P) S_case (N_case tt) o.
  End Thunked.
End ident.

Global Opaque ident.cast. (* This should never be unfolded except in [Language.Wf] *)
