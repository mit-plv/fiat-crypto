From Coq Require Import ZArith Lia.
From Coq Require Import List.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.ArithmeticCPS.Core.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Util.CPSUtil.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Import CPSBindNotations.
Local Open Scope cps_scope.

Module Associational (Import RT : Runtime).
  Section Associational.

    Definition sat_multerm_cps s (t t' : (Z * Z)) : ~> list (Z * Z) :=
      fun T k => dlet_nd xy := RT_Z.mul_split s (snd t) (snd t') in
      k [(fst t * fst t', fst xy); (fst t * fst t' * s, snd xy)].

    Definition sat_mul_cps s (p q : list (Z * Z)) : ~> list (Z * Z) :=
      fun T => flat_map_cps (fun t T => flat_map_cps (fun t' => sat_multerm_cps s t t') q) p.

    Definition sat_multerm_const_cps s (t t' : (Z * Z)) : ~> list (Z * Z) :=
      fun T k
      => if snd t =? 1
         then k [(fst t * fst t', snd t')]
         else if snd t =? -1
              then k [(fst t * fst t', - snd t')]
              else if snd t =? 0
                   then k nil
                   else dlet_nd xy := RT_Z.mul_split s (snd t) (snd t') in
          k [(fst t * fst t', fst xy); (fst t * fst t' * s, snd xy)].

    Definition sat_mul_const_cps s (p q : list (Z * Z)) : ~> list (Z * Z) :=
      fun T => flat_map_cps (fun t T => flat_map_cps (fun t' => sat_multerm_const_cps s t t') q) p.
  End Associational.
End Associational.

Module Columns (Import RT : Runtime).
  Module Import Deps.
    Module Import Positional := Positional RT.
  End Deps.
  Section Columns.
    Context (weight : nat -> Z).

    Definition eval n (x : list (list Z)) : Z := Positional.eval weight n (map sum x).

    Section Flatten.
      Section flatten_column.
        Context (fw : Z). (* maximum size of the result *)

        (* Outputs (sum, carry) *)
        Definition flatten_column_cps (digit: list Z) : ~> (Z * Z) :=
          list_rect (fun _ => ~> (Z * Z)%type) (return (0,0))
                    (fun xx tl flatten_column_tl =>
                       list_case
                         (fun _ => ~> (Z * Z)%type) (fun T k => k ((xx mod fw)%RT, (xx / fw)%RT))
                         (fun yy tl' =>
                            list_case
                              (fun _ => ~> (Z * Z)%type) (fun T k => dlet_nd x := xx in dlet_nd y := yy in k (RT_Z.add_get_carry_full fw x y))
                              (fun _ _ =>
                                 flatten_column_tl <- flatten_column_tl;
                                 fun T k => dlet_nd x := xx in
                                   dlet_nd rec1 := fst flatten_column_tl in (* recursively get the sum and carry *)
                                   dlet_nd rec2 := snd flatten_column_tl in
                                   dlet_nd sum_carry := RT_Z.add_get_carry_full fw x rec1 in (* add the new value to the sum *)
                                   dlet_nd carry' := (snd sum_carry + rec2)%RT in (* add the two carries together *)
                                   k (fst sum_carry, carry'))
                              tl')
                         tl)
                    digit.
      End flatten_column.

      Definition flatten_step_cps (digit:list Z) (acc_carry:list Z * Z) : ~> list Z * Z :=
        (sum_carry <- flatten_column_cps (weight (S (length (fst acc_carry))) / weight (length (fst acc_carry))) (snd acc_carry::digit);
           dlet_nd sum := fst sum_carry in
           dlet_nd carry := snd sum_carry in
             return (fst acc_carry ++ sum :: nil, carry)).

      Definition flatten (xs : list (list Z)) : ~> list Z * Z :=
        fun T => fold_right_cps2 (fun a b => flatten_step_cps a b) (nil,0) (rev xs).
    End Flatten.

    Section FromAssociational.
      (* nils *)
      Definition nils n : list (list Z) := repeat nil n.
      (* cons_to_nth *)
      Definition cons_to_nth i x (xs : list (list Z)) : list (list Z) :=
        ListUtil.update_nth i (fun y => cons x y) xs.

      (* from_associational *)
      Definition from_associational_cps n (p:list (Z*Z)) : ~> list (list Z) :=
        fun T => fold_right_cps2 (fun t ls T k =>
                                    let '(p1, p2) := Positional.place weight t (pred n) in
                                    dlet_nd p2 := p2 in
                           k (cons_to_nth p1 p2 ls) ) (nils n) p.
    End FromAssociational.
  End Columns.
End Columns.

Module Rows (Import RT : Runtime).
  Module Import Deps.
    Module Associational := Associational RT.
    Module Positional := Positional RT.
    Module Columns := Columns RT.
    Module Export Core.
      Module Associational := ArithmeticCPS.Core.Associational RT.
    End Core.
  End Deps.
  Section Rows.
    Context (weight : nat -> Z).
    Local Notation rows := (list (list Z)) (only parsing).
    Local Notation cols := (list (list Z)) (only parsing).

    Definition eval n (inp : rows) :=
      sum (map (Positional.eval weight n) inp).

    Section FromAssociational.
      (* extract row *)
      Definition extract_row (inp : cols) : cols * list Z := (map (fun c => tl c) inp, map (fun c => hd 0 c) inp).

      Definition max_column_size (x:cols) := fold_right (fun a b => Nat.max a b) 0%nat (map (fun c => length c) x).

      (* from_columns *)
      Definition from_columns' n start_state : cols * rows :=
        fold_right (fun _ (state : cols * rows) =>
                      let cols'_row := extract_row (fst state) in
                      (fst cols'_row, snd state ++ [snd cols'_row])
                   ) start_state (repeat 0 n).

      Definition from_columns (inp : cols) : rows := snd (from_columns' (max_column_size inp) (inp, [])).

      (* from associational *)
      Definition from_associational_cps n (p : list (Z * Z)) : ~> _ :=
        (p <- Columns.from_associational_cps weight n p; return (from_columns p)).
    End FromAssociational.

    Section Flatten.
      Local Notation fw := (fun i => weight (S i) / weight i) (only parsing).

      Section SumRows.
        Definition sum_rows'_cps start_state (row1 row2 : list Z) : ~> list Z * Z * nat :=
          fun T => fold_right_cps2 (fun next (state : list Z * Z * nat) T k =>
                        let i := snd state in
                        let low_high := fst state in
                        let low := fst low_high in
                        let high := snd low_high in
                        dlet_nd sum_carry := RT_Z.add_with_get_carry_full (fw i) high (fst next) (snd next) in
                        let low_high' := (low ++ [fst sum_carry], snd sum_carry) in
                        k (low_high', S i)) start_state (rev (combine row1 row2)).
        Definition sum_rows_cps row1 row2 : ~> _ := (sum_rows' <- sum_rows'_cps (nil, 0, 0%nat) row1 row2; return (fst sum_rows')).
      End SumRows.

      Definition flatten'_cps (start_state : list Z * Z) (inp : rows) : ~> list Z * Z :=
        fun T => fold_right_cps2 (fun next_row (state : list Z * Z)=>
                      out_carry <- sum_rows_cps (fst state) next_row;
                        return (fst out_carry, (snd state + snd out_carry)%RT)) start_state inp.

      (* In order for the output to have the right length and bounds,
         we insert rows of zeroes if there are fewer than two rows. *)
      Definition flatten_cps n (inp : rows) : ~> list Z * Z :=
        let default := Positional.zeros n in
        flatten'_cps (hd default inp, 0) (hd default (tl inp) :: tl (tl inp)).
    End Flatten.

    Section Ops.
      Definition add_cps n p q : ~> _ := flatten_cps n [p; q].

      (* TODO: Although cleaner, using Positional.negate snd inserts
      dlets which prevent add-opp=>sub transformation in partial
      evaluation. Should probably either make partial evaluation
      handle that or remove the dlet in Positional.from_associational.

      NOTE(from jgross): I think partial evaluation now handles that
      fine; we should check this. *)
      Definition sub_cps n p q : ~> _ := (_q <- fun T => map_cps2 (fun x T k => dlet y := x in k (-y)%RT) q; flatten_cps n [p; _q]).

      Definition conditional_add_cps n mask cond (p q:list Z) : ~> _ :=
        (qq <- Positional.zselect_cps mask cond q;
           add_cps n p qq).

      (* Subtract q if and only if p >= q. *)
      Definition conditional_sub_cps n (p q:list Z) : ~> _ :=
        (vc <- sub_cps n p q;
           let '(v, c) := vc in
           return (Positional.select (-c)%RT v p)).

      (* the carry will be 0 unless we underflow--we do the addition only
         in the underflow case *)
      Definition sub_then_maybe_add_cps n mask (p q r:list Z) : ~> _ :=
        (p_minus_q_c <- sub_cps n p q;
           let '(p_minus_q, c) := p_minus_q_c in
           rr <- Positional.zselect_cps mask (-c)%RT r;
             res_c' <- add_cps n p_minus_q rr;
             let '(res, c') := res_c' in
         return (res, (c' - c)%RT)).

      Definition mul_cps base n m (p q : list Z) : ~> _ :=
        let p_a := Positional.to_associational weight n p in
        let q_a := Positional.to_associational weight n q in
        (pq_a <- Associational.sat_mul_cps base p_a q_a;
           pq_a <- from_associational_cps m pq_a;
           flatten_cps m pq_a).

      (* if [s] is not exactly equal to a weight, we must adjust it to
         be a weight, so that rather than dividing by s and
         multiplying by c, we divide by w and multiply by c*(w/s).
         See
         https://github.com/mit-plv/fiat-crypto/issues/326#issuecomment-404135131
         for a bit more discussion *)
      Definition adjust_s fuel s : Z * bool :=
        fold_right
          (fun w_i res
           => let '(v, found_adjustment) := res in
              let res := (v, found_adjustment) in
              if found_adjustment:bool
              then res
              else if w_i mod s =? 0
                   then (w_i, true)
                   else res)
          (s, false)
          (map weight (List.rev (seq 0 fuel))).

      (* TODO : move sat_reduce and repeat_sat_reduce to Saturated.Associational *)
      Definition sat_reduce_cps base s c n (p : list (Z * Z)) : ~> _ :=
        let '(s', _) := adjust_s (S (S n)) s in
        let lo_hi := Associational.split s' p in
        (p <- Associational.sat_mul_const_cps base c (snd lo_hi);
           p <- Associational.sat_mul_const_cps base [(1, s'/s)] p;
         return (fst lo_hi ++ p)).

      Definition repeat_sat_reduce_cps base s c (p : list (Z * Z)) n : ~> _ :=
        fun T => fold_right_cps2 (fun _ q => sat_reduce_cps base s c n q) p (seq 0 n).

      Definition mulmod_cps base s c n nreductions (p q : list Z) : ~> _ :=
        let p_a := Positional.to_associational weight n p in
        let q_a := Positional.to_associational weight n q in
        (pq_a <- Associational.sat_mul_cps base p_a q_a;
           r_a <- repeat_sat_reduce_cps base s c pq_a nreductions;
           r_a <- from_associational_cps n r_a;
           flatten_cps n r_a).

      (* returns all-but-lowest-limb and lowest limb *)
      Definition divmod (p : list Z) : list Z * Z
        := (tl p, hd 0 p).
    End Ops.
  End Rows.
End Rows.
