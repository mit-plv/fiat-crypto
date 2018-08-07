Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.UnderLets.
Import ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Module Compilers.
  Export Language.Compilers.
  Export UnderLets.Compilers.
  Import invert_expr.

  Module ZRange.
    Module type.
      Local Notation binterp := base.interp.
      Local Notation tinterp_gen := type.interp.
      Local Notation einterp := (type.interp base.interp).
      Module base.
        (** turn a [base.type] into a [Set] describing the type of
          bounds on that primitive; Z is a range, nat and bool are exact values *)
        Fixpoint interp (t : base.type) : Set
          := match t with
             | base.type.Z => zrange
             | base.type.unit as t
             | base.type.nat as t
             | base.type.bool as t
               => base.interp t
             | base.type.prod A B => interp A * interp B
             | base.type.list A => list (interp A)
             end%type.
        Definition is_neg {t} : interp t -> bool
          := match t with
             | base.type.Z => fun r => (lower r <? 0) && (upper r <=? 0)
             | _ => fun _ => false
             end.
        Fixpoint is_tighter_than {t} : interp t -> interp t -> bool
          := match t with
             | base.type.Z => is_tighter_than_bool
             | base.type.nat => Nat.eqb
             | base.type.unit => fun _ _ => true
             | base.type.bool => bool_eq
             | base.type.prod A B
               => fun '(a, b) '(a', b')
                  => @is_tighter_than A a a' && @is_tighter_than B b b'
             | base.type.list A
               => fold_andb_map (@is_tighter_than A)
             end%bool.
        Fixpoint is_bounded_by {t} : interp t -> binterp t -> bool
          := match t with
             | base.type.Z => fun r z => (lower r <=? z) && (z <=? upper r)
             | base.type.nat => Nat.eqb
             | base.type.unit => fun _ _ => true
             | base.type.bool => bool_eq
             | base.type.prod A B
               => fun '(a, b) '(a', b')
                  => @is_bounded_by A a a' && @is_bounded_by B b b'
             | base.type.list A
               => fold_andb_map (@is_bounded_by A)
             end.
        Module option.
          (** turn a [base.type] into a [Set] describing the type
              of optional bounds on that primitive; bounds on a [Z]
              may be either a range, or [None], generally indicating
              that the [Z] is unbounded. *)
          Fixpoint interp (t : base.type) : Set
            := match t with
               | base.type.Z => option zrange
               | base.type.unit => unit
               | base.type.nat as t
               | base.type.bool as t
                 => option (base.interp t)
               | base.type.prod A B => interp A * interp B
               | base.type.list A => option (list (interp A))
               end%type.
          Fixpoint None {t} : interp t
            := match t with
               | base.type.unit => tt
               | base.type.list _
               | base.type.Z
               | base.type.nat
               | base.type.bool
                 => Datatypes.None
               | base.type.prod A B
                 => (@None A, @None B)
               end.
          Fixpoint Some {t} : base.interp t -> interp t
            := match t with
               | base.type.Z
               | base.type.nat
               | base.type.bool
                 => Datatypes.Some
               | base.type.list A
                 => fun ls => Datatypes.Some (List.map (@Some A) ls)
               | base.type.prod A B
                 => fun '(a, b)
                    => (@Some A a, @Some B b)
               | _ => fun _ => tt
               end.
          Fixpoint lift_Some {t} : interp t -> option (base.interp t)
            := match t with
               | base.type.Z
               | base.type.nat
               | base.type.bool
                 => fun x => x
               | base.type.unit
                 => fun x => Datatypes.Some tt
               | base.type.list A
                 => fun ls => ls <- ls; ls <-- List.map (@lift_Some A) ls; Datatypes.Some ls
               | base.type.prod A B
                 => fun '(a, b) => a <- @lift_Some A a; b <- @lift_Some B b; Datatypes.Some (a, b)
               end%option.
          (** Keep data about list length and nat value, but not zrange *)
          Fixpoint strip_ranges {t} : interp t -> interp t
            := match t with
               | base.type.Z => fun _ => Datatypes.None
               | base.type.nat
               | base.type.bool
               | base.type.unit
                 => fun x => x
               | base.type.list A
                 => fun ls => ls <- ls; Datatypes.Some (List.map (@strip_ranges A) ls)
               | base.type.prod A B
                 => fun '(a, b)
                    => (@strip_ranges A a, @strip_ranges B b)
               end%option.
          Definition is_neg {t} : interp t -> bool
            := match t with
               | base.type.Z
                 => fun v => match v with
                             | Datatypes.Some v => @is_neg base.type.Z v
                             | Datatypes.None => false
                             end
               | t => fun _ => false
               end.
          Fixpoint is_tighter_than {t} : interp t -> interp t -> bool
            := match t with
               | base.type.Z as t
               | base.type.nat as t
               | base.type.bool as t
                 => fun r1 r2
                    => match r1, r2 with
                       | _, Datatypes.None => true
                       | Datatypes.None, Datatypes.Some _ => false
                       | Datatypes.Some r1, Datatypes.Some r2 => base.is_tighter_than (t:=t) r1 r2
                       end
               | base.type.prod A B
                 => fun '(a, b) '(a', b')
                    => @is_tighter_than A a a' && @is_tighter_than B b b'
               | base.type.list A
                 => fun ls1 ls2
                    => match ls1, ls2 with
                       | Datatypes.None, Datatypes.None => true
                       | Datatypes.Some _, Datatypes.None => true
                       | Datatypes.None, Datatypes.Some _ => false
                       | Datatypes.Some ls1, Datatypes.Some ls2 => fold_andb_map (@is_tighter_than A) ls1 ls2
                       end
               | _ => fun 'tt 'tt => true
               end.
          Fixpoint is_bounded_by {t} : interp t -> binterp t -> bool
            := match t with
               | base.type.Z as t
               | base.type.nat as t
               | base.type.bool as t
                 => fun r
                    => match r with
                       | Datatypes.Some r => @base.is_bounded_by t r
                       | Datatypes.None => fun _ => true
                       end
               | base.type.prod A B
                 => fun '(a, b) '(a', b')
                    => @is_bounded_by A a a' && @is_bounded_by B b b'
               | base.type.list A
                 => fun ls1 ls2
                    => match ls1 with
                       | Datatypes.None => true
                       | Datatypes.Some ls1 => fold_andb_map (@is_bounded_by A) ls1 ls2
                       end
               | _ => fun 'tt _ => true
               end.

          Lemma is_bounded_by_Some {t} r val
            : is_bounded_by (@Some t r) val = base.is_bounded_by r val.
          Proof.
            induction t;
              repeat first [ reflexivity
                           | progress cbn in *
                           | progress destruct_head'_prod
                           | progress destruct_head' base.type.base
                           | rewrite fold_andb_map_map1
                           | match goal with H : _ |- _ => rewrite H end
                           | match goal with H : _ |- _ => setoid_rewrite H end ].
          Qed.

          Lemma is_tighter_than_is_bounded_by {t} r1 r2 val
                (Htight : @is_tighter_than t r1 r2 = true)
                (Hbounds : is_bounded_by r1 val = true)
            : is_bounded_by r2 val = true.
          Proof.
            induction t;
              repeat first [ progress destruct_head'_prod
                           | progress destruct_head'_and
                           | progress destruct_head'_unit
                           | progress cbn in *
                           | progress destruct_head' option
                           | solve [ eauto with nocore ]
                           | progress cbv [is_tighter_than_bool] in *
                           | progress rewrite ?Bool.andb_true_iff in *
                           | discriminate
                           | apply conj
                           | Z.ltb_to_lt; omega
                           | progress break_innermost_match_hyps
                           | progress subst
                           | rewrite NPeano.Nat.eqb_refl
                           | reflexivity
                           | match goal with
                             | [ H : Nat.eqb _ _ = true |- _ ] => apply beq_nat_true in H
                             | [ H : bool_eq _ _ = true |- _ ] => apply bool_eq_ok in H
                             | [ |- bool_eq ?x ?x = true ] => destruct x; reflexivity
                             end ].
            { lazymatch goal with
              | [ r1 : list (interp t), r2 : list (interp t), val : list (binterp t) |- _ ]
                => revert r1 r2 val Htight Hbounds IHt
              end; intros r1 r2 val; revert r1 r2 val.
              induction r1, r2, val; cbn; auto with nocore; try congruence; [].
              rewrite !Bool.andb_true_iff; intros; destruct_head'_and; split; eauto with nocore. }
          Qed.

          Lemma is_tighter_than_Some_is_bounded_by {t} r1 r2 val
                (Htight : @is_tighter_than t r1 (Some r2) = true)
                (Hbounds : is_bounded_by r1 val = true)
            : base.is_bounded_by r2 val = true.
          Proof.
            rewrite <- is_bounded_by_Some.
            eapply is_tighter_than_is_bounded_by; eassumption.
          Qed.
        End option.
      End base.

      (** turn a [type] into a [Set] describing the type of bounds on
          that type; this lifts [base.interp] from
          [type.base] to [type] *)
      Definition interp (t : type base.type)
        := type.interp base.interp t.
      Fixpoint is_tighter_than {t} : interp t -> interp t -> bool
        := match t with
           | type.base x => @base.is_tighter_than x
           | type.arrow s d => fun _ _ => false
           end.
      Fixpoint is_bounded_by {t} : interp t -> einterp t -> bool
        := match t return interp t -> einterp t -> bool with
           | type.base x => @base.is_bounded_by x
           | type.arrow s d => fun _ _ => false
           end.
      Module option.
        (** turn a [type] into a [Set] describing the type of optional
            bounds on that base type; bounds on a [Z] may be either a
            range, or [None], generally indicating that the [Z] is
            unbounded.  This lifts [base.option.interp] from
            [base.type] to [type] *)
        Definition interp (t : type base.type)
          := tinterp_gen base.option.interp t.
        Fixpoint None {t : type base.type} : interp t
          := match t with
             | type.base x => @base.option.None x
             | type.arrow s d => fun _ => @None d
             end.
        Fixpoint Some {t : type base.type} : type.interp t -> interp t
          := match t with
             | type.base x => @base.option.Some x
             | type.arrow s d => fun _ _ => @None d
             end.
        Fixpoint strip_ranges {t : type base.type} : interp t -> interp t
          := match t with
             | type.base x => @base.option.strip_ranges x
             | type.arrow s d => fun f x => @strip_ranges d (f x)
             end.
        Fixpoint is_tighter_than {t} : interp t -> interp t -> bool
          := match t with
             | type.base x => @base.option.is_tighter_than x
             | type.arrow s d => fun _ _ => false
             end.
        Fixpoint is_bounded_by {t} : interp t -> einterp t -> bool
          := match t with
             | type.base x => @base.option.is_bounded_by x
             | type.arrow s d => fun _ _ => false
             end.

        Lemma is_bounded_by_Some {t} r val
          : is_bounded_by (@Some t r) val = type.is_bounded_by r val.
        Proof.
          induction t; [ apply base.option.is_bounded_by_Some | reflexivity ].
        Qed.

        Lemma is_tighter_than_is_bounded_by {t} r1 r2 val
              (Htight : @is_tighter_than t r1 r2 = true)
              (Hbounds : is_bounded_by r1 val = true)
          : is_bounded_by r2 val = true.
        Proof.
          induction t; cbn in *;
            eauto using base.option.is_tighter_than_is_bounded_by.
        Qed.

        Lemma is_tighter_than_Some_is_bounded_by {t} r1 r2 val
              (Htight : @is_tighter_than t r1 (Some r2) = true)
              (Hbounds : is_bounded_by r1 val = true)
          : type.is_bounded_by r2 val = true.
        Proof.
          rewrite <- is_bounded_by_Some.
          eapply is_tighter_than_is_bounded_by; eassumption.
        Qed.
      End option.
    End type.

    Module ident.
      Module option.
        Local Open Scope zrange_scope.

        Fixpoint of_literal {t} : base.interp t -> type.base.option.interp t
          := match t with
             | base.type.Z => fun z => Some r[z~>z]%zrange
             | base.type.nat
             | base.type.bool
               => fun n => Some n
             | base.type.unit
               => fun _ => tt
             | base.type.prod A B
               => fun '(a, b) => (@of_literal A a, @of_literal B b)
             | base.type.list A
               => fun ls => Some (List.map (@of_literal A) ls)
             end.
        Fixpoint to_literal {t} : type.base.option.interp t -> option (base.interp t)
          := match t with
             | base.type.Z => fun r => r <- r; if r.(lower) =? r.(upper) then Some r.(lower) else None
             | base.type.nat
             | base.type.bool
               => fun v => v
             | base.type.unit
               => fun _ => Some tt
             | base.type.prod A B
               => fun '(a, b) => a <- @to_literal A a; b <- @to_literal B b; Some (a, b)
             | base.type.list A
               => fun ls => ls <- ls; fold_right (fun x xs => x <- x; xs <- xs; Some (x :: xs))
                                                 (Some nil)
                                                 (List.map (@to_literal A) ls)
             end%option%Z.
        Local Notation rSome v
          := (ZRange.type.base.option.Some (t:=base.reify_norm_type_of v) v)
               (only parsing).
        (** do bounds analysis on identifiers; take in optional bounds
            on arguments, return optional bounds on outputs. *)
        Definition interp {t} (idc : ident t) : type.option.interp t
          := match idc in ident.ident t return type.option.interp t with
             | ident.Literal _ v => of_literal v
             | ident.Nat_succ as idc
             | ident.Nat_pred as idc
               => option_map (ident.interp idc)
             | ident.Z_of_nat as idc
               => option_map (fun n => r[Z.of_nat n~>Z.of_nat n]%zrange)
             | ident.Z_to_nat as idc
               => fun v => v <- to_literal v; Some (ident.interp idc v)
             | ident.List_length _
               => option_map (@List.length _)
             | ident.Nat_max as idc
             | ident.Nat_mul as idc
             | ident.Nat_add as idc
             | ident.Nat_sub as idc
             | ident.List_seq as idc
               => fun x y => x <- x; y <- y; rSome (ident.interp idc x y)
             | ident.List_repeat _
               => fun x y => y <- y; Some (repeat x y)
             | ident.List_firstn _
               => fun n ls => n <- n; ls <- ls; Some (firstn n ls)
             | ident.List_skipn _
               => fun n ls => n <- n; ls <- ls; Some (skipn n ls)
             | ident.List_combine _ _
               => fun x y => x <- x; y <- y; Some (List.combine x y)
             | ident.List_flat_map _ _
               => fun f ls
                 => (ls <- ls;
                      let fls := List.map f ls in
                      List.fold_right
                        (fun ls1 ls2 => ls1 <- ls1; ls2 <- ls2; Some (ls1 ++ ls2))
                        (Some nil)
                        fls)
             | ident.List_partition _
               => fun f ls
                 => match ls with
                   | Some ls
                     => list_rect
                         _
                         (Some nil, Some nil)
                         (fun x tl partition_tl
                          => let '(g, d) := partition_tl in
                            ((fx <- f x;
                                if fx then (g <- g; Some (x::g)) else g),
                             (fx <- f x;
                                if fx then d else (d <- d; Some (x::d)))))
                         ls
                   | None => (None, None)
                   end
             | ident.Z_eqb as idc
             | ident.Z_leb as idc
             | ident.Z_geb as idc
             | ident.Z_pow as idc
             | ident.Z_modulo as idc
               => fun x y => match to_literal x, to_literal y with
                             | Some x, Some y => of_literal (ident.interp idc x y)
                             | _, _ => ZRange.type.base.option.None
                             end
             | ident.Z_bneg as idc
               => fun x => match to_literal x with
                           | Some x => of_literal (ident.interp idc x)
                           | None => Datatypes.Some r[0~>1]
                           end
             | ident.Z_lnot_modulo as idc
               => fun v m
                 => match to_literal m, to_literal v with
                   | Some m, Some v => of_literal (ident.interp idc v m)
                   | Some m, None => Some r[0 ~> m]
                   | _, _ => None
                   end
             | ident.bool_rect _
               => fun t f b
                 => match b with
                   | Some b => if b then t tt else f tt
                   | None => ZRange.type.base.option.None
                   end
             | ident.nat_rect _
               => fun O_case S_case n
                 => match n with
                   | Some n
                     => nat_rect
                         _
                         (O_case tt)
                         (fun n' rec => S_case (Some n') rec)
                         n
                   | None => ZRange.type.base.option.None
                   end
             | ident.nat_rect_arrow _ _
               => fun O_case S_case n v
                 => match n with
                   | Some n
                     => nat_rect
                         _
                         O_case
                         (fun n' rec => S_case (Some n') rec)
                         n
                         v
                   | None => ZRange.type.base.option.None
                   end
             | ident.list_rect _ _
               => fun N C ls
                 => match ls with
                   | Some ls
                     => list_rect
                         _
                         (N tt)
                         (fun x xs rec => C x (Some xs) rec)
                         ls
                   | None => ZRange.type.base.option.None
                   end
             | ident.list_case _ _
               => fun N C ls
                 => match ls with
                   | Some ls
                     => list_case
                         _
                         (N tt)
                         (fun x xs => C x (Some xs))
                         ls
                   | None => ZRange.type.base.option.None
                   end
             | ident.List_fold_right _ _
               => fun f v ls
                 => match ls with
                   | Some ls
                     => fold_right f v ls
                   | None => ZRange.type.base.option.None
                   end
             | ident.List_nth_default _
               => fun d ls n
                 => match ls, n with
                   | Some ls, Some n
                     => nth_default d ls n
                   | _, _ => ZRange.type.base.option.None
                   end
             | ident.List_update_nth _
               => fun n f ls => ls <- ls; n <- n; Some (update_nth n f ls)
             | ident.nil t => Some nil
             | ident.cons t => fun x => option_map (cons x)
             | ident.pair A B => pair
             | ident.fst A B => fst
             | ident.snd A B => snd
             | ident.prod_rect A B P => fun f '(a, b) => f a b
             | ident.List_map _ _
               => fun f ls => ls <- ls; Some (List.map f ls)
             | ident.List_app _
               => fun ls1 ls2 => ls1 <- ls1; ls2 <- ls2; Some (List.app ls1 ls2)
             | ident.List_rev _ => option_map (@List.rev _)
             | ident.Z_opp as idc
             | ident.Z_log2 as idc
             | ident.Z_log2_up as idc
               => fun x => x <- x; Some (ZRange.two_corners (ident.interp idc) x)
             | ident.Z_add as idc
             | ident.Z_mul as idc
             | ident.Z_sub as idc
             | ident.Z_div as idc
             | ident.Z_shiftr as idc
             | ident.Z_shiftl as idc
               => fun x y => x <- x; y <- y; Some (ZRange.four_corners (ident.interp idc) x y)
             | ident.Z_add_with_carry as idc
               => fun x y z => x <- x; y <- y; z <- z; Some (ZRange.eight_corners (ident.interp idc) x y z)
             | ident.Z_cc_m as idc
               => fun s x => s <- to_literal s; x <- x; Some (ZRange.two_corners (ident.interp idc s) x)
             | ident.Z_rshi as idc
               => fun s x y offset
                 => s <- to_literal s; x <- x; y <- y; offset <- to_literal offset;
                     Some (ZRange.four_corners (fun x' y' => ident.interp idc s x' y' offset) x y)
             | ident.Z_land
               => fun x y => x <- x; y <- y; Some (ZRange.land_bounds x y)
             | ident.Z_lor
               => fun x y => x <- x; y <- y; Some (ZRange.lor_bounds x y)
             | ident.Z_mul_split
               => fun split_at x y
                 => match to_literal split_at, x, y with
                   | Some split_at, Some x, Some y
                     => ZRange.type.base.option.Some
                         (t:=base.type.Z*base.type.Z)
                         (ZRange.split_bounds (ZRange.four_corners Z.mul x y) split_at)
                   | _, _, _ => ZRange.type.base.option.None
                   end
             | ident.Z_add_get_carry
               => fun split_at x y
                 => match to_literal split_at, x, y with
                   | Some split_at, Some x, Some y
                     => ZRange.type.base.option.Some
                         (t:=base.type.Z*base.type.Z)
                         (ZRange.split_bounds (ZRange.four_corners Z.add x y) split_at)
                   | _, _, _ => ZRange.type.base.option.None
                   end
             | ident.Z_add_with_get_carry
               => fun split_at x y z
                 => match to_literal split_at, x, y, z with
                   | Some split_at, Some x, Some y, Some z
                     => ZRange.type.base.option.Some
                         (t:=base.type.Z*base.type.Z)
                         (ZRange.split_bounds
                            (ZRange.eight_corners (fun x y z => (x + y + z)%Z) x y z)
                            split_at)
                   | _, _, _, _ => ZRange.type.base.option.None
                   end
             | ident.Z_sub_get_borrow
               => fun split_at x y
                 => match to_literal split_at, x, y with
                   | Some split_at, Some x, Some y
                     => ZRange.type.base.option.Some
                         (t:=base.type.Z*base.type.Z)
                         (let b := ZRange.split_bounds (ZRange.four_corners BinInt.Z.sub x y) split_at in
                          (* N.B. sub_get_borrow returns - ((x - y) / split_at) as the borrow, so we need to negate *)
                          (fst b, ZRange.opp (snd b)))
                   | _, _, _ => ZRange.type.base.option.None
                   end
             | ident.Z_sub_with_get_borrow
               => fun split_at x y z
                 => match to_literal split_at, x, y, z with
                   | Some split_at, Some x, Some y, Some z
                     => ZRange.type.base.option.Some
                         (t:=base.type.Z*base.type.Z)
                         (let b := ZRange.split_bounds (ZRange.eight_corners (fun x y z => (y - z - x)%Z) x y z) split_at in
                          (* N.B. sub_get_borrow returns - ((x - y) / split_at) as the borrow, so we need to negate *)
                          (fst b, ZRange.opp (snd b)))
                   | _, _, _, _ => ZRange.type.base.option.None
                   end
             | ident.Z_zselect
               => fun _ y z => y <- y; z <- z; Some (ZRange.union y z)
             | ident.Z_add_modulo
               => fun x y m
                 => (x <- x;
                      y <- y;
                      m <- m;
                      Some (ZRange.union
                              (ZRange.four_corners Z.add x y)
                              (ZRange.eight_corners (fun x y m => Z.max 0 (x + y - m))
                                                    x y m)))
             | ident.Z_cast range
               => fun r : option zrange
                 => Some match r with
                        | Some r => ZRange.intersection r range
                        | None => range
                        end
             | ident.Z_cast2 (r1, r2)
               => fun '((r1', r2') : option zrange * option zrange)
                 => (Some match r1' with
                         | Some r => ZRange.intersection r r1
                         | None => r1
                         end,
                    Some match r2' with
                         | Some r => ZRange.intersection r r2
                         | None => r2
                         end)
             (** TODO(jadep): fill in fancy bounds analysis rules *)
             | ident.fancy_add log2wordmax _
             | ident.fancy_sub log2wordmax _
               => let wordmax := 2^log2wordmax in
                  let r := r[0~>wordmax-1] in
                  fun args
                  => if ZRange.type.base.option.is_tighter_than args (Some r, Some r)
                     then (Some r, Some r[0~>1])
                     else ZRange.type.base.option.None
             | ident.fancy_addc log2wordmax _
             | ident.fancy_subb log2wordmax _
               => let wordmax := 2^log2wordmax in
                  let r := r[0~>wordmax-1] in
                  fun args
                  => if ZRange.type.base.option.is_tighter_than args (Some r, Some r, Some r)
                     then (Some r, Some r[0~>1])
                     else ZRange.type.base.option.None
             | ident.fancy_mulll log2wordmax
             | ident.fancy_mullh log2wordmax
             | ident.fancy_mulhl log2wordmax
             | ident.fancy_mulhh log2wordmax
               => let wordmax := 2^log2wordmax in
                  let r := r[0~>wordmax-1] in
                  fun args
                  => if ZRange.type.base.option.is_tighter_than args (Some r, Some r)
                     then Some r
                     else ZRange.type.base.option.None
             | ident.fancy_rshi _ _ as idc
               => fun '(x, y) => x <- x; y <- y; Some (ZRange.four_corners (fun x y => ident.interp idc (x, y)) x y)
             | ident.fancy_selm _
             | ident.fancy_selc
             | ident.fancy_sell
               => fun '(_, y, z) => y <- y; z <- z; Some (ZRange.union y z)
             | ident.fancy_addm
               => fun '(x, y, m)
                  => (x <- x;
                        y <- y;
                        m <- m;
                        Some (ZRange.union
                                (ZRange.four_corners Z.add x y)
                                (ZRange.eight_corners (fun x y m => Z.max 0 (x + y - m))
                                                      x y m)))
             end%option.
      End option.
    End ident.
  End ZRange.

  (** XXX TODO: Do we still need to do UnderLets here? *)
  Module partial.
    Import UnderLets.
    Section with_var.
      Context {base_type : Type}.
      Local Notation type := (type base_type).
      Let type_base (x : base_type) : type := type.base x.
      Local Coercion type_base : base_type >-> type.
      Context {ident : type -> Type}
              {var : type -> Type}.
      Local Notation expr := (@expr base_type ident).
      Local Notation UnderLets := (@UnderLets base_type ident var).
      Context (abstract_domain' : base_type -> Type)
              (annotate : forall (is_let_bound : bool) t, abstract_domain' t -> @expr var t -> UnderLets (@expr var t))
              (bottom' : forall A, abstract_domain' A)
              (abstract_interp_ident : forall t, ident t -> type.interp abstract_domain' t).

      Definition abstract_domain (t : type)
        := type.interp abstract_domain' t.

      Fixpoint value (t : type)
        := (abstract_domain t
            * match t return Type (* COQBUG(https://github.com/coq/coq/issues/7727) *) with
              | type.base t
                => @expr var t
              | type.arrow s d
                => value s -> UnderLets (value d)
              end)%type.

      Definition value_with_lets (t : type)
        := UnderLets (value t).

      Context (interp_ident : forall t, ident t -> value_with_lets t).

      Fixpoint bottom {t} : abstract_domain t
        := match t with
           | type.base t => bottom' t
           | type.arrow s d => fun _ => @bottom d
           end.

      Fixpoint bottom_for_each_lhs_of_arrow {t} : type.for_each_lhs_of_arrow abstract_domain t
        := match t return type.for_each_lhs_of_arrow abstract_domain t with
           | type.base t => tt
           | type.arrow s d => (bottom, @bottom_for_each_lhs_of_arrow d)
           end.

      Definition state_of_value {t} : value t -> abstract_domain t
        := match t return value t -> abstract_domain t with
           | type.base t => fun '(st, v) => st
           | type.arrow s d => fun '(st, v) => st
           end.

      Fixpoint reify (is_let_bound : bool) {t} : value t -> type.for_each_lhs_of_arrow abstract_domain t -> UnderLets (@expr var t)
        := match t return value t -> type.for_each_lhs_of_arrow abstract_domain t -> UnderLets (@expr var t) with
           | type.base t
             => fun '(st, v) 'tt
                => annotate is_let_bound t st v
           | type.arrow s d
             => fun '(f_st, f_e) '(sv, dv)
                => Base
                     (λ x , (UnderLets.to_expr
                               (fx <-- f_e (@reflect _ (expr.Var x) sv);
                                  @reify false _ fx dv)))
           end%core%expr
      with reflect {t} : @expr var t -> abstract_domain t -> value t
           := match t return @expr var t -> abstract_domain t -> value t with
              | type.base t
                => fun e st => (st, e)
              | type.arrow s d
                => fun e absf
                   => (absf,
                       (fun v
                        => let stv := state_of_value v in
                           (rv <-- (@reify false s v bottom_for_each_lhs_of_arrow);
                              Base (@reflect d (e @ rv) (absf stv))%expr)))
              end%under_lets.

      (* N.B. Because the [App] case only looks at the second argument
              of arrow-values, we are free to set the state of [Abs]
              nodes to [bottom], because for any [Abs] nodes which are
              actually applied (here and in places where we don't
              rewrite), we just drop it. *)
      Fixpoint interp {t} (e : @expr value_with_lets t) : value_with_lets t
        := match e in expr.expr t return value_with_lets t with
           | expr.Ident t idc => interp_ident _ idc (* Base (reflect (###idc) (abstract_interp_ident _ idc))*)
           | expr.Var t v => v
           | expr.Abs s d f => Base (bottom, fun x => @interp d (f (Base x)))
           | expr.App s d f x
             => (x' <-- @interp s x;
                   f' <-- @interp (s -> d)%etype f;
                   snd f' x')
           | expr.LetIn (type.arrow _ _) B x f
             => (x' <-- @interp _ x;
                   @interp _ (f (Base x')))
           | expr.LetIn (type.base A) B x f
             => (x' <-- @interp _ x;
                   x'' <-- reify true (* this forces a let-binder here *) x' tt;
                   @interp _ (f (Base (reflect x'' (state_of_value x')))))
           end%under_lets.

      Definition eval_with_bound' {t} (e : @expr value_with_lets t)
                 (st : type.for_each_lhs_of_arrow abstract_domain t)
        : expr t
        := UnderLets.to_expr (e' <-- interp e; reify false e' st).

      Definition eval' {t} (e : @expr value_with_lets t) : expr t
        := eval_with_bound' e bottom_for_each_lhs_of_arrow.

      Definition eta_expand_with_bound' {t} (e : @expr var t)
                 (st : type.for_each_lhs_of_arrow abstract_domain t)
        : expr t
        := UnderLets.to_expr (reify false (reflect e bottom) st).

      Section extract.
        Context (ident_extract : forall t, ident t -> abstract_domain t).

        Definition extract' {t} (e : @expr abstract_domain t) : abstract_domain t
          := expr.interp (@ident_extract) e.

        Definition extract_gen {t} (e : @expr abstract_domain t) (bound : type.for_each_lhs_of_arrow abstract_domain t)
          : abstract_domain' (type.final_codomain t)
          := type.app_curried (extract' e) bound.
      End extract.
    End with_var.

    Module ident.
      Section with_var.
        Local Notation type := (type base.type).
        Let type_base (x : base.type) : type := type.base x.
        Local Coercion type_base : base.type >-> type.
        Context {var : type -> Type}.
        Local Notation expr := (@expr base.type ident).
        Local Notation UnderLets := (@UnderLets base.type ident var).
        Context (abstract_domain' : base.type -> Type).
        Local Notation abstract_domain := (@abstract_domain base.type abstract_domain').
        Context (annotate_ident : forall t, abstract_domain' t -> option (ident (t -> t)))
                (bottom' : forall A, abstract_domain' A)
                (abstract_interp_ident : forall t, ident t -> type.interp abstract_domain' t)
                (update_literal_with_state : forall A : base.type.base, abstract_domain' A -> base.interp A -> base.interp A)
                (extract_list_state : forall A, abstract_domain' (base.type.list A) -> option (list (abstract_domain' A)))
                (is_annotation : forall t, ident t -> bool)
        (*(do_again : forall t : base.type, @expr var t -> UnderLets (@expr var t))*).

        (** TODO: Is it okay to commute annotations? *)
        Definition update_annotation {t} (st : abstract_domain' t) (e : @expr var t) : @expr var t
          := match e with
             | (#cst' @ e')
               => if is_annotation _ cst'
                 then match type.try_transport base.try_make_transport_cps ident _ (t -> t) cst', type.try_transport base.try_make_transport_cps _ _ _ e' with
                      | Some cst'', Some e''
                        => match annotate_ident _ (abstract_interp_ident _ cst'' st) with
                          | Some cst''' => ###cst''' @ e''
                          | None => e
                          end%expr
                      | _, _ => e
                      end
                 else match annotate_ident _ st with
                      | Some cst => ###cst @ e
                      | None => e
                      end%expr
             | _ => match annotate_ident _ st with
                   | Some cst => ###cst @ e
                   | None => e
                   end%expr
             end%expr_pat.

        Definition annotate_with_ident (is_let_bound : bool) {t}
                   (st : abstract_domain' t) (e : @expr var t)
          : UnderLets (@expr var t)
          := let cst_e := update_annotation st e (*match annotate_ident _ st with
                          | Some cst => ###cst @ e
                          | None => e
                          end%expr*) in
             if is_let_bound
             then UnderLet cst_e (fun v => Base ($v)%expr)
             else Base cst_e.

        Definition annotate_base (is_let_bound : bool) {t : base.type.base}
                   (st : abstract_domain' t) (e : @expr var t)
          : UnderLets (@expr var t)
          := match invert_Literal e with
             | Some v => Base ##(update_literal_with_state _ st v)
             | None => annotate_with_ident is_let_bound st e
             end%expr.

        Fixpoint annotate (is_let_bound : bool) {t : base.type} : abstract_domain' t -> @expr var t -> UnderLets (@expr var t)
          := match t return abstract_domain' t -> @expr var t -> UnderLets (@expr var t) with
             | base.type.type_base t => annotate_base is_let_bound
             | base.type.prod A B
               => fun st e
                  => match invert_pair e with
                     | Some (x, y)
                       => let stx := abstract_interp_ident _ ident.fst st in
                          let sty := abstract_interp_ident _ ident.snd st in
                          (x' <-- @annotate is_let_bound A stx x;
                             y' <-- @annotate is_let_bound B sty y;
                             Base (x', y')%expr)
                     | None => annotate_with_ident is_let_bound st e
                     end
             | base.type.list A
               => fun st e
                  => match extract_list_state _ st, reflect_list e with
                     | Some ls_st, Some ls_e
                       => (retv <---- (List.map
                                         (fun '(st', e') => @annotate is_let_bound A st' e')
                                         (List.combine ls_st ls_e));
                             Base (reify_list retv))
                     | Some ls_st, None
                       => (retv <---- (List.map
                                         (fun '(n, st')
                                          => let e' := (#ident.List_nth_default @ DefaultValue.expr.base.default @ e @ ##(n:nat))%expr in
                                             @annotate is_let_bound A st' e')
                                         (List.combine (List.seq 0 (List.length ls_st)) ls_st));
                             Base (reify_list retv))
                     | None, _ => annotate_with_ident is_let_bound st e
                     end
             end%under_lets.

        Local Notation value_with_lets := (@value_with_lets base.type ident var abstract_domain').
        Local Notation reify := (@reify base.type ident var abstract_domain' annotate bottom').
        Local Notation reflect := (@reflect base.type ident var abstract_domain' annotate bottom').

        (** We manually rewrite with the rule for [nth_default], as the eliminator for eta-expanding lists in the input *)
        Definition interp_ident {t} (idc : ident t) : value_with_lets t
          := match idc in ident t return value_with_lets t with
             | ident.List_nth_default T as idc
               => let default := reflect (###idc) (abstract_interp_ident _ idc) in
                  Base
                    (fst default,
                     (fun default_arg
                      => default <-- snd default default_arg;
                           Base
                             (fst default,
                              (fun ls_arg
                               => default <-- snd default ls_arg;
                                    Base
                                      (fst default,
                                       (fun n_arg
                                        => default <-- snd default n_arg;
                                            ls' <-- @reify false (base.type.list T) ls_arg tt;
                                             Base
                                               (fst default,
                                                match reflect_list ls', invert_Literal (snd n_arg) with
                                                | Some ls, Some n
                                                  => nth_default (snd default_arg) ls n
                                                | _, _ => snd default
                                                end)))))))
             | idc => Base (reflect (###idc) (abstract_interp_ident _ idc))
             end%core%under_lets%expr.

        Definition eval_with_bound {t} (e : @expr value_with_lets t)
                   (st : type.for_each_lhs_of_arrow abstract_domain t)
          : @expr var t
          := @eval_with_bound' base.type ident var abstract_domain' annotate bottom' (@interp_ident) t e st.

        Definition eval {t} (e : @expr value_with_lets t) : @expr var t
          := @eval' base.type ident var abstract_domain' annotate bottom' (@interp_ident) t e.

        Definition eta_expand_with_bound {t} (e : @expr var t)
                   (st : type.for_each_lhs_of_arrow abstract_domain t)
          : @expr var t
          := @eta_expand_with_bound' base.type ident var abstract_domain' annotate bottom' t e st.

        Definition extract {t} (e : @expr _ t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : abstract_domain' (type.final_codomain t)
          := @extract_gen base.type ident abstract_domain' abstract_interp_ident t e bound.
      End with_var.
    End ident.

    Section specialized.
      Local Notation abstract_domain' := ZRange.type.base.option.interp.
      Local Notation abstract_domain := (@partial.abstract_domain base.type abstract_domain').
      Notation expr := (@expr base.type ident).
      Notation Expr := (@expr.Expr base.type ident).
      Local Notation type := (type base.type).
      Let type_base (x : base.type) : type := type.base x.
      Local Coercion type_base : base.type >-> type.
      Definition annotate_ident t : abstract_domain' t -> option (ident (t -> t))
        := match t return abstract_domain' t -> option (ident (t -> t)) with
           | base.type.Z
             => fun st => st' <- st; Some (ident.Z_cast st')
           | base.type.Z * base.type.Z
             => fun '(sta, stb) => sta' <- sta; stb' <- stb; Some (ident.Z_cast2 (sta', stb'))
           | _ => fun _ => None
           end%option%etype.
      Definition is_annotation t (idc : ident t) : bool
        := match idc with
           | ident.Z_cast _
           | ident.Z_cast2 _
             => true
           | _ => false
           end.
      Definition bottom' T : abstract_domain' T
        := ZRange.type.base.option.None.
      Definition abstract_interp_ident t (idc : ident t) : type.interp abstract_domain' t
        := ZRange.ident.option.interp idc.
      Definition update_Z_literal_with_state : abstract_domain' base.type.Z -> Z -> Z
        := fun r n
           => match r with
             | Some r => if ZRange.type.base.is_bounded_by (t:=base.type.Z) r n
                        then n
                        else ident.cast_outside_of_range r n
             | None => n
             end.
      Definition update_literal_with_state (t : base.type.base) : abstract_domain' t -> base.interp t -> base.interp t
        := match t with
           | base.type.Z => update_Z_literal_with_state
           | base.type.unit
           | base.type.bool
           | base.type.nat
             => fun _ => id
           end.
      Definition extract_list_state A (st : abstract_domain' (base.type.list A)) : option (list (abstract_domain' A))
        := st.

      Definition eval {var} {t} (e : @expr _ t) : expr t
        := (@partial.ident.eval)
             var abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotation t e.
      Definition eval_with_bound {var} {t} (e : @expr _ t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : expr t
        := (@partial.ident.eval_with_bound)
             var abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotation t e bound.
      Definition eta_expand_with_bound {var} {t} (e : @expr _ t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : expr t
        := (@partial.ident.eta_expand_with_bound)
             var abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotation t e bound.
      Definition Eval {t} (e : Expr t) : Expr t
        := fun var => eval (e _).
      Definition EvalWithBound {t} (e : Expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : Expr t
        := fun var => eval_with_bound (e _) bound.
      Definition EtaExpandWithBound {t} (e : Expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : Expr t
        := fun var => eta_expand_with_bound (e _) bound.
      Definition EtaExpandWithListInfoFromBound {t} (e : Expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : Expr t
        := EtaExpandWithBound e (type.map_for_each_lhs_of_arrow (@ZRange.type.option.strip_ranges) bound).
      Definition extract {t} (e : expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : abstract_domain' (type.final_codomain t)
        := @partial.ident.extract abstract_domain' abstract_interp_ident t e bound.
      Definition Extract {t} (e : Expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : abstract_domain' (type.final_codomain t)
        := @partial.ident.extract abstract_domain' abstract_interp_ident t (e _) bound.
    End specialized.
  End partial.

  Import defaults.

  Module RelaxZRange.
    Module ident.
      Section relax.
        Context (relax_zrange : zrange -> option zrange).

        Definition relax {t} (idc : ident t) : option (ident t)
          := match idc in ident.ident t return option (ident t) with
             | ident.Z_cast range
               => (r <- relax_zrange range;
                    Some (ident.Z_cast r))
             | ident.Z_cast2 (r1, r2)
               => (r1 <- relax_zrange r1;
                    r2 <- relax_zrange r2;
                    Some (ident.Z_cast2 (r1, r2)))
             | _ => None
             end%option.
      End relax.
    End ident.

    Module expr.
      Section relax.
        Context (relax_zrange : zrange -> option zrange).
        Section with_var.
          Context {var : type -> Type}.

          Fixpoint relax {t} (e : @expr var t) : @expr var t
            := match e with
               | expr.Var _ _ as e
               | expr.Ident _ _ as e
                 => e
               | expr.Abs s d f => expr.Abs (fun v => @relax d (f v))
               | expr.LetIn tx tC ex eC => expr.LetIn (@relax tx ex) (fun v => @relax tC (eC v))
               | expr.App s d f x
                 => let f' := @relax _ f in
                    let x' := @relax _ x in
                    match s, d return expr (s -> d) -> expr s -> expr d with
                    | type.base base.type.Z, type.base base.type.Z
                    | type.base (base.type.Z * base.type.Z)%etype, type.base (base.type.Z * base.type.Z)%etype
                      => fun f x
                         => match option_map (ident.relax relax_zrange)
                                             (invert_Ident f) with
                            | Some (Some idc) => expr.App (expr.Ident idc) x
                            | _ => expr.App f x
                            end
                    | _, _ => expr.App
                    end f' x'
               end.
        End with_var.

        Definition Relax {t} (e : Expr t) : Expr t
          := fun var => relax (e _).
      End relax.
    End expr.
  End RelaxZRange.

  Definition PartialEvaluateWithBounds {t} (e : Expr t)
             (bound : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : Expr t
    := partial.EvalWithBound (GeneralizeVar.GeneralizeVar (e _)) bound.
  Definition PartialEvaluateWithListInfoFromBounds {t} (e : Expr t)
             (bound : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : Expr t
    := partial.EtaExpandWithListInfoFromBound (GeneralizeVar.GeneralizeVar (e _)) bound.

  Definition CheckPartialEvaluateWithBounds
             (relax_zrange : zrange -> option zrange)
             {t} (E : Expr t)
             (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
             (b_out : ZRange.type.base.option.interp (type.final_codomain t))
    : Expr t + (ZRange.type.base.option.interp (type.final_codomain t) * Expr t)
    := let b_computed := partial.Extract E b_in in
       if ZRange.type.base.option.is_tighter_than b_computed b_out
       then @inl (Expr t) _ (RelaxZRange.expr.Relax relax_zrange E)
       else @inr _ (ZRange.type.base.option.interp (type.final_codomain t) * Expr t) (b_computed, E).

  Definition CheckedPartialEvaluateWithBounds
             (relax_zrange : zrange -> option zrange)
             {t} (E : Expr t)
             (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
             (b_out : ZRange.type.base.option.interp (type.final_codomain t))
    : Expr t + (ZRange.type.base.option.interp (type.final_codomain t) * Expr t)
    := let E := PartialEvaluateWithBounds E b_in in
       dlet_nd e := GeneralizeVar.ToFlat E in
             let E := GeneralizeVar.FromFlat e in
             CheckPartialEvaluateWithBounds relax_zrange E b_in b_out.
End Compilers.
