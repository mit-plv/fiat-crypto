Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.LetIn.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.InversionExtra.
Require Import Crypto.Language.API.
Require Import Rewriter.Language.UnderLets.
Import ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Module Compilers.
  Export Language.Compilers.
  Export UnderLets.Compilers.
  Export Language.API.Compilers.
  Import invert_expr.
  Import Language.InversionExtra.Compilers.

  Module ZRange.
    Module type.
      Local Notation binterp := base.interp.
      Local Notation tinterp_gen := type.interp.
      Local Notation einterp := (type.interp base.interp).
      Module base.
        (** turn a [base.type] into a [Set] describing the type of
          bounds on that primitive; Z is a range, nat and bool are exact values *)
        Fixpoint interp (t : base.type) : Type
          := match t with
             | base.type.type_base base.type.Z => zrange
             | base.type.type_base _ as t
             | base.type.unit as t
               => base.interp t
             | base.type.prod A B => interp A * interp B
             | base.type.list A => list (interp A)
             | base.type.option A => option (interp A)
             end%type.
        Definition is_neg {t} : interp t -> bool
          := match t with
             | base.type.type_base base.type.Z => fun r => (lower r <? 0) && (upper r <=? 0)
             | _ => fun _ => false
             end.
        Fixpoint is_tighter_than {t} : interp t -> interp t -> bool
          := match t with
             | base.type.type_base base.type.Z => is_tighter_than_bool
             | base.type.type_base _ as t
             | base.type.unit as t
               => base.interp_beq (@base.base_interp_beq)
             | base.type.prod A B
               => fun '(a, b) '(a', b')
                  => @is_tighter_than A a a' && @is_tighter_than B b b'
             | base.type.list A
               => fold_andb_map (@is_tighter_than A)
             | base.type.option A
               => option_beq (@is_tighter_than A)
             end%bool.
        Fixpoint is_bounded_by {t} : interp t -> binterp t -> bool
          := match t with
             | base.type.type_base base.type.Z => fun r z => ZRange.is_bounded_by_bool z r
             | base.type.type_base _ as t
             | base.type.unit as t
               => base.interp_beq (@base.base_interp_beq)
             | base.type.prod A B
               => fun '(a, b) '(a', b')
                  => @is_bounded_by A a a' && @is_bounded_by B b b'
             | base.type.list A
               => fold_andb_map (@is_bounded_by A)
             | base.type.option A
               => option_beq_hetero (@is_bounded_by A)
             end.
        Module option.
          (** turn a [base.type] into a [Set] describing the type
              of optional bounds on that primitive; bounds on a [Z]
              may be either a range, or [None], generally indicating
              that the [Z] is unbounded. *)
          Fixpoint interp (t : base.type) : Type
            := match t with
               | base.type.type_base base.type.Z => option zrange
               | base.type.type_base _ as t
                 => option (base.interp t)
               | base.type.prod A B => interp A * interp B
               | base.type.list A => option (list (interp A))
               | base.type.option A => option (option (interp A))
               | base.type.unit => unit
               end%type.
          Fixpoint None {t} : interp t
            := match t with
               | base.type.unit => tt
               | base.type.list _
               | base.type.option _
               | base.type.type_base base.type.Z
               | base.type.type_base _
                 => Datatypes.None
               | base.type.prod A B
                 => (@None A, @None B)
               end.
          Fixpoint Some {t} : base.interp t -> interp t
            := match t with
               | base.type.unit
                 => fun _ => tt
               | base.type.type_base base.type.Z
               | base.type.type_base _
                 => Datatypes.Some
               | base.type.list A
                 => fun ls => Datatypes.Some (List.map (@Some A) ls)
               | base.type.option A
                 => fun ls => Datatypes.Some (option_map (@Some A) ls)
               | base.type.prod A B
                 => fun '(a, b)
                    => (@Some A a, @Some B b)
               end.
          Fixpoint lift_Some {t} : interp t -> option (base.interp t)
            := match t with
               | base.type.type_base base.type.Z
               | base.type.type_base _
                 => fun x => x
               | base.type.unit
                 => fun x => Datatypes.Some tt
               | base.type.list A
                 => fun ls => ls <- ls; Option.List.lift (List.map (@lift_Some A) ls)
               | base.type.option A
                 => fun v => v <- v; Option.lift (option_map (@lift_Some A) v)
               | base.type.prod A B
                 => fun '(a, b) => a <- @lift_Some A a; b <- @lift_Some B b; Datatypes.Some (a, b)
               end%option.
          (** Keep data about list length and nat value, but not zrange *)
          Fixpoint strip_ranges {t} : interp t -> interp t
            := match t with
               | base.type.type_base base.type.Z => fun _ => Datatypes.None
               | base.type.type_base _
               | base.type.unit
                 => fun x => x
               | base.type.list A
                 => fun ls => ls <- ls; Datatypes.Some (List.map (@strip_ranges A) ls)
               | base.type.option A
                 => fun v => v <- v; Datatypes.Some (option_map (@strip_ranges A) v)
               | base.type.prod A B
                 => fun '(a, b)
                    => (@strip_ranges A a, @strip_ranges B b)
               end%option.
          Definition is_neg {t} : interp t -> bool
            := match t with
               | base.type.type_base base.type.Z
                 => fun v => match v with
                             | Datatypes.Some v => @is_neg (base.type.type_base base.type.Z) v
                             | Datatypes.None => false
                             end
               | t => fun _ => false
               end.
          Fixpoint is_tighter_than {t} : interp t -> interp t -> bool
            := match t with
               | base.type.type_base base.type.Z as t
               | base.type.type_base _ as t
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
               | base.type.option A
                 => fun v1 v2
                    => match v1, v2 with
                       | Datatypes.None, Datatypes.None => true
                       | Datatypes.Some _, Datatypes.None => true
                       | Datatypes.None, Datatypes.Some _ => false
                       | Datatypes.Some v1, Datatypes.Some v2 => option_beq (@is_tighter_than A) v1 v2
                       end
               | base.type.unit => fun 'tt 'tt => true
               end.
          Fixpoint is_bounded_by {t} : interp t -> binterp t -> bool
            := match t with
               | base.type.type_base base.type.Z as t
               | base.type.type_base _ as t
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
               | base.type.option A
                 => fun v1 v2
                    => match v1 with
                       | Datatypes.None => true
                       | Datatypes.Some v1 => option_beq_hetero (@is_bounded_by A) v1 v2
                       end
               | base.type.unit => fun 'tt _ => true
               end.

          Lemma is_bounded_by_Some {t} r val
            : is_bounded_by (@Some t r) val = base.is_bounded_by r val.
          Proof.
            induction t;
              repeat first [ reflexivity
                           | progress cbn in *
                           | progress destruct_head'_prod
                           | progress destruct_head' base.type.base
                           | progress destruct_head' option
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
                           | progress destruct_head' option
                           | progress cbn [interp binterp base.interp is_bounded_by is_tighter_than base.is_tighter_than base.is_bounded_by option_beq_hetero] in *
                           | progress subst
                           | reflexivity
                           | progress break_innermost_match_hyps
                           | solve [ eauto with nocore ]
                           | progress cbv [ZRange.is_bounded_by_bool is_tighter_than_bool] in *
                           | progress rewrite ?Bool.andb_true_iff in *
                           | discriminate
                           | apply conj
                           | Z.ltb_to_lt; omega
                           | match goal with
                             | [ H : context[@base.interp_beq _ _ ?base_interp_beq ?t] |- _ ]
                               => progress Reflect.reflect_beq_to_eq (@base.interp_beq _ _ base_interp_beq t)
                             | [ |- context[@base.interp_beq _ _ ?base_interp_beq ?t] ]
                               => progress Reflect.reflect_beq_to_eq (@base.interp_beq _ _ base_interp_beq t)
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
             | base.type.type_base base.type.Z => fun z => Some r[z~>z]%zrange
             | base.type.type_base _
               => fun n => Some n
             | base.type.unit
               => fun _ => tt
             | base.type.prod A B
               => fun '(a, b) => (@of_literal A a, @of_literal B b)
             | base.type.list A
               => fun ls => Some (List.map (@of_literal A) ls)
             | base.type.option A
               => fun v => Some (option_map (@of_literal A) v)
             end.
        Fixpoint to_literal {t} : type.base.option.interp t -> option (base.interp t)
          := match t with
             | base.type.type_base base.type.Z => fun r => r <- r; if r.(lower) =? r.(upper) then Some r.(lower) else None
             | base.type.type_base _
               => fun v => v
             | base.type.unit
               => fun _ => Some tt
             | base.type.prod A B
               => fun '(a, b) => a <- @to_literal A a; b <- @to_literal B b; Some (a, b)
             | base.type.list A
               => fun ls => ls <- ls; Option.List.lift (List.map (@to_literal A) ls)
             | base.type.option A
               => fun v => v <- v; Option.lift (option_map (@to_literal A) v)
             end%option%Z.
        Local Notation rSome v
          := (ZRange.type.base.option.Some (t:=base.reify_norm_type_of v) v)
               (only parsing).
        (** do bounds analysis on identifiers; take in optional bounds
            on arguments, return optional bounds on outputs. *)
        (** Casts are like assertions; we only guarantee anything when they're true *)
        (** If [r] is [None], that means we had a cast with a
            non-literal range.  If [v] is [None], that means we don't
            know anything about bounds on [v]. *)
        Definition interp_Z_cast (r : option zrange) (v : option zrange) : option zrange
          := match r, v with
             | Some r, Some v
               => if is_tighter_than_bool v r (* the value is definitely inside the range *)
                  then Some v
                  else None
             | _, _ => None
             end.
        Local Notation tZ := (base.type.type_base base.type.Z).
        Definition interp {t} (idc : ident t) : type.option.interp t
          := match idc in ident.ident t return type.option.interp t with
             | ident.Literal t v => @of_literal (base.type.type_base t) v
             | ident.tt as idc
               => ident.interp idc
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
             | ident.Nat_eqb as idc
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
             | ident.Z_ltb as idc
             | ident.Z_geb as idc
             | ident.Z_gtb as idc
             | ident.Z_max as idc
             | ident.Z_min as idc
             | ident.Z_pow as idc
             | ident.Z_modulo as idc
             | ident.Build_zrange as idc
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
                   | Some m, None => Some (if (0 <? m)%Z
                                           then r[0 ~> m-1]
                                           else if (m =? 0)%Z
                                                then r[0 ~> 0]
                                                else r[m+1 ~> 0])
                   | _, _ => None
                    end
             | ident.Z_truncating_shiftl as idc
               => fun bw x y => match to_literal bw, to_literal x, to_literal y with
                                | Some bw, Some x, Some y => of_literal (ident.interp idc bw x y)
                                | Some bw, _, _
                                  => x <- x;
                                       y <- y;
                                       Some (ZRange.land_bounds
                                               (ZRange.four_corners_and_zero Z.shiftl x y)
                                               (ZRange.constant (Z.ones (Z.max 0 bw))))
                                | None, _, _ => None
                                end
             | ident.bool_rect _
               => fun t f b
                 => match b with
                   | Some b => if b then t tt else f tt
                   | None => ZRange.type.base.option.None
                   end
             | ident.option_rect _ _
               => fun s n o
                 => match o with
                   | Some o => option_rect _ s (n tt) o
                   | None => ZRange.type.base.option.None
                   end
             | ident.zrange_rect _
               => fun f v
                 => match v with
                    | Some v => ZRange.zrange_rect
                                  _
                                  (fun l u => f (Some (ZRange.constant l)) (Some (ZRange.constant u)))
                                  v
                   | None => ZRange.type.base.option.None
                   end
             | ident.nat_rect _
             | ident.eager_nat_rect _
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
             | ident.eager_nat_rect_arrow _ _
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
             | ident.eager_list_rect _ _
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
             | ident.list_rect_arrow _ _ _
             | ident.eager_list_rect_arrow _ _ _
               => fun N C ls v
                 => match ls with
                   | Some ls
                     => list_rect
                         _
                         N
                         (fun x xs rec => C x (Some xs) rec)
                         ls
                         v
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
             | ident.eager_List_nth_default _
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
             | ident.None t => Some None
             | ident.Some t => fun x => Some (Some x)
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
               => fun x y => x <- x; y <- y; Some (ZRange.four_corners (ident.interp idc) x y)
             | ident.Z_div as idc
             | ident.Z_shiftr as idc
             | ident.Z_shiftl as idc
               => fun x y => x <- x; y <- y; Some (ZRange.four_corners_and_zero (ident.interp idc) x y)
             | ident.Z_add_with_carry as idc
               => fun x y z => x <- x; y <- y; z <- z; Some (ZRange.eight_corners (ident.interp idc) x y z)
             | ident.Z_cc_m as idc
               => fun s x => s <- to_literal s; x <- x; Some (ZRange.two_corners (ident.interp idc s) x)
             | ident.Z_rshi as idc
               => fun s x y offset
                 => s <- to_literal s; x <- x; y <- y; offset <- to_literal offset;
                     if (0 <? s) then Some r[0~>s-1] else None
             | ident.Z_land
               => fun x y => x <- x; y <- y; Some (ZRange.land_bounds x y)
             | ident.Z_lor
               => fun x y => x <- x; y <- y; Some (ZRange.lor_bounds x y)
             | ident.Z_mul_split
               => fun split_at x y
                 => match to_literal split_at, x, y with
                   | Some split_at, Some x, Some y
                     => ZRange.type.base.option.Some
                         (t:=tZ*tZ)
                         (ZRange.split_bounds (ZRange.four_corners Z.mul x y) split_at)
                   | _, _, _ => ZRange.type.base.option.None
                   end
             | ident.Z_add_get_carry
               => fun split_at x y
                 => match to_literal split_at, x, y with
                   | Some split_at, Some x, Some y
                     => ZRange.type.base.option.Some
                         (t:=tZ*tZ)
                         (ZRange.split_bounds (ZRange.four_corners Z.add x y) split_at)
                   | _, _, _ => ZRange.type.base.option.None
                   end
             | ident.Z_add_with_get_carry
               => fun split_at x y z
                 => match to_literal split_at, x, y, z with
                   | Some split_at, Some x, Some y, Some z
                     => ZRange.type.base.option.Some
                         (t:=tZ*tZ)
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
                         (t:=tZ*tZ)
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
                         (t:=tZ*tZ)
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
             | ident.Z_combine_at_bitwidth as idc
               => fun bitwidth lo hi
                  => bitwidth <- to_literal bitwidth;
                       lo <- lo;
                       hi <- hi;
                       Some (ZRange.four_corners (ident.interp idc bitwidth) lo hi)
             | ident.Z_cast
               => fun (range : option zrange) (r : option zrange)
                  => interp_Z_cast range r
             | ident.Z_cast2
               => fun '((r1, r2) : option zrange * option zrange) '((r1', r2') : option zrange * option zrange)
                  => (interp_Z_cast r1 r1', interp_Z_cast r2 r2')
             | ident.fancy_add
             | ident.fancy_sub
               => fun '((log2wordmax, imm), args)
                  => match to_literal (t:=tZ) log2wordmax, to_literal (t:=tZ) imm with
                     | Some log2wordmax, _
                       => let wordmax := 2^log2wordmax in
                          let r := r[0~>wordmax-1] in
                          if ZRange.type.base.option.is_tighter_than (t:=tZ*tZ) args (Some r, Some r)
                          then (Some r, Some r[0~>1])
                          else ZRange.type.base.option.None
                     | _, _ => ZRange.type.base.option.None
                     end
             | ident.fancy_addc
             | ident.fancy_subb
               => fun '((log2wordmax, imm), args)
                  => match to_literal (t:=tZ) log2wordmax, to_literal (t:=tZ) imm with
                     | Some log2wordmax, _
                       => let wordmax := 2^log2wordmax in
                          let r := r[0~>wordmax-1] in
                          if ZRange.type.base.option.is_tighter_than (t:=tZ*tZ*tZ) args (Some r[0~>1], Some r, Some r)
                          then (Some r, Some r[0~>1])
                          else ZRange.type.base.option.None
                     | _, _ => ZRange.type.base.option.None
                     end
             | ident.fancy_mulll
             | ident.fancy_mullh
             | ident.fancy_mulhl
             | ident.fancy_mulhh
               => fun '(log2wordmax, args)
                  => match to_literal (t:=tZ) log2wordmax with
                     | Some log2wordmax
                       => let wordmax := 2^log2wordmax in
                          let r := r[0~>wordmax-1] in
                          if ZRange.type.base.option.is_tighter_than (t:=tZ*tZ) args (Some r, Some r)
                          then if (Z.eqb (log2wordmax mod 2) 0)
                               then Some r
                               else ZRange.type.base.option.None
                          else ZRange.type.base.option.None
                     | _ => ZRange.type.base.option.None
                     end
             | ident.fancy_rshi as idc
               => fun '((log2wordmax, n), args)
                  => match to_literal (t:=tZ) log2wordmax, to_literal (t:=tZ) n with
                     | Some log2wordmax, Some n
                       => let wordmax := 2^log2wordmax in
                          let r := r[0~>wordmax-1] in
                          let r_nbits := r[0~>2^n-1] in
                          if (0 <=? log2wordmax)%Z
                          then if (ZRange.type.base.option.is_tighter_than (t:=tZ*tZ) args (Some r_nbits, Some r) && (0 <=? n)%Z)
                               then
                                 hi_range <- fst args;
                                   lo_range <- snd args;
                                   Some (ZRange.four_corners (fun x y => ident.interp idc ((log2wordmax, n), (x, y))) hi_range lo_range)
                               else if ZRange.type.base.option.is_tighter_than (t:=tZ*tZ) args (Some r, Some r)
                                    then Some r
                                    else ZRange.type.base.option.None
                          else ZRange.type.base.option.None
                     | _, _ => ZRange.type.base.option.None
                     end
             | ident.fancy_selm
               => fun '(_, (_, y, z)) => y <- y; z <- z; Some (ZRange.union y z)
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
        := match t return Type (* COQBUG(https://github.com/coq/coq/issues/7727) *) with
           | type.base t
             => abstract_domain t * @expr var t
           | type.arrow s d
             => value s -> UnderLets (value d)
           end%type.

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
           | type.arrow s d => fun _ => bottom
           end.

      (** We need to make sure that we ignore the state of
         higher-order arrows *everywhere*, or else the proofs don't go
         through.  So we sometimes need to replace the state of
         arrow-typed values with [⊥]. *)
      Fixpoint bottomify {t} : value t -> value_with_lets t
        := match t return value t -> value_with_lets t with
           | type.base t => fun '(st, v) => Base (bottom' t, v)
           | type.arrow s d => fun f => Base (fun x => fx <-- f x; @bottomify d fx)
           end%under_lets.

      (** We drop the state of higher-order arrows *)
      Fixpoint reify (annotate_with_state : bool) (is_let_bound : bool) {t} : value t -> type.for_each_lhs_of_arrow abstract_domain t -> UnderLets (@expr var t)
        := match t return value t -> type.for_each_lhs_of_arrow abstract_domain t -> UnderLets (@expr var t) with
           | type.base t
             => fun '(st, v) 'tt
                => if annotate_with_state
                   then annotate is_let_bound t st v
                   else if is_let_bound
                        then UnderLets.UnderLet v (fun v' => UnderLets.Base ($v'))
                        else UnderLets.Base v
           | type.arrow s d
             => fun f_e '(sv, dv)
               => let sv := match s with
                           | type.base _ => sv
                           | type.arrow _ _ => bottom
                           end in
                 Base
                   (λ x , (UnderLets.to_expr
                             (fx <-- f_e (@reflect annotate_with_state _ (expr.Var x) sv);
                                @reify annotate_with_state false _ fx dv)))
           end%core%expr
      with reflect (annotate_with_state : bool) {t} : @expr var t -> abstract_domain t -> value t
           := match t return @expr var t -> abstract_domain t -> value t with
              | type.base t
                => fun e st => (st, e)
              | type.arrow s d
                => fun e absf
                   => (fun v
                       => let stv := state_of_value v in
                          (rv <-- (@reify annotate_with_state false s v bottom_for_each_lhs_of_arrow);
                             Base (@reflect annotate_with_state d (e @ rv) (absf stv))%expr))
              end%under_lets.

      Fixpoint interp (annotate_with_state : bool) {t} (e : @expr value_with_lets t) : value_with_lets t
        := match e in expr.expr t return value_with_lets t with
           | expr.Ident t idc => interp_ident _ idc (* Base (reflect (###idc) (abstract_interp_ident _ idc))*)
           | expr.Var t v => v
           | expr.Abs s d f => Base (fun x => @interp annotate_with_state d (f (Base x)))
           | expr.App (type.base s) d f x
             => (x' <-- @interp annotate_with_state _ x;
                   f' <-- @interp annotate_with_state (_ -> d)%etype f;
                   f' x')
           | expr.App (type.arrow s' d') d f x
             => (x' <-- @interp annotate_with_state (s' -> d')%etype x;
                   x'' <-- bottomify x';
                   f' <-- @interp annotate_with_state (_ -> d)%etype f;
                   f' x'')
           | expr.LetIn (type.arrow _ _) B x f
             => (x' <-- @interp annotate_with_state _ x;
                   @interp annotate_with_state _ (f (Base x')))
           | expr.LetIn (type.base A) B x f
             => (x' <-- @interp annotate_with_state _ x;
                   x'' <-- reify annotate_with_state true (* this forces a let-binder here *) x' tt;
                   @interp annotate_with_state _ (f (Base (reflect annotate_with_state x'' (state_of_value x')))))
           end%under_lets.

      Definition eval_with_bound' (annotate_with_state : bool) {t} (e : @expr value_with_lets t)
                 (st : type.for_each_lhs_of_arrow abstract_domain t)
        : expr t
        := UnderLets.to_expr (e' <-- interp annotate_with_state e; reify annotate_with_state false e' st).

      Definition eval' {t} (e : @expr value_with_lets t) : expr t
        := eval_with_bound' false e bottom_for_each_lhs_of_arrow.

      Definition eta_expand_with_bound' {t} (e : @expr var t)
                 (st : type.for_each_lhs_of_arrow abstract_domain t)
        : expr t
        := UnderLets.to_expr (reify true false (reflect true e bottom) st).

      Section extract.
        Context (ident_extract : forall t, ident t -> abstract_domain t).

        (** like [expr.interp (@ident_extract) e], except we replace
            all higher-order state with bottom *)
        Fixpoint extract' {t} (e : @expr abstract_domain t) : abstract_domain t
          := match e in expr.expr t return abstract_domain t with
             | expr.Ident t idc => ident_extract t idc
             | expr.Var t v => v
             | expr.Abs s d f => fun v : abstract_domain s => @extract' _ (f v)
             | expr.App (type.base s) d f x
               => @extract' _ f (@extract' _ x)
             | expr.App (type.arrow s' d') d f x
               => @extract' _ f (@bottom (type.arrow s' d'))
             | expr.LetIn A B x f => dlet y := @extract' _ x in @extract' _ (f y)
             end.

        Definition extract_gen {t} (e : @expr abstract_domain t) (bound : type.for_each_lhs_of_arrow abstract_domain t)
          : abstract_domain' (type.final_codomain t)
          := type.app_curried (extract' e) bound.
      End extract.
    End with_var.

    Module ident.
      Section with_var.
        Local Notation type := (type base.type).
        Let type_base (x : base.type.base) : base.type := base.type.type_base x.
        Let base {bt} (x : Language.Compilers.base.type bt) : type.type _ := type.base x.
        Local Coercion base : base.type >-> type.type.
        Local Coercion type_base : base.type.base >-> base.type.
        Context {var : type -> Type}.
        Local Notation expr := (@expr base.type ident).
        Local Notation UnderLets := (@UnderLets base.type ident var).
        Context (abstract_domain' : base.type -> Type).
        Local Notation abstract_domain := (@abstract_domain base.type abstract_domain').
        Context (annotate_expr : forall t, abstract_domain' t -> option (@expr var (t -> t)))
                (bottom' : forall A, abstract_domain' A)
                (abstract_interp_ident : forall t, ident t -> type.interp abstract_domain' t)
                (extract_list_state : forall A, abstract_domain' (base.type.list A) -> option (list (abstract_domain' A)))
                (extract_option_state : forall A, abstract_domain' (base.type.option A) -> option (option (abstract_domain' A)))
                (is_annotated_for : forall t t', @expr var t -> abstract_domain' t' -> bool).

        (** TODO: Is it okay to commute annotations? *)
        Definition update_annotation {t} (st : abstract_domain' t) (e : @expr var t) : @expr var t
          := match e, annotate_expr _ st with
             | (cst' @ e'), Some cst
               => if is_annotated_for _ _ cst' st
                  then e
                  else cst @ e
             | _, Some cst => cst @ e
             | _, None => e
             end%expr_pat%expr.

        Definition annotate_with_expr (is_let_bound : bool) {t}
                   (st : abstract_domain' t) (e : @expr var t)
          : UnderLets (@expr var t)
          := let cst_e := update_annotation st e (*match annotate_expr _ st with
                          | Some cst => ###cst @ e
                          | None => e
                          end%expr*) in
             if is_let_bound
             then UnderLet cst_e (fun v => Base ($v)%expr)
             else Base cst_e.

        Definition annotate_base (is_let_bound : bool) {t : base.type.base}
                   (st : abstract_domain' t) (e : @expr var t)
          : UnderLets (@expr var t)
          := annotate_with_expr is_let_bound st e.

        Fixpoint annotate (is_let_bound : bool) {t : base.type} : abstract_domain' t -> @expr var t -> UnderLets (@expr var t)
          := match t return abstract_domain' t -> @expr var t -> UnderLets (@expr var t) with
             | base.type.type_base t => annotate_base is_let_bound
             | base.type.unit => fun _ e => Base e
             | base.type.prod A B
               => fun st e
                  => match invert_pair e with
                     | Some (x, y)
                       => let stx := abstract_interp_ident _ ident.fst st in
                          let sty := abstract_interp_ident _ ident.snd st in
                          (x' <-- @annotate is_let_bound A stx x;
                             y' <-- @annotate is_let_bound B sty y;
                             Base (x', y')%expr)
                     | None => annotate_with_expr is_let_bound st e
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
                     | None, _ => annotate_with_expr is_let_bound st e
                     end
             | base.type.option A
               => fun st e
                  => match extract_option_state _ st, reflect_option e with
                     | Some v_st, Some v_e
                       => (retv <----- (Option.map
                                          (fun '(st', e') => @annotate is_let_bound A st' e')
                                          (Option.combine v_st v_e));
                             Base (reify_option retv))
                     | Some _, None
                     | None, _
                       => annotate_with_expr is_let_bound st e
                     end
             end%under_lets.

        Local Notation value_with_lets := (@value_with_lets base.type ident var abstract_domain').
        Local Notation reify := (@reify base.type ident var abstract_domain' annotate bottom').
        Local Notation reflect := (@reflect base.type ident var abstract_domain' annotate bottom').

        (** We manually rewrite with the rule for [nth_default], as the eliminator for eta-expanding lists in the input *)
        Definition interp_ident (annotate_with_state : bool) {t} (idc : ident t) : value_with_lets t
          := match idc in ident t return value_with_lets t with
             | ident.List_nth_default T as idc
               => let default := reflect annotate_with_state (###idc) (abstract_interp_ident _ idc) in
                  Base
                    (fun default_arg
                     => default <-- default default_arg;
                          Base
                            (fun ls_arg
                             => default <-- default ls_arg;
                                  Base
                                    (fun n_arg
                                     => default <-- default n_arg;
                                          ls' <-- @reify annotate_with_state false (base.type.list T) ls_arg tt;
                                          Base
                                            (fst default,
                                             match reflect_list ls', invert_Literal (snd n_arg) with
                                             | Some ls, Some n
                                               => nth_default (snd default_arg) ls n
                                             | _, _ => snd default
                                             end))))
             | idc => Base (reflect annotate_with_state (###idc) (abstract_interp_ident _ idc))
             end%core%under_lets%expr.

        Definition eval_with_bound (annotate_with_state : bool) {t} (e : @expr value_with_lets t)
                   (st : type.for_each_lhs_of_arrow abstract_domain t)
          : @expr var t
          := @eval_with_bound' base.type ident var abstract_domain' annotate bottom' (@interp_ident annotate_with_state) annotate_with_state t e st.

        Definition eval {t} (e : @expr value_with_lets t) : @expr var t
          := @eval' base.type ident var abstract_domain' annotate bottom' (@interp_ident false) t e.

        Definition eta_expand_with_bound {t} (e : @expr var t)
                   (st : type.for_each_lhs_of_arrow abstract_domain t)
          : @expr var t
          := @eta_expand_with_bound' base.type ident var abstract_domain' annotate bottom' t e st.

        Definition extract {t} (e : @expr _ t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : abstract_domain' (type.final_codomain t)
          := @extract_gen base.type ident abstract_domain' bottom' abstract_interp_ident t e bound.
      End with_var.
    End ident.

    Definition default_relax_zrange (v : zrange) : option zrange := Some v.

    Section specialized.
      Local Notation abstract_domain' := ZRange.type.base.option.interp.
      Local Notation abstract_domain := (@partial.abstract_domain base.type abstract_domain').
      Notation expr := (@expr base.type ident).
      Notation Expr := (@expr.Expr base.type ident).
      Local Notation type := (type base.type).
      Let type_base (x : base.type.base) : base.type := base.type.type_base x.
      Let base {bt} (x : Language.Compilers.base.type bt) : type.type _ := type.base x.
      Local Coercion base : base.type >-> type.type.
      Local Coercion type_base : base.type.base >-> base.type.
      Local Notation tZ := (base.type.type_base base.type.Z).

      Section with_relax.
        Context (relax_zrange : zrange -> option zrange).

        Let always_relax_zrange : zrange -> zrange
          := fun range => match relax_zrange (ZRange.normalize range) with
                          | Some r => r
                          | None => range
                          end.

        Definition annotation_of_state (st : abstract_domain' base.type.Z) : option zrange
          := option_map always_relax_zrange st.

        Local Notation cstZ r
          := (expr.App
                (d:=type.arrow (type.base tZ) (type.base tZ))
                (expr.Ident ident.Z_cast)
                (expr.Ident (@ident.Literal base.type.zrange r%zrange))).
        Local Notation cstZZ r1 r2
          := (expr.App
                (d:=type.arrow (type.base (tZ * tZ)) (type.base (tZ * tZ)))
                (expr.Ident ident.Z_cast2)
                (#(@ident.Literal base.type.zrange r1%zrange), #(@ident.Literal base.type.zrange r2%zrange))%expr_pat).

        Definition annotate_expr {var} t : abstract_domain' t -> option (@expr var (t -> t))
          := match t return abstract_domain' t -> option (expr (t -> t)) with
             | tZ
               => fun st => st' <- annotation_of_state st; Some (cstZ st')
             | tZ * tZ
               => fun '(sta, stb) => sta' <- annotation_of_state sta; stb' <- annotation_of_state stb; Some (cstZZ sta' stb')
             | _ => fun _ => None
             end%option%etype.

        Definition is_annotated_for {var} t t' (idc : @expr var t) : abstract_domain' t' -> bool
          := match invert_Z_cast idc, invert_Z_cast2 idc, t' with
             | Some r, _, tZ
               => fun r'
                  => option_beq zrange_beq (Some r) (annotation_of_state r')
             | _, Some (r1, r2), base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)
               => fun '(r1', r2')
                  => (option_beq zrange_beq (Some r1) (annotation_of_state r1'))
                       && (option_beq zrange_beq (Some r2) (annotation_of_state r2'))
             | _, _, _ => fun _ => false
             end.
        Definition annotation_to_expr {var1} t (idc : @expr var1 t) : option (forall var2, @expr var2 t)
          := match invert_Z_cast idc, invert_Z_cast2 idc, t with
             | Some r, _, (type.base tZ -> type.base tZ)%etype
               => Some (fun var2 => cstZ r)
             | _, Some (r1, r2), (type.base (tZ * tZ) -> type.base (tZ * tZ))%etype
               => Some (fun var2 => cstZZ r1 r2)
             | _, _, _ => None
             end.
        Definition bottom' T : abstract_domain' T
          := ZRange.type.base.option.None.
        Definition abstract_interp_ident t (idc : ident t) : type.interp abstract_domain' t
          := ZRange.ident.option.interp idc.
        Definition extract_list_state A (st : abstract_domain' (base.type.list A)) : option (list (abstract_domain' A))
          := st.
        Definition extract_option_state A (st : abstract_domain' (base.type.option A)) : option (option (abstract_domain' A))
          := st.

        Definition eval_with_bound {var} {t} (e : @expr _ t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : expr t
          := (@partial.ident.eval_with_bound)
               var abstract_domain' annotate_expr bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for true t e bound.

        Definition eta_expand_with_bound {var} {t} (e : @expr _ t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : expr t
          := (@partial.ident.eta_expand_with_bound)
               var abstract_domain' annotate_expr bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for t e bound.

        Definition EvalWithBound {t} (e : Expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : Expr t
          := fun var => eval_with_bound (e _) bound.
        Definition EtaExpandWithBound {t} (e : Expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : Expr t
          := fun var => eta_expand_with_bound (e _) bound.
      End with_relax.

      Definition eval {var} {t} (e : @expr _ t) : expr t
        := (@partial.ident.eval)
             var abstract_domain' (annotate_expr default_relax_zrange) bottom' abstract_interp_ident extract_list_state extract_option_state (is_annotated_for default_relax_zrange) t e.
      Definition Eval {t} (e : Expr t) : Expr t
        := fun var => eval (e _).
      Definition EtaExpandWithListInfoFromBound {t} (e : Expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : Expr t
        := EtaExpandWithBound default_relax_zrange e (type.map_for_each_lhs_of_arrow (@ZRange.type.option.strip_ranges) bound).
      Definition extract {t} (e : expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : abstract_domain' (type.final_codomain t)
        := @partial.ident.extract abstract_domain' bottom' abstract_interp_ident t e bound.
      Definition Extract {t} (e : Expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : abstract_domain' (type.final_codomain t)
        := @partial.ident.extract abstract_domain' bottom' abstract_interp_ident t (e _) bound.
    End specialized.
  End partial.
  Import API.

  Module Import CheckCasts.
    Fixpoint get_casts {t} (e : expr t) : list { t : _ & forall var, @expr var t }
      := match partial.annotation_to_expr _ e with
         | Some e => [existT _ t e]
         | None
           => match e with
              | expr.Ident t idc => nil
              | expr.Var t v => v
              | expr.Abs s d f => @get_casts _ (f nil)
              | expr.App s d f x => @get_casts _ f ++ @get_casts _ x
              | expr.LetIn A B x f => @get_casts _ x ++ @get_casts _ (f nil)
              end
         end%list.

    Definition GetUnsupportedCasts {t} (e : Expr t) : list { t : _ & forall var, @expr var t }
      := get_casts (e _).
  End CheckCasts.

  Definition PartialEvaluateWithBounds
             (relax_zrange : zrange -> option zrange) {t} (e : Expr t)
             (bound : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : Expr t
    := partial.EvalWithBound relax_zrange (GeneralizeVar.GeneralizeVar (e _)) bound.
  Definition PartialEvaluateWithListInfoFromBounds {t} (e : Expr t)
             (bound : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : Expr t
    := partial.EtaExpandWithListInfoFromBound (GeneralizeVar.GeneralizeVar (e _)) bound.

  Definition CheckedPartialEvaluateWithBounds
             (relax_zrange : zrange -> option zrange)
             {t} (E : Expr t)
             (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
             (b_out : ZRange.type.base.option.interp (type.final_codomain t))
    : Expr t + (ZRange.type.base.option.interp (type.final_codomain t) * Expr t + list { t : _ & forall var, @expr var t })
    := dlet_nd e := GeneralizeVar.ToFlat E in
       let E := GeneralizeVar.FromFlat e in
       let b_computed := partial.Extract E b_in in
       match CheckCasts.GetUnsupportedCasts E with
       | nil => (let E := PartialEvaluateWithBounds relax_zrange E b_in in
                if ZRange.type.base.option.is_tighter_than b_computed b_out
                then @inl (Expr t) _ E
                else inr (@inl (ZRange.type.base.option.interp (type.final_codomain t) * Expr t) _ (b_computed, E)))
       | unsupported_casts => inr (inr unsupported_casts)
       end.
End Compilers.
