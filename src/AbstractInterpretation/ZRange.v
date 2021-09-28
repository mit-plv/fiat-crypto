Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Bool.Reflect.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Import ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Module Compilers.
  Export Language.Compilers.
  Export Language.API.Compilers.

  Module ZRange.
    Module Export Settings.
      Class shiftr_avoid_uint1_opt := shiftr_avoid_uint1 : bool.
      Typeclasses Opaque shiftr_avoid_uint1_opt.
      Module AbstractInterpretation.
        Local Set Primitive Projections.
        Class Options
          := { shiftr_avoid_uint1 : shiftr_avoid_uint1_opt
             }.
        Definition default_Options : Options
          := {| shiftr_avoid_uint1 := false |}.
        Module Export Exports.
          Global Existing Instance Build_Options.
          Global Hint Immediate shiftr_avoid_uint1 : typeclass_instances.
          Global Coercion shiftr_avoid_uint1 : Options >-> shiftr_avoid_uint1_opt.
        End Exports.
      End AbstractInterpretation.
      Export AbstractInterpretation.Exports.
    End Settings.
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
        Fixpoint map_ranges (f : zrange -> zrange) {t} : interp t -> interp t
          := match t with
             | base.type.type_base base.type.Z => f
             | base.type.type_base _ as t
             | base.type.unit as t
               => fun x => x
             | base.type.prod A B => fun '(a, b) => (@map_ranges f A a, @map_ranges f B b)
             | base.type.list A => List.map (@map_ranges f A)
             | base.type.option A => option_map (@map_ranges f A)
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
               => base.interp_beq (fun t => @base.base_interp_beq t t)
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
               => base.interp_beq (fun t => @base.base_interp_beq t t)
             | base.type.prod A B
               => fun '(a, b) '(a', b')
                  => @is_bounded_by A a a' && @is_bounded_by B b b'
             | base.type.list A
               => fold_andb_map (@is_bounded_by A)
             | base.type.option A
               => option_beq_hetero (@is_bounded_by A)
             end.
        Fixpoint interp_beq {t1 t2} : interp t1 -> interp t2 -> bool
          := match t1, t2 return interp t1 -> interp t2 -> bool with
             | base.type.type_base base.type.Z, base.type.type_base base.type.Z => zrange_beq
             | base.type.type_base base.type.Z, _ | _, base.type.type_base base.type.Z => fun _ _ => false
             | base.type.type_base _ as t1, base.type.type_base _ as t2
             | base.type.unit as t1, base.type.unit as t2
               => base.interp_beq_hetero (@base.base_interp_beq)
             | base.type.prod A1 B1, base.type.prod A2 B2
               => fun '(a, b) '(a', b')
                  => @interp_beq A1 A2 a a' && @interp_beq B1 B2 b b'
             | base.type.list A1, base.type.list A2
               => list_beq_hetero (@interp_beq A1 A2)
             | base.type.option A1, base.type.option A2
               => option_beq_hetero (@interp_beq A1 A2)
             | base.type.type_base _, _
             | base.type.unit, _
             | base.type.prod _ _, _
             | base.type.list _, _
             | base.type.option _, _
               => fun _ _ => false
             end%bool.

        Global Instance reflect_interp_eq {t} : reflect_rel (@eq _) (@interp_beq t t).
        Proof.
          induction t; cbn [interp_beq]; intros; break_innermost_match; try exact _.
        Defined.

        Lemma interp_beq_bl {t x y} : @interp_beq t t x y = true -> x = y.
        Proof. apply reflect_to_beq; exact _. Qed.
        Lemma interp_beq_lb {t x y} : x = y -> @interp_beq t t x y = true.
        Proof. apply reflect_to_beq; exact _. Qed.

        Module option.
          (** turn a [base.type] into a [Set] describing the type
              of optional bounds on that primitive; bounds on a [Z]
              may be either a range, or [None], generally indicating
              that the [Z] is unbounded. *)
          Fixpoint interp (t : base.type) : Type
            := match t with
               | base.type.type_base _ as t
                 => option (base.interp t)
               | base.type.prod A B => interp A * interp B
               | base.type.list A => option (list (interp A))
               | base.type.option A => option (option (interp A))
               | base.type.unit => unit
               end%type.
          Fixpoint map_ranges (f : zrange -> zrange) {t} : interp t -> interp t
            := match t with
               | base.type.type_base _ as t
                 => option_map (@base.map_ranges f t)
               | base.type.prod A B => fun '(a, b) => (@map_ranges f A a, @map_ranges f B b)
               | base.type.list A => option_map (List.map (@map_ranges f A))
               | base.type.option A => option_map (option_map (@map_ranges f A))
               | base.type.unit => fun 'tt => tt
               end%type.
          Fixpoint None {t} : interp t
            := match t with
               | base.type.unit => tt
               | base.type.list _
               | base.type.option _
               | base.type.type_base _
                 => Datatypes.None
               | base.type.prod A B
                 => (@None A, @None B)
               end.
          Fixpoint Some {t} : base.interp t -> interp t
            := match t with
               | base.type.unit
                 => fun _ => tt
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
          Fixpoint is_informative {t} : interp t -> bool (* true iff there's some bounds info *)
            := match t with
               | base.type.type_base _
               | base.type.list _
               | base.type.option _
                 => Option.is_Some
               | base.type.unit
                 => fun _ => false
               | base.type.prod A B
                 => fun '(a, b) => orb (@is_informative A a) (@is_informative B b)
               end.
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
          Fixpoint interp_beq {t1 t2} : interp t1 -> interp t2 -> bool
            := match t1, t2 return interp t1 -> interp t2 -> bool with
               | base.type.type_base _ as t1, base.type.type_base _ as t2 => option_beq_hetero base.interp_beq
               | base.type.prod A1 B1, base.type.prod A2 B2
                 => fun '(a, b) '(a', b')
                    => @interp_beq A1 A2 a a' && @interp_beq B1 B2 b b'
               | base.type.list A1, base.type.list A2
                 => option_beq_hetero (list_beq_hetero (@interp_beq A1 A2))
               | base.type.option A1, base.type.option A2
                 => option_beq_hetero (option_beq_hetero (@interp_beq A1 A2))
               | base.type.unit, base.type.unit => fun 'tt 'tt => true
               | base.type.type_base _, _
               | base.type.unit, _
               | base.type.prod _ _, _
               | base.type.list _, _
               | base.type.option _, _
                 => fun _ _ => false
               end.

          Global Instance reflect_interp_eq {t} : reflect_rel (@eq _) (@interp_beq t t).
          Proof.
            induction t; cbn [interp_beq]; intros; break_innermost_match; try exact _.
          Defined.

          Lemma interp_beq_bl {t x y} : @interp_beq t t x y = true -> x = y.
          Proof. apply reflect_to_beq; exact _. Qed.
          Lemma interp_beq_lb {t x y} : x = y -> @interp_beq t t x y = true.
          Proof. apply reflect_to_beq; exact _. Qed.

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
                           | Z.ltb_to_lt; lia
                           | match goal with
                             | [ H : context[@Compilers.base.interp_beq _ _ ?base_interp_beq ?t] |- _ ]
                               => progress Reflect.reflect_beq_to_eq (@Compilers.base.interp_beq _ _ base_interp_beq t)
                             | [ |- context[@Compilers.base.interp_beq _ _ ?base_interp_beq ?t] ]
                               => progress Reflect.reflect_beq_to_eq (@Compilers.base.interp_beq _ _ base_interp_beq t)
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
      Definition is_tighter_than {t} : interp t -> interp t -> bool
        := match t with
           | type.base x => @base.is_tighter_than x
           | type.arrow s d => fun _ _ => false
           end.
      Definition is_bounded_by {t} : interp t -> einterp t -> bool
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
        Definition Some {t : type base.type} : type.interp t -> interp t
          := match t with
             | type.base x => @base.option.Some x
             | type.arrow s d => fun _ _ => @None d
             end.
        Fixpoint strip_ranges {t : type base.type} : interp t -> interp t
          := match t with
             | type.base x => @base.option.strip_ranges x
             | type.arrow s d => fun f x => @strip_ranges d (f x)
             end.
        Definition is_tighter_than {t} : interp t -> interp t -> bool
          := match t with
             | type.base x => @base.option.is_tighter_than x
             | type.arrow s d => fun _ _ => false
             end.
        Definition is_bounded_by {t} : interp t -> einterp t -> bool
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
        (** Here we guarantee truncating/modular behavior of casting *)
        Definition interp_Z_cast_truncate (r : option zrange) (v : option zrange) : option zrange
          := match interp_Z_cast r v, r with
             | Some x, _ => Some x
             | None, Some r => Some (ZRange.normalize r)
             | None, None => None
             end.
        Local Notation tZ := (base.type.type_base base.type.Z).
        Definition interp {shiftr_avoid_uint1 : shiftr_avoid_uint1_opt} (assume_cast_truncates : bool) {t} (idc : ident t) : type.option.interp t
          := let interp_Z_cast := if assume_cast_truncates then interp_Z_cast_truncate else interp_Z_cast in
             match idc in ident.ident t return type.option.interp t with
             | ident.Literal t v => @of_literal (base.type.type_base t) v
             | ident.comment _
             | ident.comment_no_keep _
               => fun _ => tt
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
             | ident.value_barrier
               => fun x => x
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
             | ident.Z_lxor as idc
             | ident.Z_modulo as idc
             | ident.Build_zrange as idc
               => fun x y => match to_literal x, to_literal y with
                             | Some x, Some y => of_literal (ident.interp idc x y)
                             | _, _ => ZRange.type.base.option.None
                             end
             | ident.Z_ltz as idc
               => fun x y => match to_literal x, to_literal y with
                             | Some x, Some y => of_literal (ident.interp idc x y)
                             | _, _ => Some r[0~>1]
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
                   | Some m, None => (if (0 <? m)%Z
                                           then Some r[0 ~> m-1]
                                           else if (m =? 0)%Z
                                                then ltac:(match eval hnf in (1 mod 0) with | 0 => exact r[0 ~> 0] | _ => exact None (* if `_ mod 0` is not constant and neither is `v`, we do not bother computing the bounds of `Z.lnot v` *) end)
                                                else Some r[m+1 ~> 0])
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
                                               (ZRange.constant (Z.ones (ltac:(match eval hnf in (1 mod 0) with | 0 => exact (Z.max 0 bw) | _ => exact bw end)))))
                                | None, _, _ => None
                                end
             | ident.bool_rect _
               => fun t f b
                 => match b with
                   | Some b => if b then t tt else f tt
                   | None => ZRange.type.base.option.None
                   end
             | ident.bool_rect_nodep _
               => fun t f b
                 => match b with
                   | Some b => if b then t else f
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
             | ident.Z_shiftl as idc
               => fun x y => x <- x; y <- y; Some (ZRange.four_corners_and_zero (ident.interp idc) x y)
             | ident.Z_shiftr as idc
               => fun x y => x <- x; y <- y; Some (let r := ZRange.four_corners_and_zero (ident.interp idc) x y in
                                                   (* kludge to avoid uint1 after >> *)
                                                   if shiftr_avoid_uint1 && (r =? r[0~>1]) then r[0~>2] else r)
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
             | ident.Z_mul_high
               => fun split_at x y
                 => match to_literal split_at, x, y with
                   | Some split_at, Some x, Some y
                     => ZRange.type.base.option.Some
                         (t:=tZ)
                         (snd (ZRange.split_bounds (ZRange.four_corners Z.mul x y) split_at))
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
  Export ZRange.Settings.
End Compilers.
