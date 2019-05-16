Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.PreLanguage.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Local Definition mymap {A B} := Eval cbv in @List.map A B.
Local Definition myapp {A} := Eval cbv in @List.app A.
Local Definition myflatten {A} := Eval cbv in List.fold_right myapp (@nil A).
Local Notation dont_do_again := (pair false) (only parsing).
Local Notation do_again := (pair true) (only parsing).

Local Notation "' x" := (ident.literal x).
Local Notation cstZ := (ident.cast ident.cast_outside_of_range).
Local Notation cstZZ := (ident.cast2 ident.cast_outside_of_range).
Local Notation "'plet' x := y 'in' z"
  := (match y return _ with x => z end).

Local Notation dlet2_opp2 rvc e
  := (plet rvc' := (fst rvc, -snd rvc)%zrange in
          plet cst' := cstZZ rvc' in
          plet cst1 := cstZ (fst rvc%zrange%zrange) in
          plet cst2 := cstZ (snd rvc%zrange%zrange) in
          plet cst2' := cstZ (-snd rvc%zrange%zrange) in
          (dlet vc := cst' e in
               (cst1 (fst (cst' vc)), cst2 (-(cst2' (snd (cst' vc))))))).

Local Notation dlet2 rvc e
  := (dlet vc := cstZZ rvc e in
          (cstZ (fst rvc) (fst (cstZZ rvc vc)),
           cstZ (snd rvc) (snd (cstZZ rvc vc)))).


Local Notation "x '\in' y" := (is_bounded_by_bool x (ZRange.normalize y) = true) : zrange_scope.
Local Notation "x ∈ y" := (is_bounded_by_bool x (ZRange.normalize y) = true) : zrange_scope.
Local Notation "x <= y" := (is_tighter_than_bool (ZRange.normalize x) y = true) : zrange_scope.
Local Notation litZZ x := (ident.literal (fst x), ident.literal (snd x)) (only parsing).
Local Notation n r := (ZRange.normalize r) (only parsing).

Local Ltac generalize_cast' force_progress term :=
  let default _ := lazymatch force_progress with
                   | false => term
                   end in
  lazymatch type of term with
  | Prop => lazymatch term with
            | context[ident.cast_outside_of_range]
              => lazymatch (eval pattern ident.cast_outside_of_range in term) with
                 | (fun x : ?T => ?f) _
                   => constr:(forall x : T, f)
                 end
            | _ => default ()
            end
  | _
    => lazymatch term with
       | context[ident.cast_outside_of_range]
         => let term := match term with
                        | context F[@cons Prop ?x]
                          => let x := generalize_cast' true x in
                             let term := context F[@cons Prop x] in
                             term
                        | context F[@cons (?T * Prop) (?b, ?x)]
                          => let x := generalize_cast' true x in
                             let term := context F[@cons (T * Prop) (b, x)] in
                             term
                        end in
            generalize_cast' false term
       | _ => default ()
       end
  end.
Local Ltac early_unfold_in term := term.
Local Ltac generalize_cast term :=
  let term := early_unfold_in term in
  generalize_cast' false term.

(* Play tricks/games with [match] to get [term] interpreted as a constr rather than an ident when it's not closed, to get better error messages *)
Local Notation generalize_cast term
  := (match term return _ with
      | _TERM => ltac:(let TERM := (eval cbv delta [_TERM] in _TERM) in
                       let res := generalize_cast TERM in
                       exact res)
      end) (only parsing).

Local Notation myflatten_generalize_cast x
  := (myflatten (generalize_cast x)) (only parsing).

(* N.B. [ident.eagerly] does not play well with [do_again] *)
Definition nbe_rewrite_rulesT : list (bool * Prop)
  := Eval cbv [myapp mymap myflatten] in
      myflatten
        [mymap
           dont_do_again
           [(forall A B x y, @fst A B (x, y) = x)
            ; (forall A B x y, @snd A B (x, y) = y)
            ; (forall P t f, @ident.Thunked.bool_rect P t f true = t tt)
            ; (forall P t f, @ident.Thunked.bool_rect P t f false = f tt)
            ; (forall A B C f x y, @prod_rect A B (fun _ => C) f (x, y) = f x y)

            ; (forall A x n,
                  @List.repeat A x ('n)
                  = ident.eagerly (@nat_rect) _ nil (fun k repeat_k => x :: repeat_k) ('n))
            ; (forall A xs ys,
                  xs ++ ys
                  = ident.eagerly (@list_rect) A _ ys (fun x xs app_xs_ys => x :: app_xs_ys) xs)
            ; (forall A B f a ls,
                  @fold_right A B f a ls
                  = (ident.eagerly (@list_rect) _ _)
                      a
                      (fun x xs fold_right_xs => f x fold_right_xs)
                      ls)
            ; (forall A P N C ls,
                  @ident.Thunked.list_rect A P N C ls
                  = ident.eagerly (@ident.Thunked.list_rect) A P N C ls)
            ; (forall A P Q N C ls v,
                  @list_rect A (fun _ => P -> Q) N C ls v
                  = ident.eagerly (@list_rect) A (fun _ => P -> Q) N C ls v)
            ; (forall A P N C, @ident.Thunked.list_case A P N C nil = N tt)
            ; (forall A P N C x xs, @ident.Thunked.list_case A P N C (x :: xs) = C x xs)
            ; (forall A B f ls,
                  @List.map A B f ls
                  = (ident.eagerly (@list_rect) _ _)
                      nil
                      (fun x xs map_f_xs => f x :: map_f_xs)
                      ls)
            ; (forall P O_case S_case n,
                  @ident.Thunked.nat_rect P O_case S_case ('n)
                  = (ident.eagerly (@ident.Thunked.nat_rect) _)
                      O_case
                      S_case
                      ('n))
            ; (forall P Q O_case S_case n v,
                  @nat_rect (fun _ => P -> Q) O_case S_case ('n) v
                  = (ident.eagerly (@nat_rect) _)
                      O_case
                      S_case
                      ('n)
                      v)
            ; (forall A default ls n,
                  @List.nth_default A default ls ('n)
                  = ident.eagerly (@List.nth_default) _ default ls ('n))
           ]
         ; mymap
             do_again
             [(forall A B xs ys,
                  @List.combine A B xs ys
                  = (list_rect _)
                      (fun _ => nil)
                      (fun x xs combine_xs ys
                       => match ys with
                          | nil => nil
                          | y :: ys => (x, y) :: combine_xs ys
                          end)
                      xs
                      ys)
              ; (forall A n ls,
                    @List.firstn A ('n) ls
                    = (nat_rect _)
                        (fun _ => nil)
                        (fun n' firstn_n' ls
                         => match ls with
                            | nil => nil
                            | cons x xs => x :: firstn_n' xs
                            end)
                        ('n)
                        ls)
              ; (forall A n ls,
                    @List.skipn A ('n) ls
                    = (nat_rect _)
                        (fun ls => ls)
                        (fun n' skipn_n' ls
                         => match ls with
                            | nil => nil
                            | cons x xs => skipn_n' xs
                            end)
                        ('n)
                        ls)
              ; (forall A xs,
                    @List.length A xs
                    = (list_rect _)
                        0%nat
                        (fun _ xs length_xs => S length_xs)
                        xs)
              ; (forall A xs,
                    @List.rev A xs
                    = (list_rect _)
                        nil
                        (fun x xs rev_xs => rev_xs ++ [x])
                        xs)
              ; (forall A B f xs,
                    @List.flat_map A B f xs
                    = (list_rect _)
                        nil
                        (fun x _ flat_map_tl => f x ++ flat_map_tl)
                        xs)
              ; (forall A f xs,
                    @List.partition A f xs
                    = (list_rect _)
                        ([], [])
                        (fun x tl partition_tl
                         => let '(g, d) := partition_tl in
                            if f x then (x :: g, d) else (g, x :: d))
                        xs)
              ; (forall A n f xs,
                    @update_nth A ('n) f xs
                    = (nat_rect _)
                        (fun xs => match xs with
                                   | nil => nil
                                   | x' :: xs' => f x' :: xs'
                                   end)
                        (fun n' update_nth_n' xs
                         => match xs with
                            | nil => nil
                            | x' :: xs' => x' :: update_nth_n' xs'
                            end)
                        ('n)
                        xs)
             ]
        ].

Definition arith_rewrite_rulesT (max_const_val : Z) : list (bool * Prop)
  := Eval cbv [myapp mymap myflatten] in
      myflatten
        [mymap
           dont_do_again
           [(forall A B x y, @fst A B (x, y) = x)
            ; (forall A B x y, @snd A B (x, y) = y)
            ; (forall v, 0 + v = v)
            ; (forall v, v + 0 = v)
            ; (forall x y, (-x) + (-y) = -(x + y))
            ; (forall x y, (-x) +   y  = y - x)
            ; (forall x y,   x  + (-y) = x - y)

            ; (forall v, 0 - (-v) = v)
            ; (forall v, 0 -   v  = -v)
            ; (forall v, v -   0  = v)
            ; (forall x y, (-x) - (-y) = y - x)
            ; (forall x y, (-x) -   y  = -(x + y))
            ; (forall x y,   x  - (-y) = x + y)

            ; (forall v, 0 * v = 0)
            ; (forall v, v * 0 = 0)
            ; (forall v, 1 * v = v)
            ; (forall v, v * 1 = v)
            ; (forall v, (-1) * (-v) = v)
            ; (forall v, (-v) * (-1) = v)
            ; (forall v, (-1) *   v  = -v)
            ; (forall v,   v  * (-1) = -v)
            ; (forall x y, (-x) * (-y) = x * y)
            ; (forall x y, (-x) *   y  = -(x * y))
            ; (forall x y,   x  * (-y) = -(x * y))

            ; (forall x, x &' 0 = 0)

            ; (forall x, x / 1 = x)
            ; (forall x, x mod 1 = 0)

            ; (forall v, -(-v) = v)

            ; (forall z v, z > 0 ->  'z  + (-v) = 'z - v)
            ; (forall z v, z > 0 -> (-v) +  'z  = 'z - v)
            ; (forall z v, z < 0 ->  'z  + (-v) = -('(-z) + v))
            ; (forall z v, z < 0 -> (-v) +  'z  = -(v + '(-z)))

            ; (forall z v, z > 0 ->  'z  - (-v) = 'z + v)
            ; (forall z v, z < 0 ->  'z  - (-v) = v - '(-z))
            ; (forall z v, z < 0 ->  'z  -   v  = -('(-z) + v))
            ; (forall z v, z > 0 -> (-v) -  'z  = -(v + 'z))
            ; (forall z v, z < 0 -> (-v) -  'z  = '(-z) - v)
            ; (forall z v, z < 0 ->   v  -  'z  = v + '(-z))

            ; (forall x y, 'x * 'y = '(x*y))
            ; (forall z v, z < 0 -> 'z *  v = -('(-z) * v))
            ; (forall z v, z < 0 ->  v * 'z = -(v * '(-z)))

            ; (forall x y, y = 2^Z.log2 y -> y <> 2 ->  x * 'y = x << '(Z.log2 y))
            ; (forall x y, y = 2^Z.log2 y -> y <> 2 -> 'y *  x = x << '(Z.log2 y))

            ; (forall x y, y = 2^Z.log2 y -> x / 'y = x >> '(Z.log2 y))
            ; (forall x y, y = 2^Z.log2 y -> x mod 'y = x &' '(y-1))

            (* We reassociate some multiplication of small constants  *)
            ; (forall c1 c2 x y,
                  Z.abs c1 <= Z.abs max_const_val
                  -> Z.abs c2 <= Z.abs max_const_val
                  -> 'c1 * ('c2 * (x * y)) = (x * (y * ('c1 * 'c2))))
            ; (forall c1 c2 x y,
                  Z.abs c1 <= Z.abs max_const_val
                  -> Z.abs c2 <= Z.abs max_const_val
                  -> 'c1 * (x * (y * 'c2)) = (x * (y * ('c1 * 'c2))))
            ; (forall c x y,
                  Z.abs c <= Z.abs max_const_val
                  -> 'c * (x * y) = x * (y * 'c))
            ; (forall c x,
                  Z.abs c <= Z.abs max_const_val
                  -> 'c * x = x * 'c)

            (* transform +- to + *)
            ; (forall s y x,
                  Z.add_get_carry_full s x (- y)
                  = dlet vb := Z.sub_get_borrow_full s x y in (fst vb, - snd vb))
            ; (forall s y x,
                  Z.add_get_carry_full s (- y) x
                  = dlet vb := Z.sub_get_borrow_full s x y in (fst vb, - snd vb))
            ; (forall s y x,
                  Z.add_with_get_carry_full s 0 x (- y)
                  = dlet vb := Z.sub_get_borrow_full s x y in (fst vb, - snd vb))
            ; (forall s y x,
                  Z.add_with_get_carry_full s 0 (- y) x
                  = dlet vb := Z.sub_get_borrow_full s x y in (fst vb, - snd vb))
            ; (forall s c y x,
                  Z.add_with_get_carry_full s (- c) (- y) x
                  = dlet vb := Z.sub_with_get_borrow_full s c x y in (fst vb, - snd vb))
            ; (forall s c y x,
                  Z.add_with_get_carry_full s (- c) x (- y)
                  = dlet vb := Z.sub_with_get_borrow_full s c x y in (fst vb, - snd vb))
            ; (forall b x, (* inline negation when the rewriter wouldn't already inline it *)
                  ident.gets_inlined b x = false
                  -> -x = dlet v := x in -v)
           ]
        ].

Definition arith_with_casts_rewrite_rulesT : list (bool * Prop)
  := Eval cbv [myapp mymap myflatten] in
      myflatten_generalize_cast
        [mymap
           dont_do_again
           [(forall A B x y, @fst A B (x, y) = x)
            ; (forall A B x y, @snd A B (x, y) = y)
            ; (forall r v, lower r = upper r -> cstZ r v = cstZ r ('(lower r)))
            ; (forall r0 v, 0 ∈ r0 -> cstZ r0 0 + v = v)
            ; (forall r0 v, 0 ∈ r0 -> v + cstZ r0 0 = v)
            ; (forall r0 v, 0 ∈ r0 -> cstZ r0 0 - v = -v)
            ; (forall r0 v, 0 ∈ r0 -> cstZ r0 0 << v = 0)
            ; (forall r0 rnv rv v,
                  (rv <= -n rnv)%zrange -> 0 ∈ r0
                  -> cstZ r0 0 - cstZ rnv (-(cstZ rv v)) = cstZ rv v)
            ; (forall rnv rv v,
                  (rv <= -n rnv)%zrange
                  -> -(cstZ rnv (-(cstZ rv v))) = cstZ rv v)

            ; (forall s r0 y, 0 ∈ r0 -> Z.mul_split s (cstZ r0 0) y = (cstZ r[0~>0] 0, cstZ r[0~>0] 0))
            ; (forall s r0 y, 0 ∈ r0 -> Z.mul_split s y (cstZ r0 0) = (cstZ r[0~>0] 0, cstZ r[0~>0] 0))
            ; (forall rs s r1 ry y,
                  1 ∈ r1 -> s ∈ rs -> (ry <= r[0~>s-1])%zrange
                  -> Z.mul_split (cstZ rs ('s)) (cstZ r1 1) (cstZ ry y)
                     = (cstZ ry y, cstZ r[0~>0] 0))
            ; (forall rs s r1 ry y,
                  1 ∈ r1 -> s ∈ rs -> (ry <= r[0~>s-1])%zrange
                  -> Z.mul_split (cstZ rs ('s)) (cstZ ry y) (cstZ r1 1)
                     = (cstZ ry y, cstZ r[0~>0] 0))

            ; (forall rvc s rny ry y x,
                  (ry <= -n rny)%zrange
                  -> cstZZ rvc (Z.add_get_carry_full s (cstZ rny (-cstZ ry y)) x)
                     = dlet2_opp2 rvc (Z.sub_get_borrow_full s x (cstZ ry y)))
            ; (forall rvc s rny ry y x,
                  (ry <= -n rny)%zrange
                  -> cstZZ rvc (Z.add_get_carry_full s x (cstZ rny (-cstZ ry y)))
                     = dlet2_opp2 rvc (Z.sub_get_borrow_full s x (cstZ ry y)))
            ; (forall rvc s ryy yy x,
                  yy ∈ ryy -> yy < 0
                  -> cstZZ rvc (Z.add_get_carry_full s (cstZ ryy ('yy)) x)
                     = dlet2_opp2 rvc (Z.sub_get_borrow_full s x (cstZ (-ryy) ('(-yy)))))
            ; (forall rvc s ryy yy x,
                  yy ∈ ryy -> yy < 0
                  -> cstZZ rvc (Z.add_get_carry_full s x (cstZ ryy ('yy)))
                     = dlet2_opp2 rvc (Z.sub_get_borrow_full s x (cstZ (-ryy) ('(-yy)))))
            ; (forall rvc s rnc rc c rny ry y x,
                  (ry <= -n rny)%zrange -> (rc <= -n rnc)%zrange
                  -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ rnc (-cstZ rc c)) (cstZ rny (-cstZ ry y)) x)
                     = dlet2_opp2 rvc (Z.sub_with_get_borrow_full s (cstZ rc c) x (cstZ ry y)))
            ; (forall rvc s rnc rc c rny ry y x,
                  (ry <= -n rny)%zrange -> (rc <= -n rnc)%zrange
                  -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ rnc (-cstZ rc c)) x (cstZ rny (-cstZ ry y)))
                     = dlet2_opp2 rvc (Z.sub_with_get_borrow_full s (cstZ rc c) x (cstZ ry y)))
            ; (forall rvc s r0 rny ry y x,
                  0 ∈ r0 -> (ry <= -n rny)%zrange
                  -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ r0 0) (cstZ rny (-cstZ ry y)) x)
                     = dlet2_opp2 rvc (Z.sub_get_borrow_full s x (cstZ ry y)))
            ; (forall rvc s rcc cc rny ry y x,
                  cc < 0 -> cc ∈ rcc -> (ry <= -n rny)%zrange
                  -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ rcc ('cc)) (cstZ rny (-cstZ ry y)) x)
                     = dlet2_opp2 rvc (Z.sub_with_get_borrow_full s (cstZ (-rcc) ('(-cc))) x (cstZ ry y)))
            ; (forall rvc s r0 rny ry y x,
                  0 ∈ r0 -> (ry <= -n rny)%zrange
                  -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ r0 0) x (cstZ rny (-cstZ ry y)))
                     = dlet2_opp2 rvc (Z.sub_get_borrow_full s x (cstZ ry y)))
            ; (forall rvc s rcc cc rny ry y x,
                  cc < 0 -> cc ∈ rcc -> (ry <= -n rny)%zrange
                  -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ rcc ('cc)) x (cstZ rny (-cstZ ry y)))
                     = dlet2_opp2 rvc (Z.sub_with_get_borrow_full s (cstZ (-rcc) ('(-cc))) x (cstZ ry y)))
            ; (forall rvc s rnc rc c ryy yy x,
                  yy <= 0 -> yy ∈ ryy -> (rc <= -n rnc)%zrange
                  -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ rnc (-cstZ rc c)) (cstZ ryy ('yy)) x)
                     = dlet2_opp2 rvc (Z.sub_with_get_borrow_full s (cstZ rc c) x (cstZ (-ryy) ('(-yy)))))
            ; (forall rvc s rnc rc c ryy yy x,
                  yy <= 0 -> yy ∈ ryy -> (rc <= -n rnc)%zrange
                  -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ rnc (-cstZ rc c)) x (cstZ ryy ('yy)))
                     = dlet2_opp2 rvc (Z.sub_with_get_borrow_full s (cstZ rc c) x (cstZ (-ryy) ('(-yy)))))
            ; (forall rvc s rcc cc ryy yy x,
                  yy <= 0 -> cc <= 0 -> yy + cc < 0 (* at least one must be strictly negative *) -> yy ∈ ryy -> cc ∈ rcc
                  -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ rcc ('cc)) (cstZ ryy ('yy)) x)
                     = dlet2_opp2 rvc (Z.sub_with_get_borrow_full s (cstZ (-rcc) ('(-cc))) x (cstZ (-ryy) ('(-yy)))))
            ; (forall rvc s rcc cc ryy yy x,
                  yy <= 0 -> cc <= 0 -> yy + cc < 0 (* at least one must be strictly negative *) -> yy ∈ ryy -> cc ∈ rcc
                  -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ rcc ('cc)) x (cstZ ryy ('yy)))
                     = dlet2_opp2 rvc (Z.sub_with_get_borrow_full s (cstZ (-rcc) ('(-cc))) x (cstZ (-ryy) ('(-yy)))))


            ; (forall rs s rxx xx ryy yy,
                  s ∈ rs -> xx ∈ rxx -> yy ∈ ryy
                  -> Z.add_get_carry_full (cstZ rs ('s)) (cstZ rxx ('xx)) (cstZ ryy ('yy))
                     = litZZ (Z.add_get_carry_full s xx yy))
            ; (forall rs s r0 ry y,
                  s ∈ rs -> 0 ∈ r0 -> (ry <= r[0~>s-1])%zrange
                  -> Z.add_get_carry_full (cstZ rs ('s)) (cstZ r0 0) (cstZ ry y)
                     = (cstZ ry y, cstZ r[0~>0] 0))
            ; (forall rs s r0 ry y,
                  s ∈ rs -> 0 ∈ r0 -> (ry <= r[0~>s-1])%zrange
                  -> Z.add_get_carry_full (cstZ rs ('s)) (cstZ ry y) (cstZ r0 0)
                     = (cstZ ry y, cstZ r[0~>0] 0))

            ; (forall r0 x y, 0 ∈ r0 -> Z.add_with_carry (cstZ r0 0) x y = x + y)

            ; (forall rs s rcc cc rxx xx ryy yy,
                  s ∈ rs -> cc ∈ rcc -> xx ∈ rxx -> yy ∈ ryy
                  -> Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rcc ('cc)) (cstZ rxx ('xx)) (cstZ ryy ('yy))
                     = litZZ (Z.add_with_get_carry_full s cc xx yy))
            ; (forall rs s r0c r0x ry y,
                  s ∈ rs -> 0 ∈ r0c -> 0 ∈ r0x -> (ry <= r[0~>s-1])%zrange
                  -> Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ r0c 0) (cstZ r0x 0) (cstZ ry y)
                     = (cstZ ry y, cstZ r[0~>0] 0))
            ; (forall rs s r0c r0x ry y,
                  s ∈ rs -> 0 ∈ r0c -> 0 ∈ r0x -> (ry <= r[0~>s-1])%zrange
                  -> Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ r0c 0) (cstZ ry y) (cstZ r0x 0)
                     = (cstZ ry y, cstZ r[0~>0] 0))

            ; (forall rvc s r0 x y, (* carry = 0: ADC x y -> ADD x y *)
                  0 ∈ r0
                  -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ r0 0) x y)
                     = dlet2 rvc (Z.add_get_carry_full s x y))
            ; (forall rvc rs s rc c r0x r0y, (* ADC 0 0 -> (ADX 0 0, 0) *) (* except we don't do ADX, because C stringification doesn't handle it *)
                  0 ∈ r0x -> 0 ∈ r0y -> (rc <= r[0~>s-1])%zrange -> 0 ∈ snd rvc -> s ∈ rs
                  -> cstZZ rvc (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ r0x 0) (cstZ r0y 0))
                     = (dlet vc := (cstZZ rvc (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ r0x 0) (cstZ r0y 0))) in
                            (cstZ (fst rvc) (fst (cstZZ rvc vc)),
                             cstZ r[0~>0] 0)))

            (* let-bind any adc/sbb/mulx *)
            ; (forall rvc s c x y,
                  cstZZ rvc (Z.add_with_get_carry_full s c x y)
                  = dlet2 rvc (Z.add_with_get_carry_full s c x y))
            ; (forall rv c x y,
                  cstZ rv (Z.add_with_carry c x y)
                  = (dlet vc := cstZ rv (Z.add_with_carry c x y) in
                         cstZ rv vc))
            ; (forall rvc s x y,
                  cstZZ rvc (Z.add_get_carry_full s x y)
                  = dlet2 rvc (Z.add_get_carry_full s x y))
            ; (forall rvc s c x y,
                  cstZZ rvc (Z.sub_with_get_borrow_full s c x y)
                  = dlet2 rvc (Z.sub_with_get_borrow_full s c x y))
            ; (forall rvc s x y,
                  cstZZ rvc (Z.sub_get_borrow_full s x y)
                  = dlet2 rvc (Z.sub_get_borrow_full s x y))
            ; (forall rvc s x y,
                  cstZZ rvc (Z.mul_split s x y)
                  = dlet2 rvc (Z.mul_split s x y))
           ]%Z%zrange
         ; mymap
             do_again
             [ (* [do_again], so that if one of the arguments is concrete, we automatically get the rewrite rule for [Z_cast] applying to it *)
               (forall r x y, cstZZ r (x, y) = (cstZ (fst r) x, cstZ (snd r) y))
             ]
         ; mymap
             dont_do_again
             [(forall r1 r2 x, (r2 <= n r1)%zrange -> cstZ r1 (cstZ r2 x) = cstZ r2 x)
             ]%Z%zrange
        ].

Definition strip_literal_casts_rewrite_rulesT : list (bool * Prop)
  := generalize_cast [dont_do_again (forall rx x, x ∈ rx -> cstZ rx ('x) = 'x)]%Z%zrange.

(** FIXME Don't use [ident.interp] for the fancy identifier rewrite rules *)
Require Import Crypto.Language.
Import Compilers.

Ltac early_unfold_in term ::= (eval cbv [ident.interp ident.to_fancy Option.invert_Some] in term).

Section fancy.
  Context (invert_low invert_high : Z (*log2wordmax*) -> Z -> option Z)
          (value_range flag_range : zrange).

  Definition fancy_rewrite_rulesT : list (bool * Prop)
    := [].

  Local Coercion ZRange.constant : Z >-> zrange. (* for ease of use with sanity-checking bounds *)
  Local Notation bounds1_good f
    := (fun (output x_bs : zrange)
        => is_tighter_than_bool (f (ZRange.normalize x_bs)) (ZRange.normalize output) = true).
  Local Notation bounds2_good f
    := (fun (output x_bs y_bs : zrange)
        => is_tighter_than_bool (f (ZRange.normalize x_bs) (ZRange.normalize y_bs)) (ZRange.normalize output) = true).
  Local Notation range_in_bitwidth r s
    := (is_tighter_than_bool (ZRange.normalize r) r[0~>s-1]%zrange = true).
  Local Notation shiftl_good := (bounds2_good ZRange.shiftl).
  Local Notation shiftr_good := (bounds2_good ZRange.shiftr).
  Local Notation land_good := (bounds2_good ZRange.land).
  Local Notation mul_good := (bounds2_good ZRange.mul).
  Local Notation cc_m_good output s := (bounds1_good (ZRange.cc_m s) output).
  Local Notation lit_good x rx := (is_bounded_by_bool x (ZRange.normalize rx)).

  Definition fancy_with_casts_rewrite_rulesT : list (bool * Prop)
    := Eval cbv [myapp mymap myflatten] in
        myflatten_generalize_cast
          [mymap
             dont_do_again
             [(*
(Z.add_get_carry_concrete 2^256) @@ (?x, ?y << 128) --> (add 128) @@ (x, y)
(Z.add_get_carry_concrete 2^256) @@ (?x << 128, ?y) --> (add 128) @@ (y, x)
(Z.add_get_carry_concrete 2^256) @@ (?x, ?y >> 128) --> (add (- 128)) @@ (x, y)
(Z.add_get_carry_concrete 2^256) @@ (?x >> 128, ?y) --> (add (- 128)) @@ (y, x)
(Z.add_get_carry_concrete 2^256) @@ (?x, ?y)        --> (add 0) @@ (y, x)
               *)
               (forall r rs s rx x rshiftl rland ry y rmask mask roffset offset,
                   s = 2^Z.log2 s -> s ∈ rs -> offset ∈ roffset -> mask ∈ rmask -> shiftl_good rshiftl rland offset -> land_good rland ry mask -> range_in_bitwidth rshiftl s -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                   -> cstZZ r (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rx x) (cstZ rshiftl ((cstZ rland (cstZ ry y &' cstZ rmask ('mask))) << cstZ roffset ('offset))))
                      = cstZZ r (ident.interp (ident.fancy_add (Z.log2 s) (offset)) (cstZ rx x, cstZ ry y)))
               ; (forall r rs s rx x rshiftl rland ry y rmask mask roffset offset,
                     (s = 2^Z.log2 s) -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s) -> s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> shiftl_good rshiftl rland offset -> land_good rland ry mask -> range_in_bitwidth rshiftl s
                     -> cstZZ r (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rx x) (cstZ rshiftl (cstZ rland (cstZ ry y &' cstZ rmask ('mask)) << cstZ roffset ('offset))))
                        = cstZZ r (ident.interp (ident.fancy_add (Z.log2 s) offset) (cstZ rx x, cstZ ry y)))

               ; (forall r rs s rshiftl rland ry y rmask mask roffset offset rx x,
                     s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftl_good rshiftl rland offset -> land_good rland ry mask -> range_in_bitwidth rshiftl s -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                     -> cstZZ r (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rshiftl (Z.shiftl (cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask)))) (cstZ roffset ('offset)))) (cstZ rx x))
                        = cstZZ r (ident.interp (ident.fancy_add (Z.log2 s) offset) (cstZ rx x, cstZ ry y)))

               ; (forall r rs s rx x rshiftr ry y roffset offset,
                     s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                     -> cstZZ r (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rx x) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))))
                        = cstZZ r (ident.interp (ident.fancy_add (Z.log2 s) (-offset)) (cstZ rx x, cstZ ry y)))

               ; (forall r rs s rshiftr ry y roffset offset rx x,
                     s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                     -> cstZZ r (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))) (cstZ rx x))
                        = cstZZ r (ident.interp (ident.fancy_add (Z.log2 s) (-offset)) (cstZ rx x, cstZ ry y)))

               ; (forall r rs s rx x ry y,
                     s ∈ rs -> (s = 2^Z.log2 s) -> range_in_bitwidth ry s
                     -> cstZZ r (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rx x) (cstZ ry y))
                        = cstZZ r (ident.interp (ident.fancy_add (Z.log2 s) 0) (cstZ rx x, cstZ ry y)))

               (*
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x, ?y << 128) --> (addc 128) @@ (c, x, y)
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x << 128, ?y) --> (addc 128) @@ (c, y, x)
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x, ?y >> 128) --> (addc (- 128)) @@ (c, x, y)
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x >> 128, ?y) --> (addc (- 128)) @@ (c, y, x)
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x, ?y)        --> (addc 0) @@ (c, y, x)
                *)
               ; (forall r rs s rc c rx x rshiftl rland ry y rmask mask roffset offset,
                     s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftl_good rshiftl rland offset -> land_good rland ry mask -> range_in_bitwidth rshiftl s -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                     -> cstZZ r (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rx x) (cstZ rshiftl (Z.shiftl (cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask)))) (cstZ roffset ('offset)))))
                        = cstZZ r (ident.interp (ident.fancy_addc (Z.log2 s) offset) (cstZ rc c, cstZ rx x, cstZ ry y)))

               ; (forall r rs s rc c rshiftl rland ry y rmask mask roffset offset rx x,
                     s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftl_good rshiftl rland offset -> range_in_bitwidth rshiftl s -> land_good rland ry mask -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                     -> cstZZ r (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rshiftl (Z.shiftl (cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask)))) (cstZ roffset ('offset)))) (cstZ rx x))
                        = cstZZ r (ident.interp (ident.fancy_addc (Z.log2 s) offset) (cstZ rc c, cstZ rx x, cstZ ry y)))

               ; (forall r rs s rc c rx x rshiftr ry y roffset offset,
                     s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                     -> cstZZ r (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rx x) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))))
                        = cstZZ r (ident.interp (ident.fancy_addc (Z.log2 s) (-offset)) (cstZ rc c, cstZ rx x, cstZ ry y)))

               ; (forall r rs s rc c rshiftr ry y roffset offset rx x,
                     s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                     -> cstZZ r (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))) (cstZ rx x))
                        = cstZZ r (ident.interp (ident.fancy_addc (Z.log2 s) (-offset)) (cstZ rc c, cstZ rx x, cstZ ry y)))

               ; (forall r rs s rc c rx x ry y,
                     s ∈ rs -> (s = 2^Z.log2 s) -> range_in_bitwidth ry s
                     -> cstZZ r (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rx x) (cstZ ry y))
                        = cstZZ r (ident.interp (ident.fancy_addc (Z.log2 s) 0) (cstZ rc c, cstZ rx x, cstZ ry y)))

               (*
(Z.sub_get_borrow_concrete 2^256) @@ (?x, ?y << 128) --> (sub 128) @@ (x, y)
(Z.sub_get_borrow_concrete 2^256) @@ (?x, ?y >> 128) --> (sub (- 128)) @@ (x, y)
(Z.sub_get_borrow_concrete 2^256) @@ (?x, ?y)        --> (sub 0) @@ (y, x)
                *)

               ; (forall r rs s rx x rshiftl rland ry y rmask mask roffset offset,
                     s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftl_good rshiftl rland offset -> range_in_bitwidth rshiftl s -> land_good rland ry mask -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                     -> cstZZ r (Z.sub_get_borrow_full (cstZ rs ('s)) (cstZ rx x) (cstZ rshiftl (Z.shiftl (cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask)))) (cstZ roffset ('offset)))))
                        = cstZZ r (ident.interp (ident.fancy_sub (Z.log2 s) offset) (cstZ rx x, cstZ ry y)))

               ; (forall r rs s rx x rshiftr ry y roffset offset,
                     s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                     -> cstZZ r (Z.sub_get_borrow_full (cstZ rs ('s)) (cstZ rx x) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))))
                        = cstZZ r (ident.interp (ident.fancy_sub (Z.log2 s) (-offset)) (cstZ rx x, cstZ ry y)))

               ; (forall r rs s rx x ry y,
                     s ∈ rs -> (s = 2^Z.log2 s) -> range_in_bitwidth ry s
                     -> cstZZ r (Z.sub_get_borrow_full (cstZ rs ('s)) (cstZ rx x) (cstZ ry y))
                        = cstZZ r (ident.interp (ident.fancy_sub (Z.log2 s) 0) (cstZ rx x, cstZ ry y)))

               (*
(Z.sub_with_get_borrow_concrete 2^256) @@ (?c, ?x, ?y << 128) --> (subb 128) @@ (c, x, y)
(Z.sub_with_get_borrow_concrete 2^256) @@ (?c, ?x, ?y >> 128) --> (subb (- 128)) @@ (c, x, y)
(Z.sub_with_get_borrow_concrete 2^256) @@ (?c, ?x, ?y)        --> (subb 0) @@ (c, y, x)
                *)

               ; (forall r rs s rb b rx x rshiftl rland ry y rmask mask roffset offset,
                     s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftl_good rshiftl rland offset -> range_in_bitwidth rshiftl s -> land_good rland ry mask -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                     -> cstZZ r (Z.sub_with_get_borrow_full (cstZ rs ('s)) (cstZ rb b) (cstZ rx x) (cstZ rshiftl (Z.shiftl (cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask)))) (cstZ roffset ('offset)))))
                        = cstZZ r (ident.interp (ident.fancy_subb (Z.log2 s) offset) (cstZ rb b, cstZ rx x, cstZ ry y)))

               ; (forall r rs s rb b rx x rshiftr ry y roffset offset,
                     s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                     -> cstZZ r (Z.sub_with_get_borrow_full (cstZ rs ('s)) (cstZ rb b) (cstZ rx x) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))))
                        = cstZZ r (ident.interp (ident.fancy_subb (Z.log2 s) (-offset)) (cstZ rb b, cstZ rx x, cstZ ry y)))

               ; (forall r rs s rb b rx x ry y,
                     s ∈ rs -> (s = 2^Z.log2 s) -> range_in_bitwidth ry s
                     -> cstZZ r (Z.sub_with_get_borrow_full (cstZ rs ('s)) (cstZ rb b) (cstZ rx x) (cstZ ry y))
                        = cstZZ r (ident.interp (ident.fancy_subb (Z.log2 s) 0) (cstZ rb b, cstZ rx x, cstZ ry y)))

               (*(Z.rshi_concrete 2^256 ?n) @@ (?c, ?x, ?y) --> (rshi n) @@ (x, y)*)

               ; (forall r rs s rx x ry y rn n,
                     s ∈ rs -> n ∈ rn -> (s = 2^Z.log2 s)
                     -> cstZ r (Z.rshi (cstZ rs ('s)) (cstZ rx x) (cstZ ry y) (cstZ rn ('n)))
                        = cstZ r (ident.interp (ident.fancy_rshi (Z.log2 s) n) (cstZ rx x, cstZ ry y)))

               (*
Z.zselect @@ (Z.cc_m_concrete 2^256 ?c, ?x, ?y) --> selm @@ (c, x, y)
Z.zselect @@ (?c &' 1, ?x, ?y)                  --> sell @@ (c, x, y)
Z.zselect @@ (?c, ?x, ?y)                       --> selc @@ (c, x, y)
                *)
               ; (forall r rccm rs s rc c rx x ry y,
                     s ∈ rs -> (s = 2^Z.log2 s) -> cc_m_good rccm s rc
                     -> cstZ r (Z.zselect (cstZ rccm (Z.cc_m (cstZ rs ('s)) (cstZ rc c))) (cstZ rx x) (cstZ ry y))
                        = cstZ r (ident.interp (ident.fancy_selm (Z.log2 s)) (cstZ rc c, cstZ rx x, cstZ ry y)))

               ; (forall r rland r1 rc c rx x ry y,
                     1 ∈ r1 -> land_good rland 1 rc
                     -> cstZ r (Z.zselect (cstZ rland (cstZ r1 1 &' cstZ rc c)) (cstZ rx x) (cstZ ry y))
                        = cstZ r (ident.interp ident.fancy_sell (cstZ rc c, cstZ rx x, cstZ ry y)))

               ; (forall r rland rc c r1 rx x ry y,
                     1 ∈ r1 -> land_good rland rc 1
                     -> cstZ r (Z.zselect (cstZ rland (cstZ rc c &' cstZ r1 1)) (cstZ rx x) (cstZ ry y))
                        = cstZ r (ident.interp ident.fancy_sell (cstZ rc c, cstZ rx x, cstZ ry y)))

               ; (forall r c x y,
                     cstZ r (Z.zselect c x y)
                     = cstZ r (ident.interp ident.fancy_selc (c, x, y)))

               (*Z.add_modulo @@ (?x, ?y, ?m) --> addm @@ (x, y, m)*)
               ; (forall x y m,
                     Z.add_modulo x y m
                     = ident.interp ident.fancy_addm (x, y, m))

               (*
Z.mul @@ (?x &' (2^128-1), ?y &' (2^128-1)) --> mulll @@ (x, y)
Z.mul @@ (?x &' (2^128-1), ?y >> 128)       --> mullh @@ (x, y)
Z.mul @@ (?x >> 128, ?y &' (2^128-1))       --> mulhl @@ (x, y)
Z.mul @@ (?x >> 128, ?y >> 128)             --> mulhh @@ (x, y)
                *)
               (* literal on left *)
               ; (forall r rx x rland ry y rmask mask,
                     plet s := (2*Z.log2_up mask)%Z in
                      plet xo := invert_low s x in
                      plet xv := match xo with Some x => x | None => 0 end in
                      xo <> None -> x ∈ rx -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland ry mask
                      -> cstZ r (cstZ rx ('x) * cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask))))
                         = cstZ r (ident.interp (ident.fancy_mulll s) ('xv, cstZ ry y)))

               ; (forall r rx x rland rmask mask ry y,
                     plet s := (2*Z.log2_up mask)%Z in
                      plet xo := invert_low s x in
                      plet xv := match xo with Some x => x | None => 0 end in
                      xo <> None -> x ∈ rx -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland mask ry
                      -> cstZ r (cstZ rx ('x) * cstZ rland (Z.land (cstZ rmask ('mask)) (cstZ ry y)))
                         = cstZ r (ident.interp (ident.fancy_mulll s) ('xv, cstZ ry y)))

               ; (forall r rx x rshiftr ry y roffset offset,
                     plet s := (2*offset)%Z in
                      plet xo := invert_low s x in
                      plet xv := match xo with Some x => x | None => 0 end in
                      xo <> None -> x ∈ rx -> offset ∈ roffset -> shiftr_good rshiftr ry offset
                      -> cstZ r (cstZ rx ('x) * cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset))))
                         = cstZ r (ident.interp (ident.fancy_mullh s) ('xv, cstZ ry y)))

               ; (forall r rx x rland rmask mask ry y,
                     plet s := (2*Z.log2_up mask)%Z in
                      plet xo := invert_high s x in
                      plet xv := match xo with Some x => x | None => 0 end in
                      xo <> None -> x ∈ rx -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland mask ry
                      -> cstZ r (cstZ rx ('x) * cstZ rland (Z.land (cstZ rmask ('mask)) (cstZ ry y)))
                         = cstZ r (ident.interp (ident.fancy_mulhl s) ('xv, cstZ ry y)))

               ; (forall r rx x rland ry y rmask mask,
                     plet s := (2*Z.log2_up mask)%Z in
                      plet xo := invert_high s x in
                      plet xv := match xo with Some x => x | None => 0 end in
                      xo <> None -> x ∈ rx -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland ry mask
                      -> cstZ r (cstZ rx ('x) * cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask))))
                         = cstZ r (ident.interp (ident.fancy_mulhl s) ('xv, cstZ ry y)))

               ; (forall r rx x rshiftr ry y roffset offset,
                     plet s := (2*offset)%Z in
                      plet xo := invert_high s x in
                      plet xv := match xo with Some x => x | None => 0 end in
                      xo <> None -> x ∈ rx -> offset ∈ roffset -> shiftr_good rshiftr ry offset
                      -> cstZ r (cstZ rx ('x) * cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset))))
                         = cstZ r (ident.interp (ident.fancy_mulhh s) ('xv, cstZ ry y)))

               (* literal on right *)
               ; (forall r rland rmask mask rx x ry y,
                     plet s := (2*Z.log2_up mask)%Z in
                      plet yo := invert_low s y in
                      plet yv := match yo with Some y => y | None => 0 end in
                      yo <> None -> y ∈ ry -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland mask rx
                      -> cstZ r (cstZ rland (Z.land (cstZ rmask ('mask)) (cstZ rx x)) * cstZ ry ('y))
                         = cstZ r (ident.interp (ident.fancy_mulll s) (cstZ rx x, 'yv)))

               ; (forall r rland rx x rmask mask ry y,
                     plet s := (2*Z.log2_up mask)%Z in
                      plet yo := invert_low s y in
                      plet yv := match yo with Some y => y | None => 0 end in
                      yo <> None -> y ∈ ry -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland rx mask
                      -> cstZ r (cstZ rland (Z.land (cstZ rx x) (cstZ rmask ('mask))) * cstZ ry ('y))
                         = cstZ r (ident.interp (ident.fancy_mulll s) (cstZ rx x, 'yv)))

               ; (forall r rland rmask mask rx x ry y,
                     plet s := (2*Z.log2_up mask)%Z in
                      plet yo := invert_high s y in
                      plet yv := match yo with Some y => y | None => 0 end in
                      yo <> None -> y ∈ ry -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland mask rx
                      -> cstZ r (cstZ rland (Z.land (cstZ rmask ('mask)) (cstZ rx x)) * cstZ ry ('y))
                         = cstZ r (ident.interp (ident.fancy_mullh s) (cstZ rx x, 'yv)))

               ; (forall r rland rx x rmask mask ry y,
                     plet s := (2*Z.log2_up mask)%Z in
                      plet yo := invert_high s y in
                      plet yv := match yo with Some y => y | None => 0 end in
                      yo <> None -> y ∈ ry -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland rx mask
                      -> cstZ r (cstZ rland (Z.land (cstZ rx x) (cstZ rmask ('mask))) * cstZ ry ('y))
                         = cstZ r (ident.interp (ident.fancy_mullh s) (cstZ rx x, 'yv)))

               ; (forall r rshiftr rx x roffset offset ry y,
                     plet s := (2*offset)%Z in
                      plet yo := invert_low s y in
                      plet yv := match yo with Some y => y | None => 0 end in
                      yo <> None -> y ∈ ry -> offset ∈ roffset -> shiftr_good rshiftr rx offset
                      -> cstZ r (cstZ rshiftr (Z.shiftr (cstZ rx x) (cstZ roffset ('offset))) * cstZ ry ('y))
                         = cstZ r (ident.interp (ident.fancy_mulhl s) (cstZ rx x, 'yv)))

               ; (forall r rshiftr rx x roffset offset ry y,
                     plet s := (2*offset)%Z in
                      plet yo := invert_high s y in
                      plet yv := match yo with Some y => y | None => 0 end in
                      yo <> None -> y ∈ ry -> offset ∈ roffset -> shiftr_good rshiftr rx offset
                      -> cstZ r (cstZ rshiftr (Z.shiftr (cstZ rx x) (cstZ roffset ('offset))) * cstZ ry ('y))
                         = cstZ r (ident.interp (ident.fancy_mulhh s) (cstZ rx x, 'yv)))

               (* no literal *)
               ; (forall r rland1 rmask1 mask1 rx x rland2 rmask2 mask2 ry y,
                     plet s := (2*Z.log2_up mask1)%Z in
                      mask1 ∈ rmask1 -> mask2 ∈ rmask2 -> (mask1 = 2^(s/2)-1) -> (mask2 = 2^(s/2)-1) -> land_good rland1 mask1 rx -> land_good rland2 mask2 ry
                      -> cstZ r (cstZ rland1 (Z.land (cstZ rmask1 ('mask1)) (cstZ rx x)) * cstZ rland2 (Z.land (cstZ rmask2 ('mask2)) (cstZ ry y)))
                         = cstZ r (ident.interp (ident.fancy_mulll s) (cstZ rx x, cstZ ry y)))

               ; (forall r rland1 rx x rmask1 mask1 rland2 rmask2 mask2 ry y,
                     plet s := (2*Z.log2_up mask1)%Z in
                      mask1 ∈ rmask1 -> mask2 ∈ rmask2 -> (mask1 = 2^(s/2)-1) -> (mask2 = 2^(s/2)-1) -> land_good rland1 rx mask1 -> land_good rland2 mask2 ry
                      -> cstZ r (cstZ rland1 (Z.land (cstZ rx x) (cstZ rmask1 ('mask1))) * cstZ rland2 (Z.land (cstZ rmask2 ('mask2)) (cstZ ry y)))
                         = cstZ r (ident.interp (ident.fancy_mulll s) (cstZ rx x, cstZ ry y)))

               ; (forall r rland1 rmask1 mask1 rx x rland2 ry y rmask2 mask2,
                     plet s := (2*Z.log2_up mask1)%Z in
                      mask1 ∈ rmask1 -> mask2 ∈ rmask2 -> (mask1 = 2^(s/2)-1) -> (mask2 = 2^(s/2)-1) -> land_good rland1 mask1 rx -> land_good rland2 ry mask2
                      -> cstZ r (cstZ rland1 (Z.land (cstZ rmask1 ('mask1)) (cstZ rx x)) * cstZ rland2 (Z.land (cstZ ry y) (cstZ rmask2 ('mask2))))
                         = cstZ r (ident.interp (ident.fancy_mulll s) (cstZ rx x, cstZ ry y)))

               ; (forall r rland1 rx x rmask1 mask1 rland2 ry y rmask2 mask2,
                     plet s := (2*Z.log2_up mask1)%Z in
                      mask1 ∈ rmask1 -> mask2 ∈ rmask2 -> (mask1 = 2^(s/2)-1) -> (mask2 = 2^(s/2)-1) -> land_good rland1 rx mask1 -> land_good rland2 ry mask2
                      -> cstZ r (cstZ rland1 (Z.land (cstZ rx x) (cstZ rmask1 ('mask1))) * cstZ rland2 (Z.land (cstZ ry y) (cstZ rmask2 ('mask2))))
                         = cstZ r (ident.interp (ident.fancy_mulll s) (cstZ rx x, cstZ ry y)))

               ; (forall r rland1 rmask mask rx x rshiftr2 ry y roffset offset,
                     plet s := (2*offset)%Z in
                      mask ∈ rmask -> offset ∈ roffset -> (mask = 2^(s/2)-1) -> land_good rland1 mask rx -> shiftr_good rshiftr2 ry offset
                      -> cstZ r (cstZ rland1 (Z.land (cstZ rmask ('mask)) (cstZ rx x)) * cstZ rshiftr2 (Z.shiftr (cstZ ry y) (cstZ roffset ('offset))))
                         = cstZ r (ident.interp (ident.fancy_mullh s) (cstZ rx x, cstZ ry y)))

               ; (forall r rland1 rx x rmask mask rshiftr2 ry y roffset offset,
                     plet s := (2*offset)%Z in
                      mask ∈ rmask -> offset ∈ roffset -> (mask = 2^(s/2)-1) -> land_good rland1 rx mask -> shiftr_good rshiftr2 ry offset
                      -> cstZ r (cstZ rland1 (Z.land (cstZ rx x) (cstZ rmask ('mask))) * cstZ rshiftr2 (Z.shiftr (cstZ ry y) (cstZ roffset ('offset))))
                         = cstZ r (ident.interp (ident.fancy_mullh s) (cstZ rx x, cstZ ry y)))

               ; (forall r rshiftr1 rx x roffset offset rland2 rmask mask ry y,
                     plet s := (2*offset)%Z in
                      mask ∈ rmask -> offset ∈ roffset -> (mask = 2^(s/2)-1) -> shiftr_good rshiftr1 rx offset -> land_good rland2 mask ry
                      -> cstZ r (cstZ rshiftr1 (Z.shiftr (cstZ rx x) (cstZ roffset ('offset))) * cstZ rland2 (Z.land (cstZ rmask ('mask)) (cstZ ry y)))
                         = cstZ r (ident.interp (ident.fancy_mulhl s) (cstZ rx x, cstZ ry y)))

               ; (forall r rshiftr1 rx x roffset offset rland2 ry y rmask mask,
                     plet s := (2*offset)%Z in
                      mask ∈ rmask -> offset ∈ roffset -> (mask = 2^(s/2)-1) -> shiftr_good rshiftr1 rx offset -> land_good rland2 ry mask
                      -> cstZ r (cstZ rshiftr1 (Z.shiftr (cstZ rx x) (cstZ roffset ('offset))) * cstZ rland2 (Z.land (cstZ ry y) (cstZ rmask ('mask))))
                         = cstZ r (ident.interp (ident.fancy_mulhl s) (cstZ rx x, cstZ ry y)))

               ; (forall r rshiftr1 rx x roffset1 offset1 rshiftr2 ry y roffset2 offset2,
                     plet s := (2*offset1)%Z in
                      offset1 ∈ roffset1 -> offset2 ∈ roffset2 -> (offset1 = offset2) -> shiftr_good rshiftr1 rx offset1 -> shiftr_good rshiftr2 ry offset2
                      -> cstZ r (cstZ rshiftr1 (Z.shiftr (cstZ rx x) (cstZ roffset1 ('offset1))) * cstZ rshiftr2 (Z.shiftr (cstZ ry y) (cstZ roffset2 ('offset2))))
                         = cstZ r (ident.interp (ident.fancy_mulhh s) (cstZ rx x, cstZ ry y)))

               (** Dummy rule to make sure we use the two value ranges; this can be removed *)
               ; (forall rx x,
                     ((is_tighter_than_bool rx value_range = true)
                      \/ (is_tighter_than_bool rx flag_range = true))
                     -> cstZ rx x = cstZ rx x)
             ]%Z%zrange
          ].
End fancy.

Section with_bitwidth.
  Context (bitwidth : Z)
          (lgcarrymax : Z).

  Local Notation doublewidth := (cstZ r[0~>2^(2*bitwidth) - 1]).
  Local Notation singlewidth := (cstZ r[0~>2^bitwidth - 1]).
  Local Notation carrymax := (2^lgcarrymax-1).
  Local Notation carrywidth := (cstZ r[0~>carrymax]).
  Local Notation singlewidth_carry := (cstZZ (r[0~>2^bitwidth - 1], r[0~>carrymax])%zrange).
  Local Notation alt_singlewidth_carry := (cstZZ (r[0~>2^bitwidth - 1], r[0~>2^bitwidth-1])%zrange).
  Local Notation pairsinglewidth := (cstZZ (r[0~>2^bitwidth - 1], r[0~>2^bitwidth - 1])%zrange).
  Local Notation cstZsingle_to_double l h
    := (doublewidth (Z.combine_at_bitwidth ('bitwidth) (singlewidth l) (singlewidth h))).
  Local Notation cstZsingle_to_double_pair lh
    := (cstZsingle_to_double (fst lh) (snd lh)).

  Definition mul_split_rewrite_rulesT : Datatypes.list (Datatypes.bool * Prop)
    := Eval cbv [myapp mymap myflatten] in
        myflatten_generalize_cast
          [mymap
             dont_do_again
             [(forall r x, cstZ r (cstZ r x) = cstZ r x) (* when inlining Z.combine_at_bitwidth, casts will sometimes get doubled up, so we need to strip the extra casts *)
              ; (forall x y,
                    doublewidth (singlewidth x * singlewidth y)
                    = (dlet lh := pairsinglewidth (Z.mul_split ('(2^bitwidth)) (singlewidth x) (singlewidth y)) in
                           cstZsingle_to_double_pair lh))
              ; (forall xl xh yl yh,
                    doublewidth (cstZsingle_to_double xl xh + cstZsingle_to_double yl yh)
                    = (dlet lc := singlewidth_carry (Z.add_get_carry_full ('(2^bitwidth)) (singlewidth xl) (singlewidth yl)) in
                           dlet hc := singlewidth_carry (Z.add_with_get_carry_full ('(2^bitwidth)) (carrywidth (snd lc)) (singlewidth xh) (singlewidth yh)) in
                           cstZsingle_to_double (fst lc) (fst hc)))
              ; (forall x yl yh,
                    doublewidth (singlewidth x + cstZsingle_to_double yl yh)
                    = (dlet lc := singlewidth_carry (Z.add_get_carry_full ('(2^bitwidth)) (singlewidth x) (singlewidth yl)) in
                           dlet h := singlewidth (Z.add(*_with_carry*) (carrywidth (snd lc)) (*(singlewidth ('0))*) (singlewidth yh)) in
                           cstZsingle_to_double (fst lc) h))
              ; (forall xl xh y,
                    doublewidth (cstZsingle_to_double xl xh + singlewidth y)
                    = (dlet lc := singlewidth_carry (Z.add_get_carry_full ('(2^bitwidth)) (singlewidth xl) (singlewidth y)) in
                           dlet h := singlewidth (Z.add(*_with_carry*) (carrywidth (snd lc)) (singlewidth xh) (*(singlewidth ('0))*)) in
                           cstZsingle_to_double (fst lc) h))
              ; (forall xl xh mask,
                    0 <= mask < 2^bitwidth
                    -> singlewidth (cstZsingle_to_double xl xh &' singlewidth ('mask))
                       = singlewidth (singlewidth xl &' singlewidth ('mask)))
              ; (forall xl xh mask,
                    0 <= mask < 2^bitwidth
                    -> singlewidth (singlewidth ('mask) &' cstZsingle_to_double xl xh)
                       = singlewidth (singlewidth ('mask) &' singlewidth xl))
              ; (forall xl xh offset,
                    0 < offset < bitwidth
                    -> singlewidth (cstZsingle_to_double xl xh >> singlewidth ('offset))
                       = singlewidth (Z.lor (singlewidth (singlewidth xl >> singlewidth ('offset)))
                                            (singlewidth
                                               (Z.truncating_shiftl
                                                  (singlewidth ('bitwidth))
                                                  (singlewidth xh)
                                                  (singlewidth ('(bitwidth - offset)))))))
             ]
          ].
End with_bitwidth.
