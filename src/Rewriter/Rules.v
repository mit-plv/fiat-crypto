Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Language.PreExtra.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Local Definition mymap {A B} := Eval cbv in @List.map A B.
Local Definition myapp {A} := Eval cbv in @List.app A.
Local Definition myflatten {A} := Eval cbv in List.fold_right myapp (@nil A).
Local Notation dont_do_again := (pair false) (only parsing).
Local Notation do_again := (pair true) (only parsing).

Local Notation "' x" := (ident.literal x).
Local Notation cstZ r := (ident.cast ('r%zrange)).
Local Notation cstZZ r1 r2 := (ident.cast2 ('(r1%zrange), '(r2%zrange))).
Local Notation "'plet' x := y 'in' z"
  := (match y return _ with x => z end).

Local Notation dlet2_opp2 rv rc e
  := (plet rc' := (-rc)%zrange in
          plet cst' := cstZZ rv rc' in
          plet cst1 := cstZ rv in
          plet cst2 := cstZ rc in
          plet cst2' := cstZ rc' in
          (dlet vc := cst' e in
               (cst1 (fst (cst' vc)), cst2 (-(cst2' (snd (cst' vc))))))).

Local Notation dlet2 rv rc e
  := (dlet vc := cstZZ rv rc e in
          (cstZ rv (fst (cstZZ rv rc vc)),
           cstZ rc (snd (cstZZ rv rc vc)))).


Local Notation "x '\in' y" := (is_bounded_by_bool x (ZRange.normalize y) = true) : zrange_scope.
Local Notation "x ∈ y" := (is_bounded_by_bool x (ZRange.normalize y) = true) : zrange_scope.
Local Notation "x <= y" := (is_tighter_than_bool (ZRange.normalize x) y = true) : zrange_scope.
Local Notation "x <= y <= z" := (andb (is_tighter_than_bool (ZRange.normalize x) y) (is_tighter_than_bool (ZRange.normalize y) z) = true) : zrange_scope.
Local Notation litZZ x := (ident.literal (fst x), ident.literal (snd x)) (only parsing).
Local Notation n r := (ZRange.normalize r) (only parsing).

(* N.B. [ident.eagerly] does not play well with [do_again] *)
Definition nbe_rewrite_rulesT : list (bool * Prop)
  := Eval cbv [myapp mymap myflatten] in
      myflatten
        [mymap
           dont_do_again
           [(forall A B x y, @fst A B (x, y) = x)
            ; (forall A B x y, @snd A B (x, y) = y)
            ; (forall P t f, @Thunked.bool_rect P t f true = t tt)
            ; (forall P t f, @Thunked.bool_rect P t f false = f tt)
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
                  @Thunked.list_rect A P N C ls
                  = ident.eagerly (@Thunked.list_rect) A P N C ls)
            ; (forall A P Q N C ls v,
                  @list_rect A (fun _ => P -> Q) N C ls v
                  = ident.eagerly (@list_rect) A (fun _ => P -> Q) N C ls v)
            ; (forall A P N C, @Thunked.list_case A P N C nil = N tt)
            ; (forall A P N C x xs, @Thunked.list_case A P N C (x :: xs) = C x xs)
            ; (forall A B f ls,
                  @List.map A B f ls
                  = (ident.eagerly (@list_rect) _ _)
                      nil
                      (fun x xs map_f_xs => f x :: map_f_xs)
                      ls)
            ; (forall P O_case S_case n,
                  @Thunked.nat_rect P O_case S_case ('n)
                  = (ident.eagerly (@Thunked.nat_rect) _)
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

Definition unfold_value_barrier_rewrite_rulesT : list (bool * Prop)
  := Eval cbv [myapp mymap myflatten] in
      myflatten
        [mymap
           dont_do_again
           [(forall x, Z.value_barrier x = x)
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

            ; (forall v, Z.land v ('0) = '0)
            ; (forall v, Z.land ('0) v = '0)
            ; (forall v, Z.land v ('-1) = v)
            ; (forall v, Z.land ('-1) v = v)

            ; (forall v, Z.lor v ('0) = v)
            ; (forall v, Z.lor ('0) v = v)
            ; (forall v, Z.lor v ('-1) = '-1)
            ; (forall v, Z.lor ('-1) v = '-1)

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

Definition arith_with_casts_rewrite_rulesT (adc_no_carry_to_add : bool) : list (bool * Prop)
  := Eval cbv [myapp mymap myflatten] in
      myflatten
        [mymap
           dont_do_again
           [(forall A B x y, @fst A B (x, y) = x)
            ; (forall A B x y, @snd A B (x, y) = y)
            ; (forall r v, lower r = upper r -> cstZ r v = cstZ r ('(lower r)))
            ; (forall r0 v, 0 ∈ r0 -> cstZ r0 0 + v = v)
            ; (forall r0 v, 0 ∈ r0 -> v + cstZ r0 0 = v)
            ; (forall r0 v, 0 ∈ r0 -> v - cstZ r0 0 = v)
            ; (forall r0 v, 0 ∈ r0 -> cstZ r0 0 - v = -v)
            ; (forall r0 v, 0 ∈ r0 -> cstZ r0 0 << v = 0)
            ; (forall r0 rnv rv v,
                  (rv <= -n rnv)%zrange -> 0 ∈ r0
                  -> cstZ r0 0 - cstZ rnv (-(cstZ rv v)) = cstZ rv v)
            ; (forall rnv rv v,
                  (rv <= -n rnv)%zrange
                  -> -(cstZ rnv (-(cstZ rv v))) = cstZ rv v)

            ; (forall rland r0 rv v,
                  0 ∈ rland -> 0 ∈ r0
                  -> cstZ rland (Z.land (cstZ rv v) (cstZ r0 ('0))) = cstZ r0 ('0))
            ; (forall rland r0 rv v,
                  0 ∈ rland -> 0 ∈ r0
                  -> cstZ rland (Z.land (cstZ r0 ('0)) (cstZ rv v)) = cstZ r0 ('0))
            ; (forall rland rm1 rv v,
                  (rv <= rland)%zrange -> -1 ∈ rm1
                  -> cstZ rland (Z.land (cstZ rv v) (cstZ rm1 ('-1))) = cstZ rv v)
            ; (forall rland rm1 rv v,
                  (rv <= rland)%zrange -> -1 ∈ rm1
                  -> cstZ rland (Z.land (cstZ rm1 ('-1)) (cstZ rv v)) = cstZ rv v)

            ; (forall rlor r0 rv v,
                  (rv <= rlor)%zrange -> 0 ∈ r0
                  -> cstZ rlor (Z.lor (cstZ rv v) (cstZ r0 ('0))) = cstZ rv v)
            ; (forall rlor r0 rv v,
                  (rv <= rlor)%zrange -> 0 ∈ r0
                  -> cstZ rlor (Z.lor (cstZ r0 ('0)) (cstZ rv v)) = cstZ rv v)
            ; (forall rlor rm1 rv v,
                  -1 ∈ rlor -> -1 ∈ rm1
                  -> cstZ rlor (Z.lor (cstZ rv v) (cstZ rm1 ('-1))) = cstZ rm1 ('-1))
            ; (forall rlor rm1 rv v,
                  -1 ∈ rlor -> -1 ∈ rm1
                  -> cstZ rlor (Z.lor (cstZ rm1 ('-1)) (cstZ rv v)) = cstZ rm1 ('-1))

            ; (forall rx x ry y, upper (n rx) < lower (n ry) -> Z.ltz (cstZ rx x) (cstZ ry y) = 1)
            ; (forall rx x ry y, upper (n ry) <= lower (n rx) -> Z.ltz (cstZ rx x) (cstZ ry y) = 0)
            ; (forall rx x rc c, c ∈ rc -> upper (n rx) < c -> Z.ltz (cstZ rx x) (cstZ rc ('c)) = 1)
            ; (forall rx x rc c, c ∈ rc -> c <= lower (n rx) -> Z.ltz (cstZ rx x) (cstZ rc ('c)) = 0)
            ; (forall rc c ry y, c ∈ rc -> c < lower (n ry) -> Z.ltz (cstZ rc ('c)) (cstZ ry y) = 1)
            ; (forall rc c ry y, c ∈ rc -> upper (n ry) <= c -> Z.ltz (cstZ rc ('c)) (cstZ ry y) = 0)

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
           ]
         ; mymap
             dont_do_again
             [ (** remove unnecessary masks *)
               (forall rv rx x ry y,
                   (rx <= rv)%zrange ->
                   (rx <= r[0~>y])%zrange ->
                   y ∈ ry -> y = Z.ones (Z.succ (Z.log2 y))
                   -> cstZ rv (cstZ rx x &' cstZ ry ('y)) = cstZ rx x);
                 (forall rv rx x ry y,
                   (rx <= rv)%zrange ->
                   (rx <= r[0~>y])%zrange ->
                   y ∈ ry -> y = Z.ones (Z.succ (Z.log2 y))
                   -> cstZ rv (cstZ ry ('y) &' cstZ rx x) = cstZ rx x)
             ]%Z%zrange
         ; mymap
             do_again
             [ (* [do_again], so that we can trigger add/sub rules on the output *)
               (** flatten add/sub which incurs no carry/borrow *)
               (forall rv rs s rx x ry y,
                   adc_no_carry_to_add = true -> s ∈ rs -> (n rx + n ry <= r[0~>s-1])%zrange
                   -> cstZZ rv r[0~>0] (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rx x) (cstZ ry y))
                      = (cstZ rv (cstZ rx x + cstZ ry y), cstZ r[0~>0] ('0)))
               ; (forall rv rs s rc c rx x ry y,
                     adc_no_carry_to_add = true -> s ∈ rs -> (n rc + n rx + n ry <= r[0~>s-1])%zrange
                     -> cstZZ rv r[0~>0] (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rx x) (cstZ ry y))
                        = (cstZ rv (cstZ rc c + cstZ rx x + cstZ ry y), cstZ r[0~>0] ('0)))
               ; (forall rv rs s rx x ry y,
                     adc_no_carry_to_add = true -> s ∈ rs -> (n rx - n ry <= r[0~>s-1])%zrange
                     -> cstZZ rv r[0~>0] (Z.sub_get_borrow_full (cstZ rs ('s)) (cstZ rx x) (cstZ ry y))
                        = (cstZ rv (cstZ rx x - cstZ ry y), (cstZ r[0~>0] ('0))))
               ; (forall rv rs s rc c rx x ry y,
                     adc_no_carry_to_add = true -> s ∈ rs -> (n rx - n ry - n rc <= r[0~>s-1])%zrange
                     -> cstZZ rv r[0~>0] (Z.sub_with_get_borrow_full (cstZ rs ('s)) (cstZ rc c) (cstZ rx x) (cstZ ry y))
                        = (cstZ rv (cstZ rx x - cstZ ry y - cstZ rc c), (cstZ r[0~>0] ('0))))
             ]%Z%zrange
         ; mymap
             dont_do_again
             [(forall rv rc s rny ry y x,
                  (ry <= -n rny)%zrange
                  -> cstZZ rv rc (Z.add_get_carry_full s (cstZ rny (-cstZ ry y)) x)
                     = dlet2_opp2 rv rc (Z.sub_get_borrow_full s x (cstZ ry y)))
              ; (forall rv rc s rny ry y x,
                    (ry <= -n rny)%zrange
                    -> cstZZ rv rc (Z.add_get_carry_full s x (cstZ rny (-cstZ ry y)))
                       = dlet2_opp2 rv rc (Z.sub_get_borrow_full s x (cstZ ry y)))
              ; (forall rv rc s ryy yy x,
                    yy ∈ ryy -> yy < 0
                    -> cstZZ rv rc (Z.add_get_carry_full s (cstZ ryy ('yy)) x)
                       = dlet2_opp2 rv rc (Z.sub_get_borrow_full s x (cstZ (-ryy) ('(-yy)))))
              ; (forall rv rc s ryy yy x,
                    yy ∈ ryy -> yy < 0
                    -> cstZZ rv rc (Z.add_get_carry_full s x (cstZ ryy ('yy)))
                       = dlet2_opp2 rv rc (Z.sub_get_borrow_full s x (cstZ (-ryy) ('(-yy)))))
              ; (forall rv rc s rnc rc' c' rny ry y x,
                    (ry <= -n rny)%zrange -> (rc' <= -n rnc)%zrange
                    -> cstZZ rv rc (Z.add_with_get_carry_full s (cstZ rnc (-cstZ rc' c')) (cstZ rny (-cstZ ry y)) x)
                       = dlet2_opp2 rv rc (Z.sub_with_get_borrow_full s (cstZ rc' c') x (cstZ ry y)))
              ; (forall rv rc s rnc rc' c' rny ry y x,
                    (ry <= -n rny)%zrange -> (rc' <= -n rnc)%zrange
                    -> cstZZ rv rc (Z.add_with_get_carry_full s (cstZ rnc (-cstZ rc' c')) x (cstZ rny (-cstZ ry y)))
                       = dlet2_opp2 rv rc (Z.sub_with_get_borrow_full s (cstZ rc' c') x (cstZ ry y)))
              ; (forall rv rc s r0 rny ry y x,
                    0 ∈ r0 -> (ry <= -n rny)%zrange
                    -> cstZZ rv rc (Z.add_with_get_carry_full s (cstZ r0 0) (cstZ rny (-cstZ ry y)) x)
                       = dlet2_opp2 rv rc (Z.sub_get_borrow_full s x (cstZ ry y)))
              ; (forall rv rc s rcc cc rny ry y x,
                    cc < 0 -> cc ∈ rcc -> (ry <= -n rny)%zrange
                    -> cstZZ rv rc (Z.add_with_get_carry_full s (cstZ rcc ('cc)) (cstZ rny (-cstZ ry y)) x)
                       = dlet2_opp2 rv rc (Z.sub_with_get_borrow_full s (cstZ (-rcc) ('(-cc))) x (cstZ ry y)))
              ; (forall rv rc s r0 rny ry y x,
                    0 ∈ r0 -> (ry <= -n rny)%zrange
                    -> cstZZ rv rc (Z.add_with_get_carry_full s (cstZ r0 0) x (cstZ rny (-cstZ ry y)))
                       = dlet2_opp2 rv rc (Z.sub_get_borrow_full s x (cstZ ry y)))
              ; (forall rv rc s rcc cc rny ry y x,
                    cc < 0 -> cc ∈ rcc -> (ry <= -n rny)%zrange
                    -> cstZZ rv rc (Z.add_with_get_carry_full s (cstZ rcc ('cc)) x (cstZ rny (-cstZ ry y)))
                       = dlet2_opp2 rv rc (Z.sub_with_get_borrow_full s (cstZ (-rcc) ('(-cc))) x (cstZ ry y)))
              ; (forall rv rc s rnc rc' c' ryy yy x,
                    yy <= 0 -> yy ∈ ryy -> (rc' <= -n rnc)%zrange
                    -> cstZZ rv rc (Z.add_with_get_carry_full s (cstZ rnc (-cstZ rc' c')) (cstZ ryy ('yy)) x)
                       = dlet2_opp2 rv rc (Z.sub_with_get_borrow_full s (cstZ rc' c') x (cstZ (-ryy) ('(-yy)))))
              ; (forall rv rc s rnc rc' c' ryy yy x,
                    yy <= 0 -> yy ∈ ryy -> (rc' <= -n rnc)%zrange
                    -> cstZZ rv rc (Z.add_with_get_carry_full s (cstZ rnc (-cstZ rc' c')) x (cstZ ryy ('yy)))
                       = dlet2_opp2 rv rc (Z.sub_with_get_borrow_full s (cstZ rc' c') x (cstZ (-ryy) ('(-yy)))))
              ; (forall rv rc s rcc cc ryy yy x,
                    yy <= 0 -> cc <= 0 -> yy + cc < 0 (* at least one must be strictly negative *) -> yy ∈ ryy -> cc ∈ rcc
                    -> cstZZ rv rc (Z.add_with_get_carry_full s (cstZ rcc ('cc)) (cstZ ryy ('yy)) x)
                       = dlet2_opp2 rv rc (Z.sub_with_get_borrow_full s (cstZ (-rcc) ('(-cc))) x (cstZ (-ryy) ('(-yy)))))
              ; (forall rv rc s rcc cc ryy yy x,
                    yy <= 0 -> cc <= 0 -> yy + cc < 0 (* at least one must be strictly negative *) -> yy ∈ ryy -> cc ∈ rcc
                    -> cstZZ rv rc (Z.add_with_get_carry_full s (cstZ rcc ('cc)) x (cstZ ryy ('yy)))
                       = dlet2_opp2 rv rc (Z.sub_with_get_borrow_full s (cstZ (-rcc) ('(-cc))) x (cstZ (-ryy) ('(-yy)))))


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

              ; (forall rv rc s r0 x y, (* carry = 0: ADC x y -> ADD x y *)
                    0 ∈ r0
                    -> cstZZ rv rc (Z.add_with_get_carry_full s (cstZ r0 0) x y)
                       = dlet2 rv rc (Z.add_get_carry_full s x y))
              ; (forall rv rc rs s rc' c' r0x r0y, (* ADC 0 0 -> (ADX 0 0, 0) *) (* except we don't do ADX, because C stringification doesn't handle it *)
                    0 ∈ r0x -> 0 ∈ r0y -> (rc' <= r[0~>s-1])%zrange -> 0 ∈ rc -> s ∈ rs
                    -> cstZZ rv rc (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc' c') (cstZ r0x 0) (cstZ r0y 0))
                       = (dlet vc := (cstZZ rv rc (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc' c') (cstZ r0x 0) (cstZ r0y 0))) in
                              (cstZ rv (fst (cstZZ rv rc vc)),
                               cstZ r[0~>0] 0)))

                  (* let-bind any adc/sbb/mulx *)
              ; (forall rv rc s c x y,
                    cstZZ rv rc (Z.add_with_get_carry_full s c x y)
                    = dlet2 rv rc (Z.add_with_get_carry_full s c x y))
              ; (forall rv c x y,
                    cstZ rv (Z.add_with_carry c x y)
                    = (dlet vc := cstZ rv (Z.add_with_carry c x y) in
                           cstZ rv vc))
              ; (forall rv rc s x y,
                    cstZZ rv rc (Z.add_get_carry_full s x y)
                    = dlet2 rv rc (Z.add_get_carry_full s x y))
              ; (forall rv rc s c x y,
                    cstZZ rv rc (Z.sub_with_get_borrow_full s c x y)
                    = dlet2 rv rc (Z.sub_with_get_borrow_full s c x y))
              ; (forall rv rc s x y,
                    cstZZ rv rc (Z.sub_get_borrow_full s x y)
                    = dlet2 rv rc (Z.sub_get_borrow_full s x y))
              ; (forall rv rc s x y,
                    cstZZ rv rc (Z.mul_split s x y)
                    = dlet2 rv rc (Z.mul_split s x y))
             ]
         ; mymap
             do_again
             [ (* [do_again], so that if one of the arguments is concrete, we automatically get the rewrite rule for [Z_cast] applying to it *)
               (forall rx ry x y, cstZZ rx ry (x, y) = (cstZ rx x, cstZ ry y))
             ]
         ; mymap
             dont_do_again
             [(forall r1 r2 x, (r2 <= n r1)%zrange -> cstZ r1 (cstZ r2 x) = cstZ r2 x)
             ]
        ]%Z%zrange.

Definition strip_literal_casts_rewrite_rulesT : list (bool * Prop)
  := [dont_do_again (forall rx x, x ∈ rx -> cstZ rx ('x) = 'x)]%Z%zrange.

Definition add_assoc_left_rewrite_rulesT : list (bool * Prop)
  := Eval cbv [myapp mymap myflatten] in
      myflatten
        [mymap
           dont_do_again
           [(forall x y z, x + (y + z) = (x + y) + z)
            ; (forall x y z, x + (y + z) = (x + y) + z)%nat
           ]
        ].

Definition flatten_thunked_rects_rewrite_rulesT : list (bool * Prop)
  := [dont_do_again (forall P t f b, @Thunked.bool_rect P t f b = @bool_rect_nodep P (t tt) (f tt) b)].

Definition relax_bitwidth_adc_sbb_rewrite_rulesT (which_bitwidths : list Z) : list (bool * Prop)
  := Eval cbv [myapp mymap myflatten] in
      mymap
        dont_do_again
        [(forall rv rc' rs s rc c rx x ry y,
             (((ZRange.normalize rc + ZRange.normalize rx + ZRange.normalize ry) / ZRange.normalize rs) <= rc' <= rv)%zrange ->
             List.existsb (Z.eqb (Z.log2 s)) which_bitwidths = true ->
             cstZZ rv rc' (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rx x) (cstZ ry y))
             = cstZZ rv rv (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rx x) (cstZ ry y)))
         ; (forall rv rc' rs s rx x ry y,
             (((ZRange.normalize rx + ZRange.normalize ry) / ZRange.normalize rs) <= rc' <= rv)%zrange ->
             List.existsb (Z.eqb (Z.log2 s)) which_bitwidths = true ->
             cstZZ rv rc' (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rx x) (cstZ ry y))
             = cstZZ rv rv (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rx x) (cstZ ry y)))
         ; (forall rv rc' rs s rc c rx x ry y,
             (- ((ZRange.normalize rx - ZRange.normalize ry - ZRange.normalize rc) / ZRange.normalize rs) <= rc' <= rv)%zrange ->
             List.existsb (Z.eqb (Z.log2 s)) which_bitwidths = true ->
             cstZZ rv rc' (Z.sub_with_get_borrow_full (cstZ rs ('s)) (cstZ rc c) (cstZ rx x) (cstZ ry y))
             = cstZZ rv rv (Z.sub_with_get_borrow_full (cstZ rs ('s)) (cstZ rc c) (cstZ rx x) (cstZ ry y)))
         ; (forall rv rc' rs s rx x ry y,
             (- ((ZRange.normalize rx - ZRange.normalize ry) / ZRange.normalize rs) <= rc' <= rv)%zrange ->
             List.existsb (Z.eqb (Z.log2 s)) which_bitwidths = true ->
             cstZZ rv rc' (Z.sub_get_borrow_full (cstZ rs ('s)) (cstZ rx x) (cstZ ry y))
             = cstZZ rv rv (Z.sub_get_borrow_full (cstZ rs ('s)) (cstZ rx x) (cstZ ry y)))
        ].

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
        myflatten
          [mymap
             dont_do_again
             [(*
(Z.add_get_carry_concrete 2^256) @@@ (?x, ?y << 128) --> (add 128) @@@ (x, y)
(Z.add_get_carry_concrete 2^256) @@@ (?x << 128, ?y) --> (add 128) @@@ (y, x)
(Z.add_get_carry_concrete 2^256) @@@ (?x, ?y >> 128) --> (add (- 128)) @@@ (x, y)
(Z.add_get_carry_concrete 2^256) @@@ (?x >> 128, ?y) --> (add (- 128)) @@@ (y, x)
(Z.add_get_carry_concrete 2^256) @@@ (?x, ?y)        --> (add 0) @@@ (y, x)
               *)
               (forall r1 r2 rs s rx x rshiftl rland ry y rmask mask roffset offset,
                   s = 2^Z.log2 s -> s ∈ rs -> offset ∈ roffset -> mask ∈ rmask -> shiftl_good rshiftl rland offset -> land_good rland ry mask -> range_in_bitwidth rshiftl s -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                   -> cstZZ r1 r2 (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rx x) (cstZ rshiftl ((cstZ rland (cstZ ry y &' cstZ rmask ('mask))) << cstZ roffset ('offset))))
                      = cstZZ r1 r2 (ident.fancy.add (('(Z.log2 s), 'offset), (cstZ rx x, cstZ ry y))))
               ; (forall r1 r2 rs s rx x rshiftl rland ry y rmask mask roffset offset,
                     (s = 2^Z.log2 s) -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s) -> s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> shiftl_good rshiftl rland offset -> land_good rland ry mask -> range_in_bitwidth rshiftl s
                     -> cstZZ r1 r2 (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rx x) (cstZ rshiftl (cstZ rland (cstZ ry y &' cstZ rmask ('mask)) << cstZ roffset ('offset))))
                        = cstZZ r1 r2 (ident.fancy.add (('(Z.log2 s), 'offset), (cstZ rx x, cstZ ry y))))

               ; (forall r1 r2 rs s rshiftl rland ry y rmask mask roffset offset rx x,
                     s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftl_good rshiftl rland offset -> land_good rland ry mask -> range_in_bitwidth rshiftl s -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                     -> cstZZ r1 r2 (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rshiftl (Z.shiftl (cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask)))) (cstZ roffset ('offset)))) (cstZ rx x))
                        = cstZZ r1 r2 (ident.fancy.add (('(Z.log2 s), 'offset), (cstZ rx x, cstZ ry y))))

               ; (forall r1 r2 rs s rx x rshiftr ry y roffset offset,
                     s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                     -> cstZZ r1 r2 (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rx x) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))))
                        = cstZZ r1 r2 (ident.fancy.add (('(Z.log2 s), '(-offset)), (cstZ rx x, cstZ ry y)))%core)

               ; (forall r1 r2 rs s rshiftr ry y roffset offset rx x,
                     s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                     -> cstZZ r1 r2 (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))) (cstZ rx x))
                        = cstZZ r1 r2 (ident.fancy.add (('(Z.log2 s), '(-offset)), (cstZ rx x, cstZ ry y))%core))

               ; (forall r1 r2 rs s rx x ry y,
                     s ∈ rs -> (s = 2^Z.log2 s) -> range_in_bitwidth ry s
                     -> cstZZ r1 r2 (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rx x) (cstZ ry y))
                        = cstZZ r1 r2 (ident.fancy.add (('(Z.log2 s), '0), (cstZ rx x, cstZ ry y))))

               (*
(Z.add_with_get_carry_concrete 2^256) @@@ (?c, ?x, ?y << 128) --> (addc 128) @@@ (c, x, y)
(Z.add_with_get_carry_concrete 2^256) @@@ (?c, ?x << 128, ?y) --> (addc 128) @@@ (c, y, x)
(Z.add_with_get_carry_concrete 2^256) @@@ (?c, ?x, ?y >> 128) --> (addc (- 128)) @@@ (c, x, y)
(Z.add_with_get_carry_concrete 2^256) @@@ (?c, ?x >> 128, ?y) --> (addc (- 128)) @@@ (c, y, x)
(Z.add_with_get_carry_concrete 2^256) @@@ (?c, ?x, ?y)        --> (addc 0) @@@ (c, y, x)
                *)
               ; (forall r1 r2 rs s rc c rx x rshiftl rland ry y rmask mask roffset offset,
                     s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftl_good rshiftl rland offset -> land_good rland ry mask -> range_in_bitwidth rshiftl s -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                     -> cstZZ r1 r2 (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rx x) (cstZ rshiftl (Z.shiftl (cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask)))) (cstZ roffset ('offset)))))
                        = cstZZ r1 r2 (ident.fancy.addc (('(Z.log2 s), 'offset), (cstZ rc c, cstZ rx x, cstZ ry y))))

               ; (forall r1 r2 rs s rc c rshiftl rland ry y rmask mask roffset offset rx x,
                     s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftl_good rshiftl rland offset -> range_in_bitwidth rshiftl s -> land_good rland ry mask -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                     -> cstZZ r1 r2 (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rshiftl (Z.shiftl (cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask)))) (cstZ roffset ('offset)))) (cstZ rx x))
                        = cstZZ r1 r2 (ident.fancy.addc (('(Z.log2 s), 'offset), (cstZ rc c, cstZ rx x, cstZ ry y))))

               ; (forall r1 r2 rs s rc c rx x rshiftr ry y roffset offset,
                     s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                     -> cstZZ r1 r2 (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rx x) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))))
                        = cstZZ r1 r2 (ident.fancy.addc (('(Z.log2 s), '(-offset)), (cstZ rc c, cstZ rx x, cstZ ry y))%core))

               ; (forall r1 r2 rs s rc c rshiftr ry y roffset offset rx x,
                     s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                     -> cstZZ r1 r2 (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))) (cstZ rx x))
                        = cstZZ r1 r2 (ident.fancy.addc (('(Z.log2 s), '(-offset)), (cstZ rc c, cstZ rx x, cstZ ry y))%core))

               ; (forall r1 r2 rs s rc c rx x ry y,
                     s ∈ rs -> (s = 2^Z.log2 s) -> range_in_bitwidth ry s
                     -> cstZZ r1 r2 (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rx x) (cstZ ry y))
                        = cstZZ r1 r2 (ident.fancy.addc (('(Z.log2 s), '0), (cstZ rc c, cstZ rx x, cstZ ry y))))

               (*
(Z.sub_get_borrow_concrete 2^256) @@@ (?x, ?y << 128) --> (sub 128) @@@ (x, y)
(Z.sub_get_borrow_concrete 2^256) @@@ (?x, ?y >> 128) --> (sub (- 128)) @@@ (x, y)
(Z.sub_get_borrow_concrete 2^256) @@@ (?x, ?y)        --> (sub 0) @@@ (y, x)
                *)

               ; (forall r1 r2 rs s rx x rshiftl rland ry y rmask mask roffset offset,
                     s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftl_good rshiftl rland offset -> range_in_bitwidth rshiftl s -> land_good rland ry mask -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                     -> cstZZ r1 r2 (Z.sub_get_borrow_full (cstZ rs ('s)) (cstZ rx x) (cstZ rshiftl (Z.shiftl (cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask)))) (cstZ roffset ('offset)))))
                        = cstZZ r1 r2 (ident.fancy.sub (('(Z.log2 s), 'offset), (cstZ rx x, cstZ ry y))))

               ; (forall r1 r2 rs s rx x rshiftr ry y roffset offset,
                     s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                     -> cstZZ r1 r2 (Z.sub_get_borrow_full (cstZ rs ('s)) (cstZ rx x) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))))
                        = cstZZ r1 r2 (ident.fancy.sub (('(Z.log2 s), '(-offset)), (cstZ rx x, cstZ ry y))%core))

               ; (forall r1 r2 rs s rx x ry y,
                     s ∈ rs -> (s = 2^Z.log2 s) -> range_in_bitwidth ry s
                     -> cstZZ r1 r2 (Z.sub_get_borrow_full (cstZ rs ('s)) (cstZ rx x) (cstZ ry y))
                        = cstZZ r1 r2 (ident.fancy.sub (('(Z.log2 s), '0), (cstZ rx x, cstZ ry y))))

               (*
(Z.sub_with_get_borrow_concrete 2^256) @@@ (?c, ?x, ?y << 128) --> (subb 128) @@@ (c, x, y)
(Z.sub_with_get_borrow_concrete 2^256) @@@ (?c, ?x, ?y >> 128) --> (subb (- 128)) @@@ (c, x, y)
(Z.sub_with_get_borrow_concrete 2^256) @@@ (?c, ?x, ?y)        --> (subb 0) @@@ (c, y, x)
                *)

               ; (forall r1 r2 rs s rb b rx x rshiftl rland ry y rmask mask roffset offset,
                     s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftl_good rshiftl rland offset -> range_in_bitwidth rshiftl s -> land_good rland ry mask -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                     -> cstZZ r1 r2 (Z.sub_with_get_borrow_full (cstZ rs ('s)) (cstZ rb b) (cstZ rx x) (cstZ rshiftl (Z.shiftl (cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask)))) (cstZ roffset ('offset)))))
                        = cstZZ r1 r2 (ident.fancy.subb (('(Z.log2 s), 'offset), (cstZ rb b, cstZ rx x, cstZ ry y))))

               ; (forall r1 r2 rs s rb b rx x rshiftr ry y roffset offset,
                     s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                     -> cstZZ r1 r2 (Z.sub_with_get_borrow_full (cstZ rs ('s)) (cstZ rb b) (cstZ rx x) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))))
                        = cstZZ r1 r2 (ident.fancy.subb (('(Z.log2 s), '(-offset)), (cstZ rb b, cstZ rx x, cstZ ry y))%core))

               ; (forall r1 r2 rs s rb b rx x ry y,
                     s ∈ rs -> (s = 2^Z.log2 s) -> range_in_bitwidth ry s
                     -> cstZZ r1 r2 (Z.sub_with_get_borrow_full (cstZ rs ('s)) (cstZ rb b) (cstZ rx x) (cstZ ry y))
                        = cstZZ r1 r2 (ident.fancy.subb (('(Z.log2 s), '0), (cstZ rb b, cstZ rx x, cstZ ry y))))

               (*(Z.rshi_concrete 2^256 ?n) @@@ (?c, ?x, ?y) --> (rshi n) @@@ (x, y)*)

               ; (forall r rs s rx x ry y rn n,
                     s ∈ rs -> n ∈ rn -> (s = 2^Z.log2 s)
                     -> cstZ r (Z.rshi (cstZ rs ('s)) (cstZ rx x) (cstZ ry y) (cstZ rn ('n)))
                        = cstZ r (ident.fancy.rshi (('(Z.log2 s), 'n), (cstZ rx x, cstZ ry y))))

               (*
Z.zselect @@@ (Z.cc_m_concrete 2^256 ?c, ?x, ?y) --> selm @@@ (c, x, y)
Z.zselect @@@ (?c &' 1, ?x, ?y)                  --> sell @@@ (c, x, y)
Z.zselect @@@ (?c, ?x, ?y)                       --> selc @@@ (c, x, y)
                *)
               ; (forall r rccm rs s rc c rx x ry y,
                     s ∈ rs -> (s = 2^Z.log2 s) -> cc_m_good rccm s rc
                     -> cstZ r (Z.zselect (cstZ rccm (Z.cc_m (cstZ rs ('s)) (cstZ rc c))) (cstZ rx x) (cstZ ry y))
                        = cstZ r (ident.fancy.selm ('(Z.log2 s), (cstZ rc c, cstZ rx x, cstZ ry y))))

               ; (forall r rland r1 rc c rx x ry y,
                     1 ∈ r1 -> land_good rland 1 rc
                     -> cstZ r (Z.zselect (cstZ rland (cstZ r1 1 &' cstZ rc c)) (cstZ rx x) (cstZ ry y))
                        = cstZ r (ident.fancy.sell (cstZ rc c, cstZ rx x, cstZ ry y)))

               ; (forall r rland rc c r1 rx x ry y,
                     1 ∈ r1 -> land_good rland rc 1
                     -> cstZ r (Z.zselect (cstZ rland (cstZ rc c &' cstZ r1 1)) (cstZ rx x) (cstZ ry y))
                        = cstZ r (ident.fancy.sell (cstZ rc c, cstZ rx x, cstZ ry y)))

               ; (forall r c x y,
                     cstZ r (Z.zselect c x y)
                     = cstZ r (ident.fancy.selc (c, x, y)))

               (*Z.add_modulo @@@ (?x, ?y, ?m) --> addm @@@ (x, y, m)*)
               ; (forall x y m,
                     Z.add_modulo x y m
                     = ident.fancy.addm (x, y, m))

               (*
Z.mul @@@ (?x &' (2^128-1), ?y &' (2^128-1)) --> mulll @@@ (x, y)
Z.mul @@@ (?x &' (2^128-1), ?y >> 128)       --> mullh @@@ (x, y)
Z.mul @@@ (?x >> 128, ?y &' (2^128-1))       --> mulhl @@@ (x, y)
Z.mul @@@ (?x >> 128, ?y >> 128)             --> mulhh @@@ (x, y)
                *)
               (* literal on left *)
               ; (forall r rx x rland ry y rmask mask,
                     plet s := (2*Z.log2_up mask)%Z in
                      plet xo := invert_low s x in
                      plet xv := match xo with Some x => x | None => 0 end in
                      xo <> None -> x ∈ rx -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland ry mask
                      -> cstZ r (cstZ rx ('x) * cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask))))
                         = cstZ r (ident.fancy.mulll (('s), ('xv, cstZ ry y))))

               ; (forall r rx x rland rmask mask ry y,
                     plet s := (2*Z.log2_up mask)%Z in
                      plet xo := invert_low s x in
                      plet xv := match xo with Some x => x | None => 0 end in
                      xo <> None -> x ∈ rx -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland mask ry
                      -> cstZ r (cstZ rx ('x) * cstZ rland (Z.land (cstZ rmask ('mask)) (cstZ ry y)))
                         = cstZ r (ident.fancy.mulll (('s), ('xv, cstZ ry y))))

               ; (forall r rx x rshiftr ry y roffset offset,
                     plet s := (2*offset)%Z in
                      plet xo := invert_low s x in
                      plet xv := match xo with Some x => x | None => 0 end in
                      xo <> None -> x ∈ rx -> offset ∈ roffset -> shiftr_good rshiftr ry offset
                      -> cstZ r (cstZ rx ('x) * cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset))))
                         = cstZ r (ident.fancy.mullh (('s), ('xv, cstZ ry y))))

               ; (forall r rx x rland rmask mask ry y,
                     plet s := (2*Z.log2_up mask)%Z in
                      plet xo := invert_high s x in
                      plet xv := match xo with Some x => x | None => 0 end in
                      xo <> None -> x ∈ rx -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland mask ry
                      -> cstZ r (cstZ rx ('x) * cstZ rland (Z.land (cstZ rmask ('mask)) (cstZ ry y)))
                         = cstZ r (ident.fancy.mulhl (('s), ('xv, cstZ ry y))))

               ; (forall r rx x rland ry y rmask mask,
                     plet s := (2*Z.log2_up mask)%Z in
                      plet xo := invert_high s x in
                      plet xv := match xo with Some x => x | None => 0 end in
                      xo <> None -> x ∈ rx -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland ry mask
                      -> cstZ r (cstZ rx ('x) * cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask))))
                         = cstZ r (ident.fancy.mulhl (('s), ('xv, cstZ ry y))))

               ; (forall r rx x rshiftr ry y roffset offset,
                     plet s := (2*offset)%Z in
                      plet xo := invert_high s x in
                      plet xv := match xo with Some x => x | None => 0 end in
                      xo <> None -> x ∈ rx -> offset ∈ roffset -> shiftr_good rshiftr ry offset
                      -> cstZ r (cstZ rx ('x) * cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset))))
                         = cstZ r (ident.fancy.mulhh (('s), ('xv, cstZ ry y))))

               (* literal on right *)
               ; (forall r rland rmask mask rx x ry y,
                     plet s := (2*Z.log2_up mask)%Z in
                      plet yo := invert_low s y in
                      plet yv := match yo with Some y => y | None => 0 end in
                      yo <> None -> y ∈ ry -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland mask rx
                      -> cstZ r (cstZ rland (Z.land (cstZ rmask ('mask)) (cstZ rx x)) * cstZ ry ('y))
                         = cstZ r (ident.fancy.mulll (('s), (cstZ rx x, 'yv))))

               ; (forall r rland rx x rmask mask ry y,
                     plet s := (2*Z.log2_up mask)%Z in
                      plet yo := invert_low s y in
                      plet yv := match yo with Some y => y | None => 0 end in
                      yo <> None -> y ∈ ry -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland rx mask
                      -> cstZ r (cstZ rland (Z.land (cstZ rx x) (cstZ rmask ('mask))) * cstZ ry ('y))
                         = cstZ r (ident.fancy.mulll (('s), (cstZ rx x, 'yv))))

               ; (forall r rland rmask mask rx x ry y,
                     plet s := (2*Z.log2_up mask)%Z in
                      plet yo := invert_high s y in
                      plet yv := match yo with Some y => y | None => 0 end in
                      yo <> None -> y ∈ ry -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland mask rx
                      -> cstZ r (cstZ rland (Z.land (cstZ rmask ('mask)) (cstZ rx x)) * cstZ ry ('y))
                         = cstZ r (ident.fancy.mullh (('s), (cstZ rx x, 'yv))))

               ; (forall r rland rx x rmask mask ry y,
                     plet s := (2*Z.log2_up mask)%Z in
                      plet yo := invert_high s y in
                      plet yv := match yo with Some y => y | None => 0 end in
                      yo <> None -> y ∈ ry -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland rx mask
                      -> cstZ r (cstZ rland (Z.land (cstZ rx x) (cstZ rmask ('mask))) * cstZ ry ('y))
                         = cstZ r (ident.fancy.mullh (('s), (cstZ rx x, 'yv))))

               ; (forall r rshiftr rx x roffset offset ry y,
                     plet s := (2*offset)%Z in
                      plet yo := invert_low s y in
                      plet yv := match yo with Some y => y | None => 0 end in
                      yo <> None -> y ∈ ry -> offset ∈ roffset -> shiftr_good rshiftr rx offset
                      -> cstZ r (cstZ rshiftr (Z.shiftr (cstZ rx x) (cstZ roffset ('offset))) * cstZ ry ('y))
                         = cstZ r (ident.fancy.mulhl (('s), (cstZ rx x, 'yv))))

               ; (forall r rshiftr rx x roffset offset ry y,
                     plet s := (2*offset)%Z in
                      plet yo := invert_high s y in
                      plet yv := match yo with Some y => y | None => 0 end in
                      yo <> None -> y ∈ ry -> offset ∈ roffset -> shiftr_good rshiftr rx offset
                      -> cstZ r (cstZ rshiftr (Z.shiftr (cstZ rx x) (cstZ roffset ('offset))) * cstZ ry ('y))
                         = cstZ r (ident.fancy.mulhh (('s), (cstZ rx x, 'yv))))

               (* no literal *)
               ; (forall r rland1 rmask1 mask1 rx x rland2 rmask2 mask2 ry y,
                     plet s := (2*Z.log2_up mask1)%Z in
                      mask1 ∈ rmask1 -> mask2 ∈ rmask2 -> (mask1 = 2^(s/2)-1) -> (mask2 = 2^(s/2)-1) -> land_good rland1 mask1 rx -> land_good rland2 mask2 ry
                      -> cstZ r (cstZ rland1 (Z.land (cstZ rmask1 ('mask1)) (cstZ rx x)) * cstZ rland2 (Z.land (cstZ rmask2 ('mask2)) (cstZ ry y)))
                         = cstZ r (ident.fancy.mulll (('s), (cstZ rx x, cstZ ry y))))

               ; (forall r rland1 rx x rmask1 mask1 rland2 rmask2 mask2 ry y,
                     plet s := (2*Z.log2_up mask1)%Z in
                      mask1 ∈ rmask1 -> mask2 ∈ rmask2 -> (mask1 = 2^(s/2)-1) -> (mask2 = 2^(s/2)-1) -> land_good rland1 rx mask1 -> land_good rland2 mask2 ry
                      -> cstZ r (cstZ rland1 (Z.land (cstZ rx x) (cstZ rmask1 ('mask1))) * cstZ rland2 (Z.land (cstZ rmask2 ('mask2)) (cstZ ry y)))
                         = cstZ r (ident.fancy.mulll (('s), (cstZ rx x, cstZ ry y))))

               ; (forall r rland1 rmask1 mask1 rx x rland2 ry y rmask2 mask2,
                     plet s := (2*Z.log2_up mask1)%Z in
                      mask1 ∈ rmask1 -> mask2 ∈ rmask2 -> (mask1 = 2^(s/2)-1) -> (mask2 = 2^(s/2)-1) -> land_good rland1 mask1 rx -> land_good rland2 ry mask2
                      -> cstZ r (cstZ rland1 (Z.land (cstZ rmask1 ('mask1)) (cstZ rx x)) * cstZ rland2 (Z.land (cstZ ry y) (cstZ rmask2 ('mask2))))
                         = cstZ r (ident.fancy.mulll (('s), (cstZ rx x, cstZ ry y))))

               ; (forall r rland1 rx x rmask1 mask1 rland2 ry y rmask2 mask2,
                     plet s := (2*Z.log2_up mask1)%Z in
                      mask1 ∈ rmask1 -> mask2 ∈ rmask2 -> (mask1 = 2^(s/2)-1) -> (mask2 = 2^(s/2)-1) -> land_good rland1 rx mask1 -> land_good rland2 ry mask2
                      -> cstZ r (cstZ rland1 (Z.land (cstZ rx x) (cstZ rmask1 ('mask1))) * cstZ rland2 (Z.land (cstZ ry y) (cstZ rmask2 ('mask2))))
                         = cstZ r (ident.fancy.mulll (('s), (cstZ rx x, cstZ ry y))))

               ; (forall r rland1 rmask mask rx x rshiftr2 ry y roffset offset,
                     plet s := (2*offset)%Z in
                      mask ∈ rmask -> offset ∈ roffset -> (mask = 2^(s/2)-1) -> land_good rland1 mask rx -> shiftr_good rshiftr2 ry offset
                      -> cstZ r (cstZ rland1 (Z.land (cstZ rmask ('mask)) (cstZ rx x)) * cstZ rshiftr2 (Z.shiftr (cstZ ry y) (cstZ roffset ('offset))))
                         = cstZ r (ident.fancy.mullh (('s), (cstZ rx x, cstZ ry y))))

               ; (forall r rland1 rx x rmask mask rshiftr2 ry y roffset offset,
                     plet s := (2*offset)%Z in
                      mask ∈ rmask -> offset ∈ roffset -> (mask = 2^(s/2)-1) -> land_good rland1 rx mask -> shiftr_good rshiftr2 ry offset
                      -> cstZ r (cstZ rland1 (Z.land (cstZ rx x) (cstZ rmask ('mask))) * cstZ rshiftr2 (Z.shiftr (cstZ ry y) (cstZ roffset ('offset))))
                         = cstZ r (ident.fancy.mullh (('s), (cstZ rx x, cstZ ry y))))

               ; (forall r rshiftr1 rx x roffset offset rland2 rmask mask ry y,
                     plet s := (2*offset)%Z in
                      mask ∈ rmask -> offset ∈ roffset -> (mask = 2^(s/2)-1) -> shiftr_good rshiftr1 rx offset -> land_good rland2 mask ry
                      -> cstZ r (cstZ rshiftr1 (Z.shiftr (cstZ rx x) (cstZ roffset ('offset))) * cstZ rland2 (Z.land (cstZ rmask ('mask)) (cstZ ry y)))
                         = cstZ r (ident.fancy.mulhl (('s), (cstZ rx x, cstZ ry y))))

               ; (forall r rshiftr1 rx x roffset offset rland2 ry y rmask mask,
                     plet s := (2*offset)%Z in
                      mask ∈ rmask -> offset ∈ roffset -> (mask = 2^(s/2)-1) -> shiftr_good rshiftr1 rx offset -> land_good rland2 ry mask
                      -> cstZ r (cstZ rshiftr1 (Z.shiftr (cstZ rx x) (cstZ roffset ('offset))) * cstZ rland2 (Z.land (cstZ ry y) (cstZ rmask ('mask))))
                         = cstZ r (ident.fancy.mulhl (('s), (cstZ rx x, cstZ ry y))))

               ; (forall r rshiftr1 rx x roffset1 offset1 rshiftr2 ry y roffset2 offset2,
                     plet s := (2*offset1)%Z in
                      offset1 ∈ roffset1 -> offset2 ∈ roffset2 -> (offset1 = offset2) -> shiftr_good rshiftr1 rx offset1 -> shiftr_good rshiftr2 ry offset2
                      -> cstZ r (cstZ rshiftr1 (Z.shiftr (cstZ rx x) (cstZ roffset1 ('offset1))) * cstZ rshiftr2 (Z.shiftr (cstZ ry y) (cstZ roffset2 ('offset2))))
                         = cstZ r (ident.fancy.mulhh (('s), (cstZ rx x, cstZ ry y))))

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

  Local Notation singlewidth_range := r[0~>2^bitwidth - 1]%zrange.
  Local Notation doublewidth := (cstZ r[0~>2^(2*bitwidth) - 1]).
  Local Notation singlewidth := (cstZ singlewidth_range).
  Local Notation carrymax := (2^lgcarrymax-1).
  Local Notation carrywidth := (cstZ r[0~>carrymax]).
  Local Notation singlewidth_carry := (cstZZ singlewidth_range r[0~>carrymax]).
  Local Notation alt_singlewidth_carry := (cstZZ singlewidth_range r[0~>2^bitwidth-1]).
  Local Notation pairsinglewidth := (cstZZ singlewidth_range singlewidth_range).
  Local Notation cstZsingle_to_double l h
    := (doublewidth (Z.combine_at_bitwidth ('bitwidth) (singlewidth l) (singlewidth h))).
  Local Notation cstZsingle_to_double_pair lh
    := (cstZsingle_to_double (fst lh) (snd lh)).
  Local Notation cstZ_pow2_bitwidth
    := (cstZ r[2^bitwidth~>2^bitwidth] ('(2^bitwidth))).

  Definition mul_split_rewrite_rulesT : Datatypes.list (Datatypes.bool * Prop)
    := Eval cbv [myapp mymap myflatten] in
        myflatten
          [mymap
             dont_do_again
             [(forall r x, cstZ r (cstZ r x) = cstZ r x) (* when inlining Z.combine_at_bitwidth, casts will sometimes get doubled up, so we need to strip the extra casts *)
              ; (forall x y,
                    0 <= bitwidth
                    -> doublewidth (singlewidth x * singlewidth y)
                       = (dlet lh := pairsinglewidth (Z.mul_split cstZ_pow2_bitwidth (singlewidth x) (singlewidth y)) in
                              cstZsingle_to_double_pair lh))
              ; (forall xl xh y,
                    0 <= bitwidth
                    -> doublewidth (cstZsingle_to_double xl xh * singlewidth y)
                       = (dlet lh1 := pairsinglewidth (Z.mul_split cstZ_pow2_bitwidth (singlewidth xl) (singlewidth y)) in
                              dlet h2 := singlewidth (singlewidth xh * singlewidth y) in
                              dlet h := singlewidth (singlewidth (snd lh1) + singlewidth h2) in
                              cstZsingle_to_double (fst lh1) h))
              ; (forall x yl yh,
                    0 <= bitwidth
                    -> doublewidth (singlewidth x * cstZsingle_to_double yl yh)
                       = (dlet lh1 := pairsinglewidth (Z.mul_split cstZ_pow2_bitwidth (singlewidth x) (singlewidth yl)) in
                              dlet h2 := singlewidth (singlewidth x * singlewidth yh) in
                              dlet h := singlewidth (singlewidth (snd lh1) + singlewidth h2) in
                              cstZsingle_to_double (fst lh1) h))
              ; (forall xl xh yl yh,
                    0 <= bitwidth
                    -> 1 <= lgcarrymax
                    -> doublewidth (cstZsingle_to_double xl xh + cstZsingle_to_double yl yh)
                       = (dlet lc := singlewidth_carry (Z.add_get_carry_full cstZ_pow2_bitwidth (singlewidth xl) (singlewidth yl)) in
                              dlet hc := singlewidth_carry (Z.add_with_get_carry_full cstZ_pow2_bitwidth (carrywidth (snd lc)) (singlewidth xh) (singlewidth yh)) in
                              cstZsingle_to_double (fst lc) (fst hc)))
              ; (forall x yl yh,
                    0 <= bitwidth
                    -> 1 <= lgcarrymax
                    -> doublewidth (singlewidth x + cstZsingle_to_double yl yh)
                       = (dlet lc := singlewidth_carry (Z.add_get_carry_full cstZ_pow2_bitwidth (singlewidth x) (singlewidth yl)) in
                              dlet h := singlewidth (Z.add(*_with_carry*) (carrywidth (snd lc)) (*(singlewidth ('0))*) (singlewidth yh)) in
                              cstZsingle_to_double (fst lc) h))
              ; (forall xl xh y,
                    0 <= bitwidth
                    -> 1 <= lgcarrymax
                    -> doublewidth (cstZsingle_to_double xl xh + singlewidth y)
                       = (dlet lc := singlewidth_carry (Z.add_get_carry_full cstZ_pow2_bitwidth (singlewidth xl) (singlewidth y)) in
                              dlet h := singlewidth (Z.add(*_with_carry*) (carrywidth (snd lc)) (singlewidth xh) (*(singlewidth ('0))*)) in
                              cstZsingle_to_double (fst lc) h))
              ; (forall xl xh mask,
                    0 < mask < 2^bitwidth
                    -> singlewidth (cstZsingle_to_double xl xh &' singlewidth ('mask))
                       = singlewidth (singlewidth xl &' singlewidth ('mask)))
              ; (forall xl xh mask,
                    0 < mask < 2^bitwidth
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
              ; (forall xl xh offset,
                    0 < offset < bitwidth
                    -> doublewidth (cstZsingle_to_double xl xh >> singlewidth ('offset))
                       = (dlet l := singlewidth
                                      (Z.lor (singlewidth (singlewidth xl >> singlewidth ('offset)))
                                             (singlewidth
                                                (Z.truncating_shiftl
                                                   (singlewidth ('bitwidth))
                                                   (singlewidth xh)
                                                   (singlewidth ('(bitwidth - offset)))))) in
                              dlet h := singlewidth
                                          (singlewidth xh >> singlewidth ('offset)) in
                              cstZsingle_to_double l h))
              ; (forall xl xh rbitwidth,
                    0 < bitwidth -> bitwidth ∈ rbitwidth
                    -> singlewidth (cstZsingle_to_double xl xh >> cstZ rbitwidth ('bitwidth))
                       = singlewidth xh)
             ]
          ]%Z%zrange.

  Definition multiret_split_rewrite_rulesT : Datatypes.list (Datatypes.bool * Prop)
    := Eval cbv [myapp mymap myflatten] in
        myflatten
          [mymap dont_do_again []
           ; mymap
               do_again
               [(forall A B x y, @fst A B (x, y) = x)
                ; (forall A B x y, @snd A B (x, y) = y)
                    (** In order to avoid tautological compares, we need to deal with carry/borrows being 0 *)
                ; (forall r0 s x y r1 r2,
                      0 ∈ r0 ->
                      cstZZ r1 r2 (Z.add_with_get_carry_full s (cstZ r0 ('0)) x y)
                      = cstZZ r1 r2 (Z.add_get_carry_full s x y))
                ; (forall r0 s x y r1 r2,
                      0 ∈ r0 ->
                      cstZZ r1 r2 (Z.sub_with_get_borrow_full s (cstZ r0 ('0)) x y)
                      = cstZZ r1 r2 (Z.sub_get_borrow_full s x y))
                ; (forall r0 s x y r1 r2,
                      0 ∈ r0 ->
                      cstZZ r1 r2 (Z.sub_with_get_borrow_full s y x (cstZ r0 ('0)))
                      = cstZZ r1 r2 (Z.sub_get_borrow_full s x y))
               ]
           ; mymap
               dont_do_again
               [(forall A B x y, @fst A B (x, y) = x)
                ; (forall A B x y, @snd A B (x, y) = y)
                ; ((** At this point, we need zeros to be casted up to bitwidth range, rather than to 0-range, so we add a rule to widen the casts *)
                 forall c rc,
                   c ∈ rc -> c ∈ singlewidth_range -> rc <> singlewidth_range
                   -> cstZ rc ('c) = singlewidth ('c))
                ; (forall x y rpow2_bitwidth,
                      0 <= lgcarrymax <= bitwidth -> 2^bitwidth ∈ rpow2_bitwidth
                      -> singlewidth_carry (Z.add_get_carry_full (cstZ rpow2_bitwidth ('(2^bitwidth))) (singlewidth x) (singlewidth y))
                         = (dlet sum_xy := singlewidth (singlewidth x + singlewidth y) in
                                dlet carry_xy := carrywidth (Z.ltz (singlewidth sum_xy) (singlewidth x)) in
                                (singlewidth sum_xy, carrywidth carry_xy)))
                ; (forall c x y rpow2_bitwidth,
                      0 <= lgcarrymax <= bitwidth -> 2^bitwidth ∈ rpow2_bitwidth
                      -> singlewidth_carry (Z.add_with_get_carry_full (cstZ rpow2_bitwidth ('(2^bitwidth))) (carrywidth c) (singlewidth x) (singlewidth y))
                         = (dlet sum_cx := singlewidth (carrywidth c + singlewidth x) in
                                dlet carry_cx := carrywidth (Z.ltz (singlewidth sum_cx) (singlewidth x)) in
                                dlet sum_cxy := singlewidth (singlewidth sum_cx + singlewidth y) in
                                dlet carry_cx_y := carrywidth (Z.ltz (singlewidth sum_cxy) (singlewidth y)) in
                                dlet carry_cxy := carrywidth (carrywidth carry_cx + carrywidth carry_cx_y) in
                                (singlewidth sum_cxy, carrywidth carry_cxy)))

                ; (forall x y rpow2_bitwidth,
                      0 <= lgcarrymax <= bitwidth -> 2^bitwidth ∈ rpow2_bitwidth
                      -> singlewidth_carry (Z.sub_get_borrow_full (cstZ rpow2_bitwidth ('(2^bitwidth))) (singlewidth x) (singlewidth y))
                         = (dlet diff_xy := singlewidth (singlewidth x - singlewidth y) in
                                dlet borrow_xy := carrywidth (Z.ltz (singlewidth x) (singlewidth diff_xy)) in
                                (singlewidth diff_xy, carrywidth borrow_xy)))
                ; (forall c x y rpow2_bitwidth,
                      0 <= lgcarrymax <= bitwidth -> 2^bitwidth ∈ rpow2_bitwidth
                      -> singlewidth_carry (Z.sub_with_get_borrow_full (cstZ rpow2_bitwidth ('(2^bitwidth))) (carrywidth c) (singlewidth x) (singlewidth y))
                         = (dlet diff_xy := singlewidth (singlewidth x - singlewidth y) in
                                dlet borrow_xy := carrywidth (Z.ltz (singlewidth x) (singlewidth diff_xy)) in
                                dlet diff_xyc := singlewidth (singlewidth diff_xy - carrywidth c) in
                                dlet borrow_xy_c := carrywidth (Z.ltz (singlewidth diff_xy) (singlewidth diff_xyc)) in
                                dlet borrow_xyc := carrywidth (carrywidth borrow_xy + carrywidth borrow_xy_c) in
                                (singlewidth diff_xyc, carrywidth borrow_xyc)))

                ; (forall x y rpow2_bitwidth,
                      0 <= lgcarrymax <= bitwidth -> 2^bitwidth ∈ rpow2_bitwidth
                      -> pairsinglewidth (Z.mul_split (cstZ rpow2_bitwidth ('(2^bitwidth))) (singlewidth x) (singlewidth y))
                         = (dlet low := singlewidth (singlewidth x * singlewidth y) in
                                dlet high := singlewidth (Z.mul_high (cstZ rpow2_bitwidth ('(2^bitwidth))) (singlewidth x) (singlewidth y)) in
                                (singlewidth low, singlewidth high)))
                ; (forall x y two_pow_n r,
                      0 <= lgcarrymax <= bitwidth
                      -> two_pow_n = 2 ^ Z.log2 two_pow_n
                      -> 0 < Z.log2 two_pow_n < bitwidth
                      -> bitwidth < Z.log2 two_pow_n + lgcarrymax
                      -> two_pow_n ∈ r
                      -> singlewidth_carry
                           (Z.add_get_carry_full (cstZ r ('two_pow_n)) (singlewidth x) (singlewidth y))
                         = (dlet sum_xy := singlewidth (singlewidth x + singlewidth y) in
                                dlet carry_xy := carrywidth (Z.ltz (singlewidth sum_xy) (singlewidth x)) in
                                dlet low := singlewidth
                                              (Z.land (singlewidth sum_xy) (singlewidth ('(two_pow_n - 1)))) in
                                dlet high :=
                              singlewidth
                                (Z.add (singlewidth (Z.shiftr (singlewidth sum_xy)
                                                              (singlewidth ('(Z.log2 two_pow_n)))))
                                       (singlewidth (Z.shiftl (carrywidth carry_xy)
                                                              (singlewidth ('(bitwidth - Z.log2 two_pow_n))))))
                              in
                                (singlewidth low, singlewidth high)))
                ; (forall c x y two_pow_n r,
                      0 <= lgcarrymax <= bitwidth
                      -> two_pow_n = 2 ^ Z.log2 two_pow_n
                      -> 0 < Z.log2 two_pow_n < bitwidth
                      -> bitwidth + 1 < Z.log2 two_pow_n + lgcarrymax
                      -> two_pow_n ∈ r
                      -> singlewidth_carry
                           (Z.add_with_get_carry_full (cstZ r ('two_pow_n)) (carrywidth c) (singlewidth x) (singlewidth y))
                         = (dlet sum_cx := singlewidth (carrywidth c + singlewidth x) in
                                dlet carry_cx := carrywidth (Z.ltz (singlewidth sum_cx) (singlewidth x)) in
                                dlet sum_cxy := singlewidth (singlewidth sum_cx + singlewidth y) in
                                dlet carry_cxy := carrywidth (Z.ltz (singlewidth sum_cxy) (singlewidth y)) in
                                dlet carry := singlewidth (Z.add (carrywidth carry_cx) (carrywidth carry_cxy)) in
                                dlet low := singlewidth
                                              (Z.land (singlewidth sum_cxy) (singlewidth ('(two_pow_n - 1)))) in
                                dlet high := singlewidth
                                               (Z.add (singlewidth (Z.shiftr (singlewidth sum_cxy)
                                                                             (singlewidth ('(Z.log2 two_pow_n)))))
                                                      (singlewidth (Z.shiftl (carrywidth carry)
                                                                             (singlewidth ('(bitwidth - Z.log2 two_pow_n)))))) in
                                (singlewidth low, singlewidth high)))
                ; (forall x y two_pow_n r,
                      0 <= lgcarrymax <= bitwidth
                      -> two_pow_n = 2 ^ Z.log2 two_pow_n
                      -> 0 < Z.log2 two_pow_n < bitwidth
                      -> bitwidth < Z.log2 two_pow_n + lgcarrymax
                      -> two_pow_n ∈ r
                      -> singlewidth_carry
                           (Z.sub_get_borrow_full (cstZ r ('two_pow_n)) (singlewidth x) (singlewidth y))
                         = (dlet diff_xy := singlewidth (singlewidth x - singlewidth y) in
                                dlet borrow_xy := carrywidth (Z.ltz (singlewidth x) (singlewidth diff_xy)) in
                                dlet low := singlewidth
                                              (Z.land (singlewidth diff_xy) (singlewidth ('(two_pow_n - 1)))) in
                                dlet high :=
                              singlewidth
                                (Z.sub (singlewidth (Z.shiftl (carrywidth borrow_xy)
                                                              (singlewidth ('(bitwidth - Z.log2 two_pow_n)))))
                                       (singlewidth (Z.shiftr (singlewidth diff_xy)
                                                              (singlewidth ('(Z.log2 two_pow_n))))))
                              in
                                (singlewidth low, carrywidth high)))
                ; (forall c x y two_pow_n r,
                      0 <= lgcarrymax <= bitwidth
                      -> two_pow_n = 2 ^ Z.log2 two_pow_n
                      -> 0 < Z.log2 two_pow_n < bitwidth
                      -> bitwidth < Z.log2 two_pow_n + lgcarrymax
                      -> two_pow_n ∈ r
                      -> singlewidth_carry
                           (Z.sub_with_get_borrow_full (cstZ r ('two_pow_n)) (carrywidth c) (singlewidth x) (singlewidth y))
                         = (dlet diff_xy := singlewidth (singlewidth x - singlewidth y) in
                                dlet borrow_xy := carrywidth (Z.ltz (singlewidth x) (singlewidth diff_xy)) in
                                dlet diff_xyc := singlewidth (singlewidth diff_xy - carrywidth c) in
                                dlet borrow_xyc := carrywidth (Z.ltz (singlewidth diff_xy) (singlewidth diff_xyc)) in
                                dlet borrow :=  singlewidth (carrywidth borrow_xy + carrywidth borrow_xyc) in
                                dlet low := singlewidth
                                              (Z.land (singlewidth diff_xyc) (singlewidth ('(two_pow_n - 1)))) in
                                dlet high :=
                              singlewidth
                                (Z.sub (singlewidth (Z.shiftl (carrywidth borrow)
                                                              (singlewidth ('(bitwidth - Z.log2 two_pow_n)))))
                                       (singlewidth (Z.shiftr (singlewidth diff_xyc)
                                                              (singlewidth ('(Z.log2 two_pow_n))))))
                              in
                                (singlewidth low, carrywidth high)))
               ]
           ; mymap
               do_again
               [ (* [do_again], so that if one of the arguments is concrete, we automatically get the rewrite rule for [Z_cast] applying to it *)
                 (forall rx ry x y, cstZZ rx ry (x, y) = (cstZ rx x, cstZ ry y))
               ]
          ]%Z%zrange.

  Definition noselect_rewrite_rulesT : list (bool * Prop)
    := Eval cbv [myapp mymap myflatten] in
        mymap
          dont_do_again
          [(* no-op rule to prevent firing on selects between 0 and mask (since
               these can be succinctly expressed as 0-c *)
            (forall rc c,
                singlewidth (Z.zselect (cstZ rc c)
                                       (singlewidth ('0))
                                       (singlewidth ('(2^bitwidth - 1))))
                = singlewidth (Z.zselect (cstZ rc c)
                                         (singlewidth ('0))
                                         (singlewidth ('(2^bitwidth - 1)))))
            ; (forall rc c x y,
                  0 <= bitwidth ->
                  singlewidth (Z.zselect (cstZ rc c) (singlewidth x) (singlewidth y))
                  = (dlet a :=
                       singlewidth
                         (Z.zselect (cstZ rc c)
                                    (singlewidth ('0))
                                    (singlewidth ('(2^bitwidth - 1)))) in
                         dlet b :=
                         singlewidth (Z.lxor (singlewidth a)
                                             (singlewidth ('(2^bitwidth-1)))) in
                           singlewidth
                             (Z.lor (singlewidth (Z.land (singlewidth y) (singlewidth a)))
                                    (singlewidth (Z.land (singlewidth x) (singlewidth b))))))
          ]%Z.
End with_bitwidth.
