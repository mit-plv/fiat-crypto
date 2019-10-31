import tactic.norm_num
open prod

example (f g : list ℤ) : (associational.split 65536 [(1, list.nth_default 0 f 0 * list.nth_default 0 g 0)]).snd = [] :=
begin
  rw [associational.split_val], norm_num [associational.split_val, (∘), list.filter], norm_num [associational.split_val, (∘), list.filter]
end


import algebra.group_power
open prod
universes u v w ℓ

def let_in {A : Type u} {B : Type v} (x : A) (f : A → B) := f x

@[simp]
def list.flat_map {A : Type u} {B : Type v} (f : A → list B) (ls : list A) : list B :=
  list.bind ls f

@[simp]
def list.combine {A : Type u} {B : Type v} (as : list A) (bs : list B) : list (A × B) :=
  list.zip as bs

-- start len
@[simp]
def list.seq : ℕ → ℕ → list ℕ
| _ 0 := []
| start (nat.succ len') := start :: list.seq (nat.succ start) len'

@[simp] theorem prod.fst_mk {A : Type u} {B : Type v} (x : A) (y : B) : fst (x, y) = x := rfl
@[simp] theorem prod.snd_mk {A : Type u} {B : Type v} (x : A) (y : B) : snd (x, y) = y := rfl

@[simp]
def list.update_nth' {T : Type u} : ∀ (n : ℕ) (f : T → T) (xs : list T), list T
| 0 f [] := []
| 0 f (x' :: xs') := f x' :: xs'
| (nat.succ n') f [] := []
| (nat.succ n') f (x' :: xs') := x' :: list.update_nth' n' f xs'

@[simp]
def list.nth_default {A : Type u} (default : A) : ∀ (ls : list A) (n : ℕ), A
| []        _             := default
| (x :: xs) 0             := x
| (x :: xs) (nat.succ n') := list.nth_default xs n'

@[simp]
def list.expand_helper {A : Type u} : ∀ (default : A) (ls : list A) (n : nat) (idx : nat), list A
| default ls 0             idx := []
| default ls (nat.succ n') idx := list.nth_default default ls idx :: list.expand_helper default ls n' (nat.succ idx)

@[simp]
def list.expand {A} (default : A) (ls : list A) (n : nat) : list A
  := list.expand_helper default ls n 0.


def int.zselect (cond zero_case nonzero_case : ℤ) :=
    if cond = 0 then zero_case else nonzero_case.

@[simp]
def int.to_nat_bit (b : bool) (v : ℤ) : int.to_nat (int.bit b v) = if v < 0 then 0 else nat.bit b (int.to_nat v) :=
begin
  cases v, cases b, refl, refl, simp [int.to_nat], cases b, simp, split_ifs, refl, exfalso, apply h, apply int.neg_succ_lt_zero
end

@[simp]
def int.to_nat_bit0 (v : ℤ) : int.to_nat (bit0 v) = if v < 0 then 0 else bit0 (int.to_nat v) := int.to_nat_bit ff _

@[simp]
def int.to_nat_bit1 (v : ℤ) : int.to_nat (bit1 v) = if v < 0 then 0 else bit1 (int.to_nat v) := int.to_nat_bit tt _

@[simp]
def int.to_nat_0 : int.to_nat 0 = 0 := rfl

@[simp]
def int.to_nat_1 : int.to_nat 1 = 1 := rfl

@[simp]
def associational.eval (p : list (ℤ × ℤ)) : ℤ :=
  list.foldr (λ x y, x + y) 0 (list.map (λ p, fst p * snd p) p)

@[simp]
def associational.mul (p q : list (ℤ × ℤ)) : list (ℤ × ℤ) :=
  list.flat_map (λ t,
    list.map (λ t',
      (fst t * fst t', snd t * snd t'))
    q) p

@[simp]
def associational.square (p : list (ℤ × ℤ)) : list (ℤ × ℤ) :=
  list.rec
    []
    (λ t ts acc,
       (let_in (2 * snd t) (λ two_t2,
        (fst t * fst t, snd t * snd t)
          :: list.map (λ t',
               (fst t * fst t', two_t2 * snd t'))
             ts))
       ++ acc)
    p

@[simp]
def associational.negate_snd (p : list (ℤ × ℤ)) : list (ℤ × ℤ) :=
  list.map (λ cx, (fst cx, -snd cx)) p

-- @[simp]
-- def associational.split (s : ℤ) (p : list (ℤ × ℤ)) : list (ℤ × ℤ) × list (ℤ × ℤ)
--     := let hi_lo := list.partition (λ t, (fst t) % s = 0) p in
--        (snd hi_lo, list.map (λ t, (fst t / s, snd t)) (fst hi_lo)).

def associational.split (s : ℤ) (p : list (ℤ × ℤ)) : list (ℤ × ℤ) × list (ℤ × ℤ) :=
  let (a, b) := list.partition (λ t, (fst t) % s = 0) p in
  (b, list.map (λ t, (fst t / s, snd t)) a)

@[simp] theorem associational.split_val {s : ℤ} {p : list (ℤ × ℤ)} {a b}
  (h : list.partition (λ t, (prod.fst t) % s = 0) p = (a, b)) :
  associational.split s p = (b, list.map (λ t, (fst t / s, snd t)) a) :=
by rw [associational.split, h, associational.split]

def associational.reduce (s c p) : list (ℤ × ℤ) :=
  let (a, b) := associational.split s p in
  a ++ associational.mul c b

@[simp] theorem associational.reduce_val (s c p) {a b}
  (h : associational.split s p = (a, b)) :
  associational.reduce s c p = a ++ associational.mul c b :=
by rw [associational.reduce, h, associational.reduce]


-- @[simp]
-- def associational.reduce (s:ℤ) (c:list _) (p:list _) : list (ℤ × ℤ) :=
--     let lo_hi := associational.split s p in fst lo_hi ++ associational.mul c (snd lo_hi)

@[simp]
def associational.repeat_reduce : ∀ (n : nat) (s:ℤ) (c:list (ℤ × ℤ)) (p:list (ℤ × ℤ)), list (ℤ × ℤ)
| 0             s c p := p
| (nat.succ n') s c p :=
    let lo_hi := associational.split s p in
    if (list.length (snd lo_hi) = 0)
    then p
    else let p := fst lo_hi ++ associational.mul c (snd lo_hi) in
         associational.repeat_reduce n' s c p

@[simp]
def associational.let_bind_for_reduce_square (c:list (ℤ × ℤ)) (p:list (ℤ × ℤ)) : list ((ℤ × ℤ) × list(ℤ × ℤ) × list(ℤ × ℤ) × list(ℤ × ℤ)) :=
    let two : list (ℤ × ℤ) := [(1,2)] in -- (weight, value)
    list.map (λ t, let_in (associational.mul [t] c) (λ c_t, let_in (associational.mul c_t two) (λ two_c_t, let_in (associational.mul [t] two) (λ two_t, (t, c_t, two_c_t, two_t))))) p

@[simp]
def associational.reduce_square (s:ℤ) (c:list (ℤ × ℤ)) (p:list (ℤ × ℤ)) : list (ℤ × ℤ) :=
    let p := associational.let_bind_for_reduce_square c p in
    let div_s := list.map (λ t : ℤ × ℤ, (fst t / s, snd t)) in
    list.rec
      []
      (λ t ts acc,
        (let (t, c_t, two_c_t, two_t) := t in
        (if ((fst t * fst t) % s = 0)
            then div_s (associational.mul [t] c_t)
            else associational.mul [t] [t])
             ++ (list.flat_map
                   (λ pat : (ℤ × ℤ) × (list (ℤ × ℤ)) × (list (ℤ × ℤ)) × list (ℤ × ℤ),
                     let (t', c_t', two_c_t', two_t') := pat in
                     if ((fst t * fst t') % s = 0)
                     then div_s
                              (if fst t' <= fst t
                               then associational.mul [t'] two_c_t
                               else associational.mul [t] two_c_t')
                     else (if fst t' <= fst t
                             then associational.mul [t'] two_t
                             else associational.mul [t] two_t'))
                   ts))
            ++ acc)
      p

@[simp]
def associational.bind_snd (p : list (ℤ × ℤ)) :=
  list.map (λ t, let_in (snd t) (λ t2, (fst t, t2))) p

-- @[simp]
def associational.carryterm (w fw:ℤ) (t:ℤ × ℤ) :=
  if (fst t = w)
  then let_in (snd t)         (λ t2,
       let_in (t2 / fw)       (λ d2,
       let_in (t2 % fw) (λ m2,
       [(w * fw, d2), (w,m2)])))
  else [t]

@[simp] theorem associational.carryterm_pos (w fw b) :
  associational.carryterm w fw (w, b) =
  let_in b               (λ t2,
  let_in (t2 / fw)       (λ d2,
  let_in (t2 % fw) (λ m2,
  [(w * fw, d2), (w,m2)]))) := if_pos rfl

@[simp] theorem associational.carryterm_neg {w fw a b}
  (h : a ≠ w) : associational.carryterm w fw (a, b) = [(a, b)] := if_neg h

@[simp]
def associational.carry (w fw:ℤ) (p:list (ℤ × ℤ)):=
  list.flat_map (associational.carryterm w fw) p

section
  parameters (weight : ℕ → ℤ)

  @[simp]
  def positional.to_associational (n:ℕ) (xs:list ℤ) : list (ℤ × ℤ)
    := list.combine (list.map weight (list.seq 0 n)) xs

  @[simp]
  def positional.zeros (n : ℕ) : list ℤ := list.repeat 0 n.

  @[simp]
  def positional.add_to_nth (i : ℕ) (x : ℤ) (ls : list ℤ) : list ℤ
    := list.update_nth' i (λ y, x + y) ls.

  @[simp]
  def positional.place (t:ℤ×ℤ) : ∀ (i:ℕ), ℕ × ℤ
  | 0             := (0, fst t * snd t)
  | (nat.succ i') := let i := nat.succ i' in
                     if ((fst t) % (weight i) = 0)
                     then (i, let c := fst t / weight i in c * snd t)
                     else positional.place i'

  @[simp]
  def positional.from_associational (n : ℕ) (p:list (ℤ×ℤ)) :=
    list.foldr (λ t ls,
      let_in (positional.place t (nat.pred n)) (λ p,
      positional.add_to_nth (fst p) (snd p) ls )) (positional.zeros n) p.

  @[simp]
  def positional.from_associational_cons (n : ℕ) (p : ℤ × ℤ) (ps:list (ℤ×ℤ))
    : positional.from_associational n (p :: ps)
      = list.foldr (λ t ls,
          let_in (positional.place t (nat.pred n)) (λ p,
          positional.add_to_nth (fst p) (snd p) ls )) (positional.zeros n) (p::ps)
      := rfl

  @[simp]
  def positional.extend_to_length (n_in n_out : ℕ) (p:list ℤ) : list ℤ :=
    p ++ positional.zeros (n_out - n_in).

  @[simp]
  def positional.drop_high_to_length (n : ℕ) (p:list ℤ) : list ℤ :=
    list.take n p.

  section
    parameters (s:ℤ)
               (c:list (ℤ×ℤ))

    @[simp]
    def positional.mulmod (n:ℕ) (a b:list ℤ) : list ℤ
      := let a_a := positional.to_associational n a in
         let b_a := positional.to_associational n b in
         let ab_a := associational.mul a_a b_a in
         let abm_a := associational.repeat_reduce n s c ab_a in
         positional.from_associational n abm_a.

    @[simp]
    def positional.squaremod (n:ℕ) (a:list ℤ) : list ℤ
      := let a_a := positional.to_associational n a in
         let aa_a := associational.reduce_square s c a_a in
         let aam_a := associational.repeat_reduce (nat.pred n) s c aa_a in
         positional.from_associational n aam_a.

  end

  @[simp]
  def positional.add (n:ℕ) (a b:list ℤ) : list ℤ
    := let a_a := positional.to_associational n a in
       let b_a := positional.to_associational n b in
       positional.from_associational n (a_a ++ b_a).

  section
    @[simp]
    def positional.carry (n m : ℕ) (index:ℕ) (p:list ℤ) : list ℤ :=
      positional.from_associational
        m (@associational.carry (weight index)
                                (weight (nat.succ index) / weight index)
                                (positional.to_associational n p)).

    @[simp]
    def positional.carry_reduce (n : ℕ) (s:ℤ) (c:list (ℤ × ℤ))
               (index:ℕ) (p : list ℤ) :=
      positional.from_associational
        n (associational.reduce
             s c (positional.to_associational (nat.succ n) (@positional.carry n (nat.succ n) index p))).
    @[simp]
    def positional.chained_carries (n : _) (s : _) (c : _) (p : _) (idxs : list nat) :=
      list.foldr (λ a b, positional.carry_reduce n s c a b) p (list.reverse idxs).
    @[simp]
    def positional.chained_carries_no_reduce (n : _) (p : _) (idxs : list nat) :=
      list.foldr (λ a b, positional.carry n n a b) p (list.reverse idxs).
    @[simp]
    def positional.encode (n : _) (s : _) (c : _) (x : ℤ) : list ℤ :=
      positional.chained_carries n s c (positional.from_associational n [(1,x)]) (list.seq 0 n).
    @[simp]
    def positional.encode_no_reduce (n : _) (x : ℤ) : list ℤ :=
      positional.chained_carries_no_reduce n (positional.from_associational n [(1,x)]) (list.seq 0 n).
  end

  section
    parameters (n:ℕ)
               (s:ℤ)
               (c:list (ℤ × ℤ))
               (coef:ℤ).

    @[simp]
    def positional.negate_snd (a:list ℤ) : list ℤ
      := let A := positional.to_associational n a in
         let negA := associational.negate_snd A in
         positional.from_associational n negA.

    @[simp]
    def positional.scmul (x:ℤ) (a:list ℤ) : list ℤ
      := let A := positional.to_associational n a in
         let R := associational.mul A [(1, x)] in
         positional.from_associational n R.

    @[simp]
    def positional.balance : list ℤ
      := positional.scmul coef (positional.encode n s c (s - associational.eval c)).

    @[simp]
    def positional.sub (a b:list ℤ) : list ℤ
      := let ca := positional.add n positional.balance a in
         let _b := positional.negate_snd b in
         positional.add n ca _b.

    @[simp]
    def positional.opp (a:list ℤ) : list ℤ
      := positional.sub (positional.zeros n) a.
  end

  section
    @[simp]
    def positional.zselect (mask cond:ℤ) (p:list ℤ) :=
      let_in (int.zselect cond 0 mask) (λ t, list.map (int.land t) p)

    @[simp]
    def positional.select (cond:ℤ) (if_zero if_nonzero:list ℤ) :=
      list.map (λ pq, let (p, q) := pq in int.zselect cond p q) (list.combine if_zero if_nonzero).

  end
end

section
  open positional
  parameters (limbwidth_num limbwidth_den : ℤ)
             (s : ℤ)
             (c : list (ℤ×ℤ))
             (n : ℕ)
             (len_c : ℕ)
             (idxs : list ℕ)

  @[simp]
  def modops.weight (i : ℕ) : ℤ
    := 2^(int.to_nat (-(-(limbwidth_num * i) / limbwidth_den))).

  @[simp]
  def modops.carry_mulmod (f g : list ℤ) : list ℤ :=
    chained_carries modops.weight n s c (mulmod modops.weight s c n f g) idxs

  @[simp]
  def modops.carry_squaremod (f : list ℤ) : list ℤ :=
    chained_carries modops.weight n s c (squaremod modops.weight s c n f) idxs

  @[simp]
  def modops.carry_scmulmod (x : ℤ) (f : list ℤ) : list ℤ :=
    chained_carries modops.weight n s c (mulmod modops.weight s c n (encode modops.weight n s c x) f) idxs

  @[simp]
  def modops.carrymod (f : list ℤ) : list ℤ :=
    chained_carries modops.weight n s c f idxs

  @[simp]
  def modops.addmod (f g : list ℤ) : list ℤ :=
    add modops.weight n f g

  @[simp]
  def modops.submod (coef : ℤ) (f g : list ℤ) : list ℤ :=
    sub modops.weight n s c coef f g

  @[simp]
  def modops.oppmod (coef : ℤ) (f : list ℤ) : list ℤ :=
    opp modops.weight n s c coef f

  @[simp]
  def modops.encodemod (f : ℤ) : list ℤ :=
    encode modops.weight n s c f
end

def let_in.lift {A : Type u} {B : Type v} {C : Type w} (F : B → C) (x : A) (f : A → B) : F (let_in x f) = let_in x (λ y, F (f y)) := rfl

def let_in.lift_zip2 {A : Type u} {B : Type v} {C : Type w} (ls : list C) (x : A) (f : A → list B) : list.zip ls (let_in x f) = let_in x (λ y, list.zip ls (f y)) := let_in.lift _ _ _.

def let_in.lift_append1 {A : Type u} {B : Type v} (x : A) (f : A → list B) (ls : list B) : list.append (let_in x f) ls = let_in x (λ y, list.append (f y) ls) := rfl

def let_in.lift_append2 {A : Type u} {B : Type v} (x : A) (f : A → list B) (ls : list B) : list.append ls (let_in x f) = let_in x (λ y, list.append ls (f y)) := rfl

def let_in.lift_foldr {A : Type u} {B : Type v} {C : Type w} (x : A) (f : A → list B) (g : B → C → C) (init : C) : list.foldr g init (let_in x f) = let_in x (λ x, list.foldr g init (f x)) := rfl

def let_in.lift_map {A : Type u} {B : Type v} {C : Type w} (x : A) (f : A → list B) (g : B → C) : list.map g (let_in x f) = let_in x (λ x, list.map g (f x)) := rfl

def let_in.lift_join {A : Type u} {B : Type v} (x : A) (f : A → list (list B)) : list.join (let_in x f) = let_in x (λ x, list.join (f x)) := rfl

def let_in.lift_bind {A : Type u} {B : Type v} {C : Type w} (x : A) (f : A → list B) (g : B → list C) : list.bind (let_in x f) g = let_in x (λ x, list.bind (f x) g) := rfl

def let_in.lift_reduce {A : Type u} (s : ℤ) (c : list (ℤ × ℤ)) (x : A) (f : A → list (ℤ × ℤ)) : associational.reduce s c (let_in x f) = let_in x (λ x, associational.reduce s c (f x)) := rfl

def let_in.lift_from_associational {A : Type u} (f : A → list (ℤ × ℤ)) (weight : ℕ → ℤ) (n : ℕ) (x : A) : positional.from_associational weight n (let_in x f) = let_in x (λ x, positional.from_associational weight n (f x)) := rfl

def let_in.lift_filter {A : Type u} {B : Type v} (x : A) (f : A → list B) (g : B → Prop) [decidable_pred g] : list.filter g (let_in x f) = let_in x (λ x, list.filter g (f x)) := rfl

def let_in.lift_update_nth' {A : Type u} {B : Type v} (x : A) (f : A → list B) (g : B → B) (n : ℕ) : list.update_nth' n g (let_in x f) = let_in x (λ x, list.update_nth' n g (f x)) := rfl

def let_in.split_pair {A : Type u} {A' : Type w} {B : Type v} (x : A) (y : A') (f : A × A' → B) : let_in (x, y) f = let_in x (λ x, let_in y (λ y, f (x, y))) := rfl

def let_in.lift_nat.zero {A : Type v} (f : ℕ → A) : let_in 0 f = f 0 := rfl

def let_in.lift_nat.one {A : Type v} (f : ℕ → A) : let_in 1 f = f 1 := rfl

@[simp]
def ex.n : ℕ := 1 -- 5
@[simp]
def ex.s : ℤ := 2^16 -- 2^255
@[simp]
def ex.c : list (ℤ × ℤ) := [(1, 1)] -- [(1, 19)]
@[simp]
def ex.idxs : list ℕ := [0, 1] -- [0, 1, 2, 3, 4, 0, 1]
@[simp]
def ex.machine_wordsize : ℤ := 8 -- 64

@[simp]
def ex2.n : ℕ := 5
@[simp]
def ex2.s : ℤ := 2^255
@[simp]
def ex2.c : list (ℤ × ℤ) := [(1, 19)]
@[simp]
def ex2.idxs : list ℕ := [0, 1, 2, 3, 4, 0, 1]
@[simp]
def ex2.machine_wordsize : ℤ := 64

local notation `dlet` binders ` ≔ ` b ` in ` c:(scoped P, P) := let_in b c

set_option pp.max_depth 1000000000
-- set_option pp.max_steps 1000000000
--set_option pp.numerals false
open modops
open ex
example (f g : list ℤ) : carry_mulmod machine_wordsize 1 s c n idxs (list.expand 0 f n) (list.expand 0 g n) = [] :=
begin
  norm_num [int.to_nat,(∘),has_append.append,list.append,list.filter,
    associational.split, associational.reduce, associational.carryterm,
    let_in.lift_zip2,let_in.split_pair,let_in.lift_nat.zero,let_in.lift_foldr,let_in.lift_nat.one,let_in.lift_update_nth',let_in.lift_filter,let_in.lift_map,let_in.lift_append1,let_in.lift_append2,let_in.lift_join,let_in.lift_from_associational,let_in.lift_bind,let_in.lift_reduce],
end
#check id
