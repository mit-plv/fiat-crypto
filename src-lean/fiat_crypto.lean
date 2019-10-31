import tactic.norm_num
import algebra.group_power
open prod
universes u v w ℓ

@[simp] def let_in {A : Type u} {B : Type v} (x : A) (f : A → B) := f x

attribute [simp] list.filter

-- start len
@[simp]
def list.seq : ℕ → ℕ → list ℕ
| _ 0 := []
| start (nat.succ len') := start :: list.seq (nat.succ start) len'

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
def list.expand_helper {A : Type u} (f : ℕ → A) : ∀ (n : nat) (idx : nat), list A
| 0             idx := []
| (nat.succ n') idx := f idx :: list.expand_helper n' (nat.succ idx)

@[simp]
def list.expand {A} (f : ℕ → A) (n : nat) : list A := list.map f (list.seq 0 n)

def int.zselect (cond zero_case nonzero_case : ℤ) :=
    if cond = 0 then zero_case else nonzero_case.

@[simp] def associational.mul : ∀ (p q : list (ℕ × ℤ)), list (ℕ × ℤ)
| [] q := []
| ((a, b) :: ts) q :=
  q.map (λ ⟨a', b'⟩, (a * a', b * b')) ++ associational.mul ts q

def associational.square (p : list (ℕ × ℤ)) : list (ℕ × ℤ) :=
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

def associational.negate_snd (p : list (ℕ × ℤ)) : list (ℕ × ℤ) :=
  list.map (λ cx, (fst cx, -snd cx)) p

@[simp]
def associational.split (s : ℕ) (p : list (ℕ × ℤ)) : list (ℕ × ℤ) × list (ℕ × ℤ)
    := let (lo, hi) := list.partition (λ t, (fst t) % s = 0) p in
       (hi, list.map (λ t, (fst t / s, snd t)) lo).

@[simp] def associational.reduce (s:ℕ) (c:list _) (p:list _) : list (ℕ × ℤ) :=
  let (lo, hi) := associational.split s p in lo ++ associational.mul c hi

@[simp]
def associational.repeat_reduce : ∀ (n : nat) (s:ℕ) (c:list (ℕ × ℤ)) (p:list (ℕ × ℤ)), list (ℕ × ℤ)
| 0             s c p := p
| (nat.succ n') s c p :=
    let (lo, hi) := associational.split s p in
    if (list.length hi = 0)
    then p
    else let p := lo ++ associational.mul c hi in
         associational.repeat_reduce n' s c p

@[simp]
def associational.let_bind_for_reduce_square (c:list (ℕ × ℤ)) (p:list (ℕ × ℤ)) : list ((ℕ × ℤ) × list(ℕ × ℤ) × list(ℕ × ℤ) × list(ℕ × ℤ)) :=
    let two : list (ℕ × ℤ) := [(1,2)] in -- (weight, value)
    list.map (λ t, let_in (associational.mul [t] c) (λ c_t, let_in (associational.mul c_t two) (λ two_c_t, let_in (associational.mul [t] two) (λ two_t, (t, c_t, two_c_t, two_t))))) p

@[simp] def associational.reduce_square_aux (s:ℕ) :
  list ((ℕ × ℤ) × list(ℕ × ℤ) × list(ℕ × ℤ) × list(ℕ × ℤ)) → list (ℕ × ℤ)
| [] := []
| ((t, c_t, two_c_t, two_t) :: ts) :=
  let div_s := list.map (λ t : ℕ × ℤ, (fst t / s, snd t)) in
  ((if ((fst t * fst t) % s = 0)
      then div_s (associational.mul [t] c_t)
      else associational.mul [t] [t])
        ++ (ts.bind $ λ ⟨t', c_t', two_c_t', two_t'⟩,
                if ((fst t * fst t') % s = 0)
                then div_s
                        (if fst t' <= fst t
                          then associational.mul [t'] two_c_t
                          else associational.mul [t] two_c_t')
                else (if fst t' <= fst t
                        then associational.mul [t'] two_t
                        else associational.mul [t] two_t')))
      ++ associational.reduce_square_aux ts

@[simp] def associational.reduce_square (s:ℕ) (c:list (ℕ × ℤ)) (p : list (ℕ × ℤ)) : list (ℕ × ℤ) :=
associational.reduce_square_aux s $
  let two : list (ℕ × ℤ) := [(1,2)] in -- (weight, value)
  list.map (λ t, let_in (associational.mul [t] c) (λ c_t, let_in (associational.mul c_t two) (λ two_c_t, let_in (associational.mul [t] two) (λ two_t, (t, c_t, two_c_t, two_t))))) p

@[simp]
def associational.carryterm (w fw:ℕ) : ℕ × ℤ → list (ℕ × ℤ)
| (a, b) :=
  if a = w
  then let_in b         (λ t2,
       let_in (t2 / fw) (λ d2,
       let_in (t2 % fw) (λ m2,
       [(w * fw, d2), (w,m2)])))
  else [(a, b)]

@[simp]
def associational.carry (w fw:ℕ) (p:list (ℕ × ℤ)):=
  p.bind (associational.carryterm w fw)

section
  parameters (weight : ℕ → ℕ)

  @[simp]
  def positional.to_associational (n:ℕ) (xs:list ℤ) : list (ℕ × ℤ)
    := list.enum xs

  @[simp]
  def positional.zeros (n : ℕ) : list ℤ := list.repeat 0 n.

  @[simp]
  def positional.add_to_nth (i : ℕ) (x : ℤ) (ls : list ℤ) : list ℤ
    := list.update_nth' i (λ y, x + y) ls.

  @[simp]
  def positional.place (a : ℕ) (b : ℤ) : ∀ (i:ℕ), ℕ × ℤ
  | 0             := (0, a * b)
  | (nat.succ i') := let i := nat.succ i' in
                     if (a % (weight i) = 0)
                     then (i, let c := a / weight i in c * b)
                     else positional.place i'

  @[simp]
  def positional.from_associational (n : ℕ) : list (ℕ × ℤ) → list ℤ
  | [] := positional.zeros n
  | ((a, b) :: ts) :=
      let_in (positional.place a b (nat.pred n)) $ λ p,
      positional.add_to_nth p.1 p.2 (positional.from_associational ts)

  @[simp]
  def positional.extend_to_length (n_in n_out : ℕ) (p:list ℤ) : list ℤ :=
    p ++ positional.zeros (n_out - n_in).

  @[simp]
  def positional.drop_high_to_length (n : ℕ) (p:list ℤ) : list ℤ :=
    list.take n p.

  section
    parameters (s:ℕ)
               (c:list (ℕ × ℤ))

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
    def positional.carry_reduce (n : ℕ) (s:ℕ) (c:list (ℕ × ℤ))
               (index:ℕ) (p : list ℤ) :=
      positional.from_associational
        n (associational.reduce
             s c (positional.to_associational (nat.succ n) (@positional.carry n (nat.succ n) index p))).

    @[simp] def positional.chained_carries (n s c p) (idxs : list nat) :=
      match list.reverse idxs with
      | [] := p
      | (a::l) := positional.carry_reduce n s c a (by exact _match l)
      end

    @[simp]
    def positional.chained_carries_no_reduce (n p) (idxs : list nat) :=
      match list.reverse idxs with
      | [] := p
      | (a::l) := positional.carry n n a (by exact _match l)
      end

    @[simp]
    def positional.encode (n s c) (x : ℕ) : list ℤ :=
      positional.chained_carries n s c (positional.from_associational n [(1,x)]) (list.seq 0 n).
    @[simp]
    def positional.encode_no_reduce (n : _) (x : ℕ) : list ℤ :=
      positional.chained_carries_no_reduce n (positional.from_associational n [(1,x)]) (list.seq 0 n).
  end

  section
    parameters (n:ℕ)
               (s:ℕ)
               (c:list (ℕ × ℤ))
               (coef:ℕ).

    @[simp]
    def positional.negate_snd (a:list ℤ) : list ℤ
      := let A := positional.to_associational n a in
         let negA := associational.negate_snd A in
         positional.from_associational n negA.

    @[simp]
    def positional.scmul (x:ℕ) (a:list ℤ) : list ℤ
      := let A := positional.to_associational n a in
         let R := associational.mul A [(1, x)] in
         positional.from_associational n R.
  end

  section
    @[simp]
    def positional.zselect (mask cond:ℕ) (p:list ℤ) :=
      let_in (int.zselect cond 0 mask) (λ t, list.map (int.land t) p)

    @[simp]
    def positional.select (cond:ℕ) (if_zero if_nonzero:list ℤ) :=
      list.map (λ pq, let (p, q) := pq in int.zselect cond p q) (list.zip if_zero if_nonzero).

  end
end
@[simp]
def divup (a b : ℕ) : ℕ := (a + b - 1) / b
  -- := 2^(int.to_nat (-(-(limbwidth_num * i) / limbwidth_den))).

section
  open positional
  parameters (limbwidth_num limbwidth_den : ℕ)
             (s : ℕ)
             (c : list (ℕ × ℤ))
             (n : ℕ)
             (len_c : ℕ)
             (idxs : list ℕ)

  @[simp]
  def modops.weight (i : ℕ) : ℕ
    := 2^(divup (limbwidth_num * i) limbwidth_den)

  @[simp]
  def modops.carry_mulmod (f g : list ℤ) : list ℤ :=
    chained_carries modops.weight n s c (mulmod modops.weight s c n f g) idxs

  @[simp]
  def modops.carry_squaremod (f : list ℤ) : list ℤ :=
    chained_carries modops.weight n s c (squaremod modops.weight s c n f) idxs

  @[simp]
  def modops.carry_scmulmod (x : ℕ) (f : list ℤ) : list ℤ :=
    chained_carries modops.weight n s c (mulmod modops.weight s c n (encode modops.weight n s c x) f) idxs

  @[simp]
  def modops.carrymod (f : list ℤ) : list ℤ :=
    chained_carries modops.weight n s c f idxs

  @[simp]
  def modops.addmod (f g : list ℤ) : list ℤ :=
    add modops.weight n f g

  @[simp]
  def modops.encodemod (f : ℕ) : list ℤ :=
    encode modops.weight n s c f
end

def let_in.lift {A : Type u} {B : Type v} {C : Type w} (F : B → C) (x : A) (f : A → B) : F (let_in x f) = let_in x (λ y, F (f y)) := rfl

def let_in.lift_zip2 {A : Type u} {B : Type v} {C : Type w} (ls : list C) (x : A) (f : A → list B) : list.zip ls (let_in x f) = let_in x (λ y, list.zip ls (f y)) := let_in.lift _ _ _.

def let_in.lift_append1 {A : Type u} {B : Type v} (x : A) (f : A → list B) (ls : list B) : list.append (let_in x f) ls = let_in x (λ y, list.append (f y) ls) := rfl

def let_in.lift_append2 {A : Type u} {B : Type v} (x : A) (f : A → list B) (ls : list B) : list.append ls (let_in x f) = let_in x (λ y, list.append ls (f y)) := rfl

def let_in.lift_foldr {A : Type u} {B : Type v} {C : Type w} (x : A) (f : A → list B) (g : B → C → C) (init : C) : list.foldr g init (let_in x f) = let_in x (λ x, list.foldr g init (f x)) := rfl

def let_in.lift_map {A : Type u} {B : Type v} {C : Type w} (x : A) (f : A → list B) (g : B → C) : list.map g (let_in x f) = let_in x (λ x, list.map g (f x)) := rfl

def let_in.lift_join {A : Type u} {B : Type v} (x : A) (f : A → list (list B)) : list.join (let_in x f) = let_in x (λ x, list.join (f x)) := rfl

def let_in.lift_from_associational {A : Type u} (f : A → list (ℕ × ℤ)) (weight : ℕ → ℕ) (n : ℕ) (x : A) : positional.from_associational weight n (let_in x f) = let_in x (λ x, positional.from_associational weight n (f x)) := rfl

def let_in.lift_filter {A : Type u} {B : Type v} (x : A) (f : A → list B) (g : B → Prop) [decidable_pred g] : list.filter g (let_in x f) = let_in x (λ x, list.filter g (f x)) := rfl

def let_in.lift_update_nth' {A : Type u} {B : Type v} (x : A) (f : A → list B) (g : B → B) (n : ℕ) : list.update_nth' n g (let_in x f) = let_in x (λ x, list.update_nth' n g (f x)) := rfl

def let_in.split_pair {A : Type u} {A' : Type w} {B : Type v} (x : A) (y : A') (f : A × A' → B) : let_in (x, y) f = let_in x (λ x, let_in y (λ y, f (x, y))) := rfl

def let_in.lift_nat.zero {A : Type v} (f : ℕ → A) : let_in 0 f = f 0 := rfl

def let_in.lift_nat.one {A : Type v} (f : ℕ → A) : let_in 1 f = f 1 := rfl

@[simp]
def ex.n : ℕ := 1 -- 5
@[simp]
def ex.s : ℕ := 2^16 -- 2^255
@[simp]
def ex.c : list (ℕ × ℤ) := [(1, 1)] -- [(1, 19)]
@[simp]
def ex.idxs : list ℕ := [0, 1] -- [0, 1, 2, 3, 4, 0, 1]
@[simp]
def ex.machine_wordsize : ℕ := 8 -- 64

@[simp]
def ex2.n : ℕ := 5
@[simp]
def ex2.s : ℕ := 2^255
@[simp]
def ex2.c : list (ℕ × ℤ) := [(1, 19)]
@[simp]
def ex2.idxs : list ℕ := [0, 1, 2, 3, 4, 0, 1]
@[simp]
def ex2.machine_wordsize : ℕ := 64

local notation `dlet` binders ` ≔ ` b ` in ` c:(scoped P, P) := let_in b c

-- set_option pp.max_depth 1000000000
-- set_option pp.max_steps 1000000000
--set_option pp.numerals false
open modops
open ex2
-- set_option trace.simplify.rewrite true
example (f g : ℕ → ℤ) : carry_mulmod machine_wordsize 1 s c n idxs (list.expand f n) (list.expand g n) = [0, 0, 0, 0, 0] :=
begin
  norm_num [nat.succ_eq_add_one, -add_comm, -list.partition_eq_filter_filter, list.enum,
    list.enum_from, list.partition, -list.reverse_cons, list.reverse, list.reverse_core],
end
