Require Crypto.Assembly.Parse Crypto.Assembly.Parse.Examples.fiat_25519_carry_square_optimised_seed20.
Definition lines' := Eval native_compute in
  Assembly.Parse.parse
  Assembly.Parse.Examples.fiat_25519_carry_square_optimised_seed20.example.
Definition lines := Eval cbv in ErrorT.invert_result lines'.
Require Crypto.Assembly.Parse Crypto.Assembly.Parse.Examples.fiat_25519_carry_square_optimised_seed10.
Definition lines'10 := Eval native_compute in
  Assembly.Parse.parse
  Assembly.Parse.Examples.fiat_25519_carry_square_optimised_seed10.example.
Definition lines10 := Eval cbv in ErrorT.invert_result lines'10.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Crypto.Util.Tuple.
Require Import Util.OptionList.
Require Import Crypto.Util.ErrorT.
Module Import List.
  Section IndexOf.
    Context [A] (f : A -> bool).
    Fixpoint indexof (l : list A) : option nat :=
      match l with
      | nil => None
      | cons a l =>
          if f a then Some 0
          else option_map S (indexof l )
      end.
    Lemma indexof_none l (H : indexof l = None) :
      forall i a, nth_error l i = Some a -> f a = false.
    Admitted.
    Lemma indexof_Some l i (H : indexof l = Some i) :
      exists a, nth_error l i = Some a -> f a = true.
    Admitted.
    Lemma indexof_first l i (H : indexof l = Some i) :
      forall j a, j < i -> nth_error l j = Some a -> f a = false.
    Admitted.
  End IndexOf.


  Section FoldMap. (* map over a list in the state monad *)
    Context [A B S] (f : A -> S -> B * S).
    Fixpoint foldmap (l : list A) (s : S) : list B * S :=
      match l with
      | nil => (nil, s)
      | cons a l =>
          let b_s := f a s in
          let bs_s := foldmap l (snd b_s) in
          (cons (fst b_s) (fst bs_s), snd bs_s)
      end.
  End FoldMap.
End List.

Require Coq.Sorting.Mergesort.
Module NOrder <: Orders.TotalLeBool.
  Local Open Scope N_scope.
  Definition t := N.
  Definition ltb := N.ltb.
  Definition leb := N.leb.
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb ltb]; intros a1 a2.
    repeat first [ rewrite !Bool.andb_true_iff
                 | rewrite !Bool.orb_true_iff
                 | rewrite !N.eqb_eq
                 | rewrite !N.ltb_lt
                 | rewrite !N.leb_le ].
    Lia.lia.
  Qed.
End NOrder.
Module NSort := Mergesort.Sort NOrder.
Notation sortN := NSort.sort.

Require Import Crypto.Assembly.Syntax.
Definition idx := N.
Local Set Boolean Equality Schemes.
Variant opname := old (_:REG*option nat) | const (_ : N) | add | addcarry | notaddcarry | neg | shl | shr | and | or | xor | slice (lo sz : N) | mul | mulhuu | set_slice (lo sz : N)(* | ... *).

Definition associative o := match o with add|mul|or|and => true | _ => false end.
Definition commutative o := match o with add|addcarry|mul|mulhuu => true | _ => false end.
Definition identity o := match o with add|addcarry => Some 0%N | mul|mulhuu=>Some 1%N |_=> None end.

Class OperationSize := operation_size : N.
Definition op : Set := opname * OperationSize.
Definition op_beq := Prod.prod_beq _ _ opname_beq N.eqb.

Definition node (A : Set) : Set := op * list A.

Local Unset Elimination Schemes.
Inductive expr : Set :=
| ExprRef (_ : idx)
| ExprApp (_ : node expr).
  (* Note: need custom induction principle *)
Local Unset Elimination Schemes.
Definition invert_ExprRef (e : expr) : option idx :=
  match e with ExprRef i => Some i | _ => None end.

Definition node_beq [A : Set] (arg_eqb : A -> A -> bool) : node A -> node A -> bool := 
  Prod.prod_beq _ _ op_beq (ListUtil.list_beq _ arg_eqb).

Definition dag := list (node idx).

Section Reveal.
  Context (dag : dag).
  Definition reveal_step reveal (i : idx) : expr :=
    match List.nth_error dag (N.to_nat i) with
    | None => (* undefined *) ExprRef i
    | Some (op, args) => ExprApp (op, List.map reveal args)
    end.
  Fixpoint reveal (n : nat) (i : idx) :=
    match n with
    | O => ExprRef i
    | S n => reveal_step (reveal n) i
    end.

  Definition reveal_node n '(op, args) :=
    ExprApp (op, List.map (reveal n) args).
End Reveal.

Definition merge_node (n : node idx) (d : dag) : idx * dag :=
  match List.indexof (node_beq N.eqb n) d with
  | Some i => (N.of_nat i, d)
  | None => (N.of_nat (length d), List.app d (cons n nil))
  end.
Fixpoint merge (e : expr) (d : dag) : idx * dag :=
  match e with
  | ExprRef i => (i, d)
  | ExprApp (op, args) =>
    let idxs_d := List.foldmap merge args d in
    let idxs := if commutative (fst op)
                then sortN (fst idxs_d)
                else (fst idxs_d) in
    merge_node (op, idxs) (snd idxs_d)
  end.

Lemma reveal_merge : forall d e, exists n, reveal (snd (merge e d)) n (fst (merge e d)) = e.
Proof.
Admitted.

Require Import Crypto.Util.Option Crypto.Util.Notations.
Import ListNotations.

Require Import Crypto.Util.Option Crypto.Util.Notations.
Import ListNotations.

Definition interp_op o s args :=
  match o, args with
  | add, args => Some (N.land (List.fold_right N.add 0 args) (N.ones s))
  | neg, [a] => Some (N.land (2^s - a) (N.ones s))
  | const z, nil => Some (N.land z (N.ones s))
  (* note: incomplete *)
  | _, _ => None
  end%N.

Definition zconst s (z:Z) :=
  const (if z <? 0 then invert_Some (interp_op neg s [Z.abs_N z]) else Z.to_N z)%Z.

Fixpoint interp_expr (e : expr) : option N :=
  match e with
  | ExprApp ((o,s), arges) =>
      args <- Option.List.lift (List.map interp_expr arges);
      interp_op o s args
  | _ => None
  end%option.

Definition isCst (e : expr) :=
  match e with ExprApp ((const _, _), _) => true | _ => false end.
Definition simplify_expr : expr -> expr :=
  List.fold_left (fun e f => f e)
  [fun e => match interp_expr e with
            | Some v => ExprApp ((const v, 64(*note:arbitrary*)), nil)
            | _ => e end
  ;fun e => match e with
    ExprApp (o, args) =>
    if associative (fst o) then
      ExprApp (o, List.flat_map (fun e' =>
        match e' with
        | ExprApp (o', args') => if op_beq o o' then args' else [e']
        | _ => [e'] end) args)
    else e | _ => e end
  ;fun e => match e with
    ExprApp (o, args) =>
    if commutative (fst o) then
    let csts_exprs := List.partition isCst args in
    match interp_expr (ExprApp (o, fst csts_exprs)) with None => e | Some v =>
    ExprApp (o, ExprApp (const v, snd o, nil):: snd csts_exprs)
    end else e | _ => e end
  ;fun e => match e with
    ExprApp ((slice 0 s',s), [a]) =>
      if N.eqb s s' then a else e | _ => e end
  ;fun e => match e with
    ExprApp (o, args) =>
    match identity (fst o) with
    | Some i => 
        let args := List.filter (fun a => negb (option_beq N.eqb (interp_expr a) (Some i))) args in
        match args with
        | nil => ExprApp ((const i, snd o), nil)
        | cons a nil => a
        | _ => ExprApp (o, args)
        end
    | _ => e end | _ => e end
  ;fun e => match e with ExprApp ((xor,s),[x;y]) =>
    if expr_beq x y then ExprApp ((const 0, s), nil) else e | _ => e end
  ]%N%bool.
Definition simplify (dag : dag) (e : node idx) : expr :=
  simplify_expr (reveal_node dag 2 e).

Definition reg_state := Tuple.tuple (option idx) 16.
Definition flag_state := Tuple.tuple (option idx) 6.
Definition mem_state := list (idx * idx).

Definition get_flag (st : flag_state) (f : FLAG) : option idx
  := let '(cfv, pfv, afv, zfv, sfv, ofv) := st in
     match f with
     | CF => cfv
     | PF => pfv
     | AF => afv
     | ZF => zfv
     | SF => sfv
     | OF => ofv
     end.
Definition set_flag_internal (st : flag_state) (f : FLAG) (v : option idx) : flag_state
  := let '(cfv, pfv, afv, zfv, sfv, ofv) := st in
     (match f with CF => v | _ => cfv end,
      match f with PF => v | _ => pfv end,
      match f with AF => v | _ => afv end,
      match f with ZF => v | _ => zfv end,
      match f with SF => v | _ => sfv end,
      match f with OF => v | _ => ofv end).
Definition set_flag (st : flag_state) (f : FLAG) (v : idx) : flag_state
  := set_flag_internal st f (Some v).
Definition havoc_flag (st : flag_state) (f : FLAG) : flag_state
  := set_flag_internal st f None.
Definition havoc_flags : flag_state
  := (None, None, None, None, None, None).

Definition get_reg (st : reg_state) (ri : nat) : option idx
  := Tuple.nth_default None ri st.
Definition set_reg (st : reg_state) ri (i : idx) : reg_state
  := Tuple.from_list_default None _ (ListUtil.set_nth
       ri
       (Some i)
       (Tuple.to_list _ st)).

Definition load (a : idx) (s : mem_state) : option idx :=
  option_map snd (find (fun p => fst p =? a)%N s).
Definition store (a v : idx) (s : mem_state) : option mem_state :=
  n <- indexof (fun p => fst p =? a)%N s;
  Some (ListUtil.update_nth n (fun ptsto => (fst ptsto, v)) s).

Record symbolic_state := { dag_state :> dag ; symbolic_reg_state :> reg_state ; symbolic_flag_state :> flag_state ; symbolic_mem_state :> mem_state }.
Definition update_dag_with (st : symbolic_state) (f : dag -> dag) : symbolic_state
  := {| dag_state := f st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_reg_with (st : symbolic_state) (f : reg_state -> reg_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := f st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_flag_with (st : symbolic_state) (f : flag_state -> flag_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := f st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_mem_with (st : symbolic_state) (f : mem_state -> mem_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := f st.(symbolic_mem_state) |}.

Module error.
  Variant error :=
  | nth_error_dag (_ : nat)

  | get_flag (f : FLAG)
  | get_reg (r : REG)
  | load (a : idx)
  | store (a v : idx)
  | set_const (_ : CONST) (_ : idx)

  | unimplemented_instruction (_ : NormalInstruction)
  | ambiguous_operation_size (_ : NormalInstruction)

  | failed_to_unify (_ : list (expr * (option idx * option idx))).
End error.
Notation error := error.error.

Definition M T := symbolic_state -> ErrorT (error * symbolic_state) (T * symbolic_state).
Definition ret {A} (x : A) : M A :=
  fun s => Success (x, s).
Definition err {A} (e : error) : M A :=
  fun s => Error (e, s).
Definition some_or {A} (f : symbolic_state -> option A) (e : error) : M A :=
  fun st => match f st with Some x => Success (x, st) | None => Error (e, st) end.
Definition bind {A B} (x : M A) (f : A -> M B) : M B :=
  fun s => (x_s <- x s; f (fst x_s) (snd x_s))%error.
Declare Scope x86symex_scope.
Delimit Scope x86symex_scope with x86symex.
Bind Scope x86symex_scope with M.
Notation "x <- y ; f" := (bind y (fun x => f%x86symex)) : x86symex_scope.
Section MapM. (* map over a list in the state monad *)
  Context [A B] (f : A -> M B).
  Fixpoint mapM (l : list A) : M (list B) :=
    match l with
    | nil => ret nil
    | cons a l => b <- f a; bs <- mapM l; ret (cons b bs)
    end%x86symex.
End MapM.
Definition mapM_ [A B] (f: A -> M B) l : M unit := _ <- mapM f l; ret tt.

Definition GetFlag f : M idx :=
  some_or (fun s => get_flag s f) (error.get_flag f).
Definition GetReg64 ri : M idx :=
  some_or (fun st => get_reg st ri) (error.get_reg (widest_register_of_index ri)).
Definition Load64 (a : idx) : M idx := some_or (load a) (error.load a).
Definition SetFlag f i : M unit :=
  fun s => Success (tt, update_flag_with s (fun s => set_flag s f i)).
Definition HavocFlags : M unit :=
  fun s => Success (tt, update_flag_with s (fun _ => Tuple.repeat None 6)).
Definition SetReg64 rn i : M unit :=
  fun s => Success (tt, update_reg_with s (fun s => set_reg s rn i)).
Definition Store64 (a v : idx) : M unit :=
  ms <- some_or (store a v) (error.store a v);
  fun s => Success (tt, update_mem_with s (fun _ => ms)).
Definition Merge (e : expr) : M idx := fun s =>
  let i_dag := merge e s in
  Success (fst i_dag, update_dag_with s (fun _ => snd i_dag)).
Definition App (n : node idx) : M idx :=
  fun s => Merge (simplify s n) s.
Definition Reveal n (i : idx) : M expr :=
  fun s => Success (reveal s n i, s).

Definition GetReg r : M idx :=
  let '(rn, lo, sz) := index_and_shift_and_bitcount_of_reg r in
  v <- GetReg64 rn;
  App ((slice lo sz, 64%N), [v]).
Definition SetReg r (v : idx) : M unit :=
  let '(rn, lo, sz) := index_and_shift_and_bitcount_of_reg r in
  if N.eqb sz 64
  then SetReg64 rn v (* works even if old value is unspecified *)
  else old <- GetReg64 rn;
       v <- App ((set_slice lo sz, 64%N), [old; v]);
       SetReg64 rn v.

Class AddressSize := address_size : N.
Definition Address {sa : AddressSize} (a : MEM) : M idx :=
  base <- GetReg a.(mem_reg);
  index <- match a.(mem_extra_reg) with
           | Some r => GetReg r
           | None => App ((const 0, sa), nil)
           end;
  offset <- App ((zconst sa (match a.(mem_offset) with
                             | Some s => s 
                             | None => 0 end), sa), nil);
  bi <- App ((add, sa), [base; index]);
  App ((add, sa), [bi; offset]).

Definition Load {sa : AddressSize} (a : MEM) : M idx :=
  addr <- Address a;
  v <- Load64 addr;
  if a.(mem_is_byte)
  then App ((slice 0 8, 64%N), [v])
  else ret v.

Definition Store {sa : AddressSize} (a : MEM) v : M unit :=
  addr <- Address a;
  if negb a.(mem_is_byte) (* works even if old value undefined *)
  then Store64 addr v
  else old <- Load64 addr;
       v <- App ((set_slice 0 8, 64), [old; v])%N;
       Store64 addr v.

(* note: this could totally just handle truncation of constants if semanics handled it *)
Definition GetOperand {sa : AddressSize} (o : ARG) : M idx :=
  match o with
  | Syntax.const a => App ((zconst 64 a, 64%N), [])
  | mem a => Load a
  | reg r => GetReg r
  end.

Definition SetOperand {sa : AddressSize} (o : ARG) (v : idx) : M unit :=
  match o with
  | Syntax.const a => err (error.set_const a v)
  | mem a => Store a v
  | reg a => SetReg a v
  end.

Local Unset Elimination Schemes.
Inductive pre_expr : Set :=
| PreARG (_ : ARG)
| PreFLG (_ : FLAG)
| PreApp (_ : opname) {_ : OperationSize} (_ : list pre_expr).
(* note: need custom induction principle *)
Local Set Elimination Schemes.
Local Coercion PreARG : ARG >-> pre_expr.
Local Coercion PreFLG : FLAG >-> pre_expr.
Example __testPreARG_boring : ARG -> list pre_expr := fun x : ARG => @cons pre_expr x nil.
(*
Example __testPreARG : ARG -> list pre_expr := fun x : ARG => [x].
*)

Fixpoint Symeval {sa : AddressSize} (e : pre_expr) : M idx :=
  match e with
  | PreARG o => GetOperand o
  | PreFLG f => GetFlag f
  | PreApp op s args =>
      idxs <- mapM Symeval args;
      App ((op, s), idxs)
  end.

Notation "f @ ( x , y , .. , z )" := (PreApp f (@cons pre_expr x (@cons pre_expr y .. (@cons pre_expr z nil) ..))) (at level 10) : x86symex_scope.
Definition SymexNormalInstruction (instr : NormalInstruction) : M unit :=
  let sa : AddressSize := 64%N in
  match Syntax.operation_size instr with Some (Some s) =>
  let s : OperationSize := s in
  match instr.(Syntax.op), instr.(args) with
  | mov, [dst; src] => (* Note: unbundle when switching from N to Z *)
    v <- GetOperand src;
    SetOperand dst v
  | Syntax.add, [dst; src] =>
    v <- Symeval (add@(dst, src));
    c <- Symeval (addcarry@(dst, src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    SetFlag CF c
  | Syntax.adc, [dst; src] =>
    v <- Symeval (add@(dst, src, CF));
    c <- Symeval (addcarry@(dst, src, CF));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    SetFlag CF c
  | (adcx|adox) as op, [dst; src] =>
    let f := match op with adcx => CF | _ => OF end in
    v <- Symeval (add@(dst, src, f));
    c <- Symeval (addcarry@(dst, src, f));
    _ <- SetOperand dst v;
    SetFlag f c
  | Syntax.sub, [dst; src] =>
    v <- Symeval (add@(dst, PreApp neg [PreARG src]));
    _ <- SetOperand dst v;
    HavocFlags
  | lea, [dst; mem src] =>
    a <- Address src;
    SetOperand dst a
  | imul, ([dst as src1; src2] | [dst; src1; src2]) =>
    v <- Symeval (mul@(src1,src2));
    _ <- SetOperand dst v;
    HavocFlags
  | Syntax.xor, [dst; src] =>
    v <- Symeval (xor@(dst,src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    zero <- Symeval (PreApp (const 0) nil);
    _ <- SetFlag CF zero;
    SetFlag OF zero
  | Syntax.and, [dst; src] =>
    v <- Symeval (and@(dst,src));
    _ <- SetOperand dst v;
    HavocFlags
  | mulx, [hi; lo; src2] =>
    let src1 : ARG := rdx in
    vl <- Symeval (mul@(src1,src2));
    vh <- Symeval (mulhuu@(src1,src2));
    _ <- SetOperand lo vl;
         SetOperand hi vh
   | Syntax.shr, [dst; cnt] =>
    v <- Symeval (shr@(dst, cnt));
    _ <- SetOperand dst v;
    HavocFlags
  | shrd, [lo as dst; hi; cnt] =>
    let cnt' := add@(Z.of_N s, PreApp neg [PreARG cnt]) in
    v <- Symeval (or@(shr@(lo, cnt), shl@(hi, cnt')));
    _ <- SetOperand dst v;
    HavocFlags
  | inc, [dst] =>
    orig <- GetOperand dst; orig <- Reveal 1 orig;
    v <- Symeval (add@(dst, PreARG 1%Z));
    _ <- SetOperand dst v;
    cf <- GetFlag CF; _ <- HavocFlags; _ <- SetFlag CF cf;
    if match orig with ExprApp (const n, _, nil) => n =? 2^s-1 | _ => false end
    then zero <- Symeval (PreApp (const 0) nil); SetFlag OF zero else SetFlag CF cf
  | dec, [dst] =>
    orig <- GetOperand dst; orig <- Reveal 1 orig;
    v <- Symeval (add@(dst, PreApp neg [PreARG 1%Z]));
    _ <- SetOperand dst v;
    cf <- GetFlag CF; _ <- HavocFlags; _ <- SetFlag CF cf;
    if match orig with ExprApp (const n, _, nil) => n =? 0 | _ => false end
    then zero <- Symeval (PreApp (const 0) nil); SetFlag OF zero else SetFlag CF cf
  | test, [a;b] =>
      _ <- HavocFlags;
    zero <- Symeval (PreApp (const 0) nil);
    _ <- SetFlag CF zero;
    SetFlag OF zero
      (* note: ZF *)
  | _, _ => err (error.unimplemented_instruction instr)
 end
  | _ =>
  match instr.(Syntax.op), instr.(args) with
  | clc, [] => zero <- Symeval (@PreApp (const 0) 1 nil); SetFlag CF zero
  | Syntax.ret, [] => ret tt
  | _, _ => err (error.ambiguous_operation_size instr) end end%N%x86symex.

Definition SymexNormalInstructions := fun st is => mapM_ SymexNormalInstruction is st.


Definition OldReg (r : REG) : M unit :=
  i <- Merge (ExprApp ((old (r, None), reg_size r), nil));
  SetReg r i.
Definition OldCell (r : REG) (i : nat) : M unit :=
  a <- @Address 64%N {| mem_reg := r; mem_offset := Some (Z.of_nat(8*i));
                 mem_is_byte := false; mem_extra_reg:=None |};
  v <- Merge (ExprApp ((old (r, Some i), 64%N), nil));
  (fun s => Success (tt, update_mem_with s (cons (a,v)))).
Definition OldStack (r := rsp) (i : nat) : M unit :=
  a <- @Address 64%N {| mem_reg := r; mem_offset := Some (Z.opp (Z.of_nat(8*S i)));
                 mem_is_byte := false; mem_extra_reg:=None |};
  v <- Merge (ExprApp ((old (r, Some i), 64%N), nil));
  (fun s => Success (tt, update_mem_with s (cons (a,v)))).

Definition init
  (arrays : list (REG * nat)) (* full 64-bit registers only *)
  (stack : nat)
  (d : dag)
  : symbolic_state :=
  let sz := 64%N in
  let s0 :=
    {|
      dag_state := d;
      symbolic_reg_state := Tuple.repeat None 16;
      symbolic_mem_state := [];
      symbolic_flag_state := Tuple.repeat None 6;
    |} in
  let es :=
    (_ <- mapM_ OldReg (List.map widest_register_of_index (seq 0 16));
     _ <- mapM_ (fun '(r, n) => mapM_ (OldCell r) (seq 0 n)) arrays;
     mapM_ OldStack (seq 0 stack))%x86symex s0 in
  match es with
  | Success (_, s) => s
  | _ => s0
  end.

Example test1 : match (
  let st := init [(rsi, 4)] 0 [] in
  (SymexNormalInstructions st
    [Build_NormalInstruction lea [reg rax; mem (Build_MEM false rsi None (Some 16%Z))]
    ;Build_NormalInstruction mov [reg rbx; mem (Build_MEM false rsi None (Some 16%Z))]
    ;Build_NormalInstruction lea [reg rcx; mem (Build_MEM false rsi (Some rbx) (Some 7%Z))]
    ;Build_NormalInstruction mov [         mem (Build_MEM false rsi None (Some 24%Z)); reg rcx]
     ])
) with Error _ => False | Success st => True end. native_cast_no_check I. Qed.

Definition invert_rawline l := match l.(rawline) with INSTR instr => Some instr | _ => None end.
Definition SymexLines st (lines : list Syntax.Line) :=
  SymexNormalInstructions st (Option.List.map invert_rawline lines).

Import Coq.Strings.String.
Local Open Scope string_scope.
Notation "f" := (ExprApp ((f,64%N), (@nil expr))) (at level 10, only printing).
Notation "f @ ( x , y , .. , z )" := (ExprApp ((f,64%N), (@cons expr x%N (@cons expr y%N .. (@cons expr z%N nil) ..)))) (at level 10).
Local Coercion ExprRef : idx >-> expr.

Ltac step e :=
  let ev := eval cbv [e] in e in
  let X := match ev with (x <- ?X; _)%x86symex _ => X end in
  let C := match ev with (x <- ?X; @?C x)%x86symex _ => C end in
  let s := match ev with _ ?s => s end in
  let Y := eval hnf in (X s) in
  match Y with
  | Success (?r, ?s) => clear e; set (e:=C r s); simpl in e
  | Error (?e, ?s) => fail e
  end.

Definition symex_asm_asm args stack impl1 impl2 : ErrorT _ _ :=
  let s0 := init args stack nil in
  _s1 <- SymexLines s0 impl1; let s1 := snd _s1 in
  _s2 <- SymexLines s1 impl2; let s2 := snd _s2 in
  let answers := List.map
    (fun '(k, _) => (reveal s0 2 k, (load k s1, load k s2)))
    ((init args 0 s0).(symbolic_mem_state)) in
  if List.forallb (fun '(_, (a, b)) =>
      match a,b with Some a, Some b => N.eqb a b | _, _ => false end) answers
  then Success tt
  else Error (error.failed_to_unify answers, s2).

Example curve25519_square_same : symex_asm_asm [(rsi, 5); (rdi, 5)] 7 lines lines10 = Success tt. vm_cast_no_check (eq_refl (@Success (error.error*symbolic_state) unit tt)). Qed.

Example evaluation : True.
  pose (s0 := init [(rsi, 5); (rdi, 5)] 7 nil).
  let n := constr:(600%nat) in
  pose (s1 := SymexLines s0 (firstn n lines10));
  cbv in s1;
  let v := eval cbv delta [s1] in s1 in
  match v with Error (?e, ?s) =>
    let n := fresh in
    simple notypeclasses refine (let n : symbolic_state := _ in _);
    [ transparent_abstract (exact s) |];
    let g := eval cbv delta [n] in n in
    idtac (* g *);

    try (match e with context [?i] => 
      let d := eval cbv in (reveal evaluation_subterm 999 170%N) in
      idtac d end)
  | Success (_, ?s) =>
      let ss := fresh "s" in 
      set s as ss; clear s1; rename ss into s1;
      let v := eval cbv in (Option.bind (nth_error lines10 n) invert_rawline) in
      match v with
      | Some ?ni => pose (SymexNormalInstruction ni ss)
      | _ => idtac (* "COMMENT" *)
      end
  end.

  set (s2 := invert_result (SymexLines s1 (firstn 151 lines))).
  native_compute in s2.
  pose (s2' := snd s2); cbv in s2'; clear s2; rename s2' into s2.
  pose (output :=
  let answers := List.map
    (fun '(k, _) => (reveal s0 2 k, (load k s1, load k s2)))
    ((init [(rsi, 5); (rdi, 5)] 0 s0).(symbolic_mem_state)) in
    (answers,
    List.forallb (fun '(_, (a, b)) =>
    match a,b with Some a, Some b => N.eqb a b | _, _ => false end) answers));
  vm_compute in output.

  exact I.
Defined.
