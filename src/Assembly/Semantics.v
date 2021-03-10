Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Bool.Bool.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Notations.
Require Import Crypto.Assembly.Syntax.
Require Crypto.Util.Tuple.
Import ListNotations.

Local Open Scope list_scope.

Local Set Implicit Arguments.
Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.
Local Set Primitive Projections.

(** denotational semantics *)

Definition flag_state := Tuple.tuple (option bool) 6.
Definition get_flag (st : flag_state) (f : FLAG) : option bool
  := let '(cfv, pfv, afv, zfv, sfv, ofv) := st in
     match f with
     | CF => cfv
     | PF => pfv
     | AF => afv
     | ZF => zfv
     | SF => sfv
     | OF => ofv
     end.
Definition set_flag_internal (st : flag_state) (f : FLAG) (v : option bool) : flag_state
  := let '(cfv, pfv, afv, zfv, sfv, ofv) := st in
     (match f with CF => v | _ => cfv end,
      match f with PF => v | _ => pfv end,
      match f with AF => v | _ => afv end,
      match f with ZF => v | _ => zfv end,
      match f with SF => v | _ => sfv end,
      match f with OF => v | _ => ofv end).
Definition set_flag (st : flag_state) (f : FLAG) (v : bool) : flag_state
  := set_flag_internal st f (Some v).
Definition havoc_flag (st : flag_state) (f : FLAG) : flag_state
  := set_flag_internal st f None.
Definition havoc_flags : flag_state
  := (None, None, None, None, None, None).

Definition reg_state := list N.
Definition reg_index (r : REG) : nat
  :=  match r with
      |     rax
      |     eax
      |      ax
      |(ah | al)
       => 0
      |     rcx
      |     ecx
      |      cx
      |(ch | cl)
       => 1
      |     rdx
      |     edx
      |      dx
      |(dh | dl)
       => 2
      |     rbx
      |     ebx
      |      bx
      |(bh | bl)
       => 3
      | rsp
      | esp
      |  sp
      |( spl)
       => 4
      | rbp
      | ebp
      |  bp
      |( bpl)
       => 5
      | rsi
      | esi
      |  si
      |( sil)
       => 6
      | rdi
      | edi
      |  di
      |( dil)
       => 7
      | r8
      | r8d
      | r8w
      | r8b
        => 8
      | r9
      | r9d
      | r9w
      | r9b
        => 9
      | r10
      | r10d
      | r10w
      | r10b
        => 10
      | r11
      | r11d
      | r11w
      | r11b
        => 11
      | r12
      | r12d
      | r12w
      | r12b
        => 12
      | r13
      | r13d
      | r13w
      | r13b
        => 13
      | r14
      | r14d
      | r14w
      | r14b
        => 14
      | r15
      | r15d
      | r15w
      | r15b
        => 15
      end.
Definition reg_offset (r : REG) : N :=
      match r with
      |(    rax |     rcx |     rdx |     rbx | rsp  | rbp  | rsi  | rdi  | r8  | r9  | r10  | r11  | r12  | r13  | r14  | r15 )
      |(    eax |     ecx |     edx |     ebx | esp  | ebp  | esi  | edi  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d)
      |(     ax |      cx |      dx |      bx |  sp  |  bp  |  si  |  di  | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w)
      |(     al |      cl |      dl |      bl |  spl |  bpl |  sil |  dil | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b)
       => 0
      |(ah      | ch      | dh      | bh      )
       => 8
      end.
Definition reg_size (r : REG) : N :=
      match r with
      |(    rax |     rcx |     rdx |     rbx | rsp  | rbp  | rsi  | rdi  | r8  | r9  | r10  | r11  | r12  | r13  | r14  | r15 )
       => 64
      |(    eax |     ecx |     edx |     ebx | esp  | ebp  | esi  | edi  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d)
       => 32
      |(     ax |      cx |      dx |      bx |  sp  |  bp  |  si  |  di  | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w)
       => 16
      |(ah | al | ch | cl | dh | dl | bh | bl |  spl |  bpl |  sil |  dil | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b)
       => 8
      end.

Definition index_and_shift_and_bitcount_of_reg (r : REG) :=
  (reg_index r, reg_offset r, reg_size r).
Definition bitmask_of_reg (r : REG) : N
  := let '(idx, shift, bitcount) := index_and_shift_and_bitcount_of_reg r in
     N.shiftl (N.ones bitcount) shift.
Definition get_reg (st : reg_state) (r : REG) : N
  := let '(idx, shift, bitcount) := index_and_shift_and_bitcount_of_reg r in
     let rv := nth_default 0%N st idx in
     N.land (N.shiftr rv shift) (N.ones bitcount).
Definition set_reg (st : reg_state) (r : REG) (v : N) : reg_state
  := let '(idx, shift, bitcount) := index_and_shift_and_bitcount_of_reg r in
     let bitmask := bitmask_of_reg r in
     ListUtil.update_nth
       idx
       (fun curv => N.lor (N.land bitmask (N.shiftl v shift))
                          (N.ldiff curv bitmask))
       st.

(** convenience printing function *)
Definition widest_register_of_index (n : nat) : REG
  := match n with
     | 0 => rax
     | 1 => rcx
     | 2 => rdx
     | 3 => rbx
     | 4 => rsp
     | 5 => rbp
     | 6 => rsi
     | 7 => rdi
     | 8 => r8
     | 9 => r9
     | 10 => r10
     | 11 => r11
     | 12 => r12
     | 13 => r13
     | 14 => r14
     | 15 => r15
     | _ => rax
     end%nat.
Lemma widest_register_of_index_correct
  : forall n,
    (~exists r, fst (fst (index_and_shift_and_bitcount_of_reg r)) = n)
    \/ (let r := widest_register_of_index n in
        fst (fst (index_and_shift_and_bitcount_of_reg r)) = n
        /\ forall r', fst (fst (index_and_shift_and_bitcount_of_reg r')) = n
                      -> r = r' \/ (snd (index_and_shift_and_bitcount_of_reg r') < snd (index_and_shift_and_bitcount_of_reg r))%N).
Proof.
  intro n; set (r := widest_register_of_index n).
  cbv in r.
  repeat match goal with r := context[match ?n with _ => _ end] |- _ => destruct n; [ right | ] end;
    [ .. | left; intros [ [] H]; cbv in H; congruence ].
  all: subst r; split; [ reflexivity | ].
  all: intros [] H; cbv in H; try (exfalso; congruence).
  all: try (left; reflexivity).
  all: try (right; vm_compute; reflexivity).
Qed.
Definition annotate_reg_state (st : reg_state) : list (REG * N)
  := List.map (fun '(n, v) => (widest_register_of_index n, v)) (enumerate st).
Ltac print_reg_state st := let st' := (eval cbv in (annotate_reg_state st)) in idtac st'.

(* Kludge since [byte] isn't present in Coq 8.9 *)
Module Byte.
  Notation byte := N (only parsing).
  Definition to_N (x : byte) : N := x.
  Definition of_N (x : N) : option byte
    := if (x <? 2^256)%N then Some x else None.
  Notation x00 := 0%N (only parsing).
End Byte.

Record mem_state := { mem_bytes_state :> PositiveMap.t Byte.byte }.
Definition get_mem_byte (st : mem_state) (addr : N) : option Byte.byte
  := match addr with
     | Npos p => PositiveMap.find p st.(mem_bytes_state)
     | _ => None
     end.
Definition set_mem_byte (st : mem_state) (addr : positive) (b : Byte.byte) : mem_state
  := {| mem_bytes_state := PositiveMap.add addr b st.(mem_bytes_state) |}.
Definition set_mem_byte_error (st : mem_state) (addr : N) (b : Byte.byte) : option mem_state
  := match addr with
     | Npos addr => Some (set_mem_byte st addr b)
     | _ => None
     end.
Definition set_mem_byte_default (st : mem_state) (addr : N) (b : Byte.byte) : mem_state
  := match set_mem_byte_error st addr b with
     | Some st => st
     | None => st
     end.
Fixpoint get_mem_bytes (st : mem_state) (addr : N) (nbytes : nat) : option (list Byte.byte)
  := match nbytes with
     | O => Some nil
     | S nbytes => match get_mem_byte st addr, get_mem_bytes st (addr + 1) nbytes with
                   | Some b, Some bs => Some (b :: bs)
                   | _, _ => None
                   end
     end.
Fixpoint set_mem_bytes (st : mem_state) (addr : positive) (v : list Byte.byte) : mem_state
  := match v with
     | nil => st
     | v :: vs => let st := set_mem_byte st addr v in
                  set_mem_bytes st (addr + 1) vs
     end.
Definition set_mem_bytes_error (st : mem_state) (addr : N) (v : list Byte.byte) : option mem_state
  := match addr with
     | Npos addr => Some (set_mem_bytes st addr v)
     | _ => None
     end.
Definition set_mem_bytes_default (st : mem_state) (addr : N) (v : list Byte.byte) : mem_state
  := match set_mem_bytes_error st addr v with
     | Some st => st
     | None => st
     end.
(* x86 is little-endian according to https://stackoverflow.com/a/25939262/377022, so we have l[0] + 8*l[1] + ... *)
Fixpoint mem_bytes_to_N (bytes : list Byte.byte) : N
  := match bytes with
     | nil => 0
     | b :: bs => Byte.to_N b + 8 * mem_bytes_to_N bs
     end%N.
(* returns the carry as well *)
Fixpoint mem_bytes_of_N_split (nbytes : nat) (v : N) : list Byte.byte * N
  := match nbytes with
     | O => (nil, v)
     | S nbytes => let '(vh, vl) := (N.shiftr v 8, N.land v (N.ones 8)) in
                   let '(bs, carry) := mem_bytes_of_N_split nbytes vh in
                   let vl := match Byte.of_N vl with
                             | Some vl => vl
                             | None (* should be impossible *) => Byte.x00
                             end in
                   (vl :: bs, carry)
     end%N.
Definition mem_bytes_of_N_error (nbytes : nat) (v : N) : option (list Byte.byte)
  := let '(bs, carry) := mem_bytes_of_N_split nbytes v in
     if (carry =? 0)%N then Some bs else None.
Definition mem_bytes_of_N_masked (nbytes : nat) (v : N) : list Byte.byte
  := let '(bs, carry) := mem_bytes_of_N_split nbytes v in bs.
Definition get_mem (st : mem_state) (addr : N) (nbytes : nat) : option N
  := option_map mem_bytes_to_N (get_mem_bytes st addr nbytes).
Definition set_mem_error (st : mem_state) (addr : N) (nbytes : nat) (v : N) : option mem_state
  := (bs <- mem_bytes_of_N_error nbytes v;
     set_mem_bytes_error st addr bs)%option.
Definition set_mem_masked_error (st : mem_state) (addr : N) (nbytes : nat) (v : N) : option mem_state
  := set_mem_bytes_error st addr (mem_bytes_of_N_masked nbytes v).
Definition set_mem_default (st : mem_state) (addr : N) (nbytes : nat) (v : N) : mem_state
  := Option.value (set_mem_masked_error st addr nbytes v) st.

Record machine_state := { machine_reg_state :> reg_state ; machine_flag_state :> flag_state ; machine_mem_state :> mem_state }.
Definition update_reg_with (st : machine_state) (f : reg_state -> reg_state) : machine_state
  := {| machine_reg_state := f st.(machine_reg_state) ; machine_flag_state := st.(machine_flag_state) ; machine_mem_state := st.(machine_mem_state) |}.
Definition update_flag_with (st : machine_state) (f : flag_state -> flag_state) : machine_state
  := {| machine_reg_state := st.(machine_reg_state) ; machine_flag_state := f st.(machine_flag_state) ; machine_mem_state := st.(machine_mem_state) |}.
Definition update_mem_with (st : machine_state) (f : mem_state -> mem_state) : machine_state
  := {| machine_reg_state := st.(machine_reg_state) ; machine_flag_state := st.(machine_flag_state) ; machine_mem_state := f st.(machine_mem_state) |}.

Definition operand_size (x : ARG) : option N :=
  match x with
  | reg r => Some (reg_size r)
  | mem m => if m.(mem_is_byte)
             then Some 8
             else None
  | const c => None
  end%N.
Definition unify_operand_size (a : option N)  (b : option (option N)) : option (option N) :=
  match a with
  | None => b
  | Some s =>
      match b with
      | None => None
      | Some None => Some (Some s)
      | Some (Some s') => if N.eqb s s' then Some (Some s) else None
      end
  end.
(* None => contradiction, Some None => underconstrained, Some Some s => size s *)
Definition operation_size (instr : NormalInstruction) : option (option N) :=
  List.fold_right unify_operand_size (Some None) (List.map operand_size instr.(args)).

Definition DenoteConst (s : N) (a : CONST) : N :=
  Z.to_N (Z.land a (Z.ones (Z.of_N s))).

Definition DenoteAddress (sa : N) (st : machine_state) (a : MEM) : N :=
  N.land (N.ones sa) (
    get_reg st (mem_reg a) +
    match mem_extra_reg a with Some e => get_reg st e | _ => 0 end +
    (match mem_offset a with Some z => DenoteConst sa z | _ => 0 end)).

Definition DenoteOperand (sa s : N) (st : machine_state) (a : ARG) : option N :=
  match a with
  | reg a => Some (get_reg st a)
  | mem a => get_mem st (DenoteAddress sa st a) (N.to_nat (N.div s 8))
  | const a => Some (DenoteConst s a)
  end.

Definition SetOperand (sa s : N) (st : machine_state) (a : ARG) (v : N) : option machine_state :=
  match a with
  | reg a => Some (update_reg_with st (fun rs => set_reg rs a v))
  | mem a => ms <- set_mem_error st (DenoteAddress sa st a) (N.to_nat (N.div s 8)) v;
             Some (update_mem_with st (fun _ => ms))
  | const a => None
  end.

Definition result_flags s v :=
  (* note: AF and PF remain undefined *)
  let fs := set_flag havoc_flags ZF (N.eqb v 0) in
  let fs := set_flag fs SF (N.testbit v (s-1)) in
  fs.

Definition signed s z : Z :=
  Z.land (Z.shiftl 1 (s-1) + z) (Z.ones s) - Z.shiftl 1 (s-1).
Local Coercion Z.of_N : N >-> Z.

(* NOTE: currently immediate operands are treated as if sign-extension has been
 * performed ahead of time. *)
Definition DenoteNormalInstruction (st : machine_state) (instr : NormalInstruction) : option machine_state.
  refine (let sa := 64%N in _).
  refine (match operation_size instr with Some (Some s) => _ | _ => None end).
  refine match instr.(op), instr.(args) with
  | adc, [(reg _ | mem _) as dst; src] =>
      v1 <- DenoteOperand sa s st dst;
      v2 <- DenoteOperand sa s st src;
      c <- get_flag st CF; let c := N.b2n c in
      st <- SetOperand sa s st dst (v1 + v2 + c);
      Some (update_flag_with st (fun fs =>
        let fs := result_flags s (v1 + v2 + c) in
        let v := N.land (v1 + v2 + c) (N.ones s) in
        let fs := set_flag fs CF (negb (v =? v1 + v2 + c)) in
        set_flag fs OF (negb (signed s v =? signed s v1 + signed s v2 + c)%Z)))
  | adcx, [dst; src] =>
      v1 <- DenoteOperand sa s st dst;
      v2 <- DenoteOperand sa s st src;
      c <- get_flag st CF; let c := N.b2n c in
      st <- SetOperand sa s st dst (v1 + v2 + c);
      Some (update_flag_with st (fun fs =>
        let v := N.land (v1 + v2 + c) (N.ones s) in
        set_flag fs CF (negb (v =? v1 + v2 + c))))
  | add, [dst; src] => 
      v1 <- DenoteOperand sa s st dst;
      v2 <- DenoteOperand sa s st src;
      st <- SetOperand sa s st dst (v1 + v2);
      Some (update_flag_with st (fun fs =>
        let fs := result_flags s (v1 + v2) in
        let v := N.land (v1 + v2) (N.ones s) in
        let fs := set_flag fs CF (negb (v =? v1 + v2)) in
        set_flag fs OF (negb (signed s v =? signed s v1 + signed s v2)%Z)))
  | adox, [dst; src] =>
      v1 <- DenoteOperand sa s st dst;
      v2 <- DenoteOperand sa s st src;
      c <- get_flag st OF; let c := N.b2n c in
      st <- SetOperand sa s st dst (v1 + v2 + c);
      Some (update_flag_with st (fun fs =>
        let v := N.land (v1 + v2 + c) (N.ones s) in
        set_flag fs OF (negb (v =? v1 + v2 + c))))
  | and, [dst; src] =>
      v1 <- DenoteOperand sa s st dst;
      v2 <- DenoteOperand sa s st src;
      let v := N.land v1 v2 in
      Some (update_flag_with st (fun fs =>
        let fs := result_flags s v in
        let fs := set_flag fs CF false in
        let fs := set_flag fs OF false in
        havoc_flag fs AF
      ))
  | clc, [] => Some (update_flag_with st (fun fs =>
      set_flag fs CF false))
  | cmovnz, [dst; src] => (* Flags Affected: None *)
      v <- DenoteOperand sa s st src;
      zf <- get_flag st ZF;
      if negb zf
      then SetOperand sa s st dst v
      else Some st
  | dec, [dst] =>
      v1 <- DenoteOperand sa s st dst;
      let v := Z.to_N (Z.land (v1 - 1) (Z.ones s)) in
      st <- SetOperand sa s st dst v;
      Some (update_flag_with st (fun fs =>
        let fs := result_flags s v in
        let fs := set_flag_internal fs CF (get_flag st CF) in
        set_flag fs OF (negb (signed s v =? signed s v1 - 1)%Z)))
  | imul, [_] => None (* Note: exists, not supported yet, different CF/OF *)
  | imul, [dst; src] =>
      dst <- DenoteOperand sa s st dst;
      src <- DenoteOperand sa s st src;
      let v := (signed s dst * signed s src)%Z in
      let lo := Z.land v (Z.ones s) in
      st <- SetOperand sa s st dst (Z.to_N lo);
      Some (update_flag_with st (fun fs =>
        let c := negb (v =? lo)%Z in
        set_flag (set_flag havoc_flags OF c) CF c))
  | imul, [dst; src1; src2] =>
      src1 <- DenoteOperand sa s st src1;
      src2 <- DenoteOperand sa s st src2;
      let v := (signed s src1 * signed s src2)%Z in
      let lo := Z.land v (Z.ones s) in
      st <- SetOperand sa s st dst (Z.to_N lo);
      Some (update_flag_with st (fun fs =>
        let c := negb (v =? lo)%Z in
        set_flag (set_flag havoc_flags OF c) CF c))
  | inc, [dst] =>
      v1 <- DenoteOperand sa s st dst;
      st <- SetOperand sa s st dst (v1 + 1);
      Some (update_flag_with st (fun fs =>
        let fs := result_flags s (v1 + 1) in
        let v := N.land (v1 + 1) (N.ones s) in
        let fs := set_flag_internal fs CF (get_flag st CF) in
        set_flag fs OF (negb (signed s v =? signed s v1 + 1)%Z)))
  | lea, [reg dst; mem src] => (* Flags Affected: None *)
      Some (update_reg_with st (fun rs => set_reg rs dst (DenoteAddress sa st src)))
  | mov, [dst; src]
    | movzx, [dst; src] =>
      v <- DenoteOperand sa s st src;
      SetOperand sa s st dst v
  | mulx, [hi; lo; src2] => (* Flags Affected: None *)
      let src1 : ARG := rdx in (* Note: assumes s=64 *)
      v1 <- DenoteOperand sa s st src1;
      v2 <- DenoteOperand sa s st src2;
      let v := v1 * v2 in
      st <- SetOperand sa s st lo v;
      SetOperand sa s st hi (N.shiftr v s)
  | sar, [dst; cnt] =>
      v1 <- DenoteOperand sa s st dst;
      cnt <- DenoteOperand sa s st cnt;
      let v := Z.to_N (Z.land (Z.shiftr v1 (N.land cnt (s-1))) (Z.ones s)) in
      st <- SetOperand sa s st dst v;
      Some (update_flag_with st (fun fs =>
        if cnt =? 0 then fs else
        let fs := result_flags s v in
        let fs := set_flag_internal fs OF
          (if cnt =? 1 then Some false else None) in
        let fs := set_flag_internal fs CF
          (if cnt <? s then Some (N.testbit v1 (cnt-1)) else None) in
        havoc_flag fs AF))
  | sbb, [dst; src] =>
      v1 <- DenoteOperand sa s st dst;
      v2 <- DenoteOperand sa s st src;
      c <- get_flag st CF; let c := N.b2n c in
      let v := Z.to_N (Z.land (Z.of_N v1 - Z.of_N (v2 + c)) (Z.ones (Z.of_N s))) in
      st <- SetOperand sa s st dst v;
      Some (update_flag_with st (fun fs =>
        let fs := result_flags s v in
        let fs := set_flag fs CF (negb (Z.of_N v =? Z.of_N v1 - (Z.of_N v2 + Z.of_N c))%Z) in
        set_flag fs OF (negb (signed s v =? signed s v1 - (signed s v2 + Z.of_N c))%Z)))
  | setc, [dst] => (* Flags Affected: None *)
      b <- get_flag st CF;
      SetOperand sa s st dst (N.b2n b)
  | seto, [dst] => (* Flags Affected: None *)
      b <- get_flag st OF;
      SetOperand sa s st dst (N.b2n b)
  | shr, [dst; cnt] =>
      v1 <- DenoteOperand sa s st dst;
      cnt <- DenoteOperand sa s st cnt;
      let v := N.shiftr v1 (N.land cnt (s-1)) in
      st <- SetOperand sa s st dst v;
      Some (update_flag_with st (fun fs =>
        if cnt =? 0 then fs else
        let fs := result_flags s v in
        let fs := set_flag_internal fs OF
          (if cnt =? 1 then Some (N.testbit v1 (s-1)) else None) in
        let fs := set_flag_internal fs CF
          (if cnt <? s then Some (N.testbit v1 (cnt-1)) else None) in
        havoc_flag fs AF))
  | shrd, [lo as dst; hi; cnt] =>
      lo <- DenoteOperand sa s st lo;
      hi <- DenoteOperand sa s st hi;
      cnt <- DenoteOperand sa s st cnt;
      let l := N.lor lo (N.shiftl hi s) in
      let v := N.shiftr l (N.land cnt (s-1)) in
      st <- SetOperand sa s st dst v;
      Some (update_flag_with st (fun fs =>
        if cnt =? 0 then fs else
        let fs := result_flags s l in
        let signchange := xorb (signed s lo <? 0)%Z (signed s v <? 0)%Z in
        (* Note: IA-32 SDM does not make it clear what sign change is in question *)
        let fs := set_flag_internal fs OF
          (if cnt =? 1 then Some signchange else None) in
        let fs := set_flag fs CF (N.testbit l (cnt-1)) in
        let fs := havoc_flag fs AF in
        if cnt <? s then fs else havoc_flags))
  | sub, [dst; src] =>
      v1 <- DenoteOperand sa s st dst;
      v2 <- DenoteOperand sa s st src;
      let v := Z.to_N (Z.land (Z.of_N v1 - Z.of_N v2) (Z.ones (Z.of_N s))) in
      st <- SetOperand sa s st dst v;
      Some (update_flag_with st (fun fs =>
        let fs := result_flags s v in
        let fs := set_flag fs CF (negb (Z.of_N v =? Z.of_N v1 - Z.of_N v2)%Z) in
        set_flag fs OF (negb (signed s v =? signed s v1 - signed s v2)%Z)))
  | test, [src1; src2] =>
      v1 <- DenoteOperand sa s st src1;
      v2 <- DenoteOperand sa s st src2;
      let v := N.land v1 v2 in
      Some (update_flag_with st (fun fs =>
        let fs := result_flags s v in
        let fs := set_flag fs CF false in
        let fs := set_flag fs OF false in
        havoc_flag fs AF
      ))
  | xchg, [a; b] => (* Flags Affected: None *)
      va <- DenoteOperand sa s st a;
      vb <- DenoteOperand sa s st b;
      st <- SetOperand sa s st b va;
      SetOperand sa s st a vb
  | xor, [dst; src] =>
      v1 <- DenoteOperand sa s st dst;
      v2 <- DenoteOperand sa s st src;
      let v := N.lxor v1 v2 in
      Some (update_flag_with st (fun fs =>
        let fs := result_flags s v in
        let fs := set_flag fs CF false in
        let fs := set_flag fs OF false in
        havoc_flag fs AF
      ))

  | ret, _ => None (* not sure what to do with this ret, maybe exlude it? *)

  | adc, _
  | adcx, _
  | add, _
  | adox, _
  | and, _
  | mulx, _
  | cmovnz, _
  | setc, _
  | seto, _
  | clc, _
  | dec, _
  | lea, _
  | mov, _
  | movzx, _
  | imul, _
  | inc, _
  | sar, _
  | sbb, _
  | shr, _
  | shrd, _
  | sub, _
  | test, _
  | xor, _
  | xchg, _ => None
  end%N%option.
