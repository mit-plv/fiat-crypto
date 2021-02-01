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
Definition havoc_flags (st : flag_state) : flag_state
  := (None, None, None, None, None, None).

Definition reg_state := list N.
Definition index_and_shift_and_bitcount_of_reg (r : REG) : nat * N * N
  := (match r with
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
      end,
      match r with
      |(    rax |     rcx |     rdx |     rbx | rsp  | rbp  | rsi  | rdi  | r8  | r9  | r10  | r11  | r12  | r13  | r14  | r15 )
      |(    eax |     ecx |     edx |     ebx | esp  | ebp  | esi  | edi  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d)
      |(     ax |      cx |      dx |      bx |  sp  |  bp  |  si  |  di  | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w)
      |(     al |      cl |      dl |      bl |  spl |  bpl |  sil |  dil | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b)
       => 0
      |(ah      | ch      | dh      | bh      )
       => 8
      end%N,
      match r with
      |(    rax |     rcx |     rdx |     rbx | rsp  | rbp  | rsi  | rdi  | r8  | r9  | r10  | r11  | r12  | r13  | r14  | r15 )
       => 64
      |(    eax |     ecx |     edx |     ebx | esp  | ebp  | esi  | edi  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d)
       => 32
      |(     ax |      cx |      dx |      bx |  sp  |  bp  |  si  |  di  | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w)
       => 16
      |(ah | al | ch | cl | dh | dl | bh | bl |  spl |  bpl |  sil |  dil | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b)
       => 8
      end%N).
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
Definition get_mem_byte (st : mem_state) (addr : Z) : option Byte.byte
  := match addr with
     | Zpos p => PositiveMap.find p st.(mem_bytes_state)
     | _ => None
     end.
Definition set_mem_byte (st : mem_state) (addr : positive) (b : Byte.byte) : mem_state
  := {| mem_bytes_state := PositiveMap.add addr b st.(mem_bytes_state) |}.
Definition set_mem_byte_error (st : mem_state) (addr : Z) (b : Byte.byte) : option mem_state
  := match addr with
     | Zpos addr => Some (set_mem_byte st addr b)
     | _ => None
     end.
Definition set_mem_byte_default (st : mem_state) (addr : Z) (b : Byte.byte) : mem_state
  := match set_mem_byte_error st addr b with
     | Some st => st
     | None => st
     end.
Fixpoint get_mem_bytes (st : mem_state) (addr : Z) (nbytes : nat) : option (list Byte.byte)
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
Definition set_mem_bytes_error (st : mem_state) (addr : Z) (v : list Byte.byte) : option mem_state
  := match addr with
     | Zpos addr => Some (set_mem_bytes st addr v)
     | _ => None
     end.
Definition set_mem_bytes_default (st : mem_state) (addr : Z) (v : list Byte.byte) : mem_state
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
Definition get_mem (st : mem_state) (addr : Z) (nbytes : nat) : option N
  := option_map mem_bytes_to_N (get_mem_bytes st addr nbytes).
Definition set_mem_error (st : mem_state) (addr : Z) (nbytes : nat) (v : N) : option mem_state
  := (bs <- mem_bytes_of_N_error nbytes v;
     set_mem_bytes_error st addr bs)%option.
Definition set_mem_masked_error (st : mem_state) (addr : Z) (nbytes : nat) (v : N) : option mem_state
  := set_mem_bytes_error st addr (mem_bytes_of_N_masked nbytes v).
Definition set_mem_default (st : mem_state) (addr : Z) (nbytes : nat) (v : N) : mem_state
  := Option.value (set_mem_masked_error st addr nbytes v) st.

Record machine_state := { machine_reg_state :> reg_state ; machine_flag_state :> flag_state ; machine_mem_state :> mem_state }.
Definition update_reg_with (st : machine_state) (f : reg_state -> reg_state) : machine_state
  := {| machine_reg_state := f st.(machine_reg_state) ; machine_flag_state := st.(machine_flag_state) ; machine_mem_state := st.(machine_mem_state) |}.
Definition update_flag_with (st : machine_state) (f : flag_state -> flag_state) : machine_state
  := {| machine_reg_state := st.(machine_reg_state) ; machine_flag_state := f st.(machine_flag_state) ; machine_mem_state := st.(machine_mem_state) |}.
Definition update_mem_with (st : machine_state) (f : mem_state -> mem_state) : machine_state
  := {| machine_reg_state := st.(machine_reg_state) ; machine_flag_state := st.(machine_flag_state) ; machine_mem_state := f st.(machine_mem_state) |}.
(*
Definition DenoteNormalInstruction (st : machine_state) (instr : NormalInstruction) : option machine_state.
  refine match instr.(op), instr.(args) with
           (* https://www.felixcloutier.com/x86/adc *)
         | adc, [(reg _ | mem _) as dst; src]
           => _
         | adc, _ => None
         | adcx, _ => _
         | add, _ => _
         | adox, _ => _
         | and, _ => _
         | clc, _ => _
         | cmovnz, _ => _
         | dec, _ => _
         | imul, _ => _
         | inc, _ => _
         | lea, _ => _
         | mov, _ => _
         | movzx, _ => _
         | mulx, _ => _
         | ret, _ => _
         | sar, _ => _
         | sbb, _ => _
         | setc, _ => _
         | seto, _ => _
         | shr, _ => _
         | shrd, _ => _
         | sub, _ => _
         | test, _ => _
         | xchg, _ => _
         | xor, _ => _
         end.
*)
