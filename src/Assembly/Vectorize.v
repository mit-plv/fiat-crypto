(** * Scalar → Vector Assembly Synthesis *)
(** THIS IS BEING REFACTORED AND PROBABLY WILL BE COMPELTELY REMOVED. *)
(** Given a scalar element-wise primitive (like [add] or [sub]),
    synthesize AVX2 assembly that performs 4 independent copies
    in parallel using YMM registers (4 × 64-bit lanes).

    Memory layout: structure-of-arrays. For a 4-wide batch of [n]-limb
    field elements, the [4*n]-element flat array is arranged as:
      [limb0_e0, limb0_e1, limb0_e2, limb0_e3,
       limb1_e0, limb1_e1, limb1_e2, limb1_e3, ...].
    Each group of 4 consecutive uint64s loads into one YMM register. *)

From Coq Require Import ZArith List String NArith Nat.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Symbolic.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope N_scope.

(** ** Assembly construction helpers *)

Definition mk_line (rl : RawLine) : Line :=
  {| indent := "	" ; rawline := rl ; pre_comment_whitespace := "" ;
     comment := None ; line_number := 0 |}.

Definition mk_header (rl : RawLine) : Line :=
  {| indent := "" ; rawline := rl ; pre_comment_whitespace := "" ;
     comment := None ; line_number := 0 |}.

Definition mk_instr (oc : OpCode) (a : list ARG) : Line :=
  mk_line (INSTR {| prefix := None ; Syntax.op := oc ; args := a |}).

(** Memory operand: [[base_reg + byte_offset]] *)
Definition mem_at (base : SREG) (byte_offset : Z) : MEM :=
  {| mem_bits_access_size := None ;
     mem_base_reg := Some base ;
     mem_scale_reg := None ;
     mem_base_label := None ;
     mem_offset := if Z.eqb byte_offset 0 then None else Some byte_offset ;
     rip_relative := not_rip_relative |}.

(** YMM register allocation: one register per limb *)
Definition nth_ymm (i : nat) : VREG :=
  nth i [ymm0; ymm1; ymm2; ymm3; ymm4; ymm5; ymm6; ymm7;
         ymm8; ymm9; ymm10; ymm11; ymm12; ymm13; ymm14; ymm15] ymm0.

(** ** Per-limb code generation *)

(** A [limb_op] describes what to do for one group (YMM register). *)
Inductive limb_op :=
  | LimbBinop (oc : OpCode)
      (** [dst = oc(arg1[i], arg2[i])] — e.g. vpaddq *)
  | LimbConstBinop (oc : OpCode) (c : Z)
      (** [dst = oc(arg1[i] + c, arg2[i])] — broadcast same constant to all lanes *)
  | LimbVecConstBinop (oc : OpCode) (cs : list Z)
      (** [dst = oc(arg1[i] + cs, arg2[i])] — per-lane constants (length 4),
          built via vpbroadcastq of lane-1 value + vpblendd patches *).

(** vpblendd immediate mask for a 64-bit lane index (each lane = 2 dwords). *)
Definition blend_mask_for_lane (lane : nat) : Z :=
  Z.shiftl 3 (Z.of_nat (lane * 2)).

(** Emit instructions to patch one lane of [dst_reg] with a different constant.
    Uses ymm15 as scratch; assumes rax is available. *)
Definition emit_blend_lane (dst_reg : REG) (lane : nat) (c : Z) : list Line :=
  let scratch := VReg ymm15 in
  [ mk_instr mov     [reg (SReg rax); Syntax.const c]
  ; mk_instr vmovq   [reg scratch; reg (SReg rax)]
  ; mk_instr vpbroadcastq [reg scratch; reg scratch]
  ; mk_instr vpblendd [reg dst_reg; reg dst_reg; reg scratch;
                        Syntax.const (blend_mask_for_lane lane)]
  ].

(** Generate instructions for one group (YMM register).
    Calling convention: rdi=out, rsi=arg1, rdx=arg2. *)
Definition emit_limb (limb_idx : nat) (lop : limb_op) : list Line :=
  let off := (Z.of_nat limb_idx * 32)%Z in
  let dst := VReg (nth_ymm limb_idx) in
  match lop with
  | LimbBinop oc =>
    [ mk_instr vmovdqu [reg dst; mem (mem_at rsi off)]
    ; mk_instr oc      [reg dst; reg dst; mem (mem_at rdx off)]
    ; mk_instr vmovdqu [mem (mem_at rdi off); reg dst]
    ]
  | LimbConstBinop oc c =>
    let tmp := VReg (nth_ymm (limb_idx + 8)) in
    [ mk_instr mov     [reg (SReg rax); Syntax.const c]
    ; mk_instr vmovq   [reg tmp; reg (SReg rax)]
    ; mk_instr vpbroadcastq [reg tmp; reg tmp]
    ; mk_instr vmovdqu [reg dst; mem (mem_at rsi off)]
    ; mk_instr vpaddq  [reg dst; reg dst; reg tmp]
    ; mk_instr oc      [reg dst; reg dst; mem (mem_at rdx off)]
    ; mk_instr vmovdqu [mem (mem_at rdi off); reg dst]
    ]
  | LimbVecConstBinop oc cs =>
    let tmp := VReg (nth_ymm (limb_idx + 8)) in
    let bval := nth 0%nat cs 0%Z in
    let build_const :=
      ([ mk_instr mov     [reg (SReg rax); Syntax.const bval]
       ; mk_instr vmovq   [reg tmp; reg (SReg rax)]
       ; mk_instr vpbroadcastq [reg tmp; reg tmp]
       ]
       ++ (if Z.eqb (nth 1%nat cs 0%Z) bval then [] else emit_blend_lane tmp 1 (nth 1%nat cs 0%Z))
       ++ (if Z.eqb (nth 2%nat cs 0%Z) bval then [] else emit_blend_lane tmp 2 (nth 2%nat cs 0%Z))
       ++ (if Z.eqb (nth 3%nat cs 0%Z) bval then [] else emit_blend_lane tmp 3 (nth 3%nat cs 0%Z)))%list
    in
    (build_const
     ++ [ mk_instr vmovdqu [reg dst; mem (mem_at rsi off)]
        ; mk_instr vpaddq  [reg dst; reg dst; reg tmp]
        ; mk_instr oc      [reg dst; reg dst; mem (mem_at rdx off)]
        ; mk_instr vmovdqu [mem (mem_at rdi off); reg dst]
        ])%list
  end.

(** ** Top-level: generate complete function *)

Definition emit_function (fname : string) (limb_ops : list limb_op) : Lines :=
  let header :=
    [ mk_header (SECTION ".text")
    ; mk_header (GLOBAL fname)
    ; mk_header (LABEL fname)
    ] in
  let body := flat_map (fun p => emit_limb (fst p) (snd p))
                       (combine (seq 0 (List.length limb_ops)) limb_ops) in
  let footer :=
    [ mk_instr vzeroupper []
    ; mk_instr Syntax.ret []
    ] in
  (header ++ body ++ footer)%list.

(** ** Concrete primitives *)

(** Vectorized [add]: all limbs are simple vpaddq, no constants. *)
Definition vectorized_add (fname : string) (n_limbs : nat) : Lines :=
  emit_function fname (repeat (LimbBinop vpaddq) n_limbs).

(** Group a flat list into chunks of [n], padding the last chunk with [d]. *)
Fixpoint chunks_of_aux {A} (fuel : nat) (n : nat) (d : A) (xs : list A) : list (list A) :=
  match fuel with
  | O => []
  | S fuel' =>
    match xs with
    | [] => []
    | _ => firstn n (xs ++ repeat d n) :: chunks_of_aux fuel' n d (skipn n xs)
    end
  end.

Definition chunks_of {A} (n : nat) (d : A) (xs : list A) : list (list A) :=
  chunks_of_aux (List.length xs) n d xs.

(** Vectorized [sub]: takes flat list of underflow constants (one per batched limb),
    groups them by 4 lanes per YMM, and uses [LimbVecConstBinop] for each group. *)
Definition vectorized_sub (fname : string) (consts : list Z) : Lines :=
  emit_function fname (map (LimbVecConstBinop vpsubq) (chunks_of 4 0%Z consts)).

(** ** Scalar op mapping (for future general DAG transformation) *)

(** Maps a scalar arithmetic operation to its AVX2 vector opcode.
    Returns [None] for ops without a 1:1 equivalent (e.g. mul, mulhuu). *)
Definition scalar_to_vector_opcode (s : N) (scalar : Symbolic.op) : option OpCode :=
  match scalar with
  | Symbolic.add 64 => Some vpaddq
  | Symbolic.sub 64 => Some vpsubq
  | Symbolic.and 64 => Some vpandq
  | Symbolic.or  64 => Some vporq
  | Symbolic.xor 64 => Some vpxorq
  | Symbolic.add 32 => Some vpaddd
  | Symbolic.sub 32 => Some vpsubd
  | _ => None
  end.
