Require Import bedrock2.Array.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.Loops.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ZnWords.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.OfListWord.
From coqutil.Tactics Require Import Tactics letexists eabstract rdelta reference_to_string ident_of_string.
Require Import coqutil.Word.Bitwidth64.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Group.ScalarMult.CSwap.
Require Import Crypto.Bedrock.Secp256k1.Field256k1.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Arithmetic.FLia.
Require Import Crypto.Algebra.Hierarchy.
Require Import Numbers.DecimalString.
Require Import Crypto.Util.Decidable.
Require Import Lia.
Require Crypto.Bedrock.Field.Synthesis.New.Signature.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Import LittleEndianList.
Import ListNotations.
Import ProgramLogic.Coercions.
Import WeakestPrecondition.

(*
addchain: expr: "2^256 - 2^32 - 977 - 2"
addchain: hex: fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2d
addchain: dec: 115792089237316195423570985008687907853269984665640564039457584007908834671661
addchain: best: opt(dictionary(hybrid(3,0),continued_fractions(dichotomic)))
addchain: cost: 270
*)
(*
tmp	t0	t1	t2	t3	t4
double	t0	x
double	z	t0
add	z	x	z
add	t1	t0	z
double	t0	t1
shift	t2	t0	2
add	t2	t1	t2
shift	t2	t2	4
add	t0	t0	t2
shift	t2	t0	2
add	t2	t1	t2
shift	t2	t2	10
add	t0	t0	t2
add	t0	x	t0
double	t3	t0
shift	t2	t3	2
shift	t4	t2	22
add	t2	t2	t4
shift	t4	t2	20
add	t3	t3	t4
shift	t3	t3	46
add	t2	t2	t3
shift	t3	t2	110
add	t2	t2	t3
add	t1	t1	t2
shift	t1	t1	23
add	t0	t0	t1
shift	t0	t0	7
add	t0	z	t0
shift	t0	t0	3
add	z	z	t0
*)

Local Existing Instance field_parameters.
Local Instance frep256k1 : Field.FieldRepresentation := field_representation Field256k1.m.
Local Existing Instance frep256k1_ok.

(* TODO: This could probably be automated *)

(* Renders program way too long for the program logic to handle. *)
(* Unroll the loop *)
(* Fixpoint secp256k1_shift x y n := *)
(*   match n with *)
(*   | O => cmd.skip *)
(*   | S n => (cmd.seq bedrock_cmd:(secp256k1_square(coq:(expr.var x), coq:(expr.var y))) *)
(*                    bedrock_cmd:(coq:(secp256k1_shift x x n))) *)
(*   end. *)

(* Peel off one iteration in all cases. *)
Definition secp256k1_shift x y (n: nat) :=
  cmd.seq bedrock_cmd:(secp256k1_square(coq:(expr.var x), coq:(expr.var y)))
          (cmd.seq bedrock_cmd:(i = $1)
                   bedrock_cmd:(while (i < coq:(n)) {
                                  secp256k1_square(coq:(expr.var x), coq:(expr.var x));
                                  i = i + $1
                                })).

Definition secp256k1_inv :=
  func! (z, x) {
    stackalloc 32 as t0;
    stackalloc 32 as t1;
    stackalloc 32 as t2;
    stackalloc 32 as t3;
    stackalloc 32 as t4;
    secp256k1_square(t0, x);            (* double	t0	x *)
    secp256k1_square(z, t0);            (* double	z	t0 *)
    secp256k1_mul(z, x, z);             (* add	z	x	z *)
    secp256k1_mul(t1, t0, z);           (* add	t1	t0	z *)
    secp256k1_square(t0, t1);           (* double	t0	t1 *)
    coq:(secp256k1_shift "t2" "t0" 2);  (* shift	t2	t0	2 *)
    secp256k1_mul(t2, t1, t2);          (* add	t2	t1	t2 *)
    coq:(secp256k1_shift "t2" "t2" 4);  (* shift	t2	t2	4 *)
    secp256k1_mul(t0, t0, t2);          (* add	t0	t0	t2 *)
    coq:(secp256k1_shift "t2" "t0" 2);  (* shift	t2	t0	2 *)
    secp256k1_mul(t2, t1, t2);          (* add	t2	t1	t2 *)
    coq:(secp256k1_shift "t2" "t2" 10); (* shift	t2	t2	10 *)
    secp256k1_mul(t0, t0, t2);          (* add	t0	t0	t2 *)
    secp256k1_mul(t0, x, t0);           (* add	t0	x	t0 *)
    secp256k1_square(t3, t0);           (* double	t3	t0 *)
    coq:(secp256k1_shift "t2" "t3" 2);  (* shift	t2	t3	2 *)
    coq:(secp256k1_shift "t4" "t2" 22); (* shift	t4	t2	22 *)
    secp256k1_mul(t2, t2, t4);          (* add	t2	t2	t4 *)
    coq:(secp256k1_shift "t4" "t2" 20); (* shift	t4	t2	20 *)
    secp256k1_mul(t3, t3, t4);          (* add	t3	t3	t4 *)
    coq:(secp256k1_shift "t3" "t3" 46); (* shift	t3	t3	46 *)
    secp256k1_mul(t2, t2, t3);          (* add	t2	t2	t3 *)
    coq:(secp256k1_shift "t3" "t2" 110);(* shift	t3	t2	110 *)
    secp256k1_mul(t2, t2, t3);          (* add	t2	t2	t3 *)
    secp256k1_mul(t1, t1, t2);          (* add	t1	t1	t2 *)
    coq:(secp256k1_shift "t1" "t1" 23); (* shift	t1	t1	23 *)
    secp256k1_mul(t0, t0, t1);          (* add	t0	t0	t1 *)
    coq:(secp256k1_shift "t0" "t0" 7);  (* shift	t0	t0	7 *)
    secp256k1_mul(t0, z, t0);           (* add	t0	z	t0 *)
    coq:(secp256k1_shift "t0" "t0" 3);  (* shift	t0	t0	3 *)
    secp256k1_mul(z, z, t0)             (* add	z	z	t0 *)
}.

(* Compute ToCString.c_func ("secp256k1_inv", secp256k1_inv). *)

Section WithParameters.
  Context {two_lt_M: 2 < M_pos}.
  Context {char_ge_3 : (@Ring.char_ge (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos BinNat.N.two))}.
  Context {field:@Algebra.Hierarchy.field (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}.
  Context {secp256k1_prime: prime m}.
  Context {F_M_pos : Z.pos M_pos = m}.

  Local Coercion F.to_Z : F >-> Z.
  Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
  Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").

  Local Notation FElem := (FElem(FieldRepresentation:=frep256k1)).
  Local Notation word := (Naive.word 64).
  Local Notation felem := (felem(FieldRepresentation:=frep256k1)).

  Local Instance spec_of_secp256k1_square : spec_of "secp256k1_square" := Field.spec_of_UnOp un_square.
  Local Instance spec_of_secp256k1_mul : spec_of "secp256k1_mul" := Field.spec_of_BinOp bin_mul.

  Global Instance spec_of_inv : spec_of "secp256k1_inv" :=
    fnspec! "secp256k1_inv"
      (zK xK : word) / (z x : felem) (vx : F M_pos) (R : _ -> Prop),
    { requires t m :=
        vx = feval x /\
        bounded_by loose_bounds x /\
        m =* (FElem zK z) * (FElem xK x) * R;
      ensures t' m' :=
        t = t' /\
        exists z',
        feval z' = (F.inv vx) /\
        bounded_by tight_bounds z' /\
        m' =* (FElem zK z') * (FElem xK x) * R
    }.

  Local Arguments word.rep : simpl never.
  Local Arguments word.wrap : simpl never.
  Local Arguments word.unsigned : simpl never.
  Local Arguments word.of_Z : simpl never.

  Local Ltac solve_mem :=
    repeat match goal with
      | |- exists _ : _ -> Prop, _%sep _ => eexists
      | |- _%sep _ => ecancel_assumption
      end.

  Local Ltac cbv_bounds H :=
    cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds] in H;
    cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds].

  Local Ltac solve_bounds :=
    match goal with
      | H: bounded_by _ ?x |- bounded_by _ ?x => apply H
      end.

  Local Ltac solve_stack :=
    (* Rewrites the `stack$@a` term in H to use a Bignum instead *)
    cbv [FElem];
    match goal with
    | H: _%sep ?m |- (Bignum.Bignum felem_size_in_words ?a _ * _)%sep ?m =>
        seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 4 a) H
    end;
    [> transitivity 32%nat; trivial | ];
    (* proves the memory matches up *)
    use_sep_assumption; cancel; cancel_seps_at_indices 0%nat 0%nat; cbn; [> trivial | eapply RelationClasses.reflexivity].

  Local Ltac single_step :=
    repeat straightline; straightline_call; ssplit; try solve_mem; try solve_bounds; try solve_stack.

  Lemma spec_of_shift functions tr mem loc post :
    forall var to (Hvar: var <> "i") (Hto: 2 <= to < 2^32) pvar vvar R,
      spec_of_secp256k1_square functions ->
      map.get loc var = Some pvar ->
      (FElem pvar vvar * R)%sep mem ->
      bounded_by un_outbounds vvar ->
      (forall tr' mem' loc',
          (tr' = tr /\
           loc' = map.put loc "i" (word.of_Z to) /\
           exists vvar',
             (FElem pvar vvar' * R)%sep mem' /\
             feval vvar' = F.pow (feval vvar) (N.pow 2%N (Z.to_N (to - 1))) /\
             bounded_by un_outbounds vvar') ->
          post tr' mem' loc'
      ) ->
      cmd functions
          bedrock_func_body:(
            {$"i" = coq:(expr.literal 1)};
             while coq:(expr.var "i") < coq:(expr.literal to) {
               {$"secp256k1_square"(coq:(expr.var var), coq:(expr.var var))};
                $"i" = coq:(expr.var "i") + coq:(expr.literal 1)
                }) tr mem loc post.
  Proof.
    intros. repeat straightline.
    pose (inv := fun (v: nat) (t: trace) (m: @map.rep word byte _) (l: @map.rep string word locals) => t = tr /\
                          exists i (Hi: 1 <= i <= to),
                          v = Z.to_nat (to - i) /\
                          (exists vx, ((FElem pvar vx) * R)%sep m /\
                                   feval vx = F.pow (feval vvar) (N.pow 2%N (Z.to_N (i - 1))) /\
                                   bounded_by un_outbounds vx) /\
                          l = map.put loc "i" (word.of_Z i)).
    eapply wp_while. exists nat, lt, inv. ssplit; [eapply lt_wf|..].
    eexists. unfold inv; ssplit; [reflexivity|..].
    exists 1. exists (ltac:(lia): 1 <= 1 <= to). ssplit; [reflexivity|..].
    eexists. ssplit.
    ecancel_assumption. rewrite F.pow_1_r. reflexivity. auto.
    reflexivity.
    intros fuel * Hinv.
    destruct Hinv as (-> & vi & Hvi & -> & Hmem & ->).
    eexists ?[b]; ssplit.
    eexists; split; [apply map.get_put_same|].
    eapply Core.WeakestPrecondition_dexpr_expr; [|apply ExprCompiler.expr_compile_Z_literal].
    cbn. rewrite <- Core.word.morph_ltu by lia.
    reflexivity.
    all: pose proof Zlt_cases vi to;
         intros Hnz; destruct (vi <? to);
         try (rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1 in Hnz;
              congruence); [].
    repeat straightline.
    eexists. split. eexists. split.
    rewrite map.get_put_diff by congruence. eauto.
    eexists. split. rewrite map.get_put_diff by congruence. eauto.
    reflexivity.
    single_step. repeat straightline.
    eexists. split.
    eexists. split. apply map.get_put_same. cbn. reflexivity.
    eexists. split. split; [reflexivity|].
    exists (vi + 1). exists (ltac:(lia): 1 <= vi + 1 <= to).
    ssplit; [reflexivity|..]. eexists; ssplit; [ecancel_assumption|..].
    repeat match goal with
           | H : feval ?a = _ |- context [feval ?a] => rewrite H
           end. cbv [un_model un_square].
    rewrite F.pow_pow_l, N.mul_comm, <- N.pow_succ_r', <- Z2N.inj_succ.
    f_equal. f_equal. lia. lia. auto.
    unfold l'. rewrite <- word.ring_morph_add, map.put_put_same. reflexivity.
    lia. assert (vi = to) as -> by lia.
    destruct Hmem as (? & ? & ? & ?).
    apply H3.
    ssplit; [reflexivity|reflexivity|].
    eexists; ssplit; eassumption.
  Qed.

  Lemma secp256k1_inv_ok : program_logic_goal_for_function! secp256k1_inv.
  Proof.
    Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds].

    repeat single_step.
    destruct H64 as (-> & -> & ? & ? & ? & ?).
    eexists; split; [reflexivity|].
    eapply spec_of_shift. congruence. lia. auto. reflexivity.
    ecancel_assumption. eassumption.
    repeat single_step.
    destruct H82 as (-> & -> & ? & ? & ? & ?).
    eexists; split; [reflexivity|].
    eapply spec_of_shift. congruence. lia. auto. reflexivity.
    ecancel_assumption. eassumption.
    repeat single_step.
    destruct H91 as (-> & -> & ? & ? & ? & ?).
    eexists; split; [reflexivity|].
    eapply spec_of_shift. congruence. lia. auto. reflexivity.
    ecancel_assumption. eassumption.
    repeat single_step.
    destruct H100 as (-> & -> & ? & ? & ? & ?).
    eexists; split; [reflexivity|].
    eapply spec_of_shift. congruence. lia. auto. reflexivity.
    ecancel_assumption. eassumption.
    repeat single_step.
    destruct H109 as (-> & -> & ? & ? & ? & ?).
    eexists; split; [reflexivity|].
    eapply spec_of_shift. congruence. lia. auto. reflexivity.
    ecancel_assumption. eassumption.
    repeat single_step.
    destruct H124 as (-> & -> & ? & ? & ? & ?).
    eexists; split; [reflexivity|].
    eapply spec_of_shift. congruence. lia. auto. reflexivity.
    ecancel_assumption. eassumption.
    repeat single_step.
    destruct H130 as (-> & -> & ? & ? & ? & ?).
    eexists; split; [reflexivity|].
    eapply spec_of_shift. congruence. lia. auto. reflexivity.
    ecancel_assumption. eassumption.
    repeat single_step.
    destruct H139 as (-> & -> & ? & ? & ? & ?).
    eexists; split; [reflexivity|].
    eapply spec_of_shift. congruence. lia. auto. reflexivity.
    ecancel_assumption. eassumption.
    repeat single_step.
    destruct H148 as (-> & -> & ? & ? & ? & ?).
    eexists; split; [reflexivity|].
    eapply spec_of_shift. congruence. lia. auto. reflexivity.
    ecancel_assumption. eassumption.
    repeat single_step.
    destruct H157 as (-> & -> & ? & ? & ? & ?).
    eexists; split; [reflexivity|].
    eapply spec_of_shift. congruence. lia. auto. reflexivity.
    ecancel_assumption. eassumption.
    repeat single_step.
    destruct H169 as (-> & -> & ? & ? & ? & ?).
    eexists; split; [reflexivity|].
    eapply spec_of_shift. congruence. lia. auto. reflexivity.
    ecancel_assumption. eassumption.
    repeat single_step.
    destruct H178 as (-> & -> & ? & ? & ? & ?).
    eexists; split; [reflexivity|].
    eapply spec_of_shift. congruence. lia. auto. reflexivity.
    ecancel_assumption. eassumption.
    repeat single_step.

    repeat straightline.
    cbv [FElem] in *.
    repeat match goal with
    | |- context [anybytes ?a _ _] =>
        match goal with
        | H: _ ?a' |- context [map.split ?a' _ _] =>
            seprewrite_in (@Bignum.Bignum_to_bytes _ _ _ _ _ _ felem_size_in_words a) H
        end
    end.
    extract_ex1_and_emp_in H194.

    repeat straightline.
    exists x42. ssplit; [|solve_bounds|ecancel_assumption].
    repeat match goal with
           | H : feval ?a = _ |- context [feval ?a] => rewrite H
           end.
    cbv [un_model bin_model un_square bin_mul].
    unfold vx. rewrite (@F.Fq_inv_fermat _ _ two_lt_M).
    rewrite F_M_pos.
    repeat match goal with
    | |- context [F.pow (F.pow (feval x) ?a) ?b] => rewrite (F.pow_pow_l (feval x) a b)
    | |- context [F.mul (feval x) (F.pow (feval x) ?n)] => rewrite <- (F.pow_succ_r (feval x) n)
    | |- context [F.mul (F.pow (feval x) ?n1) (F.pow (feval x) ?n2)] => rewrite <- (F.pow_add_r (feval x) n1 n2)
    end.
    f_equal.
  Qed.

End WithParameters.
