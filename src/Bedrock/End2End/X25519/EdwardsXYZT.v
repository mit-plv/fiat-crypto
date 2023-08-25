Require Import bedrock2.Array.
Require Import bedrock2.FE310CSemantics.
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
Require Import compiler.MMIO.
Require Import compiler.Pipeline.
Require Import compiler.Symbols.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
From coqutil.Tactics Require Import Tactics letexists eabstract rdelta reference_to_string ident_of_string.
Require Import coqutil.Word.Bitwidth32.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Interface.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Group.AdditionChains.
Require Import Crypto.Bedrock.Group.ScalarMult.CSwap.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Require Import Crypto.Bedrock.End2End.X25519.Field25519.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Util.Decidable.
Require Import Curves.Edwards.XYZT.Basic.
Require Import Curves.Edwards.XYZT.Precomputed.
Require Import Lia.
Require Crypto.Bedrock.Field.Synthesis.New.Signature.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Import LittleEndianList.
Import ListNotations.
Import ProgramLogic.Coercions.
Import WeakestPrecondition.

Local Existing Instance field_parameters.
Local Instance frep25519 : Field.FieldRepresentation := field_representation n Field25519.s c.
Local Existing Instance frep25519_ok.

Definition add_precomputed := func! (ox, oy, oz, ot, X1, Y1, Z1, T1, ypx2, ymx2, xy2d2) {
  stackalloc 40 as YpX1;
  fe25519_add(YpX1, Y1, X1);
  stackalloc 40 as YmX1;
  fe25519_sub(YmX1, Y1, X1);
  stackalloc 40 as A;
  fe25519_mul(A, YpX1, ypx2);
  stackalloc 40 as B;
  fe25519_mul(B, YmX1, ymx2);
  stackalloc 40 as C;
  fe25519_mul(C, xy2d2, T1);
  stackalloc 40 as D;
  fe25519_carry_add(D, Z1, Z1);
  fe25519_sub(ox, A, B);
  fe25519_add(oy, A, B);
  fe25519_add(oz, D, C);
  fe25519_sub(ot, D, C);
  fe25519_mul(ox, ox, ot);
  fe25519_mul(oy, oy, oz);
  fe25519_mul(oz, ot, oz);
  fe25519_mul(ot, ox, oy)
}.

(* Equivalent of m1double in src/Curves/Edwards/XYZT/Basic.v *)
(* TODO: T is unused..? *)
Definition double := func! (ox, oy, oz, ot, X, Y, Z, T) {
  stackalloc 40 as trX;
  fe25519_square(trX, X);
  stackalloc 40 as trZ;
  fe25519_square(trZ, Y);
  stackalloc 40 as t0;
  fe25519_square(t0, Z);
  stackalloc 40 as trT;
  fe25519_carry_add(trT, t0, t0);
  stackalloc 40 as rY;
  fe25519_add(rY, X, Y);
  fe25519_square(t0, rY);
  stackalloc 40 as cY;
  fe25519_carry_add(cY, trZ, trX);
  stackalloc 40 as cZ;
  fe25519_sub(cZ, trZ, trX); (* TODO: use carry_sub once #1641 is merged *)
  stackalloc 40 as cX;
  fe25519_sub(cX, t0, cY);
  stackalloc 40 as cT;
  fe25519_sub(cT, trT, cZ);
  fe25519_mul(ox, cX, cT);
  fe25519_mul(oy, cY, cZ);
  fe25519_mul(oz, cZ, cT);
  fe25519_mul(ot, cX, cY)
}.

Section WithParameters.
  Context {two_lt_M: 2 < M_pos}.
  (* TODO: Can we provide actual values/proofs for these, rather than just sticking them in the context? *)
  Context {char_ge_3 : (@Ring.char_ge (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos BinNat.N.two))}.
  Context {field:@Algebra.Hierarchy.field (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}.
  Context {a d: F M_pos}
          {nonzero_a : a <> F.zero}
          {square_a : exists sqrt_a, (F.mul sqrt_a sqrt_a) = a}
          {nonsquare_d : forall x, (F.mul x x) <> d}.
  Context {a_eq_minus1:a = F.opp F.one} {twice_d} {k_eq_2d:twice_d = (F.add d d)}.

Local Coercion F.to_Z : F >-> Z.
Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").

Local Notation FElem := (FElem(FieldRepresentation:=frep25519)).
Local Notation bounded_by := (bounded_by(FieldRepresentation:=frep25519)).
Local Notation word := (Naive.word 32).
Local Notation felem := (felem(FieldRepresentation:=frep25519)).
Local Notation point := (point(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(d:=d)).
Local Notation coordinates := (coordinates(Feq:=Logic.eq)).
Local Notation m1double :=
  (m1double(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
           (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
           (field:=field)(char_ge_3:=char_ge_3)(Feq_dec:=F.eq_dec)
           (a:=a)(d:=d)(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)
           (a_eq_minus1:=a_eq_minus1)(twice_d:=twice_d)(k_eq_2d:=k_eq_2d)).


Global Instance spec_of_add_precomputed : spec_of "add_precomputed" :=
  fnspec! "add_precomputed"
    (oxK oyK ozK otK X1K Y1K Z1K T1K ypx2K ymx2K xy2d2K : word) /
    (ox oy oz ot X1 Y1 Z1 T1 ypx2 ymx2 xy2d2 : felem) (R : _ -> Prop),
  { requires t m :=
      bounded_by tight_bounds X1 /\
      bounded_by tight_bounds Y1 /\
      bounded_by tight_bounds Z1 /\
      bounded_by loose_bounds T1 /\
      bounded_by loose_bounds ypx2 /\
      bounded_by loose_bounds ymx2 /\
      bounded_by loose_bounds xy2d2 /\
      m =* (FElem X1K X1) * (FElem Y1K Y1) * (FElem Z1K Z1) * (FElem T1K T1) * (FElem ypx2K ypx2) * (FElem ymx2K ymx2) * (FElem xy2d2K xy2d2) * (FElem oxK ox) * (FElem oyK oy) * (FElem ozK oz) * (FElem otK ot) * R;
    ensures t' m' :=
      t = t' /\
      exists ox' oy' oz' ot',
        ((feval ox'), (feval oy'), (feval oz'), (feval ot')) = (@m1add_precomputed_coordinates (F M_pos) (F.add) (F.sub) (F.mul) ((feval X1), (feval Y1), (feval Z1), (feval T1)) ((feval ypx2), (feval ymx2), (feval xy2d2))) /\
        bounded_by loose_bounds ox' /\
        bounded_by loose_bounds oy' /\
        bounded_by loose_bounds oz' /\
        bounded_by loose_bounds ot' /\
        m' =* (FElem X1K X1) * (FElem Y1K Y1) * (FElem Z1K Z1) * (FElem T1K T1) * (FElem ypx2K ypx2) * (FElem ymx2K ymx2) * (FElem xy2d2K xy2d2) * (FElem oxK ox') * (FElem oyK oy') * (FElem ozK oz') * (FElem otK ot') * R }.

Global Instance spec_of_double : spec_of "double" :=
  fnspec! "double"
    (oxK oyK ozK otK XK YK ZK TK : word) /
    (ox oy oz ot X Y Z T : felem) (p : point) (R : _ -> Prop),
  { requires t m :=
      coordinates p = ((feval X), (feval Y), (feval Z), (feval T)) /\
      bounded_by tight_bounds X /\
      bounded_by tight_bounds Y /\
      bounded_by loose_bounds Z /\
      bounded_by loose_bounds T /\
      m =* (FElem XK X) * (FElem YK Y) * (FElem ZK Z) * (FElem TK T) * (FElem oxK ox) * (FElem oyK oy) * (FElem ozK oz) * (FElem otK ot) * R;
    ensures t' m' :=
      t = t' /\
      exists ox' oy' oz' ot',
        ((feval ox'), (feval oy'), (feval oz'), (feval ot')) = coordinates (@m1double p) /\
        bounded_by tight_bounds ox' /\
        bounded_by tight_bounds oy' /\
        bounded_by tight_bounds oz' /\
        bounded_by tight_bounds ot' /\
        m' =* (FElem XK X) * (FElem YK Y) * (FElem ZK Z) * (FElem TK T) * (FElem oxK ox') * (FElem oyK oy') * (FElem ozK oz') * (FElem otK ot') * R }.


Local Instance spec_of_fe25519_square : spec_of "fe25519_square" := Field.spec_of_UnOp un_square.
Local Instance spec_of_fe25519_mul : spec_of "fe25519_mul" := Field.spec_of_BinOp bin_mul.
Local Instance spec_of_fe25519_add : spec_of "fe25519_add" := Field.spec_of_BinOp bin_add.
Local Instance spec_of_fe25519_carry_add : spec_of "fe25519_carry_add" := Field.spec_of_BinOp bin_carry_add.
Local Instance spec_of_fe25519_sub : spec_of "fe25519_sub" := Field.spec_of_BinOp bin_sub.
Local Instance spec_of_fe25519_from_word : spec_of "fe25519_from_word" := Field.spec_of_from_word.

Local Arguments word.rep : simpl never.
Local Arguments word.wrap : simpl never.
Local Arguments word.unsigned : simpl never.
Local Arguments word.of_Z : simpl never.

(* TODO: Make these changes in ProgramLogic instead *)
Local Ltac straightline_cleanup :=
  match goal with
  (* TODO remove superfluous _ after .rep, but that will break some proofs that rely on
     x not being cleared to instantiate evars with terms depending on x *)
  | x : Word.Interface.word.rep _ |- _ => clear x
  | x : Init.Byte.byte |- _ => clear x
  | x : Semantics.trace |- _ => clear x
  | x : Syntax.cmd |- _ => clear x
  | x : Syntax.expr |- _ => clear x
  | x : coqutil.Map.Interface.map.rep |- _ => clear x
  | x : BinNums.Z |- _ => clear x
  | x : unit |- _ => clear x
  | x : bool |- _ => clear x
  | x : list _ |- _ => clear x
  | x : nat |- _ => clear x
  (* same TODO as above *)
  | x := _ : Word.Interface.word.rep _ |- _ => clear x
  | x := _ : Init.Byte.byte |- _ => clear x
  | x := _ : Semantics.trace |- _ => clear x
  | x := _ : Syntax.cmd |- _ => clear x
  | x := _ : Syntax.expr |- _ => clear x
  | x := _ : coqutil.Map.Interface.map.rep |- _ => clear x
  | x := _ : BinNums.Z |- _ => clear x
  | x := _ : unit |- _ => clear x
  | x := _ : bool |- _ => clear x
  | x := _ : list _ |- _ => clear x
  | x := _ : nat |- _ => clear x
  | |- forall _, _ => intros
  | |- let _ := _ in _ => intros
  | |- dlet.dlet ?v (fun x => ?P) => change (let x := v in P); intros
  | _ => progress (cbn [Semantics.interp_binop] in * )
  | H: exists _, _ |- _ => destruct H; assert_fails (idtac; let __ := constr:(H) in idtac)
  | H: _ /\ _ |- _ => destruct H
  | x := ?y |- ?G => is_var y; subst x
  | H: ?x = ?y |- _ => constr_eq x y; clear H
  | H: ?x = ?y |- _ => is_var x; is_var y; assert_fails (idtac; let __ := eval cbv [x] in x in idtac); subst x
  | H: ?x = ?y |- _ => is_var x; is_var y; assert_fails (idtac; let __ := eval cbv [y] in y in idtac); subst y
  | H: ?x = ?v |- _ =>
    is_var x;
    assert_fails (idtac; let __ := eval cbv delta [x] in x in idtac);
    lazymatch v with context[x] => fail | _ => idtac end;
    let x' := fresh x in
    rename x into x';
    simple refine (let x := v in _);
    change (x' = x) in H;
    symmetry in H;
    destruct H
  end.

Local Ltac straightline :=
  match goal with
  | _ => straightline_cleanup
  | |- program_logic_goal_for ?f _ =>
    enter f; intros;
    match goal with
    | H: map.get ?functions ?fname = Some _ |- _ =>
        eapply start_func; [exact H | clear H]
    end;
    cbv match beta delta [WeakestPrecondition.func]
  | |- WeakestPrecondition.cmd _ (cmd.set ?s ?e) _ _ _ ?post =>
    unfold1_cmd_goal; cbv beta match delta [cmd_body];
    let __ := match s with String.String _ _ => idtac | String.EmptyString => idtac end in
    ident_of_constr_string_cps s ltac:(fun x =>
      ensure_free x;
      (* NOTE: keep this consistent with the [exists _, _ /\ _] case far below *)
      letexists _ as x; split; [solve [repeat straightline]|])
  | |- cmd _ ?c _ _ _ ?post =>
    let c := eval hnf in c in
    lazymatch c with
    | cmd.while _ _ => fail
    | cmd.cond _ _ _ => fail
    | cmd.interact _ _ _ => fail
    | _ => unfold1_cmd_goal; cbv beta match delta [cmd_body]
    end
  | |- @list_map _ _ (get _) _ _ => unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | |- @list_map _ _ (expr _ _) _ _ => unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | |- @list_map _ _ _ nil _ => cbv beta match fix delta [list_map list_map_body]
  | |- expr _ _ _ _ => unfold1_expr_goal; cbv beta match delta [expr_body]
  | |- dexpr _ _ _ _ => cbv beta delta [dexpr]
  | |- dexprs _ _ _ _ => cbv beta delta [dexprs]
  | |- literal _ _ => cbv beta delta [literal]
  | |- @get ?w ?W ?L ?l ?x ?P =>
      let get' := eval cbv [get] in @get in
      change (get' w W L l x P); cbv beta
  | |- load _ _ _ _ => cbv beta delta [load]
  | |- @Loops.enforce ?width ?word ?locals ?names ?values ?map =>
    let values := eval cbv in values in
    change (@Loops.enforce width word locals names values map);
    exact (conj (eq_refl values) eq_refl)
  | |- @eq (@coqutil.Map.Interface.map.rep String.string Interface.word.rep _) _ _ =>
    eapply SortedList.eq_value; exact eq_refl
  | |- @map.get String.string Interface.word.rep ?M ?m ?k = Some ?e' =>
    let e := rdelta e' in
    is_evar e;
    once (let v := multimatch goal with x := context[@map.put _ _ M _ k ?v] |- _ => v end in
          (* cbv is slower than this, cbv with whitelist would have an enormous whitelist, cbv delta for map is slower than this, generalize unrelated then cbv is slower than this, generalize then vm_compute is slower than this, lazy is as slow as this: *)
          unify e v; exact (eq_refl (Some v)))
  | |- @coqutil.Map.Interface.map.get String.string Interface.word.rep _ _ _ = Some ?v =>
    let v' := rdelta v in is_evar v'; (change v with v'); exact eq_refl
  | |- ?x = ?y =>
    let y := rdelta y in is_evar y; change (x=y); exact eq_refl
  | |- ?x = ?y =>
    let x := rdelta x in is_evar x; change (x=y); exact eq_refl
  | |- ?x = ?y =>
    let x := rdelta x in let y := rdelta y in constr_eq x y; exact eq_refl
  | |- store Syntax.access_size.one _ _ _ _ =>
    eapply Scalars.store_one_of_sep; [solve[ecancel_assumption]|]
  | |- store Syntax.access_size.two _ _ _ _ =>
    eapply Scalars.store_two_of_sep; [solve[ecancel_assumption]|]
  | |- store Syntax.access_size.four _ _ _ _ =>
    eapply Scalars.store_four_of_sep; [solve[ecancel_assumption]|]
  | |- store Syntax.access_size.word _ _ _ _ =>
    eapply Scalars.store_word_of_sep; [solve[ecancel_assumption]|]
  | |- bedrock2.Memory.load Syntax.access_size.one ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_one_of_sep _ _ _ _ _ _ _ _ _ _); ecancel_assumption
  | |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.two ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_two_of_sep _ word _ mem _ a _ _ m _); ecancel_assumption
  | |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.four ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_four_of_sep_32bit _ word _ mem _ eq_refl a _ _ m _); ecancel_assumption
  | |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.four ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_four_of_sep _ word _ mem _ a _ _ m _); ecancel_assumption
  | |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.word ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_word_of_sep _ word _ mem _ a _ _ m _); ecancel_assumption
  | |- exists l', Interface.map.of_list_zip ?ks ?vs = Some l' /\ _ =>
    letexists; split; [exact eq_refl|] (* TODO: less unification here? *)
  | |- exists l', Interface.map.putmany_of_list_zip ?ks ?vs ?l = Some l' /\ _ =>
    letexists; split; [exact eq_refl|] (* TODO: less unification here? *)
  | _ => fwd_uniq_step
  | |- exists x, ?P /\ ?Q =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P /\ Q) x _);
                        split; [solve [repeat straightline]|]
  | |- exists x, Markers.split (?P /\ ?Q) =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P /\ Q) x _);
                        split; [solve [repeat straightline]|]
  | |- Markers.unique (exists x, Markers.split (?P /\ ?Q)) =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P /\ Q) x _);
                        split; [solve [repeat straightline]|]
  | |- Markers.unique (Markers.left ?G) =>
    change G;
    unshelve (idtac; repeat match goal with
                     | |- Markers.split (?P /\ Markers.right ?Q) =>
                       split; [eabstract (repeat straightline) | change Q]
                     | |- exists _, _ => letexists
                     end); []
  | |- Markers.split ?G => change G; split
  | |- True => exact I
  | |- False \/ _ => right
  | |- _ \/ False => left
  | |- BinInt.Z.modulo ?z (Memory.bytes_per_word _) = BinInt.Z0 /\ _ =>
      lazymatch Coq.setoid_ring.InitialRing.isZcst z with
      | true => split; [exact eq_refl|]
      end
  | |- _ => straightline_stackalloc
  | |- _ => straightline_stackdealloc
  | |- context[sep (sep _ _) _] => progress (flatten_seps_in_goal; cbn [seps])
  | H : context[sep (sep _ _) _] |- _ => progress (flatten_seps_in H; cbn [seps] in H)
  end.
(* end of modified straightline section *)

Local Ltac cbv_bounds H :=
  cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds] in H;
  cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds].

Local Ltac solve_bounds :=
  repeat match goal with
  | H: bounded_by loose_bounds ?x |- bounded_by loose_bounds ?x => apply H
  | H: bounded_by tight_bounds ?x |- bounded_by tight_bounds ?x => apply H
  | H: bounded_by tight_bounds ?x |- bounded_by loose_bounds ?x => apply relax_bounds
  | H: bounded_by _ ?x |- bounded_by _ ?x => cbv_bounds H
  end.

Local Ltac solve_mem :=
  repeat match goal with
  | |- exists _ : _ -> Prop, _%sep _ => eexists
  | |- _%sep _ => ecancel_assumption
  end.

Local Ltac solve_stack :=
  (* Rewrites the `stack$@a` term in H to use a Bignum instead *)
  cbv [FElem];
  match goal with
  | H: _%sep ?m |- (Bignum.Bignum felem_size_in_words ?a _ * _)%sep ?m =>
       seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 10 a) H
  end;
  [> transitivity 40%nat; trivial | ];
  (* proves the memory matches up *)
  use_sep_assumption; cancel; cancel_seps_at_indices 0%nat 0%nat; cbn; [> trivial | eapply RelationClasses.reflexivity].

Local Ltac single_step :=
  repeat straightline; straightline_call; ssplit; try solve_mem; try solve_bounds; try solve_stack.

(* An example that demonstrates why we need to set Strategy in add_precomputed_ok below *)
Example demo_strategy : forall x,
  (@Field.bounded_by field_parameters (Zpos (xO (xO (xO (xO (xO xH))))))
        BW32 (Naive.word (Zpos (xO (xO (xO (xO (xO xH)))))))
        (@SortedListWord.map (Zpos (xO (xO (xO (xO (xO xH))))))
           (Naive.word (Zpos (xO (xO (xO (xO (xO xH))))))) Naive.word32_ok
           byte) frep25519
        (@loose_bounds field_parameters (Zpos (xO (xO (xO (xO (xO xH))))))
           BW32 (Naive.word (Zpos (xO (xO (xO (xO (xO xH)))))))
           (@SortedListWord.map (Zpos (xO (xO (xO (xO (xO xH))))))
              (Naive.word (Zpos (xO (xO (xO (xO (xO xH))))))) Naive.word32_ok
              byte) frep25519) x =
          @Field.bounded_by field_parameters (Zpos (xO (xO (xO (xO (xO xH))))))
        BW32 (Naive.word (Zpos (xO (xO (xO (xO (xO xH)))))))
        (@SortedListWord.map (Zpos (xO (xO (xO (xO (xO xH))))))
           (Naive.word (Zpos (xO (xO (xO (xO (xO xH))))))) Naive.word32_ok
           byte) frep25519
        (@bin_outbounds (Zpos (xO (xO (xO (xO (xO xH)))))) BW32
           (Naive.word (Zpos (xO (xO (xO (xO (xO xH)))))))
           (@SortedListWord.map (Zpos (xO (xO (xO (xO (xO xH))))))
              (Naive.word (Zpos (xO (xO (xO (xO (xO xH))))))) Naive.word32_ok
              byte) field_parameters frep25519 (@add field_parameters)
           (@bin_add (Zpos (xO (xO (xO (xO (xO xH)))))) BW32
              (Naive.word (Zpos (xO (xO (xO (xO (xO xH)))))))
              (@SortedListWord.map (Zpos (xO (xO (xO (xO (xO xH))))))
                 (Naive.word (Zpos (xO (xO (xO (xO (xO xH)))))))
                 Naive.word32_ok byte) field_parameters frep25519)) x).
Proof.
  (* reflexivity. *) (* Does not complete within 1 minute. *)
  (* Now set Strategy precedence... *)
  Strategy -1000 [bin_outbounds bin_add].
  reflexivity. (* ...and completes immediately *)
Qed.

Lemma add_precomputed_ok : program_logic_goal_for_function! add_precomputed.
Proof.
  (* Without this, resolution of cbv stalls out Qed. *)
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds].

  (* Unwrap each call in the program. *)
  (* Each binop produces 2 memory goals on the inputs, 2 bounds goals on the inputs, and 1 memory goal on the output. *)
  single_step. (* fe25519_add(YpX1, Y1, X1) *)
  single_step. (* fe25519_sub(YmX1, Y1, X1) *)
  single_step. (* fe25519_mul(A, YpX1, ypx2) *)
  single_step. (* fe25519_mul(B, YmX1, ymx2) *)
  single_step. (* fe25519_mul(C, xy2d2, T1) *)
  single_step. (* fe25519_carry_add(D, Z1, Z1) *)
  single_step. (* fe25519_sub(ox, A, B) *)
  single_step. (* fe25519_add(oy, A, B) *)
  single_step. (* fe25519_add(oz, D, C) *)
  single_step. (* fe25519_sub(ot, D, C) *)
  single_step. (* fe25519_mul(ox, ox, ot) *)
  single_step. (* fe25519_mul(oy, oy, oz) *)
  single_step. (* fe25519_mul(oz, ot, oz) *)
  single_step. (* fe25519_mul(ot, ox, oy) *)

  (* Solve the postconditions *)
  repeat straightline.
  (* Rewrites the FElems for the stack (in H87) to be about bytes instead *)
    cbv [FElem] in *.
    (* Prevent output from being rewritten by seprewrite_in *) 
    remember (Bignum.Bignum felem_size_in_words otK _) as Pt in H87.
    remember (Bignum.Bignum felem_size_in_words ozK _) as Pz in H87.
    remember (Bignum.Bignum felem_size_in_words oyK _) as Py in H87.
    remember (Bignum.Bignum felem_size_in_words oxK _) as Px in H87.
    do 6 (seprewrite_in @Bignum.Bignum_to_bytes H87).
    subst Pt Pz Py Px.
    extract_ex1_and_emp_in H87.

  (* Solve stack/memory stuff *)
  repeat straightline.

  (* Post-conditions *)
  exists x9,x10,x11,x12; ssplit. 2,3,4,5:solve_bounds.
  { (* Correctness: result matches Gallina *)
    cbv [bin_model bin_mul bin_add bin_carry_add bin_sub] in *.
    cbv match beta delta [m1add_precomputed_coordinates].
    congruence.
  }
  (* Safety: memory is what it should be *)
  ecancel_assumption.
Qed.

Lemma double_ok : program_logic_goal_for_function! double.
Proof.
  (* Without this, resolution of cbv stalls out Qed. *)
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds].

  (* Unwrap each call in the program. *)
  (* Each binop produces 2 memory goals on the inputs, 2 bounds goals on the inputs, and 1 memory goal on the output. *)
  single_step. (* fe25519_square(trX, X) *)
  single_step. (* fe25519_square(trZ, Y) *)
  single_step. (* fe25519_square(t0, Z) *)
  single_step. (* fe25519_carry_add(trT, t0, t0) *)
  single_step. (* fe25519_add(rY, X, Y) *)
  single_step. (* fe25519_square(t0, rY) *)
  single_step. (* fe25519_carry_add(cY, trZ, trX) *)
  single_step. (* fe25519_sub(cZ, trZ, trX) *)
  single_step. (* fe25519_sub(cX, t0, cY) *)
  single_step. (* fe25519_sub(cT, trT, cZ) *)
  admit. (* bounds issue on cZ -- 3 lines up needs carry_sub instead *)
  single_step. (* fe25519_mul(ox, cX, cT) *)
  single_step. (* fe25519_mul(oy, cY, cZ) *)
  single_step. (* fe25519_mul(oz, cZ, cT) *)
  single_step. (* fe25519_mul(ot, cX, cY) *)

  (* Solve the postconditions *)
  repeat straightline.
  (* Rewrites the FElems for the stack (in H97) to be about bytes instead *)
    cbv [FElem] in *.
    (* Prevent output from being rewritten by seprewrite_in *) 
    remember (Bignum.Bignum felem_size_in_words otK _) as Pt in H97.
    remember (Bignum.Bignum felem_size_in_words ozK _) as Pz in H97.
    remember (Bignum.Bignum felem_size_in_words oyK _) as Py in H97.
    remember (Bignum.Bignum felem_size_in_words oxK _) as Px in H97.
    do 9 (seprewrite_in @Bignum.Bignum_to_bytes H97).
    subst Pt Pz Py Px.
    extract_ex1_and_emp_in H97.

  (* Solve stack/memory stuff *)
  repeat straightline.

  (* Post-conditions *)
  exists x9,x10,x11,x12; ssplit. 2,3,4,5:solve_bounds.
  { (* Correctness: result matches Gallina *)
    cbv [bin_model bin_mul bin_add bin_carry_add bin_sub un_model un_square] in *.
    cbv match beta delta [m1double coordinates proj1_sig].
    destruct p. cbv [coordinates proj1_sig] in H13.
    rewrite H13.
    rewrite F.pow_2_r in *.
    congruence.
  }
  (* Safety: memory is what it should be *)
  ecancel_assumption.
Admitted.

End WithParameters.
