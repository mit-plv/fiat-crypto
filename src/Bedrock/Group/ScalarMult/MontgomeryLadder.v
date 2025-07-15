Require Crypto.Bedrock.Group.Loops.
Require Import Crypto.Curves.Montgomery.XZ.
Require Import Crypto.Curves.Montgomery.XZProofs.
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Alloc.
Require Import Rupicola.Lib.SepLocals.
Require Import Rupicola.Lib.ControlFlow.DownTo.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.Group.ScalarMult.CSwap.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Util.NumTheoryUtil.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Group.AdditionChains.

Require bedrock2.NotationsCustomEntry. Import bedrock2.Syntax.Coercions.

Require Import bedrock2.ZnWords.

Local Open Scope Z_scope.

Import NoExprReflectionCompiler.
Import DownToCompiler.
(* TODO: migrate these to rupicola.
   Currently break when put in Notations.v
 *)
Notation "'let/n' ( w , x , y , z ) := val 'in' body" :=
  (nlet [IdentParsing.TC.ident_to_string w;
        IdentParsing.TC.ident_to_string x;
        IdentParsing.TC.ident_to_string y;
        IdentParsing.TC.ident_to_string z]
        val  (fun '\<w, x, y, z\> => body))
    (at level 200, w name, x  name, y name, z name, body at level 200,
     only parsing).


Notation "'let/n' ( v , w , x , y , z ) := val 'in' body" :=
  (nlet [IdentParsing.TC.ident_to_string v;
        IdentParsing.TC.ident_to_string w;
        IdentParsing.TC.ident_to_string x;
        IdentParsing.TC.ident_to_string y;
        IdentParsing.TC.ident_to_string z]
        val (fun vwxyz => let '\< v, w, x, y, z \> := vwxyz in body))
    (at level 200, v name, w name, x name, y name, z name, body at level 200,
     only parsing).

Section Gallina.
  Local Open Scope F_scope.
  Context {m : positive} (a24 : F m) (count : nat).
  Definition montladder_gallina (k : Z) (u : F m)
    : F m :=
    let/n X1 := stack 1 in
    let/n Z1 := stack 0 in
    let/n X2 := stack u in
    let/n Z2 := stack 1 in
    let/n swap := false in
    let/n (X1, Z1, X2, Z2, swap) :=
       downto
         \<X1, Z1, X2, Z2, swap\> (* initial state *)
         count
         (fun state i =>
            let '\<X1, Z1, X2, Z2, swap\> := state in
            let/n s_i := Z.testbit k (Z.of_nat i) in
            let/n swap := xorb swap s_i in
            let/n (X1, X2) := cswap swap X1 X2 in
            let/n (Z1, Z2) := cswap swap Z1 Z2 in
            let/n (X1, Z1, X2, Z2) := ladderstep_gallina m a24 u X1 Z1 X2 Z2 in
            let/n swap := s_i in
            \<X1, Z1, X2, Z2, swap\>
         ) in
    let/n (X1, X2) := cswap swap X1 X2 in
    let/n (Z1, Z2) := cswap swap Z1 Z2 in
    let/n OUT := (F.inv Z1) in
    let/n OUT := (X1 * OUT) in
    OUT.

  (*TODO: which of ladderstep_gallina and M.xzladderstep should we change? either?*)
  Definition reorder_pairs {A B C D} (p : \<<A , B , C , D\>>) : (A*B)*(C*D) :=
    (P2.car p, P2.car (P2.cdr p),((P2.car (P2.cdr (P2.cdr p))),(P2.cdr (P2.cdr (P2.cdr p))))).

  (* TODO: should M.montladder change to accomodate this? *)
  Definition to_pair {A B} p : A*B := (P2.car p, P2.cdr p).

  Lemma invert_reorder_pairs {A B C D} (p : \<<A , B , C , D\>>) w x y z
    : reorder_pairs p = (w,x, (y,z)) <-> p = \<w,x,y,z\>.
  Proof.
    destruct p as [? [? [? ?]]].
    cbv.
    intuition congruence.
  Qed.

  Lemma ladderstep_gallina_equiv X1 P1 P2 :
    reorder_pairs (ladderstep_gallina _ a24 X1 (fst P1) (snd P1) (fst P2) (snd P2)) =
    @M.xzladderstep _ F.add F.sub F.mul a24 X1 P1 P2.
  Proof.
    intros. cbv [ladderstep_gallina M.xzladderstep].
    destruct P1 as [x1 z1]. destruct P2 as [x2 z2].
    cbv [Rewriter.Util.LetIn.Let_In nlet]. cbn [fst snd].
    rewrite !F.pow_2_r; trivial.
  Qed.

  Lemma montladder_gallina_equiv n point :
    montladder_gallina n point =
    @M.montladder _ F.zero F.one F.add F.sub F.mul F.inv a24 (Z.of_nat count) (Z.testbit n) point.
  Proof.
    cbv [montladder_gallina M.montladder Rewriter.Util.LetIn.Let_In stack].
    do 5 (unfold nlet at 1); cbn [fst snd P2.car P2.cdr].
    rewrite Loops.downto_while.
    match goal with
    | |- ?lhs = ?rhs =>
      match lhs with context [Loops.while ?ltest ?lbody ?fuel ?linit] =>
      match rhs with context [Loops.while ?rtest ?rbody ?fuel ?rinit] =>
      rewrite (Loops.while.preservation ltest lbody rtest rbody
        (fun s1 s2 => s1 = let '(x2, z2, x3, z3, swap, i) := s2 in
        (\<x2, z2, x3, z3, swap\>, i))) with (init2:=rinit)
    end end end.
    { rewrite !Nat2Z.id. destruct (Loops.while _ _ _ _) eqn:? at 1 2.
      destruct_products. case b; reflexivity. }
    { intros. destruct_products. congruence. }
    { intros. destruct_products. Prod.inversion_prod. LtbToLt.Z.ltb_to_lt. subst.
      rewrite !Z2Nat.id by lia.
      cbv [nlet M.cswap].
      repeat match goal with
             | H : (_,_) = (_,_) |- _ => inversion H; subst; clear H
             | _ => progress BreakMatch.break_match
             | _ => progress BreakMatch.break_match_hyps
             end;
      rewrite <- ladderstep_gallina_equiv, invert_reorder_pairs in Heqp0;
      cbn [fst snd to_pair] in Heqp0; inversion_clear Heqp0; trivial. }
    { reflexivity. }
  Qed.

  Context
    (field : @Hierarchy.field (F m) eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div)
    (Hm' : (28 <= m)%positive)
     a (a24_correct : (1 + 1 + 1 + 1) * a24 = a - (1 + 1))
    (a2m4_nonsq : ~(exists r, F.mul r r = F.sub (F.mul a a) (F.of_Z _ 4)))
    (b : F m) (b_nonzero : b <> 0).

  Local Instance char_ge_28 : @Ring.char_ge (F m) eq 0 1 F.opp F.add F.sub F.mul 28.
  Proof. eapply Algebra.Hierarchy.char_ge_weaken; try eapply F.char_gt; trivial. Qed.

  Context {char_ge_3 : @Ring.char_ge (F m) eq 0 1 F.opp F.add F.sub F.mul 3}. (* appears in statement *)
  Import MontgomeryCurve Montgomery.Affine.
  Local Notation X0 := (@M.X0 _ eq F.zero F.add F.mul a b).
  Local Notation add := (M.add(field:=field)(char_ge_3:=char_ge_3)(a:=a)(b_nonzero:=b_nonzero)).
  Local Notation opp := (M.opp(field:=field)(a:=a)(b_nonzero:=b_nonzero)).
  Local Notation scalarmult := (@ScalarMult.scalarmult_ref _ add M.zero opp).
  Add Ring Private_ring : (F.ring_theory m) (morphism (F.ring_morph m), constants [F.is_constant]).

  Lemma montladder_gallina_equiv_affine n P :
    montladder_gallina n (X0 P) = X0 (scalarmult (n mod 2^Z.of_nat count) P).
  Proof.
    unshelve erewrite montladder_gallina_equiv, M.montladder_correct;
      try lia; try exact _; trivial using F.inv_0.
   { intros r Hr. apply a2m4_nonsq; exists r. rewrite Hr. f_equal. ring. }
  Qed.
End Gallina.

Section __.

  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}.
  Context {field_representaton : FieldRepresentation}.
  Context {field_representation_ok : FieldRepresentation_ok}.
  Hint Resolve relax_bounds : compiler.

  Section MontLadder.
    Context scalarbits (scalarbits_small : word.wrap (Z.of_nat scalarbits) = Z.of_nat scalarbits).
    Local Notation "bs $@ a" := (array ptsto (word.of_Z 1) a bs) (at level 20).
    Let m : positive := M_pos.
    Context
      (field : @Hierarchy.field (F m) eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div) (Hm' : (28 <= m)%positive)
      (a : F m) (b : F m) (b_nonzero : b <> F.zero).

    Context {char_ge_3 : @Ring.char_ge (F m) eq F.zero F.one F.opp F.add F.sub F.mul 3}. (* appears in statement *)
    Import MontgomeryCurve Montgomery.Affine.
    Local Notation X0 := (@M.X0 _ eq F.zero F.add F.mul a b).
    Local Notation add := (M.add(field:=field)(char_ge_3:=char_ge_3)(a:=a)(b_nonzero:=b_nonzero)).
    Local Notation opp := (M.opp(field:=field)(a:=a)(b_nonzero:=b_nonzero)).
    Local Notation scalarmult := (@ScalarMult.scalarmult_ref _ add M.zero opp).

    Import MontgomeryCurve.
    Instance spec_of_montladder : spec_of "montladder" :=
      fnspec! "montladder"
            (pOUT pK pU : word)
            / Kbytes (K : Z) (U : F M_pos) (* inputs *)
            out_bound OUT
            R,
      { requires tr mem :=
          mem =* FElem out_bound pOUT OUT * Kbytes$@pK * FElem (Some tight_bounds) pU U *  R /\
          LittleEndianList.le_combine Kbytes = K /\
          Z.of_nat scalarbits <= 8*Z.of_nat (length Kbytes);
        ensures tr' mem' :=
          tr' = tr /\ (
          let OUT := montladder_gallina a24 scalarbits K U in
              (FElem (Some tight_bounds) pOUT OUT * Kbytes$@pK
               * FElem (Some tight_bounds) pU U
               * R)%sep mem') }.

    (* Adding word.unsigned_of_Z_1 and word.unsigned_of_Z_0 as hints to
       compiler doesn't work, presumably because of the typeclass
       preconditions. This is a hacky workaround. *)
    (* TODO: figure out a cleaner way to do this *)
    Lemma unsigned_of_Z_1 : word.unsigned (@word.of_Z _ word 1) = 1.
    Proof using word_ok. exact word.unsigned_of_Z_1. Qed.
    Lemma unsigned_of_Z_0 : word.unsigned (@word.of_Z _ word 0) = 0.
    Proof using word_ok. exact word.unsigned_of_Z_0. Qed.
    Hint Resolve unsigned_of_Z_0 unsigned_of_Z_1 : compiler.
    Import bedrock2.NotationsCustomEntry.
 Lemma compile_sctestbit : forall {tr mem locals functions} bs x i,
   let v := Z.testbit x (Z.of_nat i) in
   forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
     R x_ptr x_var wi i_var out_var,

     (bs$@x_ptr * R)%sep mem ->
     map.get locals x_var = Some x_ptr ->

     LittleEndianList.le_combine bs = x ->

     wi = word.of_Z (Z.of_nat i) ->
     0 <= Z.of_nat i < 2 ^ width ->
     Z.of_nat i < 8 * Z.of_nat (length bs) ->
     map.get locals i_var = Some wi ->

     (let v := v in
        (<{ Trace := tr;
            Memory := mem;
            Locals := map.put locals out_var (word.b2w v);
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>)) ->
     <{ Trace := tr;
        Memory := mem;
        Locals := locals;
        Functions := functions }>
     bedrock_cmd:($out_var = (load1($x_var+$i_var>>coq:(3))>>($i_var&coq:(7)))&coq:(1); coq:(k_impl))
     <{ pred (nlet_eq [out_var] v k) }>.
 Proof using mem_ok scalarbits word_ok.
   clear dependent m.
   repeat straightline.
   repeat (eexists; split; repeat straightline'; eauto); cbn [Semantics.interp_binop].

   eapply load_one_of_sep.
   (*
     (* Note: could instead add the following two lines to seprewrite0_in but kinda wanna avoid reduction/conversion there...  *)
    let t := type of Hrw in
    let t := eval cbv zeta in t in
    *)
   unshelve (
   let Hrw := open_constr:(@bytearray_index_inbounds _ _ _ _ _ _ _ _ _ : Lift1Prop.iff1 _ _) in
   seprewrite0_in Hrw H; ecancel_assumption).
   all : cycle 1.

   all: try eapply word.unsigned_inj.
   all: unfold word.b2w.
   all: subst_lets_in_goal; subst.
   all : repeat rewrite
     ?word.unsigned_of_Z_b2z, ?word.unsigned_of_Z, ?word.unsigned_and_nowrap, ?word.unsigned_sru_nowrap.
   all : cbv [word.wrap]; rewrite ?Z.mod_small.
   all : change 7 with (Z.ones 3); change 1 with (Z.ones 1); rewrite ?Z.land_ones.
   all : rewrite ?Z.shiftr_div_pow2; change (2^3) with 8; change (2^1) with 2.
   all : rewrite <-?hd_skipn_nth_default.
   1: rewrite <-Z.testbit_spec'; f_equal.
   1: setoid_rewrite Z2Nat.inj_div.
   all : try match goal with |- 0 <= byte.unsigned ?x < _ => epose proof byte.unsigned_range x end.
   all : try (destruct Bitwidth.width_cases as [E|E]; rewrite ?E in *; Lia.lia).
   all : try (destruct Bitwidth.width_cases as [E|E]; rewrite ?E in *; cbn in *; Lia.lia).

   (*
      Z.testbit (LittleEndianList.le_combine bs) (Z.of_nat i) =
      Z.testbit (byte.unsigned
        (nth_default (byte.of_Z 0) bs (Z.to_nat (Z.of_nat i) / Z.to_nat 8)))
        (Z.of_nat i mod 8)
   *)
   rewrite <-(LittleEndianList.split_le_combine bs) at 2.
   rewrite LittleEndianList.nth_default_le_split, byte.unsigned_of_Z, Nat2Z.id
     by (eapply Nat.div_lt_upper_bound; Lia.nia).
   cbv [byte.wrap]; rewrite <-Z.land_ones, Z.land_spec, Z.ones_spec_low by Lia.lia.
   rewrite Z.shiftr_spec, Bool.andb_true_r by Lia.lia; f_equal.
   rewrite Nat2Z.inj_div. Lia.lia.
 Qed.

  Hint Extern 8
       (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (Z.testbit _ _) _))) =>
  simple eapply compile_sctestbit; shelve : compiler.


  Existing Instance felem_alloc.


  Lemma cswap_same {A} : forall b (a : A), cswap b a a = \<a,a\>.
  Proof using Type.
    intros b0; destruct b0; reflexivity.
  Qed.

  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

  Lemma scalarbits_bound : Z.of_nat scalarbits < 2 ^ width.
  Proof using scalarbits_small.
    clear dependent m.
    rewrite <- scalarbits_small.
    unfold word.wrap.
    apply Z_mod_lt.
    pose proof word.width_pos.
    pose proof (Z.pow_pos_nonneg 2 width ltac:(lia)).
    lia.
  Qed.

  (* TODO: why doesn't `Existing Instance` work?
  Existing Instance spec_of_sctestbit.*)
  Hint Extern 1 (spec_of "ladderstep") =>
  (simple refine (@spec_of_ladderstep _ _ _ _ _ _ _ _)) : typeclass_instances.


  Hint Extern 1 (spec_of "cswap") =>
  (simple refine (spec_of_cswap)) : typeclass_instances.

  (* TODO: this seems a bit delicate*)
  Ltac compile_cswap :=
    eapply compile_felem_cswap;
    [solve[repeat compile_step] ..
    | repeat compile_step;
      rewrite cswap_same;
      compile_step;
      match goal with
      | [|- (WeakestPrecondition.cmd _ _ _ _ _ (_ (let (_,_) := ?v in _)))] =>
        destruct v
      end].

  Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (cswap _ _ _) _))) =>
  compile_cswap; shelve : compiler.


  Lemma word_unsigned_of_Z_eq z
    : 0 <= z < 2 ^ width -> word.unsigned (word.of_Z z : word) = z.
  Proof using word_ok.
    intros.
    rewrite word.unsigned_of_Z.
    rewrite word.wrap_small; auto.
  Qed.

  Hint Extern 8 (word.unsigned (word.of_Z _) = _) =>
  simple eapply word_unsigned_of_Z_eq; [ ZnWords |] : compiler.

  (*TODO: should this go in core rupicola?*)
  Lemma compile_copy_bool {tr _m l functions} (x: bool) :
    let v := x in
    forall P (pred: P v -> predicate)
           (k: nlet_eq_k P v) k_impl
           x_expr var,

      WeakestPrecondition.dexpr _m l x_expr (word.of_Z (Z.b2z v)) ->

      (let v := v in
       <{ Trace := tr;
          Memory := _m;
          Locals := map.put l var (word.of_Z (Z.b2z v));
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := _m;
         Locals := l;
         Functions := functions }>
      cmd.seq (cmd.set var x_expr) k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof using Type.
    intros.
    repeat straightline.
    eauto.
  Qed.
  Hint Extern 10 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ ?v _))) =>
  is_var v; simple eapply compile_copy_bool; shelve : compiler.


  Hint Resolve unsigned_of_Z_0 : compiler_side_conditions.
  Hint Resolve unsigned_of_Z_1 : compiler_side_conditions.
  Hint Unfold F.one F.zero : compiler_cleanup.

  Hint Extern 10 (_ < _) => lia : compiler_side_conditions.

  (* TODO: update the original definition in bedrock2 *)
  Ltac find_implication xs y ::=
    multimatch xs with
    | cons ?x _ =>
        (* Only proceed if we can find an implication between x and y *)
        let _ := constr:(ltac:(solve [auto 1 with nocore ecancel_impl])
                          : Lift1Prop.impl1 x y) in
        constr:(O)
    | cons _ ?xs => let i := find_implication xs y in constr:(S i)
    end.

  Context { F_M_pos : M_pos = (2^255-19)%positive }.
  Context (a24_correct : F.mul (1 + 1 + 1 + 1) Field.a24 = F.sub a (1 + 1))
          (Ha : ~(exists r, F.mul r r = F.sub (F.mul a a) (F.of_Z _ 4))).

  Hint Extern 1 (spec_of "fe25519_inv") => (simple refine (spec_of_exp_large)) : typeclass_instances.
  Hint Extern 1 (spec_of "felem_cswap") => (simple refine (spec_of_cswap)) : typeclass_instances.

  Hint Extern 1 => simple eapply compile_felem_cswap; shelve : compiler.
  Local Hint Extern 10 => lia : compiler_side_conditions.
    Derive montladder_body SuchThat
           (defn! "montladder" ("OUT", "K", "U")
                { montladder_body },
             implements (montladder_gallina(m:=M_pos))
                        using ["felem_cswap"; felem_copy; from_word;
                               "ladderstep"; "fe25519_inv"; mul])
           As montladder_correct.
    Proof.
      pose proof scalarbits_bound.
      compile.
    Qed.

  End MontLadder.
End __.

Global Hint Extern 1 (spec_of "montladder") => (simple refine (@spec_of_montladder _ _ _ _ _ _ _ _ _ _)) : typeclass_instances.

Import bedrock2.Syntax.Coercions.
Local Unset Printing Coercions.
(* Set the printing width so that arguments are printed on 1 line.
   Otherwise the build breaks.
 *)
Local Set Printing Width 160.
(*
Import NotationsCustomEntry.
*)
Redirect "Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.montladder_body" Eval cbv [montladder_body cmd_downto_fresh cmd_downto gs fold_right] in ("montladder", montladder_body 253).
