From Coq Require Import Zmod.
Require Import coqutil.Word.Bitwidth.
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
  Local Open Scope Zmod_scope.
  Context {m : Z} (a24 : Zmod m) (count : nat).
  Definition montladder_gallina (k : Z) (u : Zmod m)
    : Zmod m :=
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
    let/n OUT := (Zmod.inv Z1) in
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
    @M.xzladderstep _ Zmod.add Zmod.sub Zmod.mul a24 X1 P1 P2.
  Proof.
    intros. cbv [ladderstep_gallina M.xzladderstep].
    destruct P1 as [x1 z1]. destruct P2 as [x2 z2].
    cbv [Rewriter.Util.LetIn.Let_In nlet]. cbn [fst snd].
    rewrite !Zmod.pow_2_r; trivial.
  Qed.

  Lemma montladder_gallina_equiv n point :
    montladder_gallina n point =
    @M.montladder _ Zmod.zero Zmod.one Zmod.add Zmod.sub Zmod.mul Zmod.inv a24 (Z.of_nat count) (Z.testbit n) point.
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
    (field : @Hierarchy.field (Zmod m) eq Zmod.zero Zmod.one Zmod.opp Zmod.add Zmod.sub Zmod.mul Zmod.inv Zmod.mdiv)
    (Hm' : (28 <= m)%Z)
     a (a24_correct : (1 + 1 + 1 + 1) * a24 = a - (1 + 1))
    (a2m4_nonsq : ~(exists r, Zmod.mul r r = Zmod.sub (Zmod.mul a a) (Zmod.of_Z _ 4)))
    (b : Zmod m) (b_nonzero : b <> 0).

  Local Instance char_ge_28 : @Ring.char_ge (Zmod m) eq 0 1 Zmod.opp Zmod.add Zmod.sub Zmod.mul 28.
  Proof.
    eapply Algebra.Hierarchy.char_ge_weaken; [eapply Zmod.char_gt|].
    rewrite <-(Z2Pos.id m) in Hm' by lia; exact Hm'.
  Qed.

  Context {char_ge_3 : @Ring.char_ge (Zmod m) eq 0 1 Zmod.opp Zmod.add Zmod.sub Zmod.mul 3}. (* appears in statement *)
  Import MontgomeryCurve Montgomery.Affine.
  Local Notation X0 := (@M.X0 _ eq Zmod.zero Zmod.add Zmod.mul a b).
  Local Notation add := (M.add(field:=field)(char_ge_3:=char_ge_3)(a:=a)(b_nonzero:=b_nonzero)).
  Local Notation opp := (M.opp(field:=field)(a:=a)(b_nonzero:=b_nonzero)).
  Local Notation scalarmult := (@ScalarMult.scalarmult_ref _ add M.zero opp).
  Add Ring Private_ring : (Zmod.ring_theory m) (morphism (Zmod.ring_morph m), constants [Zmod.is_constant]).

  Lemma montladder_gallina_equiv_affine n P :
    montladder_gallina n (X0 P) = X0 (scalarmult (n mod 2^Z.of_nat count) P).
  Proof.
    unshelve erewrite montladder_gallina_equiv, M.montladder_correct;
      try lia; try exact _; trivial using Zmod.inv_0.
   { intros r Hr. apply a2m4_nonsq; exists r. rewrite Hr. f_equal. ring. }
  Qed.
End Gallina.

Section __.

  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}.
  Context {field_representaton : FieldRepresentation}.
  Context {field_representation_ok : FieldRepresentation_ok}.
  Hint Resolve relax_bounds : compiler.

  Section MontLadder.
    Context scalarbits (scalarbits_small : (Z.of_nat scalarbits) mod 2 ^ width = Z.of_nat scalarbits).
    Local Notation "bs $@ a" := (array ptsto (bits.of_Z _ 1) a bs) (at level 20).
    Let m : Z := M.
    Context
      (field : @Hierarchy.field (Zmod m) eq Zmod.zero Zmod.one Zmod.opp Zmod.add Zmod.sub Zmod.mul Zmod.inv Zmod.mdiv) (Hm' : (28 <= m)%Z)
      (a : Zmod m) (b : Zmod m) (b_nonzero : b <> Zmod.zero).

    Context {char_ge_3 : @Ring.char_ge (Zmod m) eq Zmod.zero Zmod.one Zmod.opp Zmod.add Zmod.sub Zmod.mul 3}. (* appears in statement *)
    Import MontgomeryCurve Montgomery.Affine.
    Local Notation X0 := (@M.X0 _ eq Zmod.zero Zmod.add Zmod.mul a b).
    Local Notation add := (M.add(field:=field)(char_ge_3:=char_ge_3)(a:=a)(b_nonzero:=b_nonzero)).
    Local Notation opp := (M.opp(field:=field)(a:=a)(b_nonzero:=b_nonzero)).
    Local Notation scalarmult := (@ScalarMult.scalarmult_ref _ add M.zero opp).

    Import MontgomeryCurve.
    Instance spec_of_montladder : spec_of "montladder" :=
      fnspec! "montladder"
            (pOUT pK pU : word)
            / Kbytes (K : Z) (U : Zmod M) (* inputs *)
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

    (* Adding bits.unsigned_1 and Zmod.unsigned_0 as hints to
       compiler doesn't work, presumably because of the typeclass
       preconditions. This is a hacky workaround. *)
    (* TODO: figure out a cleaner way to do this *)
    Lemma unsigned_of_Z_1 : Zmod.unsigned (bits.of_Z width 1) = 1.
    Proof using BW. apply bits.unsigned_1. clear -BW. pose proof width_pos. lia. Qed.
    Lemma unsigned_of_Z_0 : Zmod.unsigned (bits.of_Z width 0) = 0.
    Proof using. apply Zmod.unsigned_0. Qed.
    Hint Resolve unsigned_of_Z_0 unsigned_of_Z_1 : compiler.
    Import bedrock2.NotationsCustomEntry.
 Lemma compile_sctestbit : forall {tr mem locals functions} bs x i,
   let v := Z.testbit x (Z.of_nat i) in
   forall P (pred: P v -> predicate) (k: nlet_eq_k P v) k_impl
     R x_ptr x_var wi i_var out_var,

     (bs$@x_ptr * R)%sep mem ->
     map.get locals x_var = Some x_ptr ->

     LittleEndianList.le_combine bs = x ->

     wi = bits.of_Z _ (Z.of_nat i) ->
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
 Proof using mem_ok scalarbits.
  clear scalarbits_small.
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
   let Hrw := open_constr:(@bytearray_index_inbounds _ _ _ _ _ _ _ _ : Lift1Prop.iff1 _ _) in
   seprewrite0_in Hrw H; ecancel_assumption).
   all : cycle 1.

   all: try eapply Zmod.unsigned_inj.
   all: unfold word.b2w.
   all: subst_lets_in_goal; subst.
   all : repeat rewrite
     ?word.unsigned_b2w, ?bits.unsigned_of_Z, ?bits.unsigned_and, ?Zmod.unsigned_sru.
   all : rewrite ?Z.mod_small.
   all : change 7 with (Z.ones 3); change 1 with (Z.ones 1); rewrite ?Z.land_ones.
   all : rewrite ?Z.shiftr_div_pow2; change (2^3) with 8; change (2^1) with 2.
   all : rewrite <-?hd_skipn_nth_default.
   1: rewrite <-Z.testbit_spec'; f_equal.
   1: setoid_rewrite Z2Nat.inj_div.
   all : try match goal with |- 0 <= byte.unsigned ?x < _ => epose proof byte.unsigned_range x end.
   all : try (destruct Bitwidth.width_cases as [E|E]; rewrite ?E in *; Lia.lia).
   all : try (destruct Bitwidth.width_cases as [E|E]; rewrite ?E in *; cbn in *; Lia.lia).
   all : try (rewrite (Z.mod_small (Z.ones 3)) by (destruct Bitwidth.width_cases as [E|E]; rewrite E; cbn; Lia.lia);
              rewrite Z.land_ones by Lia.lia;
              match goal with |- 0 <= ?a mod 2 ^ 3 < _ => pose proof Z.mod_pos_bound a (2 ^ 3) ltac:(Lia.lia) end;
              destruct Bitwidth.width_cases as [E|E]; rewrite E; cbn; Lia.lia).
   all : try (destruct Bitwidth.width_cases as [E|E]; rewrite ?E in *; case Z.testbit; cbn; Lia.lia).

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
  Proof using BW scalarbits_small.
    clear dependent m.
    rewrite <- scalarbits_small.

    apply Z_mod_lt.
    pose proof width_pos.
    pose proof (Z.pow_pos_nonneg 2 width ltac:(lia)).
    lia.
  Qed.

  (* TODO: why doesn't `Existing Instance` work?
  Existing Instance spec_of_sctestbit.*)
  Hint Extern 1 (spec_of "ladderstep") =>
  (simple refine (@spec_of_ladderstep _ _ _ _ _ _ _)) : typeclass_instances.


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
    : 0 <= z < 2 ^ width -> Zmod.unsigned (bits.of_Z width z) = z.
  Proof using.
    intros.
    rewrite bits.unsigned_of_Z.
    rewrite Z.mod_small; auto.
  Qed.

  Hint Extern 8 (Zmod.unsigned (bits.of_Z _ _) = _) =>
  simple eapply word_unsigned_of_Z_eq; [ ZnWords |] : compiler.

  (*TODO: should this go in core rupicola?*)
  Lemma compile_copy_bool {tr _m l functions} (x: bool) :
    let v := x in
    forall P (pred: P v -> predicate)
           (k: nlet_eq_k P v) k_impl
           x_expr var,

      WeakestPrecondition.dexpr _m l x_expr (bits.of_Z _ (Z.b2z v)) ->

      (let v := v in
       <{ Trace := tr;
          Memory := _m;
          Locals := map.put l var (bits.of_Z _ (Z.b2z v));
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
  Hint Unfold Zmod.one Zmod.zero : compiler_cleanup.

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

  Context { F_M : M = 2^255-19 }.
  Context (a24_correct : Zmod.mul (1 + 1 + 1 + 1) Field.a24 = Zmod.sub a (1 + 1))
          (Ha : ~(exists r, Zmod.mul r r = Zmod.sub (Zmod.mul a a) (Zmod.of_Z _ 4))).

  Hint Extern 1 (spec_of "fe25519_inv") => (simple refine (spec_of_exp_large)) : typeclass_instances.
  Hint Extern 1 (spec_of "felem_cswap") => (simple refine (spec_of_cswap)) : typeclass_instances.

  Hint Extern 1 => simple eapply compile_felem_cswap; shelve : compiler.
  Local Hint Extern 10 => lia : compiler_side_conditions.
    Derive montladder_body SuchThat
           (defn! "montladder" ("OUT", "K", "U")
                { montladder_body },
             implements (montladder_gallina(m:=M))
                        using ["felem_cswap"; felem_copy; from_word;
                               "ladderstep"; "fe25519_inv"; mul])
           As montladder_correct.
    Proof.
      pose proof scalarbits_bound.
      compile.
    Qed.

  End MontLadder.
End __.

Global Hint Extern 1 (spec_of "montladder") => (simple refine (@spec_of_montladder _ _ _ _ _ _ _ _ _)) : typeclass_instances.

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
