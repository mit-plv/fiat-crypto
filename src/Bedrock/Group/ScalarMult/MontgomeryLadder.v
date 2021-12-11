Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Alloc.
Require Import Rupicola.Lib.SepLocals.
Require Import Rupicola.Lib.ControlFlow.CondSwap.
Require Import Rupicola.Lib.ControlFlow.DownTo.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Util.NumTheoryUtil.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.

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
    (at level 200, w ident, x  ident, y ident, z ident, body at level 200,
     only parsing).


Notation "'let/n' ( v , w , x , y , z ) := val 'in' body" :=
  (nlet [IdentParsing.TC.ident_to_string v;
        IdentParsing.TC.ident_to_string w;
        IdentParsing.TC.ident_to_string x;
        IdentParsing.TC.ident_to_string y;
        IdentParsing.TC.ident_to_string z]
        val (fun vwxyz => let '\< v, w, x, y, z \> := vwxyz in body))
    (at level 200, v ident, w ident, x ident, y ident, z ident, body at level 200,
     only parsing).

Section Gallina.
  Local Open Scope F_scope.
  Definition montladder_gallina (m : positive) (a24 : F m) (count : nat) (k : Z) (u : F m)
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
End Gallina.

Section __.

  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}.
  Context {field_representaton : FieldRepresentation}.
  Context {field_representation_ok : FieldRepresentation_ok}.
  Hint Resolve @relax_bounds : compiler.

  Section MontLadder.
    Context scalarbits (scalarbits_small : word.wrap (Z.of_nat scalarbits) = Z.of_nat scalarbits).
    Local Notation "bs $@ a" := (array ptsto (word.of_Z 1) a bs) (at level 20).

    Instance spec_of_montladder : spec_of "montladder" :=
      fnspec! "montladder"
            (pOUT pK pU : word)
            / Kbytes (K : Z) (U : F M_pos) (* inputs *)
            out_bound OUT
            R,
      { requires tr mem :=
          LittleEndianList.le_combine Kbytes = K /\
          Z.of_nat scalarbits <= 8*Z.of_nat (length Kbytes) /\
          (FElem out_bound pOUT OUT * Kbytes$@pK * FElem (Some tight_bounds) pU U
           *  R)%sep mem;
        ensures tr' mem' :=
          tr' = tr
          /\ (let OUT := montladder_gallina M_pos a24 scalarbits K U in
              (FElem (Some tight_bounds) pOUT OUT * Kbytes$@pK
               * FElem (Some tight_bounds) pU U
               * R)%sep mem') }.

    (* Adding word.unsigned_of_Z_1 and word.unsigned_of_Z_0 as hints to
       compiler doesn't work, presumably because of the typeclass
       preconditions. This is a hacky workaround. *)
    (* TODO: figure out a cleaner way to do this *)
    Lemma unsigned_of_Z_1 : word.unsigned (@word.of_Z _ word 1) = 1.
    Proof. exact word.unsigned_of_Z_1. Qed.
    Lemma unsigned_of_Z_0 : word.unsigned (@word.of_Z _ word 0) = 0.
    Proof. exact word.unsigned_of_Z_0. Qed.
    Hint Resolve unsigned_of_Z_0 unsigned_of_Z_1 : compiler.
    Import bedrock2.NotationsCustomEntry.
 Lemma compile_sctestbit : forall {tr mem locals functions} bs x i,
   let v := Z.testbit x (Z.of_nat i) in
   forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
     R x_ptr x_var wi i_var out_var,

     (bs$@x_ptr * R)%sep mem ->
     map.get locals x_var = Some x_ptr ->

     LittleEndianList.le_combine bs = x ->

     wi = word.of_Z (Z.of_nat i) ->
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
     bedrock_cmd:(out_var = (load1(x_var+i_var>>coq:(3))>>(i_var&coq:(7)))&coq:(1); coq:(k_impl))
     <{ pred (nlet_eq [out_var] v k) }>.
 Proof.
   repeat straightline.
   repeat (eexists; split; repeat straightline'; eauto); cbn; repeat straightline.

   eapply load_one_of_sep.
   (*
     (* Note: could instead add the following two lines to seprewrite0_in but kinda wanna avoid reduction/conversion there...  *)
    let t := type of Hrw in
    let t := eval cbv zeta in t in
    *)
   let Hrw := open_constr:(@bytearray_index_inbounds _ _ _ _ _ _ _ _ _ : Lift1Prop.iff1 _ _) in
   seprewrite0_in Hrw H; ecancel_assumption.

   unfold word.b2w.
   subst_lets_in_goal; subst.
   eapply word.unsigned_inj; repeat rewrite
     ?word.unsigned_of_Z, ?word.unsigned_and_nowrap, ?word.unsigned_sru_nowrap.
   all : cbv [word.wrap]; rewrite ?Z.mod_small.
   all : change 7 with (Z.ones 3); change 1 with (Z.ones 1); rewrite ?Z.land_ones.
   all : rewrite ?Z.shiftr_div_pow2; change (2^3) with 8; change (2^1) with 2.
   all : rewrite <-?hd_skipn_nth_default.
   rewrite <-Z.testbit_spec'; f_equal.
   replace (Z.to_nat (Z.of_nat i / 8)) with (i/8)%nat.
   all : try (destruct Bitwidth.width_cases; cbn; Lia.lia).
   (* word<->Z side conditions and nth_default le_combine
      Z.testbit (LittleEndianList.le_combine bs) (Z.of_nat i) =
      Z.testbit (byte.unsigned (nth_default (byte.of_Z 0) bs (i / 8))) (Z.of_nat i mod 8)
    *)
 Admitted.

  Hint Extern 8
       (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (Z.testbit _ _) _))) =>
  simple eapply compile_sctestbit; shelve : compiler.


  (*TODO: determine the best place for felem_cswap. Should it get its own file?*)
  Definition felem_cswap := "felem_cswap".
  (*TODO: move to the right place;
  TODO: instantiate
   *)  
  Instance spec_of_felem_cswap : spec_of felem_cswap :=
    fnspec! felem_cswap mask ptr1 ptr2 / b1 b2 b c1 c2 R,
    { requires tr mem :=
        mask = word.of_Z (Z.b2z b) /\
        (FElem b1 ptr1 c1 * FElem b2 ptr2 c2 * R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        let (c1,c2) := cswap b c1 c2 in
        let (b1,b2) := cswap b b1 b2 in
        (FElem b1 ptr1 c1 * FElem b2 ptr2 c2 * R)%sep mem' }.
  
  Lemma compile_felem_cswap {tr m l functions} swap (lhs rhs : F M_pos) :
    let v := cswap swap lhs rhs in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
           R mask_var lhs_ptr lhs_var b_lhs rhs_ptr rhs_var b_rhs,

      spec_of_felem_cswap functions ->

      map.get l mask_var = Some (word.of_Z (Z.b2z swap)) ->
      
      map.get l lhs_var = Some lhs_ptr ->
      map.get l rhs_var = Some rhs_ptr ->

      (FElem b_lhs lhs_ptr lhs * FElem b_rhs rhs_ptr rhs * R)%sep m ->

      (let v := v in
       let (b1,b2) := cswap swap b_lhs b_rhs in
       forall m',
         (FElem b1 lhs_ptr (fst v) * FElem b2 rhs_ptr (snd v) * R)%sep m' ->
         (<{ Trace := tr;
             Memory := m';
             Locals := l;
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr;
         Memory := m;
         Locals := l;
         Functions := functions }>
      cmd.seq
        (cmd.call [] felem_cswap [expr.var mask_var; expr.var lhs_var; expr.var rhs_var])
        k_impl
      <{ pred (nlet_eq [lhs_var; rhs_var] v k) }>.
  Proof.     
    Local Ltac prove_field_compilation locals :=
      repeat straightline' locals;
      handle_call;
      lazymatch goal with
      | |- sep _ _ _ => ecancel_assumption
      | _ => idtac
      end; eauto;
      sepsimpl; repeat straightline' locals; subst; eauto.
    prove_field_compilation l.
    destruct swap; eapply H4; unfold v; unfold cswap; simpl; eauto.
  Qed.
  Hint Resolve compile_felem_cswap : compiler.

  Existing Instance felem_alloc.


  Lemma cswap_same {A} b (a : A): cswap b a a = (a,a).
  Proof.
    destruct b; reflexivity.
  Qed.
  
  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

  Lemma scalarbits_bound : Z.of_nat scalarbits < 2 ^ width.
  Proof.
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
  Proof.
    intros.
    rewrite word.unsigned_of_Z.
    rewrite word.wrap_small; auto.
  Qed.

  Hint Extern 8 (word.unsigned (word.of_Z _) = _) =>
  simple eapply word_unsigned_of_Z_eq; [ ZnWords |] : compiler.

  (*TODO: should this go in core rupicola?*)
  Lemma compile_copy_bool {tr m l functions} (x: bool) :
    let v := x in
    forall {P} {pred: P v -> predicate}
           {k: nlet_eq_k P v} {k_impl}
           x_expr var,

      WeakestPrecondition.dexpr m l x_expr (word.of_Z (Z.b2z v)) ->

      (let v := v in
       <{ Trace := tr;
          Memory := m;
          Locals := map.put l var (word.of_Z (Z.b2z v));
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := m;
         Locals := l;
         Functions := functions }>
      cmd.seq (cmd.set var x_expr) k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof.
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
  
  Derive montladder_body SuchThat
         (defn! "montladder" ("OUT", "K", "U")
              { montladder_body },
           implements montladder_gallina
                      using [felem_cswap; felem_copy; felem_small_literal;
                             "ladderstep"; inv; mul])
         As montladder_correct.
  Proof.
    pose proof scalarbits_bound.
    compile_setup;
    repeat repeat compile_step.
    all : try compile_done.
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
Redirect "Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.montladder_body" Eval cbv [montladder_body cmd_downto_fresh cmd_downto gs fold_right] in montladder_body 253.
