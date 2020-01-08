Require Export Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Export Coq.Strings.String.
Require Import Coq.Lists.List.
Require Crypto.ArithmeticCPS.Core.
Require Crypto.ArithmeticCPS.ModOps.
Require Crypto.ArithmeticCPS.Saturated.
Require Crypto.ArithmeticCPS.WordByWordMontgomery.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import Crypto.Util.Strings.ParseArithmetic.
Require Import Crypto.Util.Strings.ParseArithmeticToTaps.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ListUtil.
Require Crypto.PushButtonSynthesis.WordByWordMontgomery.
Require Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.PushButtonSynthesis.WordByWordMontgomeryReificationCache.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinasReificationCache.
Require Import Crypto.BoundsPipeline.
Require Import Rewriter.Language.Language.
Require Import Crypto.Rewriter.All.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.Stringification.C.
Require Import Crypto.Util.ZUtil.ModInv. (* Only needed for WBW Montgomery *)
Require Import Crypto.Util.Strings.Show.

Import ListNotations.
Global Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope option_scope.
Global Open Scope Z_scope.

(* replace this with vm_compute and the next fail with idtac to enable the precomputed versions *)
Declare Reduction precompute := cbv iota.
Ltac check_precomputed_enabled :=
  let v := (eval precompute in (id true)) in
  lazymatch v with
  | true => idtac
  | _ => fail 0 "Precomputed tests are disabled"
  end.

Import
  Language.Compilers
  AbstractInterpretation.Compilers
  Rewriter.All.Compilers.

Local Existing Instance Stringification.C.Compilers.ToString.C.OutputCAPI.
Local Instance : static_opt := true.
Local Instance : use_mul_for_cmovznz_opt := false.
Local Instance : emit_primitives_opt := true.
Local Instance : should_split_mul_opt := false.
Local Instance : widen_bytes_opt := false.
Local Instance : widen_carry_opt := false.

Import API.

Local Set Primitive Projections.
Record Dyn := dyn { Ty : Type ; val :> Ty }.
Arguments dyn {_} _.

Module RT_ExtraAx := Core.RT_Extra Core.RuntimeAxioms.
Module ModOpsAx := ModOps.ModOps Core.RuntimeAxioms.
Module RT_ExtraDef := Core.RT_Extra Core.RuntimeDefinitions.
Module ModOpsDef := ModOps.ModOps Core.RuntimeDefinitions.
Module Import WordByWordMontgomeryAx := ArithmeticCPS.WordByWordMontgomery.WordByWordMontgomery Core.RuntimeAxioms.
Module Import WordByWordMontgomeryDef := ArithmeticCPS.WordByWordMontgomery.WordByWordMontgomery Core.RuntimeDefinitions.

Definition parse_Z (s : string) : option Z
  := z <- ParseArithmetic.parse_Z s;
       match snd z with
       | EmptyString => Some (fst z)
       | _ => None
       end.
Definition parse_N (s : string) : option N
  := match parse_Z s with
     | Some Z0 => Some N0
     | Some (Zpos p) => Some (Npos p)
     | _ => None
     end.
Definition parse_nat (s : string) : option nat
  := option_map N.to_nat (parse_N s).

Module Import UnsaturatedSolinas.
  Class params :=
    { n : nat;
      s : Z;
      c : list (Z * Z);
      idxs : list nat;
      limbwidth := limbwidth n s c;
      machine_wordsize : Z }.

  Global Instance show_params : Show params
    := fun _ p => ("{| n := " ++ show false n ++ "; s := " ++ show false s ++ "; c := " ++ show false c ++ "; idxs := " ++ show false idxs ++ "; machine_wordsize := " ++ show false machine_wordsize ++ "|}")%string.

  Definition of_string (p : string) (bitwidth : Z) : list params
    := match parseZ_arith_to_taps p with
       | Some (sv, cv) => List.map
                            (fun nv => {| n := nv; s := sv; c := cv; machine_wordsize := bitwidth ; idxs := carry_chains nv sv cv |})
                            (firstn 2 (get_possible_limbs sv cv bitwidth))
       | None => nil
       end.

  Definition GallinaAxOf (p : params) : Dyn
    := dyn (fun f g : list Z => ModOpsAx.carry_mulmod (Qnum limbwidth) (Zpos (Qden limbwidth)) s c n idxs (RT_ExtraAx.expand_list 0 f n) (RT_ExtraAx.expand_list 0 g n)).
  Time Definition GallinaAxComputedOf := Eval precompute in GallinaAxOf.
  Definition GallinaDefOf (p : params) : Dyn
    := dyn (fun f g : list Z => ModOpsDef.carry_mulmod (Qnum limbwidth) (Zpos (Qden limbwidth)) s c n idxs (RT_ExtraDef.expand_list 0 f n) (RT_ExtraDef.expand_list 0 g n)).

  Definition PipelineFullOf (p : params) : Pipeline.ErrorT (Expr _)
    := PushButtonSynthesis.UnsaturatedSolinas.carry_mul n s c machine_wordsize.
  Definition PipelineFullToStringsOf (p : params) : string * _
    := PushButtonSynthesis.UnsaturatedSolinas.scarry_mul n s c machine_wordsize "".
  Section pipeline.
    Context (p : params).

    Let E := (reified_carry_mul_gen
                @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n @ GallinaReify.Reify idxs)%Expr.

    Let E2 := let E := PartialEvaluateWithListInfoFromBounds E (Some (List.repeat None n), (Some (List.repeat None n), tt)) in
              let E := PartialEvaluate E in
              E.

  Definition PipelineNBEOf : Expr _
    := E2.

  Definition PipelineFlatNBEOf : GeneralizeVar.Flat.expr _
    := GeneralizeVar.ToFlat PipelineNBEOf.

  Definition PipelineArithOf : Expr _
    := let E := E2 in
       let E := Pipeline.RewriteAndEliminateDeadAndInline (RewriteRules.RewriteArith 0) true (*with_dead_code_elimination*) false (*with_subst01*) E in
       E.

  Definition PipelineFlatArithOf : GeneralizeVar.Flat.expr _
    := GeneralizeVar.ToFlat PipelineArithOf.
  End pipeline.

  Definition ForExtraction {R}
             (extr_descr : string)
             (seq : forall A B, (unit -> A) -> (unit -> B) -> R)
             (time : forall A, string -> (unit -> A) -> R)
             (prime : string) (bitwidth : string) (index : string)
             (error : list string -> R)
    : R
    := let str_bitwidth := bitwidth in
       let str_index := index in
       match parse_Z bitwidth, parse_nat index with
       | Some bitwidth, Some index
         => match List.nth_error (of_string prime bitwidth) index with
            | Some p
              => let make_descr := fun kind => ("Testing UnsaturatedSolinas " ++ prime ++ " (bitwidth = " ++ str_bitwidth ++ " ) (index = " ++ str_index ++ " ) (params = " ++ show false p ++ " ) " ++ kind ++ " with extraction " ++ extr_descr)%string in
                 (seq _ _)
                   (fun _ => time _ (make_descr "PipelineFullToStringsOf") (fun _ => PipelineFullToStringsOf p))
                   (fun _
                    => (seq _ _)
                         (fun _ => time _ (make_descr "PipelineFlatNBEOf") (fun _ => PipelineFlatNBEOf p))
                         (fun _ => time _ (make_descr "PipelineFlatArithOf") (fun _ => PipelineFlatArithOf p)))
            | None
              => error ["No such index"]
            end
       | None, None => error ["Could not parse bitwidth nor index"]
       | None, _ => error ["Could not parse bitwidth"]
       | _, None => error ["Could not parse index"]
       end.

  Tactic Notation "idtac_and_time" constr(prime) constr(bitwidth) constr(index) constr(p) string(descr) tactic3(tac) :=
    idtac "Testing UnsaturatedSolinas" prime "(bitwidth =" bitwidth ") (index =" index ") (params =" p ")" descr ":";
    time (idtac; tac ()).

  Tactic Notation "idtac_and_time2" constr(prime) constr(bitwidth) constr(index) constr(p) string(descr) tactic3(tac) :=
    idtac "Testing UnsaturatedSolinas" prime "(bitwidth =" bitwidth ") (index =" index ") (params =" p ")" descr "(1) :";
    time (idtac; tac ());
    idtac "Testing UnsaturatedSolinas" prime "(bitwidth =" bitwidth ") (index =" index ") (params =" p ")" descr "(2) :";
    time (idtac; tac ()).

  Ltac compute_p prime bitwidth index :=
    let p := (eval vm_compute in (List.nth_error (of_string prime bitwidth) index)) in
    let __ := match p with
              | Some _ => idtac
              | None => idtac "No params" index "for prime" prime
              end in
    p.

  Ltac perfGallinaAxOf' prime bitwidth index p :=
    lazymatch p with
    | Some ?p
      => idtac_and_time prime bitwidth index p "GallinaAxOf with vm_compute" (fun _ => let __ := eval vm_compute in (GallinaAxOf p) in idtac);
         idtac_and_time2 prime bitwidth index p "GallinaAxOf with native_compute" (fun _ => let __ := eval native_compute in (GallinaAxOf p) in idtac);
         idtac_and_time prime bitwidth index p "GallinaAxOf with cbv" (fun _ => let __ := eval cbv in (GallinaAxOf p) in idtac);
         idtac_and_time prime bitwidth index p "GallinaAxOf with lazy" (fun _ => let __ := eval lazy in (GallinaAxOf p) in idtac)
    | None => idtac
    end.
  Ltac perfGallinaAxOf prime bitwidth index :=
    let p := compute_p prime bitwidth index in perfGallinaAxOf' prime bitwidth index p.

  Ltac perfGallinaAxComputedOf' prime bitwidth index p :=
    check_precomputed_enabled;
    lazymatch p with
    | Some ?p
      => idtac_and_time prime bitwidth index p "GallinaAxComputedOf with vm_compute" (fun _ => let __ := eval vm_compute in (GallinaAxComputedOf p) in idtac);
         idtac_and_time prime bitwidth index p "GallinaAxComputedOf with cbv" (fun _ => let __ := eval cbv in (GallinaAxComputedOf p) in idtac);
         idtac_and_time prime bitwidth index p "GallinaAxComputedOf with lazy" (fun _ => let __ := eval lazy in (GallinaAxComputedOf p) in idtac)
    | None => idtac
    end.
  Ltac perfGallinaAxComputedOf prime bitwidth index :=
    check_precomputed_enabled;
    let p := compute_p prime bitwidth index in perfGallinaAxComputedOf' prime bitwidth index p.

  Ltac perfPipelineOf' prime bitwidth index p :=
    lazymatch p with
    | Some ?p
      => idtac_and_time prime bitwidth index p "PipelineFullOf with vm_compute" (fun _ => let __ := eval vm_compute in (PipelineFullOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineFullToStringsOf with vm_compute" (fun _ => let __ := eval vm_compute in (PipelineFullToStringsOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineNBEOf with vm_compute" (fun _ => let __ := eval vm_compute in (PipelineNBEOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineArithOf with vm_compute" (fun _ => let __ := eval vm_compute in (PipelineArithOf p) in idtac);
         idtac_and_time2 prime bitwidth index p "PipelineFullOf with native_compute" (fun _ => let __ := eval native_compute in (PipelineFullOf p) in idtac);
         idtac_and_time2 prime bitwidth index p "PipelineFullToStringsOf with native_compute" (fun _ => let __ := eval native_compute in (PipelineFullToStringsOf p) in idtac);
         idtac_and_time2 prime bitwidth index p "PipelineNBEOf with native_compute" (fun _ => let __ := eval native_compute in (PipelineNBEOf p) in idtac);
         idtac_and_time2 prime bitwidth index p "PipelineArithOf with native_compute" (fun _ => let __ := eval native_compute in (PipelineArithOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineFullOf with cbv" (fun _ => let __ := eval cbv in (PipelineFullOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineFullToStringsOf with cbv" (fun _ => let __ := eval cbv in (PipelineFullToStringsOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineNBEOf with cbv" (fun _ => let __ := eval cbv in (PipelineNBEOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineArithOf with cbv" (fun _ => let __ := eval cbv in (PipelineArithOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineFullOf with lazy" (fun _ => let __ := eval lazy in (PipelineFullOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineFullToStringsOf with lazy" (fun _ => let __ := eval lazy in (PipelineFullToStringsOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineNBEOf with lazy" (fun _ => let __ := eval lazy in (PipelineNBEOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineArithOf with lazy" (fun _ => let __ := eval lazy in (PipelineArithOf p) in idtac)
    | None => idtac
    end.
  Ltac perfPipelineOf prime bitwidth index :=
    let p := compute_p prime bitwidth index in perfPipelineOf' prime bitwidth index p.

  Ltac perfGallinaDefOf' prime bitwidth index p :=
    lazymatch p with
    | Some ?p
      => idtac_and_time prime bitwidth index p "GallinaDefOf with cbv_no_rt" (fun _ => let __ := eval cbv_no_rt in (GallinaDefOf p) in idtac);
         idtac_and_time prime bitwidth index p "GallinaDefOf with lazy_no_rt" (fun _ => let __ := eval lazy_no_rt in (GallinaDefOf p) in idtac)
    | None => idtac
    end.
  Ltac perfGallinaDefOf prime bitwidth index :=
    let p := compute_p prime bitwidth index in perfGallinaDefOf' prime bitwidth index p.

  Ltac perf prime bitwidth index :=
    let p := (eval vm_compute in (List.nth_error (of_string prime bitwidth) index)) in
    lazymatch p with
    | Some ?p
      => idtac_and_time prime bitwidth index p "GallinaAxOf with vm_compute" (fun _ => let __ := eval vm_compute in (GallinaAxOf p) in idtac);
         idtac_and_time prime bitwidth index p "GallinaAxComputedOf with vm_compute" (fun _ => let __ := eval vm_compute in (GallinaAxComputedOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineFullOf with vm_compute" (fun _ => let __ := eval vm_compute in (PipelineFullOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineFullToStringsOf with vm_compute" (fun _ => let __ := eval vm_compute in (PipelineFullToStringsOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineNBEOf with vm_compute" (fun _ => let __ := eval vm_compute in (PipelineNBEOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineArithOf with vm_compute" (fun _ => let __ := eval vm_compute in (PipelineArithOf p) in idtac);
         idtac_and_time2 prime bitwidth index p "GallinaAxOf with native_compute" (fun _ => let __ := eval native_compute in (GallinaAxOf p) in idtac);
         idtac_and_time2 prime bitwidth index p "PipelineFullOf with native_compute" (fun _ => let __ := eval native_compute in (PipelineFullOf p) in idtac);
         idtac_and_time2 prime bitwidth index p "PipelineFullToStringsOf with native_compute" (fun _ => let __ := eval native_compute in (PipelineFullToStringsOf p) in idtac);
         idtac_and_time2 prime bitwidth index p "PipelineNBEOf with native_compute" (fun _ => let __ := eval native_compute in (PipelineNBEOf p) in idtac);
         idtac_and_time2 prime bitwidth index p "PipelineArithOf with native_compute" (fun _ => let __ := eval native_compute in (PipelineArithOf p) in idtac);
         idtac_and_time prime bitwidth index p "GallinaAxOf with cbv" (fun _ => let __ := eval cbv in (GallinaAxOf p) in idtac);
         idtac_and_time prime bitwidth index p "GallinaAxComputedOf with cbv" (fun _ => let __ := eval cbv in (GallinaAxComputedOf p) in idtac);
         idtac_and_time prime bitwidth index p "GallinaAxOf with lazy" (fun _ => let __ := eval lazy in (GallinaAxOf p) in idtac);
         idtac_and_time prime bitwidth index p "GallinaAxComputedOf with lazy" (fun _ => let __ := eval lazy in (GallinaAxComputedOf p) in idtac);
         idtac_and_time prime bitwidth index p "GallinaDefOf with cbv_no_rt" (fun _ => let __ := eval cbv_no_rt in (GallinaDefOf p) in idtac);
         idtac_and_time prime bitwidth index p "GallinaDefOf with lazy_no_rt" (fun _ => let __ := eval lazy_no_rt in (GallinaDefOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineFullOf with cbv" (fun _ => let __ := eval cbv in (PipelineFullOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineFullToStringsOf with cbv" (fun _ => let __ := eval cbv in (PipelineFullToStringsOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineNBEOf with cbv" (fun _ => let __ := eval cbv in (PipelineNBEOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineArithOf with cbv" (fun _ => let __ := eval cbv in (PipelineArithOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineFullOf with lazy" (fun _ => let __ := eval lazy in (PipelineFullOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineFullToStringsOf with lazy" (fun _ => let __ := eval lazy in (PipelineFullToStringsOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineNBEOf with lazy" (fun _ => let __ := eval lazy in (PipelineNBEOf p) in idtac);
         idtac_and_time prime bitwidth index p "PipelineArithOf with lazy" (fun _ => let __ := eval lazy in (PipelineArithOf p) in idtac)
    | None => idtac "No params" index "for prime" prime
    end.

  Global Set Printing Width 1000000.
End UnsaturatedSolinas.

Module Import WordByWordMontgomery.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion QArith_base.inject_Z : Z >-> Q.
  Local Coercion Z.pos : positive >-> Z.
  Class params :=
    { m : Z;
      machine_wordsize : Z;
      s := 2^Z.log2_up m;
      n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize));
      r := 2^machine_wordsize;
      m' := match Z.modinv (-m) r with
            | Some m' => m'
            | None => 0
            end }.

  Global Instance show_params : Show params
    := fun _ p => ("{| m := " ++ show false m ++ "; machine_wordsize := " ++ show false machine_wordsize ++ "|}")%string.

  Definition of_string (p : string) (bitwidth : Z) : option params
    := match parseZ_arith p with
       | Some v => Some {| m := v ; machine_wordsize := bitwidth |}
       | None => None
       end.

  Definition GallinaAxOf (p : params) : Dyn
    := dyn (fun f g : list Z => WordByWordMontgomeryAx.mulmod machine_wordsize n m m' (RT_ExtraAx.expand_list 0 f n) (RT_ExtraAx.expand_list 0 g n)).
  Time Definition GallinaAxComputedOf := Eval precompute in GallinaAxOf.
  Definition GallinaDefOf (p : params) : Dyn
    := dyn (fun f g : list Z => WordByWordMontgomeryDef.mulmod machine_wordsize n m m' (RT_ExtraDef.expand_list 0 f n) (RT_ExtraDef.expand_list 0 g n)).

  Definition PipelineFullOf (p : params) : Pipeline.ErrorT (Expr _)
    := PushButtonSynthesis.WordByWordMontgomery.mul m machine_wordsize.
  Definition PipelineFullToStringsOf (p : params) : string * _
    := PushButtonSynthesis.WordByWordMontgomery.smul m machine_wordsize "".
  Section pipeline.
    Context (p : params).

    Let E := (reified_mul_gen
                @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')%Expr.

    Let E2 := let E := PartialEvaluateWithListInfoFromBounds E (Some (List.repeat None n), (Some (List.repeat None n), tt)) in
              let E := PartialEvaluate E in
              E.

  Definition PipelineNBEOf : Expr _
    := E2.

  Definition PipelineFlatNBEOf : GeneralizeVar.Flat.expr _
    := GeneralizeVar.ToFlat PipelineNBEOf.

  Definition PipelineArithOf : Expr _
    := let E := E2 in
       let E := Pipeline.RewriteAndEliminateDeadAndInline (RewriteRules.RewriteArith 0) true (*with_dead_code_elimination*) false (*with_subst01*) E in
       E.

  Definition PipelineFlatArithOf : GeneralizeVar.Flat.expr _
    := GeneralizeVar.ToFlat PipelineArithOf.
  End pipeline.

  Definition ForExtraction {R}
             (extr_descr : string)
             (seq : forall A B, (unit -> A) -> (unit -> B) -> R)
             (time : forall A, string -> (unit -> A) -> R)
             (prime : string) (bitwidth : string)
             (error : list string -> R)
    : R
    := let str_bitwidth := bitwidth in
       match parse_Z bitwidth with
       | Some bitwidth
         => match of_string prime bitwidth with
            | Some p
              => let make_descr := fun kind => ("Testing WordByWordMontgomery " ++ prime ++ " (bitwidth = " ++ str_bitwidth ++ " ) (params = " ++ show false p ++ " ) " ++ kind ++ " with extraction " ++ extr_descr)%string in
                 (seq _ _)
                   (fun _ => time _ (make_descr "PipelineFullToStringsOf") (fun _ => PipelineFullToStringsOf p))
                   (fun _
                    => (seq _ _)
                         (fun _ => time _ (make_descr "PipelineFlatNBEOf") (fun _ => PipelineFlatNBEOf p))
                         (fun _ => time _ (make_descr "PipelineFlatArithOf") (fun _ => PipelineFlatArithOf p)))
            | None
              => error ["Invalid prime"]
            end
       | None => error ["Could not parse bitwidth"]
       end.

  Tactic Notation "idtac_and_time" constr(prime) constr(bitwidth) constr(p) string(descr) tactic3(tac) :=
    idtac "Testing WordByWordMontgomery" prime "(bitwidth =" bitwidth ") (params =" p ")" descr ":";
    time (idtac; tac ()).

  Tactic Notation "idtac_and_time2" constr(prime) constr(bitwidth) constr(p) string(descr) tactic3(tac) :=
    idtac "Testing WordByWordMontgomery" prime "(bitwidth =" bitwidth ") (params =" p ")" descr "(1) :";
    time (idtac; tac ());
    idtac "Testing WordByWordMontgomery" prime "(bitwidth =" bitwidth ") (params =" p ")" descr "(2) :";
    time (idtac; tac ()).

  Ltac compute_p prime bitwidth :=
    let p := (eval vm_compute in (of_string prime bitwidth)) in
    let __ := match p with
              | Some _ => idtac
              | None => idtac "No params for prime" prime
              end in
    p.

  Ltac perfGallinaAxOf' prime bitwidth p :=
    lazymatch p with
    | Some ?p
      => idtac_and_time prime bitwidth p "GallinaAxOf with vm_compute" (fun _ => let __ := eval vm_compute in (GallinaAxOf p) in idtac);
         idtac_and_time2 prime bitwidth p "GallinaAxOf with native_compute" (fun _ => let __ := eval native_compute in (GallinaAxOf p) in idtac);
         idtac_and_time prime bitwidth p "GallinaAxOf with cbv" (fun _ => let __ := eval cbv in (GallinaAxOf p) in idtac);
         idtac_and_time prime bitwidth p "GallinaAxOf with lazy" (fun _ => let __ := eval lazy in (GallinaAxOf p) in idtac)
    | None => idtac
    end.
  Ltac perfGallinaAxOf prime bitwidth :=
    let p := compute_p prime bitwidth in perfGallinaAxOf' prime bitwidth p.

  Ltac perfGallinaAxComputedOf' prime bitwidth p :=
    check_precomputed_enabled;
    lazymatch p with
    | Some ?p
      => idtac_and_time prime bitwidth p "GallinaAxComputedOf with vm_compute" (fun _ => let __ := eval vm_compute in (GallinaAxComputedOf p) in idtac);
         idtac_and_time prime bitwidth p "GallinaAxComputedOf with cbv" (fun _ => let __ := eval cbv in (GallinaAxComputedOf p) in idtac);
         idtac_and_time prime bitwidth p "GallinaAxComputedOf with lazy" (fun _ => let __ := eval lazy in (GallinaAxComputedOf p) in idtac)
    | None => idtac
    end.
  Ltac perfGallinaAxComputedOf prime bitwidth :=
    check_precomputed_enabled;
    let p := compute_p prime bitwidth in perfGallinaAxComputedOf' prime bitwidth p.

  Ltac perfPipelineOf' prime bitwidth p :=
    lazymatch p with
    | Some ?p
      => idtac_and_time prime bitwidth p "PipelineFullOf with vm_compute" (fun _ => let __ := eval vm_compute in (PipelineFullOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineFullToStringsOf with vm_compute" (fun _ => let __ := eval vm_compute in (PipelineFullToStringsOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineNBEOf with vm_compute" (fun _ => let __ := eval vm_compute in (PipelineNBEOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineArithOf with vm_compute" (fun _ => let __ := eval vm_compute in (PipelineArithOf p) in idtac);
         idtac_and_time2 prime bitwidth p "PipelineFullOf with native_compute" (fun _ => let __ := eval native_compute in (PipelineFullOf p) in idtac);
         idtac_and_time2 prime bitwidth p "PipelineFullToStringsOf with native_compute" (fun _ => let __ := eval native_compute in (PipelineFullToStringsOf p) in idtac);
         idtac_and_time2 prime bitwidth p "PipelineNBEOf with native_compute" (fun _ => let __ := eval native_compute in (PipelineNBEOf p) in idtac);
         idtac_and_time2 prime bitwidth p "PipelineArithOf with native_compute" (fun _ => let __ := eval native_compute in (PipelineArithOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineFullOf with cbv" (fun _ => let __ := eval cbv in (PipelineFullOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineFullToStringsOf with cbv" (fun _ => let __ := eval cbv in (PipelineFullToStringsOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineNBEOf with cbv" (fun _ => let __ := eval cbv in (PipelineNBEOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineArithOf with cbv" (fun _ => let __ := eval cbv in (PipelineArithOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineFullOf with lazy" (fun _ => let __ := eval lazy in (PipelineFullOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineFullToStringsOf with lazy" (fun _ => let __ := eval lazy in (PipelineFullToStringsOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineNBEOf with lazy" (fun _ => let __ := eval lazy in (PipelineNBEOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineArithOf with lazy" (fun _ => let __ := eval lazy in (PipelineArithOf p) in idtac)
    | None => idtac
    end.
  Ltac perfPipelineOf prime bitwidth :=
    let p := compute_p prime bitwidth in perfPipelineOf' prime bitwidth p.

  Ltac perfGallinaDefOf' prime bitwidth p :=
    lazymatch p with
    | Some ?p
      => idtac_and_time prime bitwidth p "GallinaDefOf with cbv_no_rt" (fun _ => let __ := eval cbv_no_rt in (GallinaDefOf p) in idtac);
         idtac_and_time prime bitwidth p "GallinaDefOf with lazy_no_rt" (fun _ => let __ := eval lazy_no_rt in (GallinaDefOf p) in idtac)
    | None => idtac
    end.
  Ltac perfGallinaDefOf prime bitwidth :=
    let p := compute_p prime bitwidth in perfGallinaDefOf' prime bitwidth p.

  Ltac perf prime bitwidth :=
    let p := (eval vm_compute in (of_string prime bitwidth)) in
    lazymatch p with
    | Some ?p
      => idtac_and_time prime bitwidth p "GallinaAxOf with vm_compute" (fun _ => let __ := eval vm_compute in (GallinaAxOf p) in idtac);
         idtac_and_time prime bitwidth p "GallinaAxComputedOf with vm_compute" (fun _ => let __ := eval vm_compute in (GallinaAxComputedOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineFullOf with vm_compute" (fun _ => let __ := eval vm_compute in (PipelineFullOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineFullToStringsOf with vm_compute" (fun _ => let __ := eval vm_compute in (PipelineFullToStringsOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineNBEOf with vm_compute" (fun _ => let __ := eval vm_compute in (PipelineNBEOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineArithOf with vm_compute" (fun _ => let __ := eval vm_compute in (PipelineArithOf p) in idtac);
         idtac_and_time2 prime bitwidth p "GallinaAxOf with native_compute" (fun _ => let __ := eval native_compute in (GallinaAxOf p) in idtac);
         idtac_and_time2 prime bitwidth p "PipelineFullOf with native_compute" (fun _ => let __ := eval native_compute in (PipelineFullOf p) in idtac);
         idtac_and_time2 prime bitwidth p "PipelineFullToStringsOf with native_compute" (fun _ => let __ := eval native_compute in (PipelineFullToStringsOf p) in idtac);
         idtac_and_time2 prime bitwidth p "PipelineNBEOf with native_compute" (fun _ => let __ := eval native_compute in (PipelineNBEOf p) in idtac);
         idtac_and_time2 prime bitwidth p "PipelineArithOf with native_compute" (fun _ => let __ := eval native_compute in (PipelineArithOf p) in idtac);
         idtac_and_time prime bitwidth p "GallinaAxOf with cbv" (fun _ => let __ := eval cbv in (GallinaAxOf p) in idtac);
         idtac_and_time prime bitwidth p "GallinaAxComputedOf with cbv" (fun _ => let __ := eval cbv in (GallinaAxComputedOf p) in idtac);
         idtac_and_time prime bitwidth p "GallinaAxOf with lazy" (fun _ => let __ := eval lazy in (GallinaAxOf p) in idtac);
         idtac_and_time prime bitwidth p "GallinaAxComputedOf with lazy" (fun _ => let __ := eval lazy in (GallinaAxComputedOf p) in idtac);
         idtac_and_time prime bitwidth p "GallinaDefOf with cbv_no_rt" (fun _ => let __ := eval cbv_no_rt in (GallinaDefOf p) in idtac);
         idtac_and_time prime bitwidth p "GallinaDefOf with lazy_no_rt" (fun _ => let __ := eval lazy_no_rt in (GallinaDefOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineFullOf with cbv" (fun _ => let __ := eval cbv in (PipelineFullOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineFullToStringsOf with cbv" (fun _ => let __ := eval cbv in (PipelineFullToStringsOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineNBEOf with cbv" (fun _ => let __ := eval cbv in (PipelineNBEOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineArithOf with cbv" (fun _ => let __ := eval cbv in (PipelineArithOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineFullOf with lazy" (fun _ => let __ := eval lazy in (PipelineFullOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineFullToStringsOf with lazy" (fun _ => let __ := eval lazy in (PipelineFullToStringsOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineNBEOf with lazy" (fun _ => let __ := eval lazy in (PipelineNBEOf p) in idtac);
         idtac_and_time prime bitwidth p "PipelineArithOf with lazy" (fun _ => let __ := eval lazy in (PipelineArithOf p) in idtac)
    | None => idtac "No params for prime" prime
    end.

  Global Set Printing Width 1000000.
End WordByWordMontgomery.
(*
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perf "2^255-19" 64 0%nat.
  WordByWordMontgomery.perf "2^384 - 2^128 - 2^96 + 2^32 - 1" 32.
Abort.
*)
(*
Definition primes : list string :=
  [
    (* single-tap: *)

    "2^127 - 1"; (* "kummer strikes back" *)
      "2^129 - 25";
      "2^130 - 5"; (* poly1305 *)
      "2^137 - 13";
      "2^140 - 27";
      "2^141 - 9";
      "2^150 - 5";
      "2^150 - 3";
      "2^152 - 17";
      "2^158 - 15";
      "2^165 - 25";
      "2^166 - 5";
      "2^171 - 19";
      "2^174 - 17";
      "2^174 - 3";
      "2^189 - 25";
      "2^190 - 11";
      "2^191 - 19";
      "2^194 - 33";
      "2^196 - 15";
      "2^198 - 17";
      "2^206 - 5";
      "2^212 - 29";
      "2^213 - 3";
      "2^221 - 3";
      "2^222 - 117";
      "2^226 - 5";
      "2^230 - 27";
      "2^235 - 15";
      "2^243 - 9";
      "2^251 - 9";
      "2^255 - 765";
      "2^255 - 19"; (* curve25519 *)
      "2^256 - 189";
      "2^266 - 3";
      "2^285 - 9";
      "2^291 - 19";
      "2^321 - 9";
      "2^336 - 17";
      "2^336 - 3";
      "2^338 - 15";
      "2^369 - 25";
      "2^379 - 19";
      "2^382 - 105";
      "2^383 - 421";
      "2^383 - 187";
      "2^383 - 31";
      "2^384 - 317";
      "2^389 - 21";
      "2^401 - 31";
      "2^413 - 21";
      "2^414 - 17";
      "2^444 - 17";
      "2^452 - 3";
      "2^468 - 17";
      "2^488 - 17";
      "2^489 - 21";
      "2^495 - 31";
      "2^511 - 481";
      "2^511 - 187";
      "2^512 - 569";
      "2^521 - 1"; (* p512 *)

      (* two taps, golden ratio: *)

      "2^192 - 2^64 - 1";
      "2^216 - 2^108 - 1";
      "2^322 - 2^161 - 1";
      "2^416 - 2^208 - 1";
      "2^448 - 2^224 - 1"; (* goldilocks *)
      "2^450 - 2^225 - 1";
      "2^480 - 2^240 - 1"; (* ridinghood *)

      (* two or more taps *)

      "2^205 - 45*2^198 - 1";
      "2^224 - 2^96 + 1"; (* p224 *)
      "2^256 - 2^224 + 2^192 + 2^96 - 1"; (* p256 *)
      "2^256 - 2^32 - 977"; (* bitcoin *)
      "2^256 - 4294968273"; (* bitcoin, for 64-bit impl *)
      "2^384 - 2^128 - 2^96 + 2^32 - 1"; (* p384 *)

      (* Montgomery-Friendly *)

      "2^256 - 88*2^240 - 1";
      "2^254 - 127*2^240 - 1";
      "2^384 - 79*2^376 - 1";
      "2^384 - 5*2^368 - 1";
      "2^512 - 491*2^496 - 1";
      "2^510 - 290*2^496 - 1"
  ].
*)
