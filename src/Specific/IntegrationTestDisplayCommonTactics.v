Require Import Crypto.Util.Sigma.Lift.
Require Import Crypto.Util.Sigma.Associativity.
Require Import Crypto.Util.Sigma.MapProjections.
Require Import Crypto.Specific.IntegrationTestTemporaryMiscCommon.
Require Import Crypto.Compilers.Z.Bounds.Interpretation.
Require Import Crypto.Compilers.Eta.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Compilers.Syntax.
Require Export Crypto.Util.Notations.

Global Arguments Pos.to_nat !_ / .

Ltac display_helper_gen f make_hole :=
  let display_helper f := display_helper_gen f make_hole in
  let do_make_hole _ :=
      match goal with
      | [ |- ?T ] => let h := make_hole T in
                     refine h
      end in
  let t := type of f in
  lazymatch (eval hnf in t) with
  | forall _ : ?A, ?B
    => let x := fresh "x" in
       lazymatch (eval hnf in A) with
       | @sig ?A ?P
         => lazymatch (eval hnf in A) with
            | sig _
              => let f' := constr:(fun x : A => f (exist P x ltac:(do_make_hole ()))) in
                 display_helper f'
            | _
              => refine (fun x : A => _);
                 let f' := constr:(f (exist P x ltac:(do_make_hole ()))) in
                 display_helper f'
            end
       | _
         => lazymatch A with
            | prod ?A ?B
              => let f' := constr:(fun (a : A) (b : B) => f (a, b)%core) in
                 display_helper f'
            | _
              => refine (fun x : A => _);
                 let f' := constr:(f x) in
                 display_helper f'
            end
       end
  | @sig ?A _
    => lazymatch (eval hnf in A) with
       | sig _ => display_helper (proj1_sig f)
       | _ => refine (proj1_sig f)
       end
  | _
    => lazymatch t with
       | prod _ _
         => let a := fresh "a" in
            let b := fresh "b" in
            refine (let (a, b) := f in
                    pair _ _);
            [ display_helper a | display_helper b ]
       | _ => refine f
       end
  end.
Ltac display_helper f := display_helper_gen f ltac:(fun T => open_constr:(_)).
Ltac display_helper_with_admit f :=
  constr:(fun admit : forall T, T
          => ltac:(display_helper_gen f ltac:(fun T => constr:(admit T)))).
Ltac try_strip_admit f :=
  lazymatch f with
  | fun _ : forall T, T => ?P => P
  | ?P => P
  end.
Ltac refine_display f :=
  let do_red F := (eval cbv [f
                               proj1_sig fst snd
                               Tuple.map Tuple.map'
                               Lift.lift1_sig Lift.lift2_sig Lift.lift3_sig Lift.lift4_sig Lift.lift4_sig_sig
                               MapProjections.proj2_sig_map Associativity.sig_sig_assoc
                               sig_conj_by_impl2
                               sig_eq_trans_exist1 sig_R_trans_exist1 sig_eq_trans_rewrite_fun_exist1
                               sig_R_trans_rewrite_fun_exist1
                               adjust_tuple2_tuple2_sig
                               Tuple.tuple Tuple.tuple'
                               FixedWordSizes.wordT FixedWordSizes.word_case FixedWordSizes.ZToWord FixedWordSizes.word_case_dep
                               Bounds.actual_logsz Bounds.round_up_to_in_list Bounds.option_min
                               List.map List.filter List.fold_right List.fold_left
                               Nat.leb Nat.min
                               PeanoNat.Nat.log2 PeanoNat.Nat.log2_iter PeanoNat.Nat.pred
                               Bounds.bounds_to_base_type
                               interp_flat_type
                               Z.leb Z.compare Pos.compare Pos.compare_cont
                               ZRange.lower ZRange.upper
                               BinPos.Pos.to_nat PeanoNat.Nat.pow
                            ] in F) in
  let ret := display_helper_with_admit (proj1_sig f) in
  let ret := do_red ret in
  let ret := lazymatch ret with
             | context[match ?sz with O => _ | _ => _ end] => (eval cbv [sz] in ret)
             | _ => ret
             end in
  let ret := (eval simpl @Z.to_nat in ret) in
  let ret := (eval cbv [interp_flat_type] in ret) in
  let ret := try_strip_admit ret in
  refine ret.
Tactic Notation "display" open_constr(f) :=
  refine_display f.
Notation display f := (ltac:(let v := f in display v)) (only parsing).

(** Some helper tactics for actually pulling out the expression *)
Ltac strip_InterpEta term :=
  let retype e :=
      lazymatch type of e with
      | forall var, @Syntax.expr ?base_type_code ?op var ?T
        => constr:(e : @Syntax.Expr base_type_code op T)
      | _ => e
      end in
  lazymatch term with
  | fun x : ?T => ?P
    => let maybe_x := fresh x in
       let probably_not_x := fresh maybe_x in
       let not_x := fresh probably_not_x in
       lazymatch
         constr:(fun x : T
                 => match P with
                    | not_x => ltac:(let v := (eval cbv delta [not_x] in not_x) in
                                     let v' := strip_InterpEta v in
                                     exact v')
                    end)
       with
       | fun _ => ?P => retype P
       | ?P => retype P
       end
  | @Eta.InterpEta _ _ _ _ _ ?e
    => e
  | @Eta.InterpEta _ _ _ _ _ ?e _
    => e
  | let (a, b) := ?f in _
    => f
  | _ => let dummy := match goal with
                      | _ => fail 1 "strip_InterpEta:" term
                      end in
         I
  end.

Ltac extract_Expr f :=
  let k := constr:(ltac:(refine_display f)) in
  let k := strip_InterpEta k in
  k.
Notation extract_Expr f := (ltac:(let v := f in let v := extract_Expr v in refine v)) (only parsing).
