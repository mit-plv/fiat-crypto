Require Import Crypto.Util.Sigma.Lift.
Require Import Crypto.Util.Sigma.Associativity.
Require Import Crypto.Util.Sigma.MapProjections.
Require Import Crypto.Specific.IntegrationTestTemporaryMiscCommon.
Require Import Crypto.Compilers.Z.Bounds.Interpretation.
Require Import Crypto.Compilers.Eta.
Require Export Coq.ZArith.ZArith.
Require Export Crypto.Util.LetIn.
Require Export Crypto.Util.FixedWordSizes.
Require Export Crypto.Compilers.Syntax.
Require Export Crypto.Compilers.Z.HexNotationConstants.
Require Export Crypto.Util.Notations.

Global Arguments Pos.to_nat !_ / .
Global Arguments InterpEta {_ _ _ _ _}.
Global Set Printing Width 2000000.

Ltac display_helper f :=
  let t := type of f in
  lazymatch (eval hnf in t) with
  | forall _ : ?A, ?B
    => let x := fresh "x" in
       lazymatch (eval hnf in A) with
       | @sig ?A ?P
         => lazymatch (eval hnf in A) with
            | sig _
              => let f' := open_constr:(fun x : A => f (exist P x _)) in
                 display_helper f'
            | _
              => refine (fun x : A => _);
                 let f' := open_constr:(f (exist P x _)) in
                 display_helper f'
            end
       | _
         => lazymatch A with
            | prod ?A ?B
              => let f' := open_constr:(fun (a : A) (b : B) => f (a, b)%core) in
                 display_helper f'
            | _
              => refine (fun x : A => _);
                 let f' := open_constr:(f x) in
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
Tactic Notation "display" open_constr(f) :=
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
                            ] in F) in
  let ret := open_constr:(ltac:(display_helper (proj1_sig f))) in
  let ret := do_red ret in
  let ret := lazymatch ret with
             | context[match ?sz with O => _ | _ => _ end] => (eval cbv [sz] in ret)
             | _ => ret
             end in
  let ret := (eval simpl @Z.to_nat in ret) in
  let ret := (eval cbv [interp_flat_type] in ret) in
  refine ret.
Notation display f := (ltac:(let v := f in display v)) (only parsing).

Require Export Crypto.Compilers.Z.CNotations.

Notation "'Interp-η' f x" := (Eta.InterpEta f x) (format "'Interp-η' '//' f '//' x", at level 200, f at next level, x at next level).
Notation ReturnType := (interp_flat_type _).
Notation "'let' ( a , b ) := c 'in' d" := (let (a, b) := c in d) (at level 200, d at level 200, format "'let'  ( a ,  b )  :=  c  'in' '//' d").

Require Export Coq.Unicode.Utf8. (* for better line breaks at function display; must come last *)
