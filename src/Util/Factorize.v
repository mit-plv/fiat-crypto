Require Import Coq.Bool.Sumbool.
Require Import Coq.micromega.Psatz.
Require Import Coq.NArith.NArith.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.Init.Wf.

Local Open Scope positive_scope.

(* given [n] and [d₀], returns, possibly, [d, v] where [d ≥ d₀] is small and [d * v = n]

   Precondition: [d₀] is either 2, or an odd number > 2 *)
Definition find_N_factor (factor_val : N) (d0 : N) : option (N * N).
Proof.
  refine (let (d', r) := N.div_eucl factor_val d0 in (* special-case the first one, which might be 2 *)
          if N.eqb 0 r
          then Some (d0, d')
          else
            let sfactor_val := N.sqrt factor_val in
            Fix
              (Acc_intro_generator (S (S (S (N.to_nat (N.div2 sfactor_val))))) (@N.gt_wf sfactor_val)) (fun _ => option (N * N)%type)
              (fun d find_N_factor
               => let (d', r) := N.div_eucl factor_val d in
                  if N.eqb 0 r
                  then Some (d, d')
                  else let d' := (d + 2)%N in
                       if Sumbool.sumbool_of_bool (N.leb d' sfactor_val)
                       then find_N_factor d' _
                       else None)
              (if N.eqb 2%N d0 then 3%N else (d0 + 2)%N)).
  { subst sfactor_val d'.
    clear find_N_factor.
    let H := match goal with H : _ = true |- _ => H end in
    clear -H;
      abstract (
          apply N.leb_le in H;
          split; try assumption;
          lia
        ). }
Defined.

(* given [n] and [d₀], gives a list of factors of [n] which are ≥ d₀, lowest to highest *)
Definition factorize' (n : N) : N -> list N.
Proof.
  refine (Fix
            (Acc_intro_generator (S (S (S (S (N.to_nat (N.div2 (N.sqrt n))))))) N.lt_wf_0) (fun _ => N -> list N)
            (fun n factorize cur_max_factor
             => _)
            n).
  refine match find_N_factor n cur_max_factor with
         | Some (d, n') => if Sumbool.sumbool_of_bool (n' <? n)%N
                           then d :: factorize n' _ d
                           else d :: n' :: nil
         | None => n::nil
         end.
  { let H := match goal with H : _ = true |- _ => H end in
    clear -H;
      abstract (
          apply N.ltb_lt in H;
          assumption
        ). }
Defined.

Definition factorize (n : N) : list N := factorize' n 2%N.

Definition factorize_or_fail (n:N) : option (list N) :=
  let factors := factorize n in
  if N.eqb (List.fold_right N.mul 1%N factors) n then Some factors else None.
Lemma product_factorize_or_fail (n:N) (factors:list N)
      (H:Logic.eq (factorize_or_fail n) (Some factors))
  : Logic.eq (List.fold_right N.mul 1%N factors) n.
Proof.  cbv [factorize_or_fail] in H; destruct ((fold_right N.mul 1 (factorize n) =? n)%N) eqn:?;
          try apply N.eqb_eq; congruence. Qed.
