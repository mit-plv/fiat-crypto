(** * Push-Button Synthesis of Barrett Reduction: Reification Cache *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Arithmetic.BarrettReduction.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Local Open Scope Z_scope.

Import BarrettReduction.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Module Export BarrettReduction.
  (* all the list operations from for_reification.ident *)
  Strategy 100 [length seq repeat combine map flat_map partition app rev fold_right update_nth nth_default ].
  Strategy -10 [Fancy.fancy_reduce reduce].

  Derive reified_barrett_red_gen
         SuchThat (is_reification_of reified_barrett_red_gen Fancy.fancy_reduce)
         As reified_barrett_red_gen_correct.
  Proof. Time cache_reify (). Time Qed.

  Module Export ReifyHints.
    Hint Extern 1 (_ = _) => apply_cached_reification Fancy.fancy_reduce (proj1 reified_barrett_red_gen_correct) : reify_cache_gen.
    Hint Immediate (proj2 reified_barrett_red_gen_correct) : wf_gen_cache.
    Hint Rewrite (proj1 reified_barrett_red_gen_correct) : interp_gen_cache.
  End ReifyHints.
  Local Opaque reified_barrett_red_gen. (* needed for making [autorewrite] not take a very long time *)
End BarrettReduction.
