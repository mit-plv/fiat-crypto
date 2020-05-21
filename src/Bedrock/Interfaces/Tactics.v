Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import Crypto.Bedrock.ByteBounds.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.MakeAccessSizes.
Require Import Crypto.Bedrock.MakeNames.
Require Import Crypto.Bedrock.MaxBounds.
Require Import Crypto.Bedrock.Util.
Require Import Crypto.Bedrock.Translation.Func.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Language.API.
Require Import Coq.Lists.List. (* after SeparationLogic *)

Import Language.Compilers.
Import Types.

Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.

Ltac map_bounds_listonly t bounds :=
  lazymatch bounds with
  | (?a, ?b) =>
    let x := map_bounds_listonly t a in
    let y := map_bounds_listonly t b in
    constr:((x, y))
  | tt => constr:(tt)
  | ?b => lazymatch type of b with
          | option (list _) => t b
          | _ => constr:(tt)
          end
  end.

Ltac crush_list_ptr_subgoals :=
  repeat match goal with
         | _ => progress cbn [hd tl]
         | _ => progress cbv [WeakestPrecondition.literal]
         | _ => rewrite word.of_Z_unsigned
         | _ => rewrite map.get_put_diff by congruence
         | _ => rewrite map.get_put_same by auto
         | |- WeakestPrecondition.get _ _ _ => eexists
         | _ => solve [apply Forall_word_unsigned_within_access_size;
                       auto using width_0mod_8]
         | _ => solve [apply word.unsigned_range]
         | _ => solve [auto using eval_bytes_range]
         | _ => reflexivity
         end.
Ltac exists_list_ptr p :=
  (exists p); sepsimpl; [ ];
  eexists; sepsimpl;
  [ solve [crush_list_ptr_subgoals] .. | ];
  eexists; sepsimpl;
  [ solve [crush_list_ptr_subgoals] .. | ].

Ltac next_argument :=
  (exists 1%nat); sepsimpl; cbn [firstn skipn];
  [ solve [eauto using firstn_length_le] | ].

Ltac ssubst :=
  repeat match goal with
         | H : literal (word.unsigned _) (eq _) |- _ =>
           inversion H as [H']; clear H;
           rewrite word.of_Z_unsigned in H'
         | H : word.unsigned _ = word.unsigned _ |- _ =>
           apply word.unsigned_inj in H
         end; subst.

Ltac map_simplify :=
  repeat match goal with
         | _ => rewrite map.get_put_diff by congruence
         | _ => rewrite map.get_put_same
         end.

Ltac type_simplify :=
  cbv [expr.Interp] in *;
  cbn [fst snd type.app_curried type.final_codomain
           Compilers.base_interp] in *.
Ltac lists_reserved_simplify :=
  cbn [LoadStoreList.lists_reserved_with_initial_context
         LoadStoreList.extract_listnames
         LoadStoreList.lists_reserved
         make_innames make_innames' make_outnames make_names
         fst snd app type.final_codomain
         base_rtype_of_ltype
         rep.rtype_of_ltype rep.equiv rep.Z rep.listZ_mem
         map.of_list_zip map.putmany_of_list_zip
         Flatten.flatten_argnames Flatten.flatten_base_ltype
         Flatten.flatten_listonly_base_ltype ]; type_simplify.
Ltac translator_simplify :=
  cbn [fst snd type.final_codomain
           LoadStoreList.list_lengths_from_args
           LoadStoreList.list_lengths_from_value
           LoadStoreList.access_sizes_good_args
           LoadStoreList.base_access_sizes_good
           LoadStoreList.access_sizes_good
           LoadStoreList.base_access_sizes_good
           LoadStoreList.within_access_sizes_args
           LoadStoreList.within_base_access_sizes
           equivalent_flat_args equivalent_flat_base
           WeakestPrecondition.dexpr
           WeakestPrecondition.expr
           WeakestPrecondition.expr_body
           rep.equiv rep.Z rep.listZ_mem ].

Ltac access_size_simplify :=
  repeat match goal with
         | H: context [Z.of_nat (@Memory.bytes_per ?w _)]
           |- _ =>
           first [ progress
                     change (Z.of_nat
                               (@Memory.bytes_per
                                  w access_size.one)) with 1 in H
                 | progress
                     change (Z.of_nat
                               (@Memory.bytes_per
                                  w access_size.two)) with 2 in H
                 | progress
                     change (Z.of_nat
                               (@Memory.bytes_per
                                  w access_size.four)) with 4 in H ]
         | |- context [Z.of_nat (@Memory.bytes_per ?w _)] =>
           first [ progress
                     change (Z.of_nat
                               (@Memory.bytes_per
                                  w access_size.one)) with 1
                 | progress
                     change (Z.of_nat
                               (@Memory.bytes_per
                                  w access_size.two)) with 2
                 | progress
                     change (Z.of_nat
                               (@Memory.bytes_per
                                  w access_size.four)) with 4 ]
         end.

Ltac exists_arg_pointers :=
  repeat match goal with
         | H : sep _ _ ?m |- @Lift1Prop.ex1 nat _ _ ?m =>
           match type of H with
           | context [sep _ (_ ?p _)] =>
             next_argument; exists_list_ptr p
           | context [sep (_ ?p _)] =>
             next_argument; exists_list_ptr p
           end
         end.

Ltac simplify_translate_func_postcondition :=
  match goal with
    H : context [sep _ _ ?m] |- context [_ ?m] =>
    cbn - [Memory.bytes_per translate_func] in H
  end;
  sepsimpl_hyps.

Ltac setup_lists_reserved :=
  lists_reserved_simplify;
  translator_simplify;
  try match goal with
      | H : context [map byte.unsigned ?bs] |- _ =>
        assert (map byte.unsigned bs
                = map word.unsigned
                      (map word.of_Z (map byte.unsigned bs)))
          by (erewrite map_unsigned_of_Z, map_word_wrap_bounded;
              eauto using byte_unsigned_within_max_bounds)
      end.

Ltac handle_lists_reserved :=
  repeat match goal with
         | _ => progress sepsimpl;
                auto using Forall_map_unsigned,
                Forall_map_byte_unsigned
         | _ => rewrite bits_per_word_eq_width
             by auto using width_0mod_8
         | _ => erewrite map_unsigned_of_Z,map_word_wrap_bounded
             by eauto using byte_unsigned_within_max_bounds
         | |- WeakestPrecondition.get _ _ _ =>
           eexists; map_simplify; solve [eauto]
         | _ => congruence
         end.

Ltac get_pointer wa :=
  match goal with
  | H : sep _ _ ?m |- context [?m] =>
    match type of H with
      context [_ ?pa wa] => constr:(pa)
    end
  | _ => fail "unable to find pointers for " wa
  end.

Ltac get_value_of_pointer p :=
  match goal with
  | H : sep _ _ ?m |- context [?m] =>
    match type of H with
      context [_ p ?x] => constr:(x)
    end
  | _ => fail "unable to find value of pointer " p
  end.

Ltac get_all_arg_pointers args :=
  lazymatch args with
  | (?a, ?b) =>
    let x := get_all_arg_pointers a in
    let y := get_all_arg_pointers b in
    constr:((cons x y)%list)
  | tt => constr:(@nil (Semantics.word))
  | ?x =>
    lazymatch x with
    | map word.unsigned ?ws =>
      let p := get_pointer ws in constr:(p)
    | map byte.unsigned ?bs =>
      let p := get_pointer bs in constr:(p)
    | _ => fail "unable to find words or bytes for " x
    end
  end.

Ltac get_out_array_ptrs arg_ptrs all_ptrs :=
  lazymatch arg_ptrs with
  | nil => constr:(all_ptrs)
  | cons ?p ?x =>
    lazymatch all_ptrs with
    | cons p ?y =>
      let ps := get_out_array_ptrs x y in
      constr:(ps)
    | _ =>
      fail "no matching pointer for " p
    end
  end.

Ltac exists_out_array_placeholder zs words ptr :=
  repeat match goal with
         | _ => progress handle_lists_reserved
         | |- Lift1Prop.ex1 _ _ =>
           first [ exists zs
                        | exists words
                        | exists ptr ]
         end.
Ltac exists_all_placeholders out_array_ptrs :=
  lazymatch out_array_ptrs with
  | cons ?p ?ptrs' =>
    let bits := get_value_of_pointer p in
    let zs :=
        lazymatch type of bits with
        | list word.rep => constr:(map word.unsigned bits)
        | list Byte.byte => constr:(map byte.unsigned bits)
        | ?t => fail "unexpected placeholder type " t
        end in
    let words :=
        lazymatch type of bits with
        | list word.rep => constr:(bits)
        | list Byte.byte =>
          constr:(map word.of_Z (map byte.unsigned bits))
        | ?t => fail "unexpected placeholder type " t
        end in
    exists_out_array_placeholder zs words p;
    exists_all_placeholders ptrs'
  | nil => idtac
  end.

Ltac canonicalize_arrays :=
  repeat match goal with
         | _ => progress access_size_simplify
         | _ => seprewrite array_truncated_scalar_scalar_iff1
         | _ => seprewrite array_truncated_scalar_ptsto_iff1
         | H : sep _ _ ?m |- context [?m] =>
           seprewrite_in array_truncated_scalar_scalar_iff1 H
         | H : sep _ _ ?m |- context [?m] =>
           seprewrite_in array_truncated_scalar_ptsto_iff1 H
         | _ => rewrite <-@word_size_in_bytes_eq in * by eauto
         | _ => rewrite byte_map_of_Z_unsigned by auto
         end.

Ltac solve_translate_func_subgoals prove_bounds t :=
  auto using make_innames_varname_gen_disjoint,
  make_outnames_varname_gen_disjoint,
  make_innames_make_outnames_disjoint,
  flatten_make_innames_NoDup, flatten_make_outnames_NoDup;
  pose proof bits_per_word_eq_width width_0mod_8;
  pose proof width_ge_8;
  repeat match goal with
         | _ => progress sepsimpl
         | _ => progress translator_simplify
         | _ => progress access_size_simplify
         | |- context [expr.interp] => progress type_simplify
         | |- (_, _) = (_, _) => apply f_equal2
         | |- Forall _ _ =>
           eapply max_bounds_range_iff; solve [prove_bounds]
         | |- Forall _ _ =>
           eapply byte_bounds_range_iff; solve [prove_bounds]
         | |- context [Z.le] => lia
         | _ => reflexivity
         | _ => t
         end.

Ltac prove_bounds_direct :=
  match goal with
  | H : _ |- _ => apply H; solve [auto]
  end.
