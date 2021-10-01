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
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Util.
Require Import Crypto.Bedrock.Field.Common.Arrays.ByteBounds.
Require Import Crypto.Bedrock.Field.Common.Arrays.MakeAccessSizes.
Require Import Crypto.Bedrock.Field.Common.Arrays.MaxBounds.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Equivalence.
Require Import Crypto.Bedrock.Field.Common.Names.MakeNames.
Require Import Crypto.Bedrock.Field.Translation.Func.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Language.API.
Require Import Coq.Lists.List. (* after SeparationLogic *)

Import Language.Compilers.

Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.

Ltac map_bounds_listonly t bounds :=
  lazymatch bounds with
  | (?a, ?b) =>
    let x := map_bounds_listonly t a in
    let y := map_bounds_listonly t b in
    constr:((x, y))
  | tt => constr:(tt)
  | ?b =>
    let bt := lazymatch type of b with
             | ?bt => bt end in
    let bt := (eval cbn in bt) in
    lazymatch bt with
    | option (list _) => t b
    | _ => constr:(tt)
    end
  end.

Ltac crush_argument_equivalence_subgoals :=
  repeat match goal with
         | _ => progress cbn [hd tl]
         | _ => progress cbv [WeakestPrecondition.literal]
         | _ => rewrite word.of_Z_unsigned
         | _ => rewrite map.get_put_diff by congruence
         | _ => rewrite map.get_put_same by auto
         | |- WeakestPrecondition.get _ _ _ => eexists
         | |- map word.unsigned _ = map byte.unsigned _ =>
           erewrite map_unsigned_of_Z,map_word_wrap_bounded
             by eauto using byte_unsigned_within_max_bounds
         | _ => solve [unshelve eapply Forall_word_unsigned_within_access_size;
             rewrite ?bytes_per_word_eq, ?bits_per_word_eq_width; trivial]

         | _ => solve [auto using Forall_map_unsigned,
                       Forall_map_byte_unsigned]
         | _ => solve [apply word.unsigned_range]
         | _ => solve [auto using eval_bytes_range]
         | _ => reflexivity
         end.

Ltac next_argument :=
  exists 1%nat; cbn [firstn skipn hd]; split;
         [ repeat lazymatch goal with
                  | |- Lift1Prop.ex1 _ _ =>
                    eexists; sepsimpl;
                    [ solve [crush_argument_equivalence_subgoals] .. | ]
                  | |- exists _, _ =>
                    eexists; sepsimpl;
                    [ solve [crush_argument_equivalence_subgoals] .. | ]
                  end | ].

Ltac ssubst :=
  repeat match goal with
         | H : literal (word.unsigned _) (eq _) |- _ =>
           let H' := fresh in
           inversion H as [H']; clear H;
           rewrite word.of_Z_unsigned in H'
         | H : word.unsigned _ = word.unsigned _ |- _ =>
           apply word.unsigned_inj in H
         | H : ?x = _ |- _ => subst x
         | H : _ = ?x |- _ => subst x
         end.

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
  let do_simpl w v :=
    lazymatch v with access_size.one => idtac | access_size.two => idtac | access_size.four => idtac end;
    let from := constr:(Z.of_nat (@Memory.bytes_per w v)) in
    let to := (eval compute in from) in
    progress change from with to in * in
  repeat match goal with
         | H: context [Z.of_nat (@Memory.bytes_per ?w ?v)] |- _ => do_simpl w v
         | |- context [Z.of_nat (@Memory.bytes_per ?w ?v)] => do_simpl w v
         end.

Ltac simplify_translate_func_postcondition :=
  match goal with
    H : context [sep _ _ ?m] |- context [_ ?m] =>
    cbn - [Memory.bytes_per_word translate_func] in H;
    rewrite ?Z2Nat.id in H by (apply Z.lt_le_incl, word_size_in_bytes_pos)
  end;
  sepsimpl_hyps.

Ltac setup_lists_reserved :=
  lists_reserved_simplify;
  translator_simplify;
  try match goal with
      | H : context [map byte.unsigned ?bs] |- _ =>
        let width := open_constr:(_) in
        let __ := constr:(_ : Bitwidth.Bitwidth width) in
        let word := constr:( _ :Interface.word width) in
        assert (map byte.unsigned bs
                = map word.unsigned
                      (map (@word.of_Z _ word) (map byte.unsigned bs)))
          by (erewrite map_unsigned_of_Z, map_word_wrap_bounded;
              eauto using byte_unsigned_within_max_bounds)
      end.

Ltac handle_lists_reserved :=
  repeat match goal with
         | _ => progress sepsimpl;
                auto using Forall_map_unsigned,
                Forall_map_byte_unsigned
         | _ => solve [unshelve eapply Forall_word_unsigned_within_access_size;
             rewrite ?bytes_per_word_eq, ?bits_per_word_eq_width; trivial]
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
  | _ => fail "unable to find pointers for" wa
  end.

Ltac get_value_of_pointer p :=
  match goal with
  | H : sep _ _ ?m |- context [?m] =>
    match type of H with
      context [_ p ?x] => constr:(x)
    end
  | _ => fail "unable to find value of pointer" p
  end.

Ltac get_bedrock2_arglist args :=
  lazymatch args with
  | (?a, ?b) =>
    let x := get_bedrock2_arglist a in
    let y := get_bedrock2_arglist b in
    let ptrs := (eval cbv [app] in (x ++ y)%list) in
    constr:(ptrs)
  | tt => 
      let width := open_constr:(_) in
      let __ := constr:(_ : Bitwidth.Bitwidth width) in
      let word := constr:( _ :Interface.word width) in
      constr:(@nil word) (* end of args *)
  | ?x =>
    lazymatch type of x with
    | list _ =>
      lazymatch x with
      | map word.unsigned ?ws =>
        let p := get_pointer ws in constr:(cons p nil)
      | map byte.unsigned ?bs =>
        let p := get_pointer bs in constr:(cons p nil)
      | _ => fail "unable to find words or bytes for the list" x
      end
    | Z =>
      lazymatch x with
      | word.unsigned ?w => constr:(cons w nil)
      | _ => fail "expected something of the form (word.unsigned _), got" x
      end
    | ?t => fail "unexpected argument type" t "for argument" x
    end
  end.

Ltac get_out_array_ptrs arg_ptrs all_ptrs :=
  let n := constr:((length all_ptrs - length arg_ptrs)%nat) in
  let out_ptrs := (eval lazy in (firstn n all_ptrs)) in
  out_ptrs.

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
        | list Init.Byte.byte => constr:(map byte.unsigned bits)
        | ?t => fail "unexpected placeholder type" t
        end in
    let words :=
        lazymatch type of bits with
        | list word.rep => constr:(bits)
        | list Init.Byte.byte =>
          let width := open_constr:(_) in
          let __ := constr:(_ : Bitwidth.Bitwidth width) in
          let word := constr:( _ :Interface.word width) in
          constr:(map (@word.of_Z _ word) (map byte.unsigned bits))
        | ?t => fail "unexpected placeholder type" t
        end in
    exists_out_array_placeholder zs words p;
    exists_all_placeholders ptrs'
  | nil => idtac
  end.

Ltac canonicalize_arrays :=
  repeat match goal with
         | _ => progress access_size_simplify
         | |- context [Array.array
                         (Scalars.truncated_scalar access_size.word)
                         ?size ?start (map word.unsigned ?xs)] =>
           seprewrite (array_truncated_scalar_scalar_iff1 xs start size)
         | |- context [Array.array
                         (Scalars.truncated_scalar access_size.one)
                         ?size ?start ?xs] =>
           seprewrite (array_truncated_scalar_ptsto_iff1 xs start size)
         | H : sep _ _ ?m |- context [?m] =>
           seprewrite_in array_truncated_scalar_scalar_iff1 H
         | H : sep _ _ ?m |- context [?m] =>
           seprewrite_in array_truncated_scalar_ptsto_iff1 H
         | _ => rewrite byte_map_of_Z_unsigned by auto
         | _ => rewrite map_unsigned_of_Z by auto
         | _ => erewrite map_word_wrap_bounded by
               eauto using byte_unsigned_within_max_bounds
         | _ => progress cbn [Memory.bytes_per] in *
         | _ => rewrite !Z2Nat.id by (apply Z.lt_le_incl, word_size_in_bytes_pos)
         end.

Ltac solve_translate_func_subgoals prove_bounds t :=
  auto using make_innames_varname_gen_disjoint,
  make_outnames_varname_gen_disjoint,
  make_innames_make_outnames_disjoint,
  flatten_make_innames_NoDup, flatten_make_outnames_NoDup;
  pose proof bits_per_word_le_width;
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
