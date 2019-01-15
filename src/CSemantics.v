Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Strings.StringMap.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.Option.
Require Import Crypto.CStringification.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.ZUtil.Log2.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.LanguageWf.
Import ListNotations. Local Open Scope zrange_scope. Local Open Scope Z_scope.

Module Compilers.
  Import LanguageWf.Compilers.
  Export CStringification.Compilers.

  Module ToString.
    Export CStringification.Compilers.ToString.

    Module C.
      Export CStringification.Compilers.ToString.C.
      Export CStringification.Compilers.ToString.C.int.Notations.

      Module int.
        Record int (r : zrange)
          := Build_int' { value : Z ; bounded : is_bounded_by_bool value r = true }.
        Global Arguments value {r} _.

        (** A version that always gives [eq_refl] on concrete values in the second component *)
        Definition Build_int (r : zrange) (value : Z) (bounded : is_bounded_by_bool value r = true)
          : int r
          := Build_int' r value
                        (match is_bounded_by_bool value r as b return b = true -> b = true with
                         | true => fun _ => eq_refl
                         | false => fun pf => pf
                         end bounded).

        Definition maybe_Build_int (r : zrange) (value : Z) : option (int r)
          := match is_bounded_by_bool value r as b return is_bounded_by_bool value r = b -> option (int r) with
             | true => fun pf => Some (Build_int' r value pf)
             | false => fun _ => None
             end eq_refl.

        Definition Build_int_modulo (r : zrange) (value : Z) : option (int r)
          := maybe_Build_int r (ident.cast (fun _ x => x) r value).

        Definition interp (t : int.type) := int (int.to_zrange t).

        Axiom admit : bool.

        Definition opt_implicit_cast {t_from t_to : int.type} (v : interp t_from)
          : option (interp t_to)
          := if admit (* TODO: when are we allowed to cast implicitly? *)
             then Build_int_modulo _ (int.value v) (* TODO: should we ever do anything other than reduction modulo? *)
             else None.

        Definition opt_static_cast {t_from t_to : int.type} (v : interp t_from)
          : option (interp t_to)
          := if admit (* TODO: when are we allowed to static cast? *)
             then Build_int_modulo _ (int.value v) (* TODO: should we ever do anything other than reduction modulo? *)
             else None.
      End int.

      Module primitive.
        Definition interp (t : type.primitive) : Type
          := match t with
             | type.Z => { sz : int.type & int.interp sz }
             | type.Zptr => string
             end.
      End primitive.

      Module type.
        Fixpoint interp (t : type)
          := match t with
             | type.type_primitive t => primitive.interp t
             | type.prod A B => interp A * interp B
             | type.unit => unit
             end%type.
      End type.

      Inductive memory_value :=
      | mem_int (sz : int.type) (v : int.interp sz)
      | mem_int_array (sz : int.type) (v : list (int.interp sz)).

      Local Arguments int.bitwidth_of _ / .
      Lemma literal_good {v}
        : is_bounded_by_bool v (int.to_zrange (int.of_zrange_relaxed r[v ~> v])) = true.
      Proof using Type.
        cbv [int.of_zrange_relaxed upper lower int.to_zrange int.is_signed int.is_unsigned].
        repeat first [ progress rewrite ?Z.sub_diag, ?Z.add_0_l, ?Z.log2_up_1, ?Z2Nat.inj_0, ?Nat2Z.inj_0, ?Z.pow_0_r, ?Z.pow_1_r, ?Z2Nat.id by auto with zarith
                     | progress subst
                     | progress Z.ltb_to_lt
                     | break_innermost_match_step
                     | progress split_min_max
                     | progress change (Z.log2_up 0) with 0 in *
                     | progress change (2 - 1) with 1 in *
                     | progress change (0 - 1) with (-1) in *
                     | progress cbn [int.bitwidth_of int.lgbitwidth_of] in *
                     | lia
                     | solve [ auto with zarith ]
                     | match goal with
                       | [ H : ?T, H' : ?T |- _ ] => clear H'
                       | [ H : ?x >= ?y |- _ ] => assert (y <= x) by (clear -H; lia); clear H
                       | [ H : ?x > ?y |- _ ] => assert (y < x) by (clear -H; lia); clear H
                       | [ H : ?x <= ?y, H' : ?y <= ?x |- _ ] => assert (x = y) by lia; clear H H'
                       | [ H : ?x = ?x |- _ ] => clear H
                       | [ H : 0 = _ |- _ ] => symmetry in H
                       | [ H : Z.log2_up _ = 0 |- _ ] => rewrite Z.log2_up_null in H
                       | [ H : ?x + ?y <= ?y |- _ ] => assert (x <= 0) by lia; clear H
                       | [ H : Z.log2_up ?x <= 0 |- _ ] => unique assert (0 <= Z.log2_up x) by auto with zarith
                       | [ H : Z.log2_up ?x <= Zneg _ |- _ ] => unique assert (0 <= Z.log2_up x) by auto with zarith
                       | [ H : 1 + Z.log2_up ?x = 0 |- _ ] => unique assert (0 <= Z.log2_up x) by auto with zarith
                       | [ |- _ /\ _ ] => split; try lia; []
                       | [ H : context[Z.log2_up (?v + 1)], H' : ?v <= 0 |- _ ]
                         => replace (Z.log2_up (v + 1)) with 0 in *
                           by (symmetry; rewrite Z.log2_up_null; lia)
                       | [ H : context[Z.log2_up (?v + 1)], H' : ?v < 0 |- _ ]
                         => replace (Z.log2_up (v + 1)) with 0 in *
                           by (symmetry; rewrite Z.log2_up_null; lia)
                       | [ H' : ?v <= 0 |- context[Z.log2_up (?v + 1)] ]
                         => replace (Z.log2_up (v + 1)) with 0 in *
                           by (symmetry; rewrite Z.log2_up_null; lia)
                       | [ H' : ?v < 0 |- context[Z.log2_up (?v + 1)] ]
                         => replace (Z.log2_up (v + 1)) with 0 in *
                           by (symmetry; rewrite Z.log2_up_null; lia)
                       | [ H : 1 + Z.log2_up ?x <= ?y |- _ ]
                         => lazymatch y with
                            | context[Z.log2_up _] => fail
                            | _ => assert (Z.log2_up x <= y - 1) by lia; clear H
                            end
                       | [ |- ?v <= 2^Z.log2_up (1 + ?v) - 1 ]
                         => cut (1 + v <= 2^Z.log2_up (1 + v)); [ lia | ]
                       | [ |- ?x <= 2^?y - 1 ]
                         => lazymatch x with
                            | context[2^_] => fail
                            | context[Z.log2_up _] => fail
                            | _ => cut (x + 1 <= 2^y); [ lia | ]
                            end
                       | [ |- ?x <= 2^?y ]
                         => rewrite Z.log2_up_le_pow2_full
                       end
                     | progress cbv [is_bounded_by_bool lower upper]; rewrite Bool.andb_true_iff, !Z.leb_le_iff
                     | apply conj
                     | progress Z.replace_all_neg_with_pos ].
      Qed.

      Definition make_Literal (v : Z) : option {sz : int.type & int.interp sz}
        := Some (existT _ (int.of_zrange_relaxed r[v~>v])
                        (int.Build_int' _ v literal_good)).

      Axiom proof_admitted : False.
      Local Notation admit := match proof_admitted with end.

      Fixpoint interp_arith_expr
               (ctx : StringMap.t memory_value) (* name -> value *)
               {t : type} (e : arith_expr t)
        : option (type.interp t * StringMap.t memory_value).
      Proof.
        refine match e in arith_expr t return option (type.interp t * StringMap.t memory_value) with
               | AppIdent s d idc arg
                 => arg_value_ctx <- @interp_arith_expr ctx s arg;
                      let '(arg_value, ctx) := arg_value_ctx in
                      (** Here is where we define most of the C semantics *)
                      match idc in ident s d return arith_expr s -> type.interp s -> option (type.interp d * StringMap.t memory_value) with
                      | literal v
                        => fun _ _
                           => res <- make_Literal v;
                                Some (res, ctx)
                      | List_nth n
                        => fun _ ptr
                           => val <- StringMap.find ptr ctx;
                                match val with
                                | mem_int_array sz ls
                                  => val' <- nth_error ls n;
                                       Some (existT _ _ val', ctx)
                                | mem_int _ _ => None
                                end
                      | Addr
                        => fun arg _
                           => match arg with
                              | Var type.Z name => Some (name, ctx)
                              | _ => None
                              end
                      | Dereference
                        => fun _ ptr
                           => val <- StringMap.find ptr ctx;
                                match val with
                                | mem_int sz v
                                  => Some (existT _ sz v, ctx)
                                | mem_int_array _ _ => None
                                end
                      | Z_shiftr offset
                        => fun _ '(existT sz x)
                           => let res := Z.shiftr (int.value x) offset in
                              (* TODO: Perform type promotion on the integer type [sz] *)
                              let sz_out := admit in
                              res' <- int.maybe_Build_int (int.to_zrange sz_out) res;
                                (* TODO: decide what type [res] should go in, figure out whether or not behavior is undefined, etc; return [None] if needed *)
                                Some (existT _ _ res', ctx)
                      | Z_shiftl offset
                        => fun _ '(existT sz x)
                           => let res := Z.shiftl (int.value x) offset in
                              (* TODO: Perform type promotion on the integer type [sz] *)
                              let sz_out := admit in
                              res' <- int.maybe_Build_int (int.to_zrange sz_out) res;
                                (* TODO: decide what type [res] should go in, figure out whether or not behavior is undefined, etc; return [None] if needed *)
                                Some (existT _ _ res', ctx)
                      | Z_land
                        => fun _ '(existT x_sz x, existT y_sz y)
                           => let res := Z.land (int.value x) (int.value y) in
                              (* TODO: Perform type promotion on the integer type [sz] *)
                              let sz_out := admit in
                              res' <- int.maybe_Build_int (int.to_zrange sz_out) res;
                                (* TODO: decide what type [res] should go in, figure out whether or not behavior is undefined, etc; return [None] if needed *)
                                Some (existT _ _ res', ctx)
                      | Z_lor
                        => fun _ '(existT x_sz x, existT y_sz y)
                           => let res := Z.lor (int.value x) (int.value y) in
                              (* TODO: Perform type promotion on the integer type [sz] *)
                              let sz_out := admit in
                              res' <- int.maybe_Build_int (int.to_zrange sz_out) res;
                                (* TODO: decide what type [res] should go in, figure out whether or not behavior is undefined, etc; return [None] if needed *)
                                Some (existT _ _ res', ctx)
                      | Z_add
                        => fun _ '(existT x_sz x, existT y_sz y)
                           => let res := Z.add (int.value x) (int.value y) in
                              (* TODO: Perform type promotion on the integer type [sz] *)
                              let sz_out := admit in
                              res' <- int.maybe_Build_int (int.to_zrange sz_out) res;
                                (* TODO: decide what type [res] should go in, figure out whether or not behavior is undefined, etc; return [None] if needed *)
                                Some (existT _ _ res', ctx)
                      | Z_mul
                        => fun _ '(existT x_sz x, existT y_sz y)
                           => let res := Z.mul (int.value x) (int.value y) in
                              (* TODO: Perform type promotion on the integer type [sz] *)
                              let sz_out := admit in
                              res' <- int.maybe_Build_int (int.to_zrange sz_out) res;
                                (* TODO: decide what type [res] should go in, figure out whether or not behavior is undefined, etc; return [None] if needed *)
                                Some (existT _ _ res', ctx)
                      | Z_sub
                        => fun _ '(existT x_sz x, existT y_sz y)
                           => let res := Z.sub (int.value x) (int.value y) in
                              (* TODO: Perform type promotion on the integer type [sz] *)
                              let sz_out := admit in
                              res' <- int.maybe_Build_int (int.to_zrange sz_out) res;
                                (* TODO: decide what type [res] should go in, figure out whether or not behavior is undefined, etc; return [None] if needed *)
                                Some (existT _ _ res', ctx)
                      | Z_opp
                        => fun _ '(existT x_sz x)
                           => let res := Z.opp (int.value x) in
                              (* TODO: Perform type promotion on the integer type [sz] *)
                              let sz_out := admit in
                              res' <- int.maybe_Build_int (int.to_zrange sz_out) res;
                                (* TODO: decide what type [res] should go in, figure out whether or not behavior is undefined, etc; return [None] if needed *)
                                Some (existT _ _ res', ctx)
                      | Z_lnot ty
                        => fun _ '(existT x_sz x)
                           => let res := Z.lnot_modulo (2^int.bitwidth_of ty) (int.value x) in
                              (* TODO: Perform type promotion on the integer type [sz] *)
                              let sz_out := admit in
                              res' <- int.maybe_Build_int (int.to_zrange sz_out) res;
                                (* TODO: decide what type [res] should go in, figure out whether or not behavior is undefined, etc; return [None] if needed *)
                                if int.is_unsigned ty
                                then Some (existT _ _ res', ctx)
                                else None (* we say that [~] is invalid on signed values *)
                      | Z_bneg
                        => fun _ '(existT x_sz x)
                           => let res := Z.bneg (int.value x) in
                              (* TODO: Perform type promotion on the integer type [sz] *)
                              let sz_out := admit in
                              res' <- int.maybe_Build_int (int.to_zrange sz_out) res;
                                (* TODO: decide what type [res] should go in, figure out whether or not behavior is undefined, etc; return [None] if needed *)
                                Some (existT _ _ res', ctx)
                      | Z_mul_split lgs
                        => fun _ '(mod_part, div_part, (existT x_sz x, existT y_sz y))
                           => let '(res_mod, res_div) := Z.mul_split_at_bitwidth lgs (int.value x) (int.value y) in
                              (* TODO: Perform type promotion on the integer type [sz] *)
                              let sz_out_mod := admit in
                              let sz_out_div := admit in
                              res_mod' <- int.maybe_Build_int (int.to_zrange sz_out_mod) res_mod;
                                res_div' <- int.maybe_Build_int (int.to_zrange sz_out_div) res_div;
                                (* TODO: decide what type [res] should go in, figure out whether or not behavior is undefined, etc; return [None] if needed *)
                                Some (tt, StringMap.add
                                            mod_part (mem_int _ res_mod')
                                            (StringMap.add
                                               div_part (mem_int _ res_div')
                                               ctx))
                      | Z_add_with_get_carry lgs
                        => fun _ '(mod_part, div_part, (existT x_sz x, existT y_sz y, existT z_sz z))
                           => let '(res_mod, res_div) := Z.add_with_get_carry lgs (int.value x) (int.value y) (int.value z) in
                              (* TODO: Perform type promotion on the integer type [sz] *)
                              let sz_out_mod := admit in
                              let sz_out_div := admit in
                              res_mod' <- int.maybe_Build_int (int.to_zrange sz_out_mod) res_mod;
                                res_div' <- int.maybe_Build_int (int.to_zrange sz_out_div) res_div;
                                (* TODO: decide what type [res] should go in, figure out whether or not behavior is undefined, etc; return [None] if needed *)
                                Some (tt, StringMap.add
                                            mod_part (mem_int _ res_mod')
                                            (StringMap.add
                                               div_part (mem_int _ res_div')
                                               ctx))
                      | Z_sub_with_get_borrow lgs
                        => fun _ '(mod_part, div_part, (existT x_sz x, existT y_sz y, existT z_sz z))
                           => let '(res_mod, res_div) := Z.sub_with_get_borrow lgs (int.value x) (int.value y) (int.value z) in
                              (* TODO: Perform type promotion on the integer type [sz] *)
                              let sz_out_mod := admit in
                              let sz_out_div := admit in
                              res_mod' <- int.maybe_Build_int (int.to_zrange sz_out_mod) res_mod;
                                res_div' <- int.maybe_Build_int (int.to_zrange sz_out_div) res_div;
                                (* TODO: decide what type [res] should go in, figure out whether or not behavior is undefined, etc; return [None] if needed *)
                                Some (tt, StringMap.add
                                            mod_part (mem_int _ res_mod')
                                            (StringMap.add
                                               div_part (mem_int _ res_div')
                                               ctx))
                      | Z_zselect ty
                        => fun _ '(res_name, (existT x_sz x, existT y_sz y, existT z_sz z))
                           => let res := Z.zselect (int.value x) (int.value y) (int.value z) in
                              (* TODO: Perform type promotion on the integer type [sz] *)
                              let sz_out := admit in
                              res' <- int.maybe_Build_int (int.to_zrange sz_out) res;
                                (* TODO: decide what type [res] should go in, figure out whether or not behavior is undefined, etc; return [None] if needed *)
                                Some (tt, StringMap.add res_name (mem_int _ res') ctx)
                      | Z_add_modulo
                        => fun _ '(existT x_sz x, existT y_sz y, existT z_sz z)
                           => let res := Z.add_modulo (int.value x) (int.value y) (int.value z) in
                              (* TODO: Perform type promotion on the integer type [sz] *)
                              let sz_out := admit in
                              res' <- int.maybe_Build_int (int.to_zrange sz_out) res;
                                (* TODO: decide what type [res] should go in, figure out whether or not behavior is undefined, etc; return [None] if needed *)
                                Some (existT _ _ res', ctx)
                      | Z_static_cast ty
                        => fun _ '(existT x_sz x)
                           => x' <- int.opt_static_cast x;
                                Some (existT _ ty x', ctx)
                      end arg arg_value
               | Var type.Z v
                 => v' <- StringMap.find v ctx;
                      match v' with
                      | mem_int sz v'' => Some (existT _ sz v'', ctx)
                      | mem_int_array _ _ => None
                      end
               | Var type.Zptr v => Some (v, ctx)
               | Pair A B a b
                 => a' <- @interp_arith_expr ctx A a;
                      let '(a', ctx) := a' in
                      b' <- @interp_arith_expr ctx B b;
                        let '(b', ctx) := b' in
                        Some ((a', b'), ctx)
               | TT => Some (tt, ctx)
               end%option;
          cbn [type.interp primitive.interp] in *; cbv [primitive.interp] in *.
      Defined.

      Definition interp_stmt
                 (code : stmt)
        : StringMap.t memory_value -> option (StringMap.t memory_value)
        := match code with
           | Call val
             => fun ctx
                => option_map snd (interp_arith_expr ctx val)
           | Assign declare type.Z sz name val
             => fun ctx
                => val <- interp_arith_expr ctx val;
                     let '(existT t val, ctx) := val in
                     (* TODO: should we care about the semantics of [declare]? *)
                     Some (StringMap.add name (mem_int t val) ctx)
           | Assign declare type.Zptr sz name val
             => fun ctx
                => val <- interp_arith_expr ctx val;
                     let '(name', ctx) := val in
                     val' <- StringMap.find name' ctx;
                       (* TODO: should we care about the semantics of [declare]? *)
                       (* TODO: What are the semantics here? *)
                       (* N.B. I don't think we use this case at all in the translation to C; should we remove it? *)
                       None
           | AssignZPtr name sz val
             => fun ctx
                => val <- interp_arith_expr ctx val;
                     let '(val, ctx) := val in
                     Some (StringMap.add name (mem_int _ (projT2 val)) ctx)
           | DeclareVar t sz name
             => fun ctx
                => (* TODO: should we mark somehow that [name] has been declared? *)
                  Some ctx
           | AssignNth name n val
             => fun ctx
                => val <- interp_arith_expr ctx val;
                     let '(val, ctx) := val in
                     mem_val <- StringMap.find name ctx;
                       match mem_val with
                       | mem_int_array t ls
                         => if (List.length ls <=? n)%nat
                            then None
                            else val <- int.opt_implicit_cast (projT2 val);
                              Some (StringMap.add name (mem_int_array t (ListUtil.set_nth n val ls)) ctx)
                       | mem_int _ _ => None
                       end
           end%option.

      Fixpoint interp_expr
               (ctx : StringMap.t memory_value)
               (e : expr)
        : option (StringMap.t memory_value)
        := match e with
           | nil => Some ctx
           | code :: rest
             => ctx' <- interp_stmt code ctx;
                  interp_expr ctx' rest
           end%option.
    End C.
  End ToString.
End Compilers.
