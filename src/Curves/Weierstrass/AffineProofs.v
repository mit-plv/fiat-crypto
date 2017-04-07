Require Import Coq.Numbers.BinNums.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Spec.WeierstrassCurve Crypto.Curves.Weierstrass.Affine.
Require Import Crypto.Algebra.Field Crypto.Algebra.Hierarchy.
Require Import Crypto.Util.Decidable Crypto.Util.Tactics.DestructHead Crypto.Util.Tactics.BreakMatch.
Require Import Coq.PArith.BinPos.

Module W.
  Section W.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b:F}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Feq_dec:DecidableRel Feq}
            {char_ge_12:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12%positive}. (* FIXME: shouldn't need we need 4, not 12? *)
    Let char_ge_3 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 3.
    Proof. eapply Algebra.Hierarchy.char_ge_weaken; eauto; vm_decide. Qed.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "-" := Fsub. Local Infix "*" := Fmul.
    Local Notation "4" := (1+1+1+1). Local Notation "27" := (4*4 + 4+4 +1+1+1).

    Global Instance commutative_group {discriminant_nonzero:id(4*a*a*a + 27*b*b <> 0)} : abelian_group(eq:=W.eq(a:=a)(b:=b))(op:=W.add(char_ge_3:=char_ge_3))(id:=W.zero)(inv:=W.opp).
    Proof using Type.
      Time
        repeat match goal with
               | _ => solve [ contradiction | trivial | exact _ ]
               | _ => intro
               | |- Equivalence _ => split
               | |- abelian_group => split | |- group => split | |- monoid => split
               | |- is_associative => split | |- is_commutative => split
               | |- is_left_inverse => split | |- is_right_inverse => split
               | |- is_left_identity => split | |- is_right_identity => split
               | _ => progress destruct_head' @W.point
               | _ => progress destruct_head' sum
               | _ => progress destruct_head' prod
               | _ => progress destruct_head' unit
               | _ => progress destruct_head' and
               | _ => progress cbv [W.opp W.eq W.zero W.add W.coordinates proj1_sig]in*
               | _ => progress break_match
               end.
      (* Finished transaction in 2.098 secs (2.099u,0.s) (successful) *)
      all:  try split.
      (* Finished transaction in 0.052 secs (0.053u,0.s) (successful) *)

      (* The [discriminant_nonzero] hypothesis makes [fsatz] slow but
      is necessary in some cases. Thus, we wrap it in [id] by detault
      to hide it from [nsatz] but unfold it when normal [fsatz] fails. *)
      (* Variable re-ordering is a micro-optimization *)
      (* TODO: why does par not work here? *)
      Ltac s := abstract (
                    match goal with [H:id _ |- _] => move H at bottom end;
                    move b at bottom;
                    move a at bottom;
                    repeat match goal with [H: ?x = Fopp ?y |- _] => is_var x; is_var y; revert H end; intros;
                    repeat match goal with [H: ?x = ?y |- _] => is_var x; is_var y; revert H end; intros;
                    repeat split;
                    solve
                      [ fsatz
                      | cbv [id] in *; fsatz]
                  ).
      Time s. (* Finished transaction in 0.099 secs (0.096u,0.003s) (successful) *)
      Time s. (* Finished transaction in 0.094 secs (0.093u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.48 secs (0.48u,0.s) (successful) *)
      Time s. (* Finished transaction in 2.229 secs (2.226u,0.003s) (successful) *)
      Time s. (* Finished transaction in 3.164 secs (3.153u,0.01s) (successful) *)
      Time s. (* Finished transaction in 2.218 secs (2.199u,0.019s) (successful) *)
      Time s. (* Finished transaction in 3.499 secs (3.486u,0.01s) (successful) *)
      Time s. (* Finished transaction in 1.164 secs (1.16u,0.003s) (successful) *)
      Time s. (* Finished transaction in 1.971 secs (1.953u,0.016s) (successful) *)
      Time s. (* Finished transaction in 2.344 secs (2.343u,0.003s) (successful) *)
      Time s. (* Finished transaction in 1.287 secs (1.286u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.781 secs (1.783u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.497 secs (0.496u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.859 secs (1.856u,0.003s) (successful) *)
      Time s. (* Finished transaction in 1.499 secs (1.499u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.6 secs (1.6u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.446 secs (1.443u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.56 secs (1.563u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.62 secs (1.616u,0.003s) (successful) *)
      Time s. (* Finished transaction in 1.973 secs (1.966u,0.006s) (successful) *)
      Time s. (* Finished transaction in 7.66 secs (7.663u,0.s) (successful) *)
      Time s. (* Finished transaction in 7.645 secs (7.643u,0.003s) (successful) *)
      Time s. (* Finished transaction in 5.956 secs (5.949u,0.006s) (successful) *)
      Time s. (* Finished transaction in 7.835 secs (7.803u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.893 secs (1.893u,0.s) (successful) *)
      Time s. (* Finished transaction in 10.23 secs (10.229u,0.003s) (successful) *)
      Time s. (* Finished transaction in 11.059 secs (11.036u,0.02s) (successful) *)
      Time s. (* Finished transaction in 8.965 secs (8.963u,0.s) (successful) *)
      Time s. (* Finished transaction in 9.539 secs (9.539u,0.003s) (successful) *)
      Time s. (* Finished transaction in 2.019 secs (2.013u,0.003s) (successful) *)
      Time s. (* Finished transaction in 2.907 secs (2.9u,0.01s) (successful) *)
      Time s. (* Finished transaction in 1.622 secs (1.613u,0.01s) (successful) *)
      Time s. (* Finished transaction in 13.205 secs (13.203u,0.003s) (successful) *)
      Time s. (* Finished transaction in 14.689 secs (14.686u,0.s) (successful) *)
      Time s. (* Finished transaction in 10.672 secs (10.673u,0.s) (successful) *)
      Time s. (* Finished transaction in 13.509 secs (13.509u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.389 secs (1.386u,0.003s) (successful) *)
      Time s. (* Finished transaction in 10.331 secs (10.329u,0.003s) (successful) *)
      Time s. (* Finished transaction in 12.182 secs (12.176u,0.006s) (successful) *)
      Time s. (* Finished transaction in 9.826 secs (9.829u,0.s) (successful) *)
      Time s. (* Finished transaction in 13.709 secs (13.703u,0.003s) (successful) *)
      Time s. (* Finished transaction in 1.059 secs (1.06u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.894 secs (1.896u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.358 secs (1.356u,0.003s) (successful) *)
      Time s. (* Finished transaction in 1.537 secs (1.536u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.342 secs (1.343u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.095 secs (1.096u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.157 secs (1.153u,0.003s) (successful) *)
      Time s. (* Finished transaction in 1.603 secs (1.603u,0.s) (successful) *)
      Time s. (* Finished transaction in 6.196 secs (6.196u,0.s) (successful) *)
      Time s. (* Finished transaction in 6.949 secs (6.949u,0.s) (successful) *)
      Time s. (* Finished transaction in 4.685 secs (4.68u,0.006s) (successful) *)
      Time s. (* Finished transaction in 6.483 secs (6.483u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.451 secs (1.453u,0.s) (successful) *)
      Time s. (* Finished transaction in 13.648 secs (13.646u,0.s) (successful) *)
      Time s. (* Finished transaction in 18.053 secs (18.056u,0.s) (successful) *)
      Time s. (* Finished transaction in 7.186 secs (7.186u,0.s) (successful) *)
      Time s. (* Finished transaction in 8.817 secs (8.819u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.251 secs (1.25u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.569 secs (1.569u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.356 secs (1.356u,0.s) (successful) *)
      Time s. (* Finished transaction in 11.45 secs (11.446u,0.003s) (successful) *)
      Time s. (* Finished transaction in 17.968 secs (17.969u,0.003s) (successful) *)
      Time s. (* Finished transaction in 12.418 secs (12.366u,0.046s) (successful) *)
      Time s. (* Finished transaction in 15.323 secs (15.316u,0.01s) (successful) *)
      Time s. (* Finished transaction in 1.589 secs (1.586u,0.003s) (successful) *)
      Time s. (* Finished transaction in 10.22 secs (10.223u,0.s) (successful) *)
      Time s. (* Finished transaction in 11.887 secs (11.889u,0.s) (successful) *)
      Time s. (* Finished transaction in 7.284 secs (7.283u,0.003s) (successful) *)
      Time s. (* Finished transaction in 8.75 secs (8.753u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.291 secs (0.29u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.348 secs (0.346u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.222 secs (0.223u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.266 secs (0.266u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.296 secs (0.296u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.737 secs (0.736u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.227 secs (0.226u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.269 secs (0.269u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.054 secs (0.056u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.057 secs (0.056u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.308 secs (0.309u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.362 secs (0.363u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.226 secs (0.226u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.279 secs (0.279u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.055 secs (0.053u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.052 secs (0.053u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.057 secs (0.06u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.053 secs (0.053u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.052 secs (0.049u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.053 secs (0.056u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.055 secs (0.053u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.053 secs (0.053u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.2 secs (0.203u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.21 secs (0.21u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.208 secs (0.206u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.162 secs (1.163u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.256 secs (1.256u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.994 secs (0.996u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.017 secs (1.016u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.186 secs (0.186u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.044 secs (1.043u,0.s) (successful) *)
      Time s. (* Finished transaction in 1.123 secs (1.123u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.892 secs (0.889u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.961 secs (0.963u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.051 secs (0.05u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.052 secs (0.053u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.085 secs (0.086u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.081 secs (0.08u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.12 secs (0.119u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.116 secs (0.12u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.074 secs (0.073u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.067 secs (0.066u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.07 secs (0.073u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.063 secs (0.063u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.083 secs (0.083u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.084 secs (0.083u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.106 secs (0.106u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.097 secs (0.096u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.108 secs (0.106u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.658 secs (0.66u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.775 secs (0.773u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.527 secs (0.526u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.625 secs (0.623u,0.003s) (successful) *)
      Time s. (* Finished transaction in 0.106 secs (0.106u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.586 secs (0.586u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.687 secs (0.686u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.189 secs (0.189u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.21 secs (0.209u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.066 secs (0.066u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.078 secs (0.08u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.083 secs (0.083u,0.s) (successful) *)
      Time s. (* Finished transaction in 0.068 secs (0.066u,0.s) (successful) *)
      (* Total: 414.396 seconds, roughly 7 minutes*)

    Time Qed. (* Finished transaction in 390.998 secs (390.783u,0.276s) (successful) *)
  End W.
End W.
