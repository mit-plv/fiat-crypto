(** A version of [Rules.v] for testing *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Language.PreExtra.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Local Definition mymap {A B} := Eval cbv in @List.map A B.
Local Definition myapp {A} := Eval cbv in @List.app A.
Local Definition myflatten {A} := Eval cbv in List.fold_right myapp (@nil A).
Local Notation dont_do_again := (pair false) (only parsing).
Local Notation do_again := (pair true) (only parsing).

Local Notation "' x" := (ident.literal x).
Local Notation cstZ r := (ident.cast ('r%zrange)).
Local Notation cstZZ r1 r2 := (ident.cast2 ('(r1%zrange), '(r2%zrange))).
Local Notation "'plet' x := y 'in' z"
  := (match y return _ with x => z end).

Local Notation dlet2_opp2 rv rc e
  := (plet rc' := (-rc)%zrange in
          plet cst' := cstZZ rv rc' in
          plet cst1 := cstZ rv in
          plet cst2 := cstZ rc in
          plet cst2' := cstZ rc' in
          (dlet vc := cst' e in
               (cst1 (fst (cst' vc)), cst2 (-(cst2' (snd (cst' vc))))))).

Local Notation dlet2 rv rc e
  := (dlet vc := cstZZ rv rc e in
          (cstZ rv (fst (cstZZ rv rc vc)),
           cstZ rc (snd (cstZZ rv rc vc)))).


Local Notation "x '\in' y" := (is_bounded_by_bool x (ZRange.normalize y) = true) : zrange_scope.
Local Notation "x ∈ y" := (is_bounded_by_bool x (ZRange.normalize y) = true) : zrange_scope.
Local Notation "x <= y" := (is_tighter_than_bool (ZRange.normalize x) y = true) : zrange_scope.
Local Notation litZZ x := (ident.literal (fst x), ident.literal (snd x)) (only parsing).
Local Notation n r := (ZRange.normalize r) (only parsing).

Definition test_rewrite_rulesT : list (bool * Prop)
  := Eval cbv [myapp mymap myflatten] in
      myflatten
        [mymap
           dont_do_again
           [(forall A B x y, @fst A B (x, y) = x)
            ; (forall A B x y, @snd A B (x, y) = y)
            ; (forall x rx y ry rxy,
                  rx <> ry
                  -> cstZ rxy (cstZ rx x + cstZ ry y)
                     = cstZ rxy (cstZ rx x + cstZ ry y))
           ]
        ].
