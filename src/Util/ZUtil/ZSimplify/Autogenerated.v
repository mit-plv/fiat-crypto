Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Local Open Scope Z_scope.

Module Z.
  Local Ltac simplify_div_tac :=
    intros; Z.div_mod_to_quot_rem; nia.
  (* Naming Convention: [X] for thing being divided by, [p] for plus,
     [m] for minus, [d] for div, and [_] to separate parentheses and
     multiplication. *)
  (* Mathematica code to generate these hints:
<<
ClearAll[minus, plus, div, mul, combine, parens, ExprToString,
  ExprToExpr, ExprToName, SymbolsIn, Chars, RestFrom, a, b, c, d, e,
  f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, X];
Chars = StringSplit["abcdefghijklmnopqrstuvwxyz", ""];
RestFrom[i_, len_] :=
 Join[{mul[Chars[[i]], "X"]}, Take[Drop[Chars, i], len]]
Exprs = Flatten[
   Map[{#1, #1 /. mul[a_, "X", b___] :> mul["X", a, b]} &, Flatten[{
      Table[
       Table[div[
         combine @@
          Join[Take[Chars, start - 1], RestFrom[start, len]],
         "X"], {len, 0, 10 - start}], {start, 1, 2}],
      Table[
       Table[div[
         combine["a",
          parens @@
           Join[Take[Drop[Chars, 1], start - 1],
            RestFrom[1 + start, len]]], "X"], {len, 0,
         10 - start}], {start, 1, 2}],
      div[combine["a", parens["b", parens["c", mul["d", "X"]], "e"]],
       "X"],
      div[combine["a", "b", parens["c", mul["d", "X"]], "e"], "X"],
      div[combine["a", "b", mul["c", "X", "d"], "e", "f"], "X"],
      div[combine["a", mul["b", "X", "c"], "d", "e"], "X"],
      div[
       combine["a",
        parens["b", parens["c", mul["d", "X", "e"]], "f"]], "X"],
      div[combine["a", parens["b", mul["c", "X", "d"]], "e"], "X"]}]]];
ExprToString[div[x_, y_], withparen_: False] :=
 With[{v := ExprToString[x, True] <> " / " <> ExprToString[y, True]},
  If[withparen, "(" <> v <> ")", v]]
ExprToString[combine[x_], withparen_: False] :=
 ExprToString[x, withparen]
ExprToString[combine[x_, minus, y__], withparen_: False] :=
 With[{v :=
    ExprToString[x, False] <> " - " <>
     ExprToString[combine[y], False]},
  If[withparen, "(" <> v <> ")", v]]
ExprToString[combine[minus, y__], withparen_: False] :=
 With[{v := "-" <> ExprToString[combine[y], False]},
  If[withparen, "(" <> v <> ")", v]]
ExprToString[combine[x_, y__], withparen_: False] :=
 With[{v :=
    ExprToString[x, False] <> " + " <>
     ExprToString[combine[y], False]},
  If[withparen, "(" <> v <> ")", v]]
ExprToString[mul[x_], withparen_: False] := ExprToString[x]
ExprToString[mul[x_, y__], withparen_: False] :=
 With[{v :=
    ExprToString[x, False] <> " * " <> ExprToString[mul[y], False]},
  If[withparen, "(" <> v <> ")", v]]
ExprToString[parens[x__], withparen_: False] :=
 "(" <> ExprToString[combine[x]] <> ")"
ExprToString[x_String, withparen_: False] := x
ExprToExpr[div[x__]] := Divide @@ Map[ExprToExpr, {x}]
ExprToExpr[mul[x__]] := Times @@ Map[ExprToExpr, {x}]
ExprToExpr[combine[]] := 0
ExprToExpr[combine[minus, y_, z___]] := -ExprToExpr[y] +
  ExprToExpr[combine[z]]
ExprToExpr[combine[x_, y___]] := ExprToExpr[x] + ExprToExpr[combine[y]]
ExprToExpr[parens[x__]] := ExprToExpr[combine[x]]
ExprToExpr[x_String] := Symbol[x]
ExprToName["X", ispos_: True] := If[ispos, "X", "mX"]
ExprToName[x_String, ispos_: True] := If[ispos, "p", "m"]
ExprToName[div[x_, y_], ispos_: True] :=
 If[ispos, "p", "m"] <> ExprToName[x] <> "d" <> ExprToName[y]
ExprToName[mul[x_], ispos_: True] :=
 If[ispos, "", "m_"] <> ExprToName[x] <> "_"
ExprToName[mul[x_, y__], ispos_: True] :=
 If[ispos, "", "m_"] <> ExprToName[x] <> ExprToName[mul[y]]
ExprToName[combine[], ispos_: True] := ""
ExprToName[combine[x_], ispos_: True] := ExprToName[x, ispos]
ExprToName[combine[x_, minus, mul[y__], z___], ispos_: True] :=
 ExprToName[x, ispos] <> "m_" <> ExprToName[mul[y], True] <>
  ExprToName[combine[z], True]
ExprToName[combine[x_, mul[y__], z___], ispos_: True] :=
 ExprToName[x, ispos] <> "p_" <> ExprToName[mul[y], True] <>
  ExprToName[combine[z], True]
ExprToName[combine[x_, y__], ispos_: True] :=
 ExprToName[x, ispos] <> ExprToName[combine[y], True]
ExprToName[combine[x_, minus, y__], ispos_: True] :=
 ExprToName[x, ispos] <> ExprToName[combine[y], True]
ExprToName[combine[x_, y__], ispos_: True] :=
 ExprToName[x, ispos] <> ExprToName[combine[y], True]
ExprToName[parens[x__], ispos_: True] :=
 "_o_" <> ExprToName[combine[x], ispos] <> "_c_"
SymbolsIn[x_String] := {x <> " "}
SymbolsIn[f_[y___]] := Join @@ Map[SymbolsIn, {y}]
StringJoin @@
 Map[{"  Lemma simplify_div_" <> ExprToName[#1] <> " " <>
     StringJoin @@ Sort[DeleteDuplicates[SymbolsIn[#1]]] <>
     ": X <> 0 -> " <> ExprToString[#1] <> " = " <>
     StringReplace[(FullSimplify[ExprToExpr[#1]] // InputForm //
        ToString), "/" -> " / "] <> "." <>
     "\n  Proof. simplify_div_tac. Qed.\n  Hint Rewrite \
simplify_div_" <> ExprToName[#1] <>
     " using zutil_arith : zsimplify.\n"} &, Exprs]
>> *)
  Lemma simplify_div_ppX_dX a X : X <> 0 -> (a * X) / X = a.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_dX a X : X <> 0 -> (X * a) / X = a.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_dX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_pdX a b X : X <> 0 -> (a * X + b) / X = a + b / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_pdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_pdX a b X : X <> 0 -> (X * a + b) / X = a + b / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_pdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_ppdX a b c X : X <> 0 -> (a * X + b + c) / X = a + (b + c) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_ppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_ppdX a b c X : X <> 0 -> (X * a + b + c) / X = a + (b + c) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_ppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_pppdX a b c d X : X <> 0 -> (a * X + b + c + d) / X = a + (b + c + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_pppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_pppdX a b c d X : X <> 0 -> (X * a + b + c + d) / X = a + (b + c + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_pppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_ppppdX a b c d e X : X <> 0 -> (a * X + b + c + d + e) / X = a + (b + c + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_ppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_ppppdX a b c d e X : X <> 0 -> (X * a + b + c + d + e) / X = a + (b + c + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_ppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_pppppdX a b c d e f X : X <> 0 -> (a * X + b + c + d + e + f) / X = a + (b + c + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_pppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_pppppdX a b c d e f X : X <> 0 -> (X * a + b + c + d + e + f) / X = a + (b + c + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_pppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_ppppppdX a b c d e f g X : X <> 0 -> (a * X + b + c + d + e + f + g) / X = a + (b + c + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_ppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_ppppppdX a b c d e f g X : X <> 0 -> (X * a + b + c + d + e + f + g) / X = a + (b + c + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_ppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_pppppppdX a b c d e f g h X : X <> 0 -> (a * X + b + c + d + e + f + g + h) / X = a + (b + c + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_pppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_pppppppdX a b c d e f g h X : X <> 0 -> (X * a + b + c + d + e + f + g + h) / X = a + (b + c + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_pppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_ppppppppdX a b c d e f g h i X : X <> 0 -> (a * X + b + c + d + e + f + g + h + i) / X = a + (b + c + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_ppppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_ppppppppdX a b c d e f g h i X : X <> 0 -> (X * a + b + c + d + e + f + g + h + i) / X = a + (b + c + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_ppppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_pppppppppdX a b c d e f g h i j X : X <> 0 -> (a * X + b + c + d + e + f + g + h + i + j) / X = a + (b + c + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_pppppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_pppppppppdX a b c d e f g h i j X : X <> 0 -> (X * a + b + c + d + e + f + g + h + i + j) / X = a + (b + c + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_pppppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_dX a b X : X <> 0 -> (a + b * X) / X = b + a / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_dX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_dX a b X : X <> 0 -> (a + X * b) / X = b + a / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_dX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_pdX a b c X : X <> 0 -> (a + b * X + c) / X = b + (a + c) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_pdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_pdX a b c X : X <> 0 -> (a + X * b + c) / X = b + (a + c) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_pdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_ppdX a b c d X : X <> 0 -> (a + b * X + c + d) / X = b + (a + c + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_ppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_ppdX a b c d X : X <> 0 -> (a + X * b + c + d) / X = b + (a + c + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_ppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_pppdX a b c d e X : X <> 0 -> (a + b * X + c + d + e) / X = b + (a + c + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_pppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_pppdX a b c d e X : X <> 0 -> (a + X * b + c + d + e) / X = b + (a + c + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_pppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_ppppdX a b c d e f X : X <> 0 -> (a + b * X + c + d + e + f) / X = b + (a + c + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_ppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_ppppdX a b c d e f X : X <> 0 -> (a + X * b + c + d + e + f) / X = b + (a + c + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_ppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_pppppdX a b c d e f g X : X <> 0 -> (a + b * X + c + d + e + f + g) / X = b + (a + c + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_pppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_pppppdX a b c d e f g X : X <> 0 -> (a + X * b + c + d + e + f + g) / X = b + (a + c + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_pppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_ppppppdX a b c d e f g h X : X <> 0 -> (a + b * X + c + d + e + f + g + h) / X = b + (a + c + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_ppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_ppppppdX a b c d e f g h X : X <> 0 -> (a + X * b + c + d + e + f + g + h) / X = b + (a + c + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_ppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_pppppppdX a b c d e f g h i X : X <> 0 -> (a + b * X + c + d + e + f + g + h + i) / X = b + (a + c + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_pppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_pppppppdX a b c d e f g h i X : X <> 0 -> (a + X * b + c + d + e + f + g + h + i) / X = b + (a + c + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_pppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_ppppppppdX a b c d e f g h i j X : X <> 0 -> (a + b * X + c + d + e + f + g + h + i + j) / X = b + (a + c + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_ppppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_ppppppppdX a b c d e f g h i j X : X <> 0 -> (a + X * b + c + d + e + f + g + h + i + j) / X = b + (a + c + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_ppppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX__c_dX a b X : X <> 0 -> (a + (b * X)) / X = b + a / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX__c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp__c_dX a b X : X <> 0 -> (a + (X * b)) / X = b + a / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp__c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_p_c_dX a b c X : X <> 0 -> (a + (b * X + c)) / X = b + (a + c) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_p_c_dX a b c X : X <> 0 -> (a + (X * b + c)) / X = b + (a + c) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_pp_c_dX a b c d X : X <> 0 -> (a + (b * X + c + d)) / X = b + (a + c + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_pp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_pp_c_dX a b c d X : X <> 0 -> (a + (X * b + c + d)) / X = b + (a + c + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_pp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_ppp_c_dX a b c d e X : X <> 0 -> (a + (b * X + c + d + e)) / X = b + (a + c + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_ppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_ppp_c_dX a b c d e X : X <> 0 -> (a + (X * b + c + d + e)) / X = b + (a + c + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_ppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_pppp_c_dX a b c d e f X : X <> 0 -> (a + (b * X + c + d + e + f)) / X = b + (a + c + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_pppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_pppp_c_dX a b c d e f X : X <> 0 -> (a + (X * b + c + d + e + f)) / X = b + (a + c + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_pppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_ppppp_c_dX a b c d e f g X : X <> 0 -> (a + (b * X + c + d + e + f + g)) / X = b + (a + c + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_ppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_ppppp_c_dX a b c d e f g X : X <> 0 -> (a + (X * b + c + d + e + f + g)) / X = b + (a + c + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_ppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_pppppp_c_dX a b c d e f g h X : X <> 0 -> (a + (b * X + c + d + e + f + g + h)) / X = b + (a + c + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_pppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_pppppp_c_dX a b c d e f g h X : X <> 0 -> (a + (X * b + c + d + e + f + g + h)) / X = b + (a + c + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_pppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_ppppppp_c_dX a b c d e f g h i X : X <> 0 -> (a + (b * X + c + d + e + f + g + h + i)) / X = b + (a + c + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_ppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_ppppppp_c_dX a b c d e f g h i X : X <> 0 -> (a + (X * b + c + d + e + f + g + h + i)) / X = b + (a + c + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_ppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_pppppppp_c_dX a b c d e f g h i j X : X <> 0 -> (a + (b * X + c + d + e + f + g + h + i + j)) / X = b + (a + c + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_pppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_pppppppp_c_dX a b c d e f g h i j X : X <> 0 -> (a + (X * b + c + d + e + f + g + h + i + j)) / X = b + (a + c + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_pppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_ppppppppp_c_dX a b c d e f g h i j k X : X <> 0 -> (a + (b * X + c + d + e + f + g + h + i + j + k)) / X = b + (a + c + d + e + f + g + h + i + j + k) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_ppppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_ppppppppp_c_dX a b c d e f g h i j k X : X <> 0 -> (a + (X * b + c + d + e + f + g + h + i + j + k)) / X = b + (a + c + d + e + f + g + h + i + j + k) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_ppppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX__c_dX a b c X : X <> 0 -> (a + (b + c * X)) / X = c + (a + b) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX__c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp__c_dX a b c X : X <> 0 -> (a + (b + X * c)) / X = c + (a + b) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp__c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_p_c_dX a b c d X : X <> 0 -> (a + (b + c * X + d)) / X = c + (a + b + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_p_c_dX a b c d X : X <> 0 -> (a + (b + X * c + d)) / X = c + (a + b + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_pp_c_dX a b c d e X : X <> 0 -> (a + (b + c * X + d + e)) / X = c + (a + b + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_pp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_pp_c_dX a b c d e X : X <> 0 -> (a + (b + X * c + d + e)) / X = c + (a + b + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_pp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_ppp_c_dX a b c d e f X : X <> 0 -> (a + (b + c * X + d + e + f)) / X = c + (a + b + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_ppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_ppp_c_dX a b c d e f X : X <> 0 -> (a + (b + X * c + d + e + f)) / X = c + (a + b + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_ppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_pppp_c_dX a b c d e f g X : X <> 0 -> (a + (b + c * X + d + e + f + g)) / X = c + (a + b + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_pppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_pppp_c_dX a b c d e f g X : X <> 0 -> (a + (b + X * c + d + e + f + g)) / X = c + (a + b + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_pppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_ppppp_c_dX a b c d e f g h X : X <> 0 -> (a + (b + c * X + d + e + f + g + h)) / X = c + (a + b + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_ppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_ppppp_c_dX a b c d e f g h X : X <> 0 -> (a + (b + X * c + d + e + f + g + h)) / X = c + (a + b + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_ppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_pppppp_c_dX a b c d e f g h i X : X <> 0 -> (a + (b + c * X + d + e + f + g + h + i)) / X = c + (a + b + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_pppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_pppppp_c_dX a b c d e f g h i X : X <> 0 -> (a + (b + X * c + d + e + f + g + h + i)) / X = c + (a + b + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_pppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_ppppppp_c_dX a b c d e f g h i j X : X <> 0 -> (a + (b + c * X + d + e + f + g + h + i + j)) / X = c + (a + b + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_ppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_ppppppp_c_dX a b c d e f g h i j X : X <> 0 -> (a + (b + X * c + d + e + f + g + h + i + j)) / X = c + (a + b + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_ppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_pppppppp_c_dX a b c d e f g h i j k X : X <> 0 -> (a + (b + c * X + d + e + f + g + h + i + j + k)) / X = c + (a + b + d + e + f + g + h + i + j + k) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_pppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_pppppppp_c_dX a b c d e f g h i j k X : X <> 0 -> (a + (b + X * c + d + e + f + g + h + i + j + k)) / X = c + (a + b + d + e + f + g + h + i + j + k) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_pppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_p_o_pp_pX__c_p_c_dX a b c d e X : X <> 0 -> (a + (b + (c + d * X) + e)) / X = d + (a + b + c + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_p_o_pp_pX__c_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_p_o_pp_Xp__c_p_c_dX a b c d e X : X <> 0 -> (a + (b + (c + X * d) + e)) / X = d + (a + b + c + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_p_o_pp_Xp__c_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_o_pp_pX__c_pdX a b c d e X : X <> 0 -> (a + b + (c + d * X) + e) / X = d + (a + b + c + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_o_pp_pX__c_pdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_o_pp_Xp__c_pdX a b c d e X : X <> 0 -> (a + b + (c + X * d) + e) / X = d + (a + b + c + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_o_pp_Xp__c_pdX using zutil_arith : zsimplify.
  Lemma simplify_div_pppp_pXp_ppdX a b c d e f X : X <> 0 -> (a + b + c * X * d + e + f) / X = (a + b + e + f + c*d*X) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pppp_pXp_ppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pppp_Xpp_ppdX a b c d e f X : X <> 0 -> (a + b + X * c * d + e + f) / X = (a + b + e + f + c*d*X) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pppp_Xpp_ppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pXp_ppdX a b c d e X : X <> 0 -> (a + b * X * c + d + e) / X = (a + d + e + b*c*X) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pXp_ppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xpp_ppdX a b c d e X : X <> 0 -> (a + X * b * c + d + e) / X = (a + d + e + b*c*X) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xpp_ppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_p_o_pp_pXp__c_p_c_dX a b c d e f X : X <> 0 -> (a + (b + (c + d * X * e) + f)) / X = (a + b + c + f + d*e*X) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_p_o_pp_pXp__c_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_p_o_pp_Xpp__c_p_c_dX a b c d e f X : X <> 0 -> (a + (b + (c + X * d * e) + f)) / X = (a + b + c + f + d*e*X) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_p_o_pp_Xpp__c_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pXp__c_pdX a b c d e X : X <> 0 -> (a + (b + c * X * d) + e) / X = (a + b + e + c*d*X) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pXp__c_pdX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xpp__c_pdX a b c d e X : X <> 0 -> (a + (b + X * c * d) + e) / X = (a + b + e + c*d*X) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xpp__c_pdX using zutil_arith : zsimplify.


  (* Naming convention: [X] for thing being aggregated, [p] for plus,
     [m] for minus, [_] for parentheses *)
  (* Python code to generate these hints:
<<
#!/usr/bin/env python

def sgn(v):
    if v < 0:
        return -1
    elif v == 0:
        return 0
    elif v > 0:
        return 1

def to_eqn(name):
    vars_left = list('abcdefghijklmnopqrstuvwxyz')
    ret = ''
    close = ''
    while name:
        if name[0] == 'X':
            ret += ' X'
            name = name[1:]
        elif not name[0].isdigit():
            ret += ' ' + vars_left[0]
            vars_left = vars_left[1:]
        if name:
            if name[0] == 'm': ret += ' -'
            elif name[0] == 'p': ret += ' +'
            elif name[0].isdigit(): ret += ' %s *' % name[0]
            name = name[1:]
        if name and name[0] == '_':
            ret += ' ('
            close += ')'
            name = name[1:]
    if ret[-1] != 'X':
        ret += ' ' + vars_left[0]
    return (ret + close).strip().replace('( ', '(')

def simplify(eqn):
    counts = {}
    sign_stack = [1, 1]
    for i in eqn:
        if i == ' ': continue
        elif i == '(': sign_stack.append(sign_stack[-1])
        elif i == ')': sign_stack.pop()
        elif i == '+': sign_stack.append(sgn(sign_stack[-1]))
        elif i == '-': sign_stack.append(-sgn(sign_stack[-1]))
        elif i == '*': continue
        elif i.isdigit(): sign_stack[-1] *= int(i)
        else:
            counts[i] = counts.get(i,0) + sign_stack.pop()
    ret = ''
    for k in sorted(counts.keys()):
        if counts[k] == 1: ret += ' + %s' % k
        elif counts[k] == -1: ret += ' - %s' % k
        elif counts[k] < 0: ret += ' - %d * %s' % (abs(counts[k]), k)
        elif counts[k] > 0: ret += ' + %d * %s' % (abs(counts[k]), k)
    if ret == '': ret = '0'
    return ret.strip(' +')


def to_def(name):
    eqn = to_eqn(name)
    return r'''  Lemma simplify_%s %s X : %s = %s.
  Proof. lia. Qed.
  Hint Rewrite simplify_%s : zsimplify.''' % (name, ' '.join(sorted(set(eqn) - set('*+-() 0123456789X'))), eqn, simplify(eqn), name)

names = []
names += ['%sX%s%sX' % (a, b, c) for a in 'mp' for b in 'mp' for c in 'mp']
names += ['%sX%s_X%s' % (a, b, c) for a in 'mp' for b in 'mp' for c in 'mp']
names += ['X%s%s_X%s' % (a, b, c) for a in 'mp' for b in 'mp' for c in 'mp']
names += ['%sX%s_%sX' % (a, b, c) for a in 'mp' for b in 'mp' for c in 'mp']
names += ['X%s%s_%sX' % (a, b, c) for a in 'mp' for b in 'mp' for c in 'mp']
names += ['m2XpX', 'm2XpXpX']

print(r'''  (* Python code to generate these hints:
<<''')
print(open(__file__).read())
print(r'''
>> *)''')
for name in names:
    print(to_def(name))


>> *)
  Lemma simplify_mXmmX a b X : a - X - b - X = - 2 * X + a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXmmX : zsimplify.
  Lemma simplify_mXmpX a b X : a - X - b + X = a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXmpX : zsimplify.
  Lemma simplify_mXpmX a b X : a - X + b - X = - 2 * X + a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXpmX : zsimplify.
  Lemma simplify_mXppX a b X : a - X + b + X = a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXppX : zsimplify.
  Lemma simplify_pXmmX a b X : a + X - b - X = a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXmmX : zsimplify.
  Lemma simplify_pXmpX a b X : a + X - b + X = 2 * X + a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXmpX : zsimplify.
  Lemma simplify_pXpmX a b X : a + X + b - X = a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXpmX : zsimplify.
  Lemma simplify_pXppX a b X : a + X + b + X = 2 * X + a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXppX : zsimplify.
  Lemma simplify_mXm_Xm a b X : a - X - (X - b) = - 2 * X + a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXm_Xm : zsimplify.
  Lemma simplify_mXm_Xp a b X : a - X - (X + b) = - 2 * X + a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXm_Xp : zsimplify.
  Lemma simplify_mXp_Xm a b X : a - X + (X - b) = a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXp_Xm : zsimplify.
  Lemma simplify_mXp_Xp a b X : a - X + (X + b) = a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXp_Xp : zsimplify.
  Lemma simplify_pXm_Xm a b X : a + X - (X - b) = a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXm_Xm : zsimplify.
  Lemma simplify_pXm_Xp a b X : a + X - (X + b) = a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXm_Xp : zsimplify.
  Lemma simplify_pXp_Xm a b X : a + X + (X - b) = 2 * X + a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXp_Xm : zsimplify.
  Lemma simplify_pXp_Xp a b X : a + X + (X + b) = 2 * X + a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXp_Xp : zsimplify.
  Lemma simplify_Xmm_Xm a b X : X - a - (X - b) = - a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xmm_Xm : zsimplify.
  Lemma simplify_Xmm_Xp a b X : X - a - (X + b) = - a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xmm_Xp : zsimplify.
  Lemma simplify_Xmp_Xm a b X : X - a + (X - b) = 2 * X - a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xmp_Xm : zsimplify.
  Lemma simplify_Xmp_Xp a b X : X - a + (X + b) = 2 * X - a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xmp_Xp : zsimplify.
  Lemma simplify_Xpm_Xm a b X : X + a - (X - b) = a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xpm_Xm : zsimplify.
  Lemma simplify_Xpm_Xp a b X : X + a - (X + b) = a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xpm_Xp : zsimplify.
  Lemma simplify_Xpp_Xm a b X : X + a + (X - b) = 2 * X + a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xpp_Xm : zsimplify.
  Lemma simplify_Xpp_Xp a b X : X + a + (X + b) = 2 * X + a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xpp_Xp : zsimplify.
  Lemma simplify_mXm_mX a b X : a - X - (b - X) = a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXm_mX : zsimplify.
  Lemma simplify_mXm_pX a b X : a - X - (b + X) = - 2 * X + a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXm_pX : zsimplify.
  Lemma simplify_mXp_mX a b X : a - X + (b - X) = - 2 * X + a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXp_mX : zsimplify.
  Lemma simplify_mXp_pX a b X : a - X + (b + X) = a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXp_pX : zsimplify.
  Lemma simplify_pXm_mX a b X : a + X - (b - X) = 2 * X + a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXm_mX : zsimplify.
  Lemma simplify_pXm_pX a b X : a + X - (b + X) = a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXm_pX : zsimplify.
  Lemma simplify_pXp_mX a b X : a + X + (b - X) = a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXp_mX : zsimplify.
  Lemma simplify_pXp_pX a b X : a + X + (b + X) = 2 * X + a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXp_pX : zsimplify.
  Lemma simplify_Xmm_mX a b X : X - a - (b - X) = 2 * X - a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xmm_mX : zsimplify.
  Lemma simplify_Xmm_pX a b X : X - a - (b + X) = - a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xmm_pX : zsimplify.
  Lemma simplify_Xmp_mX a b X : X - a + (b - X) = - a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xmp_mX : zsimplify.
  Lemma simplify_Xmp_pX a b X : X - a + (b + X) = 2 * X - a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xmp_pX : zsimplify.
  Lemma simplify_Xpm_mX a b X : X + a - (b - X) = 2 * X + a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xpm_mX : zsimplify.
  Lemma simplify_Xpm_pX a b X : X + a - (b + X) = a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xpm_pX : zsimplify.
  Lemma simplify_Xpp_mX a b X : X + a + (b - X) = a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xpp_mX : zsimplify.
  Lemma simplify_Xpp_pX a b X : X + a + (b + X) = 2 * X + a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xpp_pX : zsimplify.
  Lemma simplify_m2XpX a X : a - 2 * X + X = - X + a.
  Proof. lia. Qed.
  Hint Rewrite simplify_m2XpX : zsimplify.
  Lemma simplify_m2XpXpX a X : a - 2 * X + X + X = a.
  Proof. lia. Qed.
  Hint Rewrite simplify_m2XpXpX : zsimplify.
End Z.
