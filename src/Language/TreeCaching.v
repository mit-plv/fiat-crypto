(** * Tree Caching for PHOAS Expressions *)
(** The naive encoding of PHOAS passes that need to produce both
    [expr]-like output and data-like output simultaneously involves
    exponential blowup.

    This file allows caching of results (and/or intermediates) of a
    data-producing PHOAS pass in a tree structure that mimics the
    PHOAS expression so that a subsequent pass can consume this tree
    and a PHOAS expression to produce a new expression.

    More concretely, suppose we are trying to write a pass that is
    [expr var1 * expr var2 -> A * expr var3]. We can define an
    [expr]-like-tree-structure that (a) doesn't use higher-order
    things for [Abs] nodes, and (b) stores [A] at every node. Then we
    can write a pass that is [expr var1 * expr var2 -> A * tree-of-A]
    and then [expr var1 * expr var2 * tree-of-A -> expr var3] such
    that we incur only linear overhead.

    See also
    %\href{https://github.com/mit-plv/fiat-crypto/issues/1604#issuecomment-1553341559}{mit-plv/fiat-crypto\#1604 with option (2)}%
    #<a href=https://github.com/mit-plv/fiat-crypto/issues/1604##issuecomment-1553341559">mit-plv/fiat-crypto##1604 with option (2)</a>#
    and
    %\href{https://github.com/mit-plv/fiat-crypto/issues/1761}{mit-plv/fiat-crypto\#1761}%
    #<a href=https://github.com/mit-plv/fiat-crypto/issues/1761#">mit-plv/fiat-crypto##1761</a>#. *)

Require Import Rewriter.Language.Language.

Module Compilers.
  Export Language.Compilers.
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.

  Module tree_nd.
    Section with_result.
      Context {base_type : Type}.
      Local Notation type := (type base_type).
      Context {ident : type -> Type}
              {result : Type}.
      Local Notation expr := (@expr.expr base_type ident).

      Inductive tree : Type :=
      | Ident (r : result) : tree
      | Var  (r : result) : tree
      | Abs (r : result) (f : option tree) : tree
      | App (r : result) (f : option tree) (x : option tree) : tree
      | LetIn (r : result) (x : option tree) (f : option tree) : tree
      .
    End with_result.
    Global Arguments tree result : clear implicits, assert.
  End tree_nd.

  Module tree.
    Section with_result.
      Context {base_type : Type}.
      Local Notation type := (type base_type).
      Context {ident : type -> Type}
              {result : type -> Type}.
      Local Notation expr := (@expr.expr base_type ident).

      Inductive tree : type -> Type :=
      | Ident {t} (r : result t) : tree t
      | Var {t} (r : result t) : tree t
      | Abs {s d} (r : result (s -> d)) (f : option (tree d)) : tree (s -> d)
      | App {s d} (r : result d) (f : option (tree (s -> d))) (x : option (tree s)) : tree d
      | LetIn {A B} (r : result B) (x : option (tree A)) (f : option (tree B)) : tree B
      .
    End with_result.
    Global Arguments tree {base_type} {result} t, {base_type} result t : assert.
  End tree.
End Compilers.
