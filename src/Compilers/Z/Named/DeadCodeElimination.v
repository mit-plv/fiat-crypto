Require Import Coq.PArith.BinPos.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.DeadCodeElimination.
Require Import Crypto.Compilers.Z.Syntax.

Section language.
  Context {Name : Type}
          {Context : Context Name (fun _ : base_type => positive)}.

  Definition EliminateDeadCode {t} e ls
    := @EliminateDeadCode base_type op Name _ internal_base_type_dec_bl Context t e ls.
  Definition CompileAndEliminateDeadCode {t} e ls
    := @CompileAndEliminateDeadCode base_type op Name _ internal_base_type_dec_bl Context t e ls.
End language.
