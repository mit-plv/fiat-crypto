Require Import Coq.PArith.BinPos.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.PositiveContext.
Require Import Crypto.Compilers.Z.Named.DeadCodeElimination.
Require Import Crypto.Compilers.Named.DeadCodeEliminationInterp.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Named.Syntax.

Section language.
  Context {interp_base_type : base_type -> Type}
          {interp_op : forall s d, op s d -> interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d}
          {Name : Type}
          {InContext : Context Name (fun _ : base_type => positive)}
          {InContextOk : ContextOk InContext}
          {Name_beq : Name -> Name -> bool}
          {InterpContext : Context Name interp_base_type}
          {InterpContextOk : ContextOk InterpContext}
          (Name_bl : forall n1 n2, Name_beq n1 n2 = true -> n1 = n2)
          (Name_lb : forall n1 n2, n1 = n2 -> Name_beq n1 n2 = true).

  Local Notation EliminateDeadCode := (@EliminateDeadCode Name InContext).
  Local Notation PContext var := (@PositiveContext base_type var base_type_beq internal_base_type_dec_bl).

  Lemma interp_EliminateDeadCode
        t e new_names
        (ctxi_interp : PContext _)
        (ctxr_interp : InterpContext)
        eout v1 v2 x
    : @EliminateDeadCode t e new_names = Some eout
      -> interp (interp_op:=interp_op) (ctx:=ctxr_interp) eout x = Some v1
      -> interp (interp_op:=interp_op) (ctx:=ctxi_interp) e x = Some v2
      -> v1 = v2.
  Proof using InContextOk InterpContextOk Name_bl Name_lb.
    eapply interp_EliminateDeadCode; eauto using internal_base_type_dec_lb.
  Qed.

  Lemma InterpEliminateDeadCode
        t e new_names
        eout
        v1 v2 x
    : @EliminateDeadCode t e new_names = Some eout
      -> Interp (Context:=InterpContext) (interp_op:=interp_op) eout x = Some v1
      -> Interp (Context:=PContext _) (interp_op:=interp_op) e x = Some v2
      -> v1 = v2.
  Proof using InContextOk InterpContextOk Name_bl Name_lb.
    apply interp_EliminateDeadCode.
  Qed.
End language.
