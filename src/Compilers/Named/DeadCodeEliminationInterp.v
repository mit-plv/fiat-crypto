Require Import Coq.PArith.BinPos.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.PositiveContext.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.RegisterAssignInterp.
Require Import Crypto.Compilers.Named.DeadCodeElimination.
Require Import Crypto.Util.Decidable.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {interp_base_type : base_type_code -> Type}
          {interp_op : forall s d, op s d -> interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d}
          {Name : Type}
          {InContext : Context Name (fun _ : base_type_code => BinNums.positive)}
          {InContextOk : ContextOk InContext}
          {Name_beq : Name -> Name -> bool}
          {InterpContext : Context Name interp_base_type}
          {InterpContextOk : ContextOk InterpContext}
          {base_type_code_beq : base_type_code -> base_type_code -> bool}
          (base_type_code_bl : forall t1 t2, base_type_code_beq t1 t2 = true -> t1 = t2)
          (base_type_code_lb : forall t1 t2, t1 = t2 -> base_type_code_beq t1 t2 = true)
          (Name_bl : forall n1 n2, Name_beq n1 n2 = true -> n1 = n2)
          (Name_lb : forall n1 n2, n1 = n2 -> Name_beq n1 n2 = true).

  Local Notation EliminateDeadCode := (@EliminateDeadCode base_type_code op Name _ base_type_code_bl InContext).
  Local Notation PContext var := (@PositiveContext base_type_code var base_type_code_beq base_type_code_bl).

  Local Instance Name_dec : DecidableRel (@eq Name)
    := dec_rel_of_bool_dec_rel Name_beq Name_bl Name_lb.
  Local Instance base_type_code_dec : DecidableRel (@eq base_type_code)
    := dec_rel_of_bool_dec_rel base_type_code_beq base_type_code_bl base_type_code_lb.

  Lemma interp_EliminateDeadCode
        t e new_names
        (ctxi_interp : PContext _)
        (ctxr_interp : InterpContext)
        eout v1 v2 x
    : @EliminateDeadCode t e new_names = Some eout
      -> interp (interp_op:=interp_op) (ctx:=ctxr_interp) eout x = Some v1
      -> interp (interp_op:=interp_op) (ctx:=ctxi_interp) e x = Some v2
      -> v1 = v2.
  Proof using InContextOk InterpContextOk Name_bl Name_lb base_type_code_lb.
    eapply @interp_register_reassign;
      first [ assumption
            | apply @PositiveContextOk; assumption
            | apply Peqb_true_eq
            | apply Pos.eqb_eq
            | exact _
            | intros *; rewrite !lookupb_empty by (try apply @PositiveContextOk; assumption);
              congruence ].
  Qed.

  Lemma InterpEliminateDeadCode
        t e new_names
        eout
        v1 v2 x
    : @EliminateDeadCode t e new_names = Some eout
      -> Interp (Context:=InterpContext) (interp_op:=interp_op) eout x = Some v1
      -> Interp (Context:=PContext _) (interp_op:=interp_op) e x = Some v2
      -> v1 = v2.
  Proof using InContextOk InterpContextOk Name_bl Name_lb base_type_code_lb.
    apply interp_EliminateDeadCode.
  Qed.
End language.
