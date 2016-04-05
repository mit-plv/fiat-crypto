Require Export String List Logic.
Require Export Bedrock.Word.

Require Import ZArith NArith NPeano.
Require Import Coq.Structures.OrderedTypeEx.
Require Import FMapAVL FMapList.
Require Import JMeq.

Require Import QhasmUtil QhasmCommon.

(* There's a lot in here.
   We don't want to automatically give it all to the client. *)

Module State.
    Import ListNotations.
    Import Util.

    Module NatM := FMapAVL.Make(Nat_as_OT).
    Definition DefMap: Type := NatM.t N.
    Definition StateMap: Type := NatM.t DefMap.
    Definition LabelMap: Type := NatM.t nat.

    Delimit Scope state_scope with state.
    Local Open Scope state_scope.

    (* Sugar and Tactics *)

    Definition convert {A B: Type} (x: A) (H: A = B): B :=
    eq_rect A (fun B0 : Type => B0) x B H.

    Notation "'always' A" := (fun _ => A) (at level 90) : state_scope.
    Notation "'cast' e" := (convert e _) (at level 20) : state_scope.
    Notation "'lift' e" := (exist _ e _) (at level 20) : state_scope.
    Notation "'contra'" := (False_rec _ _) : state_scope.

    Obligation Tactic := abstract intuition.

    (* The Big Definition *)

    Inductive State :=
      | fullState (regState: StateMap) (stackState: DefMap): State.

    Definition emptyState: State := fullState (NatM.empty DefMap) (NatM.empty N).

    (* Register State Manipulations *)

    Definition getReg {n} (reg: Reg n) (state: State): option (word n) :=
      match state with
      | fullState regState stackState =>
        match (NatM.find n regState) with
        | Some map =>
            match (NatM.find (getRegIndex reg) map) with
            | Some m => Some (NToWord n m)
            | _ => None
            end
        | None => None
        end
      end.

    Definition setReg {n} (reg: Reg n) (value: word n) (state: State): option State :=
      match state with
      | fullState regState stackState =>
        match (NatM.find n regState) with
        | Some map =>
            Some (fullState
                    (NatM.add n (NatM.add (getRegIndex reg) (wordToN value) map) regState)
                    stackState)
        | None => None
        end
      end.

    (* Per-word Stack Operations *)

    Definition getStack32 (entry: Stack 32) (state: State): option (word 32) :=
      match state with
      | fullState regState stackState =>
        match entry with
        | stack32 loc =>
          match (NatM.find loc stackState) with
          | Some n => Some (NToWord 32 n)
          | _ => None
          end
        end
      end.

    Definition setStack32 (entry: Stack 32) (value: word 32) (state: State): option State :=
    match state with
    | fullState regState stackState =>
        match entry with
        | stack32 loc =>
        (Some (fullState regState
              (NatM.add loc (wordToN value) stackState)))
        end
    end.

    (* Inductive Word Manipulations*)

    Definition getWords' {n} (st: (list (word 32)) * word (32 * n)) :
        Either (list (word 32)) ((list (word 32)) * word (32 * (n - 1))).

      destruct (Nat.eq_dec n 0) as [H | H];
        destruct st as [lst w].

    - refine (xleft _ _ lst).

    - refine (xright _ _
             (cons (split1 32 (32 * (n - 1)) (cast w)) lst,
             (split2 32 (32 * (n - 1)) (cast w))));
      intuition.
    Defined.

    Section GetWords.
      Program Fixpoint getWords'_iter (n: nat) (st: (list (word 32)) * word (32 * n)): list (word 32) :=
        match n with
        | O => fst st
        | S m =>
            match (getWords' st) with
            | xleft lst => lst
            | xright st => cast (getWords'_iter m st)
            end
        end.

      Definition getWords {len} (wd: word (32 * len)): list (word 32) :=
        getWords'_iter len ([], wd).
    End GetWords.

    Section JoinWords.

        Inductive Any (U: nat -> Type) (lim: nat) := | any: forall n, (n <= lim)%nat -> U n -> Any U lim.

        Definition getAnySize {U lim} (a: Any U lim) :=
          match a as a' return a = a' -> _ with
          | any n p v => fun _ => n
          end (eq_refl a).

        Lemma lim_prop: forall (n lim: nat), (n <= lim)%nat -> ((n - 1) <= lim)%nat.
        Proof. intros; intuition. Qed.

        Lemma zero_prop: forall (n m: nat), n = S m -> n <> 0.
        Proof. intros; intuition. Qed.

        Fixpoint anyExp {U: nat -> Type}
            {lim: nat}
            (f: forall n, (n <> 0)%nat -> (n <= lim)%nat -> U n -> U (n - 1))
            (rem: nat)
            (cur: Any U lim): option {a: Any U lim | getAnySize a = 0}.

          refine match rem with
          | O => None
          | S rem' =>
            match cur as c' return cur = c' -> _ with
            | any n p v => always
              match (Nat.eq_dec n 0) with
              | left peq => Some (lift cur)
              | right pneq =>
                anyExp U lim f rem' (any U lim (n - 1) (lim_prop n lim p) (f n pneq p v))
              end
            end (eq_refl cur)
          end.

          subst; unfold getAnySize; intuition.

        Defined.

        Definition JoinWordType (len: nat): nat -> Type := fun n => option (word (32 * (len - n))).

        Definition joinWordUpdate (len: nat) (wds: list (option (word 32))):
            forall n, (n <> 0)%nat -> (n <= len)%nat -> JoinWordType len n -> JoinWordType len (n - 1).

          intros n H0 Hlen v; unfold JoinWordType in v.
          refine match v with
            | Some cur =>
              match (nth_error wds n) with
              | Some (Some w) => Some (cast (combine w cur))
              | _ => None
              end
            | _ => None
            end.

          abstract (replace (32 + 32 * (len - n)) with (32 * (len - (n - 1))); intuition).
        Defined.

        Definition joinWordOpts (wds: list (option (word 32))): option (word (32 * (length wds))).
          refine (
            let len := (length wds) in
            let start := (any (JoinWordType len) len len _ (cast (Some (wzero 0)))) in
            let aopt := anyExp (cast (joinWordUpdate len wds)) (length wds) start in
            match aopt as aopt' return aopt = aopt' -> _ with
            | Some a => always
              match (proj1_sig a) as a' return (proj1_sig a) = a' -> _ with
              | any n p v => always (cast v)
              end (eq_refl (proj1_sig a))
            | _ => always None
            end (eq_refl aopt)
          ); try abstract intuition.

          - abstract ( unfold JoinWordType; replace (32 * (len-len)) with 0; intuition).

          - destruct a; simpl in _H0; destruct x, aopt.

            + abstract (
                destruct s; unfold getAnySize in e; simpl in e; subst;
                inversion _H0;
                unfold JoinWordType;
                replace (len - 0) with len by intuition;
                unfold len; intuition ).

            + inversion _H.
        Defined.

    End JoinWords.

    (* Stack Manipulations *)

    Fixpoint getStack_iter (rem: nat) (loc: nat) (state: State): list (option (word 32)) :=
      match rem with
      | O => []
      | (S rem') =>
        (getStack32 (stack32 loc) state) ::
        (getStack_iter rem' (loc + 32) state)
    end.

    Lemma getStack_iter_length: forall rem loc state,
        length (getStack_iter rem loc state) = rem.
    Proof.
      induction rem; intuition.

      replace (getStack_iter (S rem) loc state) with 
        ((getStack32 (stack32 loc) state) ::
        (getStack_iter rem (loc + 32) state)) by intuition.

      replace (Datatypes.length _) with
        (1 + Datatypes.length (getStack_iter rem (loc + 32) state)) by intuition.

      rewrite IHrem; intuition.
    Qed.

    Definition getStack {n} (entry: Stack n) (state: State) : option (word n).

      refine (
        let m := getStackWords entry in
        let i := getStackIndex entry in
        let wos := (getStack_iter m i state) in
        let joined := (joinWordOpts wos) in

        match joined as j return j = joined -> _ with
        | Some w => always Some (cast w)
        | None => always None
        end (eq_refl joined)
      ); abstract (
        intuition;
        unfold wos;
        rewrite getStack_iter_length;
        destruct entry; simpl; intuition).

    Defined.

    Definition setStack {n} (entry: Stack n) (value: word n) (state: State) : option State :=
      (fix setStack_iter (wds: list (word 32)) (nextLoc: nat) (state: State) :=
        match wds with
        | [] => Some state
        | w :: ws =>
        match (setStack32 (stack32 nextLoc) w state) with 
        | Some st' => setStack_iter ws (S nextLoc) st'
        | None => None
        end
        end) (getWords (segmentStackWord entry value)) (getStackIndex entry) state.

End State.
