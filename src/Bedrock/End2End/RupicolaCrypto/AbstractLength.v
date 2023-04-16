(* Tooling for simplifying expressions about the length of lists.
   Possibly a bit over-generalized at the moment, but  apply to other abstractions as a result.
 *)
From coqutil Require Import Datatypes.List Word.LittleEndianList.
From Coq Require Import Strings.String Lists.List micromega.Lia.
Require Import bedrock2.ArrayCasts.

Class Abstractable {C A : Type} (abstract : C -> A) (c : C) (a : A) : Prop :=
  Abstr {
      abstraction_sound : abstract c = a;
    }.

Definition abstr_hyp {C A : Type} (f : C -> A) c a : f c = a -> Abstractable f c a := Abstr _ _ _ _ _.
(* does not shelve, so should only last if an eqn is found *)
#[export] Hint Extern 10 (Abstractable _ _ _) => apply abstr_hyp : abstraction. 
#[global] Hint Extern 9 (Abstractable _ ?l _) => subst l : abstraction.

Arguments Abstr {C A}%type_scope {abstract}%function_scope {c} {a}.
                
Section Length.
  
  Local Open Scope nat.

  Import ListNotations.

  Section WithFV.
    Context (B : Type).

    
    #[refine]
      Instance abstr_combine {B'} l1 l2 llen1 llen2
      `{Abstractable _ _ (@length B) l1 llen1}
      `{Abstractable _ _ (@length B') l2 llen2}
      : Abstractable (@length _) (combine l1 l2) (Nat.min llen1 llen2) := Abstr _.
    Proof.
      rewrite (combine_length _ _).
      f_equal; apply abstraction_sound; assumption.
    Qed.

    Local Notation Abstractable := (Abstractable (@length B)).


    Instance abstr_nil : Abstractable [] 0 := Abstr eq_refl.
    
    #[refine]
    Instance abstr_cons e l llen `{Abstractable l llen} : Abstractable (e::l) (S llen) := Abstr _.
    Proof.
      simpl.
      eauto.
      f_equal.
      apply Abstractable0.
    Qed.
    
    #[refine]
      Instance abstr_app l1 llen1 l2 llen2 `{Abstractable l1 llen1} `{Abstractable l2 llen2}
      : Abstractable (l1++l2) (llen1 + llen2) := Abstr _.
    Proof.
      rewrite (app_length _ _).
      f_equal.
      - apply Abstractable0.
      - apply Abstractable1.
    Qed.

    #[refine]
      Instance abstr_skipn n l llen `{Abstractable l llen}
      : Abstractable (skipn n l) (llen - n) := Abstr _.
    Proof.
      rewrite (skipn_length _ _).
      f_equal.
      apply Abstractable0.
    Qed.

    #[refine]
      Instance abstr_firstn n l  llen `{Abstractable l llen}
      : Abstractable (firstn n l) (Nat.min n llen) := Abstr _.
    Proof.
      rewrite (firstn_length _ _).
      f_equal.
      apply Abstractable0.
    Qed.

    
    #[refine]
      Instance abstr_map {B'} (f : B' -> B) l llen `{AbstractLength.Abstractable _ _ (@length B') l llen}
      : Abstractable (map f l) llen := Abstr _.
    Proof.
      rewrite (map_length _ _).
      f_equal.
      apply H.
    Qed.
    
    
    #[refine]
      Instance abstr_upds i xs l llen `{Abstractable l llen}
      : Abstractable (upds l i xs) llen := Abstr _.
    Proof.
      rewrite (upds_length _ _).
      f_equal.
      apply Abstractable0.
    Qed.
    
    #[refine]
      Instance abstr_upd i x l llen `{Abstractable l llen}
      : Abstractable (upd l i x) llen := Abstr _.
    Proof.
      rewrite (upd_length _ _).
      f_equal.
      apply Abstractable0.
    Qed.
    
    #[refine]
      Instance abstr_chunk k (bs : list B) (_ : ~ k = 0) llen `{Abstractable bs llen}
      : AbstractLength.Abstractable (@length _) (chunk k bs)  (Nat.div_up llen k)  := Abstr _.
    Proof. rewrite length_chunk; auto.
      f_equal.
      apply Abstractable0.
    Qed.

  End WithFV.

  
    #[refine]
      Instance abstr_le_split n z : Abstractable (@length _) (le_split n z)  n := Abstr _.
    Proof.
      apply LittleEndianList.length_le_split.
    Qed.

    
    #[refine]
      Instance abstr_list_byte_of_string s strlen `{Abstractable _ _ String.length s strlen}
      : Abstractable (@length _) (list_byte_of_string s)  strlen := Abstr _.
    Proof.
      unfold list_byte_of_string.
      rewrite map_length.
      destruct H.
      revert strlen abstraction_sound0.
      induction s; simpl; intros; try congruence.
      erewrite IHs; eauto.
    Qed.

    
    Instance abstr_string_nil : Abstractable String.length EmptyString 0 := Abstr eq_refl.
    
    #[refine]
      Instance abstr_string_cons e l llen `{Abstractable _ _ String.length l llen}
      : Abstractable String.length (String e l) (S llen) := Abstr _.
    Proof.
      simpl.
      eauto.
      f_equal.
      apply H.
    Qed.


    (*TODO: bs2ws_length or bs2ws_length'?*)
    #[refine]
      Instance abstr_bs2ws width (word : Interface.word.word width)
      k (bs : list _) (_ : ~ k = 0) llen `{Abstractable _ _ (@length _) bs llen}
      : Abstractable (@length _) (bs2ws (word:=word) k bs)  (Nat.div_up llen k)  := Abstr _.
    Proof.
      rewrite bs2ws_length'; auto.
      f_equal.
      apply H.
    Qed.

    #[refine]
      Instance abstr_ws2bs width (word : Interface.word.word width)
      k (bs : list _) llen `{Abstractable _ _ (@length _) bs llen}
      : Abstractable (@length _) (ws2bs (word:=word) k bs)  (k*llen)  := Abstr _.
    Proof.
      rewrite ws2bs_length; auto.
      f_equal.
      apply H.
    Qed.
        
End Length.

#[export] Hint Extern 1 (Abstractable (@length _) (combine _ _) _) => apply abstr_combine;shelve : abstraction.

#[export] Hint Extern 1 (Abstractable (@length _) (chunk _ _) _) => apply abstr_chunk;shelve : abstraction.
#[export] Hint Extern 1 (Abstractable (@length _) (map _ _) _) => apply abstr_map;shelve : abstraction.
#[export] Hint Extern 1 (Abstractable (@length _) (upds _ _ _) _) => apply abstr_upds;shelve : abstraction.
#[export] Hint Extern 1 (Abstractable (@length _) (upd _ _ _) _) => apply abstr_upd;shelve : abstraction.
#[export] Hint Extern 1 (Abstractable (@length _) (firstn _ _) _) => apply abstr_firstn;shelve : abstraction.
#[export] Hint Extern 1 (Abstractable (@length _) (skipn _ _) _) => apply abstr_skipn;shelve : abstraction.
#[export] Hint Extern 1 (Abstractable (@length _) (_ ++ _) _) => apply abstr_app;shelve : abstraction.
#[export] Hint Extern 1 (Abstractable (@length _) (cons _ _) _) => apply abstr_cons;shelve : abstraction.
#[export] Hint Extern 1 (Abstractable (@length _) (@nil _) _) => apply abstr_nil : abstraction.

#[export] Hint Extern 1 (Abstractable (@length _) (le_split _ _) _) => apply abstr_le_split : abstraction.
#[export] Hint Extern 1 (Abstractable (@length _) (list_byte_of_string _) _) =>
  apply abstr_list_byte_of_string; shelve : abstraction.
#[export] Hint Extern 1 (Abstractable String.length (String _ _) _) => apply abstr_string_cons;shelve : abstraction.
#[export] Hint Extern 1 (Abstractable String.length EmptyString _) => apply abstr_string_nil : abstraction.


#[export] Hint Extern 1 (Abstractable (@length _) (bs2ws _ _) _) => apply abstr_bs2ws;shelve : abstraction.
#[export] Hint Extern 1 (Abstractable (@length _) (ws2bs _ _) _) => apply abstr_ws2bs;shelve : abstraction.

Ltac simplify_abstract_goal :=
  repeat (unshelve (progress typeclasses eauto with abstraction); shelve_unifiable).


Ltac abstract_at_fn f :=  
  lazymatch goal with
    |- context [f ?c] =>
      let x := open_constr:(_) in
      replace (f c) with x; [| apply (@abstraction_sound _ _ f c);  simplify_abstract_goal]
  end.



Ltac simplify_len :=
  progress multimatch goal with
    |- context [@length ?A ?c] =>
        let x := open_constr:(_) in
        replace (@length A c) with x;
        cycle 1;
        [ symmetry; eapply (@abstraction_sound _ _ (@length _) _);
          simplify_abstract_goal; first [apply Abstr; reflexivity | lia] |]
    end.
