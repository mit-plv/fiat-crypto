Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Relations.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.ContextProperties.
Require Import Crypto.Compilers.Named.ContextProperties.Tactics.
Require Import Crypto.Util.Decidable.

Section with_context.
  Context {base_type_code Name var} (Context : @Context base_type_code Name var)
          (base_type_code_dec : DecidableRel (@eq base_type_code))
          (Name_dec : DecidableRel (@eq Name))
          (ContextOk : ContextOk Context).

  Local Notation find_Name := (@find_Name base_type_code Name Name_dec).
  Local Notation find_Name_and_val := (@find_Name_and_val base_type_code Name base_type_code_dec Name_dec).

  Hint Rewrite (@find_Name_and_val_default_to_None _ base_type_code_dec _ Name_dec) using congruence : ctx_db.
  Hint Rewrite (@find_Name_and_val_different _ base_type_code_dec _ Name_dec) using assumption : ctx_db.
  Hint Rewrite (@find_Name_and_val_wrong_type _ base_type_code_dec _ Name_dec) using congruence : ctx_db.

  Lemma find_Name_and_val_flatten_binding_list
        {var' var'' t n T N V1 V2 v1 v2}
        (H1 : @find_Name_and_val var' t n T N V1 None = Some v1)
        (H2 : @find_Name_and_val var'' t n T N V2 None = Some v2)
    : List.In (existT (fun t => (var' t * var'' t)%type) t (v1, v2)) (Wf.flatten_binding_list V1 V2).
  Proof using Type.
    induction T;
      [ | | specialize (IHT1 (fst N) (fst V1) (fst V2));
            specialize (IHT2 (snd N) (snd V1) (snd V2)) ];
      repeat first [ find_Name_and_val_default_to_None_step
                   | rewrite List.in_app_iff
                   | t_step ].
  Qed.

  Lemma find_Name_SmartFlatTypeMapInterp2_None_iff {var' n f T V N}
    : @find_Name n (SmartFlatTypeMap f (t:=T) V)
                 (SmartFlatTypeMapInterp2 (var':=var') (fun _ _ (n' : Name) => n') V N) = None
      <-> find_Name n N = None.
  Proof using Type.
    split;
      (induction T;
       [ | | specialize (IHT1 (fst V) (fst N));
             specialize (IHT2 (snd V) (snd N)) ]);
      t.
  Qed.
  Hint Rewrite @find_Name_SmartFlatTypeMapInterp2_None_iff : ctx_db.
  Lemma find_Name_SmartFlatTypeMapInterp2_None {var' n f T V N}
    : @find_Name n (SmartFlatTypeMap f (t:=T) V)
                 (SmartFlatTypeMapInterp2 (var':=var') (fun _ _ (n' : Name) => n') V N) = None
      -> find_Name n N = None.
  Proof using Type. apply find_Name_SmartFlatTypeMapInterp2_None_iff. Qed.
  Hint Rewrite @find_Name_SmartFlatTypeMapInterp2_None using eassumption : ctx_db.
  Lemma find_Name_SmartFlatTypeMapInterp2_None' {var' n f T V N}
    : find_Name n N = None
      -> @find_Name n (SmartFlatTypeMap f (t:=T) V)
                    (SmartFlatTypeMapInterp2 (var':=var') (fun _ _ (n' : Name) => n') V N) = None.
  Proof using Type. apply find_Name_SmartFlatTypeMapInterp2_None_iff. Qed.
  Lemma find_Name_SmartFlatTypeMapInterp2_None_Some_wrong {var' n f T V N v}
    : @find_Name n (SmartFlatTypeMap f (t:=T) V)
                 (SmartFlatTypeMapInterp2 (var':=var') (fun _ _ (n' : Name) => n') V N) = None
      -> find_Name n N = Some v
      -> False.
  Proof using Type.
    intro; erewrite find_Name_SmartFlatTypeMapInterp2_None by eassumption; congruence.
  Qed.
  Local Hint Resolve @find_Name_SmartFlatTypeMapInterp2_None_Some_wrong.

  Lemma find_Name_SmartFlatTypeMapInterp2 {var' n f T V N}
    : @find_Name n (SmartFlatTypeMap f (t:=T) V)
                 (SmartFlatTypeMapInterp2 (var':=var') (fun _ _ (n' : Name) => n') V N)
      = match find_Name n N with
        | Some t' => match find_Name_and_val t' n N V None with
                     | Some v => Some (f t' v)
                     | None => None
                     end
        | None => None
        end.
  Proof using Type.
    induction T;
      [ | | specialize (IHT1 (fst V) (fst N));
            specialize (IHT2 (snd V) (snd N)) ].
    { t. }
    { t. }
    { repeat first [ fin_t_step
                   | inversion_step
                   | rewrite_lookupb_extendb_step
                   | misc_t_step
                   | refolder_t_step ].
      repeat match goal with
             | [ |- context[match @find_Name ?n ?T ?N with _ => _ end] ]
               => destruct (@find_Name n T N) eqn:?
             | [ H : context[match @find_Name ?n ?T ?N with _ => _ end] |- _ ]
               => destruct (@find_Name n T N) eqn:?
             end;
        repeat first [ fin_t_step
                     | rewriter_t_step
                     | fin_t_late_step ]. }
  Qed.

  Lemma find_Name_and_val__SmartFlatTypeMapInterp2__SmartFlatTypeMapUnInterp__Some_Some_alt
        {var' var'' var''' t b n f g T V N X v v'}
        (Hfg
         : forall (V : var' t) (X : var'' (f t V)) (H : f t V = f t b),
            g t b (eq_rect (f t V) var'' X (f t b) H) = g t V X)
    : @find_Name_and_val
           var'' (f t b) n (SmartFlatTypeMap f (t:=T) V)
           (SmartFlatTypeMapInterp2 (var':=var') (fun _ _ (n' : Name) => n') V N) X None = Some v
      -> @find_Name_and_val
           var''' t n T N (SmartFlatTypeMapUnInterp (f:=f) g X) None = Some v'
      -> g t b v = v'.
  Proof using Type.
    induction T;
      [ | | specialize (IHT1 (fst V) (fst N) (fst X));
            specialize (IHT2 (snd V) (snd N) (snd X)) ];
      repeat first [ find_Name_and_val_default_to_None_step
                   | t_step
                   | match goal with
                     | [ H : _ |- _ ]
                       => progress rewrite find_Name_and_val_different in H
                         by solve [ congruence
                                  | apply find_Name_SmartFlatTypeMapInterp2_None'; assumption ]
                     end ].
  Qed.

  Lemma find_Name_and_val__SmartFlatTypeMapInterp2__SmartFlatTypeMapUnInterp__Some_Some
        {var' var'' var''' t b n f g T V N X v v'}
    : @find_Name_and_val
           var'' (f t b) n (SmartFlatTypeMap f (t:=T) V)
           (SmartFlatTypeMapInterp2 (var':=var') (fun _ _ (n' : Name) => n') V N) X None = Some v
      -> @find_Name_and_val
           _ t n T N V None = Some b
      -> @find_Name_and_val
           var''' t n T N (SmartFlatTypeMapUnInterp (f:=f) g X) None = Some v'
      -> g t b v = v'.
  Proof using Type.
    induction T;
      [ | | specialize (IHT1 (fst V) (fst N) (fst X));
            specialize (IHT2 (snd V) (snd N) (snd X)) ];
      repeat first [ find_Name_and_val_default_to_None_step
                   | t_step
                   | match goal with
                     | [ H : _ |- _ ]
                       => progress rewrite find_Name_and_val_different in H
                         by solve [ congruence
                                  | apply find_Name_SmartFlatTypeMapInterp2_None'; assumption ]
                     end ].
  Qed.

  Lemma interp_flat_type_rel_pointwise__find_Name_and_val
        {var' var'' t n T N x y R v0 v1}
        (H0 : @find_Name_and_val var' t n T N x None = Some v0)
        (H1 : @find_Name_and_val var'' t n T N y None = Some v1)
        (HR : interp_flat_type_rel_pointwise R x y)
    : R _ v0 v1.
  Proof using Type.
    induction T;
      [ | | specialize (IHT1 (fst N) (fst x) (fst y));
            specialize (IHT2 (snd N) (snd x) (snd y)) ];
      repeat first [ find_Name_and_val_default_to_None_step
                   | t_step ].
  Qed.

  Lemma find_Name_and_val_SmartFlatTypeMapUnInterp2_Some_Some
        {var' var'' var''' f g}
        {T}
        {N : interp_flat_type (fun _ : base_type_code => Name) T}
        {B : interp_flat_type var' T}
        {V : interp_flat_type var'' (SmartFlatTypeMap (t:=T) f B)}
        {n : Name}
        {t : base_type_code}
        {v : var''' t}
        {b}
        {h} {i : forall v, var'' (f _ (h v))}
        (Hn : find_Name n N = Some t)
        (Hf : find_Name_and_val t n N (SmartFlatTypeMapUnInterp2 g V) None = Some v)
        (Hb : find_Name_and_val t n N B None = Some b)
        (Hig : forall B V,
               existT _ (h (g _ B V)) (i (g _ B V))
               = existT _ B V
                        :> { b : _ & var'' (f _ b)})
        (N' := SmartFlatTypeMapInterp2 (var'':=fun _ => Name) (f:=f) (fun _ _ n => n) _ N)
    : b = h v /\ find_Name_and_val (f t (h v)) n N' V None = Some (i v).
  Proof using Type.
    induction T;
      [ | | specialize (IHT1 (fst N) (fst B) (fst V));
            specialize (IHT2 (snd N) (snd B) (snd V)) ];
      repeat first [ find_Name_and_val_default_to_None_step
                   | lazymatch goal with
                     | [ H : context[find_Name ?n (@SmartFlatTypeMapInterp2 _ ?var' _ _ ?f _ ?T ?V ?N)] |- _ ]
                       => setoid_rewrite find_Name_SmartFlatTypeMapInterp2 in H
                     end
                   | t_step
                   | match goal with
                     | [ Hhg : forall B V, existT _ (?h (?g ?t B V)) _ = existT _ B _ |- context[?h (?g ?t ?B' ?V')] ]
                       => specialize (Hhg B' V'); generalize dependent (g t B' V')
                     end ].
  Qed.
End with_context.
