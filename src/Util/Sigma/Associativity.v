(** * Reassociation of [sig] *)
Definition sig_sig_assoc {A} {P : A -> Prop} {Q}
  : { a : A | P a /\ Q a } -> { ap : { a : A | P a } | Q (proj1_sig ap) }
  := fun apq => exist _ (exist _ (proj1_sig apq) (proj1 (proj2_sig apq))) (proj2 (proj2_sig apq)).
Ltac sig_sig_assoc :=
  lazymatch goal with
  | [ |- { a : ?A | ?P } ]
    => let P'' := fresh a in
       let P' := fresh P'' in
       let term := constr:(fun a : A => match P with
                                        | P' => ltac:(let v := (eval cbv [P'] in P') in
                                                      lazymatch eval pattern (proj1_sig a) in v with
                                                      | ?P _ => exact P
                                                      end)
                                        end) in
       let Q := lazymatch (eval cbv beta in term) with fun _ => ?term => term end in
       apply (@sig_sig_assoc _ _ Q)
  end.
