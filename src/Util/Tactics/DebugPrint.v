Ltac debuglevel := constr:(0%nat).

Ltac solve_debugfail tac :=
  solve [tac] ||
        ( let dbg := debuglevel in
          match dbg with
          | O => idtac
          | _ => match goal with |- ?G => idtac "couldn't prove" G end
          end;
          fail).

(** constr-based [idtac] *)
Class cidtac {T} (msg : T) := Build_cidtac : True.
Hint Extern 0 (cidtac ?msg) => idtac msg; exact I : typeclass_instances.
(** constr-based [idtac] *)
Class cidtac2 {T1 T2} (msg1 : T1) (msg2 : T2) := Build_cidtac2 : True.
Hint Extern 0 (cidtac2 ?msg1 ?msg2) => idtac msg1 msg2; exact I : typeclass_instances.
Class cidtac3 {T1 T2 T3} (msg1 : T1) (msg2 : T2) (msg3 : T3) := Build_cidtac3 : True.
Hint Extern 0 (cidtac3 ?msg1 ?msg2 ?msg3) => idtac msg1 msg2 msg3; exact I : typeclass_instances.

Class cfail {T} (msg : T) := Build_cfail : True.
Hint Extern 0 (cfail ?msg) => idtac "Error:" msg; exact I : typeclass_instances.
Class cfail2 {T1 T2} (msg1 : T1) (msg2 : T2) := Build_cfail2 : True.
Hint Extern 0 (cfail2 ?msg1 ?msg2) => idtac "Error:" msg1 msg2; exact I : typeclass_instances.
Class cfail3 {T1 T2 T3} (msg1 : T1) (msg2 : T2) (msg3 : T3) := Build_cfail3 : True.
Hint Extern 0 (cfail3 ?msg1 ?msg2 ?msg3) => idtac "Error:" msg1 msg2 msg3; exact I : typeclass_instances.

Ltac cidtac msg :=
  let dummy := match goal with
               | _ => idtac msg
               end in
  constr:(I).
Ltac cidtac2 msg1 msg2 :=
  let dummy := match goal with
               | _ => idtac msg1 msg2
               end in
  constr:(I).
Ltac cidtac3 msg1 msg2 msg3 :=
  let dummy := match goal with
               | _ => idtac msg1 msg2 msg3
               end in
  constr:(I).
Ltac cfail msg :=
  let dummy := match goal with
               | _ => idtac "Error:" msg
               end in
  constr:(I : I).
Ltac cfail2 msg1 msg2 :=
  let dummy := match goal with
               | _ => idtac "Error:" msg1 msg2
               end in
  constr:(I : I).
Ltac cfail3 msg1 msg2 msg3 :=
  let dummy := match goal with
               | _ => idtac "Error:" msg1 msg2 msg3
               end in
  constr:(I : I).

Ltac idtac_goal := lazymatch goal with |- ?G => idtac "Goal:" G end.
Ltac idtac_context :=
  try (repeat match goal with H : _ |- _ => revert H end;
       idtac_goal;
       lazymatch goal with |- ?G => idtac "Context:" G end;
       fail).
