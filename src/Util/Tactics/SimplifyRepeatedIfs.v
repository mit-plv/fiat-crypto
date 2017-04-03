Ltac simplify_repeated_ifs_step :=
  match goal with
  | [ |- context G[if ?b then ?x else ?y] ]
    => let x' := match x with
                 | context x'[b] => let x'' := context x'[true] in x''
                 end in
       let G' := context G[if b then x' else y] in
       cut G'; [ destruct b; exact (fun z => z) | cbv iota ]
  | [ |- context G[if ?b then ?x else ?y] ]
    => let y' := match y with
                 | context y'[b] => let y'' := context y'[false] in y''
                 end in
       let G' := context G[if b then x else y'] in
       cut G'; [ destruct b; exact (fun z => z) | cbv iota ]
  end.
Ltac simplify_repeated_ifs := repeat simplify_repeated_ifs_step.
