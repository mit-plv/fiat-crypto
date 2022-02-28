Require Import Coq.Lists.List.
Require Export Crypto.Util.FixCoqMistakes.
Import ListNotations.
Local Open Scope list_scope.

Module List.
  Definition combine_extend {A} {B}
    := fix combine_extend (defaultA : A) (defaultB : B) (l : list A) (l' : list B) {struct l} : list (A * B)
      := match l, l' with
         | [], [] => []
         | [], _ => List.map (fun y => (defaultA, y)) l'
         | _, [] => List.map (fun x => (x, defaultB)) l
         | x :: tl, y :: tl' => (x, y) :: combine_extend x y tl tl'
         end.
End List.
