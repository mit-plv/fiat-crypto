From Coq Require Import List.
From Coq Require Import Ascii.
From Coq Require Import String.
Require Crypto.Util.Strings.String.
Require Import Crypto.CLI.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope string_scope.

Inductive trace : Set :=
| finished
| err (msg : list string)
| read_stdin (k : list string -> trace)
| write_stdout (msg : list string) (k : trace)
| write_stderr (msg : list string) (k : trace)
| read_file (name : string) (k : list string -> trace)
| write_file (name : string) (contents : list string) (k : trace)
.

Definition IODriverTrace : ForExtraction.IODriverAPI trace
  := {| ForExtraction.error := err
     ; ForExtraction.ret := fun 'tt => finished
     ; ForExtraction.with_read_stdin := read_stdin
     ; ForExtraction.write_stdout_then msg k := write_stdout msg (k tt)
     ; ForExtraction.write_stderr_then msg k := write_stderr msg (k tt)
     ; ForExtraction.with_read_file := read_file
     ; ForExtraction.write_file_then name contents k := write_file name contents (k tt)
     |}.

Fixpoint fuse_stdout_stderr (ls : list (list string + list string)) : list string
  := match ls with
     | [] => []
     | inl msg :: ls | inr msg :: ls => msg ++ fuse_stdout_stderr ls
     end%list.

Fixpoint split_stdout_stderr (ls : list (list string + list string)) : list string * list string
  := match ls with
     | [] => ([], [])
     | inl stdout :: ls
       => let '(stdouts, stderrs) := split_stdout_stderr ls in
          (stdout ++ stdouts, stderrs)
     | inr stderr :: ls
       => let '(stdouts, stderrs) := split_stdout_stderr ls in
          (stdouts, stderr ++ stderrs)
     end%list.

Fixpoint eval' {A} (t : trace) (stdin : list (list string)) (files : list (string * list string)) (fuse_stdout_stderr : list (list string + list string) -> A) (stdout_stderr_r_acc : list (list string + list string)) (new_files : list (string * list string)) : option (list string) (* return *) * A (* stdout / stderr *) * list (string * list string) (* new files *)
  := match t with
     | finished
       => (None, fuse_stdout_stderr (List.rev' stdout_stderr_r_acc), new_files)
     | err msg
       => (Some msg, fuse_stdout_stderr (List.rev' stdout_stderr_r_acc), new_files)
     | read_stdin k
       => let '(inp, stdin) := match stdin with
                               | inp :: stdin => (inp, stdin)
                               | [] => ([], [])
                               end in
          eval' (k inp) stdin files fuse_stdout_stderr stdout_stderr_r_acc new_files
     | write_stdout msg k
       => eval' k stdin files fuse_stdout_stderr (inl msg :: stdout_stderr_r_acc) new_files
     | write_stderr msg k
       => eval' k stdin files fuse_stdout_stderr (inr msg :: stdout_stderr_r_acc) new_files
     | read_file name k
       => let contents := match List.find (fun '(fname, contents) => (fname =? name)%string) (new_files ++ files) with
                          | Some (_, contents) => contents
                          | None => []
                          end in
          eval' (k contents) stdin files fuse_stdout_stderr stdout_stderr_r_acc new_files
     | write_file name contents k
       => eval' k stdin files fuse_stdout_stderr stdout_stderr_r_acc ((name, contents) :: new_files)
     end.
Definition eval_trace {A} (t : trace) (stdin : list (list string)) (files : list (string * list string)) (fuse_stdout_stderr : list (list string + list string) -> A) : option (list string) (* return *) * A (* stdout / stderr *) * list (string * list string) (* new files *)
  := eval' t stdin files fuse_stdout_stderr [] [].
