Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion literal (z : Z) : expr := expr.literal z.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.
Local Coercion name_of_func (f : function) := fst f.

Definition hello_str : func := let i := "i" in let out := "out" in
  ("hello_str", ([out], [], bedrock_func_body:(
    i = coq:(0);
    while (i < coq:(6)) {
      store(out + i, coq:(expr.inlinetable access_size.one (list_byte_of_string "hello ") i));
      i = i + coq:(1)
    }
  ))).

Definition init : func := let s := "s" in let write := "write" in let exit := "exit" in let d := "d" in
  let STDERR_FILENO := 1 in
  ("init", ([], [], bedrock_func_body:(
    stackalloc 8 as s {
      hello_str(s);
      io! d = write(STDERR_FILENO, s, coq:(6))
    };
    output! exit(coq:(42))
  ))).

Definition loop : func := ("loop", ([], [], cmd.skip)).
