
open Result

let list_to_string s =
  let rec loop s n =
    match s with
      [] -> String.make n '?'
    | car :: cdr ->
      let result = loop cdr (n + 1) in
        Bytes.set result n car;
        result
    in loop s 0 ;;

print_string (list_to_string result) ;;
