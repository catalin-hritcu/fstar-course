module RefinedStackClient

open RefinedStack

let main() : Tot stack =
  let s = push 1 (push 2 (push 3 empty)) in
  let t = top s in
  let s' = pop s in s'
  (* pop s' -- Subtyping check failed;
       expected type (s:stack{~(is_empty s)}); got type stack *)
