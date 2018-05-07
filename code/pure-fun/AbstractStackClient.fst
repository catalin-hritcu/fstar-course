module AbstractStackClient

open AbstractStack

let main() : Tot stack =
  let s = push 1 (push 2 (push 3 empty)) in
  let t = top s in
  (* top_push 1 (push 2 (push 3 empty)); *)
  assert (t = 1);
  let s' = pop s in
  (* pop_push 1 (push 2 (push 3 empty)); *)
  pop s'
