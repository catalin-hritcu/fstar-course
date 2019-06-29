module RefinedStackClient

open RefinedStack

let main() =
  let s0 = empty (* <: stack *) in

  assert (is_empty s0);

  let s1 = push 3 s0 (* <: stack *) in
  assert (~(is_empty s1));

  let s2 = push 4 s1 (* <: stack *) in
  assert (~(is_empty s2));

  let i = top s2 (* <: int *) in
  assert (i = 4);

  let s3 = pop s2 (* <: stack *) in
  assert (s3 == s1)
