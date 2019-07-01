module RefinedStackClient

open RefinedStack

[@(expect_failure [19])] (* Remove this attribute *)
let main() =
  let s0 : stack = empty in
  assert (is_empty s0);

  let s1 : stack = push 3 s0 in
  assert (~(is_empty s1));

  let s2 : stack = push 4 s1 in
  assert (~(is_empty s2));

  let i : int = top s2 in

  let s3 : stack = pop s2 in
  assert (s3 == s1)    (* <-- Reimplement RefinedStack to make this work *)
