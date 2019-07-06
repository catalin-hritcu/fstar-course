module RefinedStackLengthClient

open RefinedStackLength

let main() =
  let s0 = empty in
  assert (length s0 = 0);

  let s1 = push 3 s0 in
  assert (length s1 = 1);

  let s2 = push 4 s1 in
  assert (length s2 = 2);

  let i = top s2 in

  let s3 = pop s2 in
  assert (length s3 = 1);

  let s4 = pop s3 in (* <-- This works now *)
  assert (length s4 = 0)
