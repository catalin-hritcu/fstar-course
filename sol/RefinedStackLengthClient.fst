module RefinedStackLengthClient

open RefinedStackLength

let main() : Tot stack =
  let s = push 1 (push 2 (push 3 empty)) in
  let t = top s in
  let s' = pop s in
  pop s'
