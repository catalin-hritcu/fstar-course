module StackClientBad

open Stack

let main () =
  let s0 = empty in
  let s1 = push 3 s0 in
  2 :: s1
